//! Test vector generation for CCM-BJC conformance testing

use super::{TestCategory, TestVector, TestVectorSet};
use crate::{encode_bjc, AlphaVec, BitWord, Float, FloatEncoding};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::vec::Vec;

#[cfg(feature = "std")]
use std::vec::Vec;

/// Generate comprehensive test vectors for a given n
pub fn generate_test_vectors<P: Float + FloatEncoding>(
    n: u8,
    alpha: AlphaVec<P>,
) -> TestVectorSet<P> {
    let mut vectors = Vec::new();

    // Add edge cases
    vectors.extend(generate_edge_cases(n, &alpha));

    // Add systematic patterns
    vectors.extend(generate_systematic_patterns(n, &alpha));

    // For small n, add exhaustive coverage
    if n <= 8 {
        vectors.extend(generate_exhaustive(n, &alpha));
    }

    TestVectorSet { n, alpha, vectors }
}

/// Generate edge case test vectors
fn generate_edge_cases<P: Float + FloatEncoding>(n: u8, alpha: &AlphaVec<P>) -> Vec<TestVector<P>> {
    let mut vectors = Vec::new();

    let edge_cases = vec![
        (TestCategory::AllZeros, "All zeros"),
        (TestCategory::AllOnes, "All ones"),
        (TestCategory::Alternating, "Alternating bits (0xAA...)"),
        (
            TestCategory::KleinEdge,
            "Klein group edge (last 2 bits set)",
        ),
        (TestCategory::MinResonance, "Minimum resonance pattern"),
        (TestCategory::MaxResonance, "Maximum resonance pattern"),
    ];

    for (category, description) in edge_cases {
        if let Some(vec) = generate_single_vector(n, alpha, category, description) {
            vectors.push(vec);
        }
    }

    vectors
}

/// Generate systematic pattern test vectors
fn generate_systematic_patterns<P: Float + FloatEncoding>(
    n: u8,
    alpha: &AlphaVec<P>,
) -> Vec<TestVector<P>> {
    let mut vectors = Vec::new();

    // Single bit patterns
    for i in 0..n.min(16) {
        if let Some(vec) = generate_single_vector(
            n,
            alpha,
            TestCategory::SingleBit(i as usize),
            "Single bit pattern",
        ) {
            vectors.push(vec);
        }
    }

    // Powers of two
    for power in 0..n.min(8) {
        if let Some(vec) = generate_single_vector(
            n,
            alpha,
            TestCategory::PowerOfTwo(power as u32),
            "Power of 2 pattern",
        ) {
            vectors.push(vec);
        }
    }

    vectors
}

/// Generate exhaustive test vectors for small n
fn generate_exhaustive<P: Float + FloatEncoding>(n: u8, alpha: &AlphaVec<P>) -> Vec<TestVector<P>> {
    let mut vectors = Vec::new();

    if n > 16 {
        return vectors; // Too large for exhaustive
    }

    let max = 1u64 << n;
    for value in 0..max {
        let bytes = n.div_ceil(8);
        let mut input = vec![0u8; bytes as usize];

        // Convert value to bytes
        for i in 0..bytes {
            if i < 8 {
                input[i as usize] = ((value >> (i * 8)) & 0xFF) as u8;
            }
        }

        // Create test vector
        match n {
            3 => {
                let word = BitWord::<3>::from(input[0] & 0b111);
                if let Ok(packet) = encode_bjc(&word, alpha, 1, false) {
                    vectors.push(TestVector {
                        n,
                        input: vec![input[0] & 0b111],
                        alpha: alpha.clone(),
                        k: 1,
                        expected_packet: packet,
                        description: "Exhaustive coverage",
                    });
                }
            }
            4 => {
                let word = BitWord::<4>::from(input[0] & 0b1111);
                if let Ok(packet) = encode_bjc(&word, alpha, 1, false) {
                    vectors.push(TestVector {
                        n,
                        input: vec![input[0] & 0b1111],
                        alpha: alpha.clone(),
                        k: 1,
                        expected_packet: packet,
                        description: "Exhaustive coverage",
                    });
                }
            }
            8 => {
                let word = BitWord::<8>::from(input[0]);
                if let Ok(packet) = encode_bjc(&word, alpha, 1, false) {
                    vectors.push(TestVector {
                        n,
                        input: vec![input[0]],
                        alpha: alpha.clone(),
                        k: 1,
                        expected_packet: packet,
                        description: "Exhaustive coverage",
                    });
                }
            }
            _ => {} // Other sizes not implemented yet
        }
    }

    vectors
}

/// Generate a single test vector for a category
fn generate_single_vector<P: Float + FloatEncoding>(
    n: u8,
    alpha: &AlphaVec<P>,
    category: TestCategory,
    description: &'static str,
) -> Option<TestVector<P>> {
    let pattern = category.generate_pattern(n as usize);

    // Encode based on n value
    match n {
        3 => {
            let word = BitWord::<3>::from(pattern[0] & 0b111);
            encode_bjc(&word, alpha, 1, false)
                .ok()
                .map(|packet| TestVector {
                    n,
                    input: vec![pattern[0] & 0b111],
                    alpha: alpha.clone(),
                    k: 1,
                    expected_packet: packet,
                    description,
                })
        }
        4 => {
            let word = BitWord::<4>::from(pattern[0] & 0b1111);
            encode_bjc(&word, alpha, 1, false)
                .ok()
                .map(|packet| TestVector {
                    n,
                    input: vec![pattern[0] & 0b1111],
                    alpha: alpha.clone(),
                    k: 1,
                    expected_packet: packet,
                    description,
                })
        }
        8 => {
            let word = BitWord::<8>::from(pattern[0]);
            encode_bjc(&word, alpha, 1, false)
                .ok()
                .map(|packet| TestVector {
                    n,
                    input: pattern.clone(),
                    alpha: alpha.clone(),
                    k: 1,
                    expected_packet: packet,
                    description,
                })
        }
        10 => {
            let value =
                u16::from_le_bytes([pattern[0], pattern.get(1).copied().unwrap_or(0)]) & 0x3FF;
            let word = BitWord::<10>::from(value as u64);
            encode_bjc(&word, alpha, 1, false)
                .ok()
                .map(|packet| TestVector {
                    n,
                    input: vec![pattern[0], (pattern.get(1).copied().unwrap_or(0) & 0b11)],
                    alpha: alpha.clone(),
                    k: 1,
                    expected_packet: packet,
                    description,
                })
        }
        16 => {
            let value = u16::from_le_bytes([pattern[0], pattern.get(1).copied().unwrap_or(0)]);
            let word = BitWord::<16>::from(value as u64);
            encode_bjc(&word, alpha, 1, false)
                .ok()
                .map(|packet| TestVector {
                    n,
                    input: vec![pattern[0], pattern.get(1).copied().unwrap_or(0)],
                    alpha: alpha.clone(),
                    k: 1,
                    expected_packet: packet,
                    description,
                })
        }
        32 => {
            let value = u32::from_le_bytes([
                pattern[0],
                pattern.get(1).copied().unwrap_or(0),
                pattern.get(2).copied().unwrap_or(0),
                pattern.get(3).copied().unwrap_or(0),
            ]);
            let word = BitWord::<32>::from(value);
            encode_bjc(&word, alpha, 1, false)
                .ok()
                .map(|packet| TestVector {
                    n,
                    input: pattern[0..4].to_vec(),
                    alpha: alpha.clone(),
                    k: 1,
                    expected_packet: packet,
                    description,
                })
        }
        64 => {
            let value = u64::from_le_bytes([
                pattern[0],
                pattern.get(1).copied().unwrap_or(0),
                pattern.get(2).copied().unwrap_or(0),
                pattern.get(3).copied().unwrap_or(0),
                pattern.get(4).copied().unwrap_or(0),
                pattern.get(5).copied().unwrap_or(0),
                pattern.get(6).copied().unwrap_or(0),
                pattern.get(7).copied().unwrap_or(0),
            ]);
            let word = BitWord::<64>::from(value);
            encode_bjc(&word, alpha, 1, false)
                .ok()
                .map(|packet| TestVector {
                    n,
                    input: pattern[0..8].to_vec(),
                    alpha: alpha.clone(),
                    k: 1,
                    expected_packet: packet,
                    description,
                })
        }
        _ => None,
    }
}

/// Generate random test vectors
pub fn generate_random_vectors<P: Float + FloatEncoding>(
    n: u8,
    alpha: &AlphaVec<P>,
    count: usize,
    seed: u64,
) -> Vec<TestVector<P>> {
    let mut vectors = Vec::new();
    let mut rng_state = seed;

    for _i in 0..count {
        // Simple PRNG
        rng_state = rng_state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);

        if let Some(vec) = generate_single_vector(
            n,
            alpha,
            TestCategory::Random(rng_state),
            "Random test vector",
        ) {
            vectors.push(vec);
        }
    }

    vectors
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_vectors::standard_alphas;

    #[test]
    fn test_generator_n3() {
        let alpha = standard_alphas::alpha_n3::<f64>();
        let vectors = generate_test_vectors(3, alpha);

        // Should have edge cases + exhaustive (8 values)
        assert!(vectors.vectors.len() >= 8);

        // Verify all vectors are valid
        for vec in &vectors.vectors {
            assert_eq!(vec.n, 3);
            assert_eq!(vec.alpha.len(), 3);
        }
    }

    #[test]
    fn test_generator_n8() {
        let alpha = standard_alphas::alpha_n8::<f64>();
        let vectors = generate_test_vectors(8, alpha);

        // Should have edge cases + patterns + exhaustive (256 values)
        assert!(vectors.vectors.len() >= 256);
    }
}
