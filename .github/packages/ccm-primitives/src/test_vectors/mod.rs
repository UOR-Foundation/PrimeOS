//! Test vector generation and validation for CCM-BJC v1.0
//!
//! This module provides infrastructure for generating and validating
//! the official test vectors required by the CCM-BJC specification.

pub mod generator;
pub mod serialization;

use crate::{AlphaVec, BjcPacket, Float};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::vec::Vec;

#[cfg(feature = "std")]
use std::vec::Vec;

/// A single test vector containing input, expected output, and metadata
#[derive(Debug, Clone)]
pub struct TestVector<P: Float> {
    /// Bit length (n)
    pub n: u8,
    /// Input bit pattern as bytes (big-endian)
    pub input: Vec<u8>,
    /// Alpha vector used for encoding
    pub alpha: AlphaVec<P>,
    /// Page modulus k (power of 2)
    pub k: usize,
    /// Expected encoded packet
    pub expected_packet: BjcPacket,
    /// Description of this test case
    pub description: &'static str,
}

/// Collection of test vectors for a specific n value
#[derive(Debug)]
pub struct TestVectorSet<P: Float> {
    /// Bit length for this set
    pub n: u8,
    /// Alpha vector for this n
    pub alpha: AlphaVec<P>,
    /// Individual test vectors
    pub vectors: Vec<TestVector<P>>,
}

/// Binary format header for serialized test vectors
#[repr(C, packed)]
pub struct BinaryHeader {
    /// Magic bytes: "BJCT" (BJC Test)
    pub magic: [u8; 4],
    /// Version (1 for v1.0)
    pub version: u8,
    /// Number of different n values
    pub n_count: u8,
    /// Reserved for future use
    pub reserved: [u8; 2],
}

/// Binary format for a single test case
#[repr(C, packed)]
pub struct BinaryTestCase {
    /// Bit length n
    pub n: u8,
    /// Page modulus log2(k)
    pub log2_k: u8,
    /// Length of input data in bytes
    pub input_len: u16,
    /// Length of packet data in bytes
    pub packet_len: u16,
    // Followed by: input bytes, then packet bytes
}

/// Test vector categories for comprehensive coverage
#[derive(Debug, Clone, Copy)]
pub enum TestCategory {
    /// All zeros
    AllZeros,
    /// All ones
    AllOnes,
    /// Alternating bits (0xAA...)
    Alternating,
    /// Single bit set at position i
    SingleBit(usize),
    /// Powers of 2
    PowerOfTwo(u32),
    /// Random pattern with specific seed
    Random(u64),
    /// Edge case for Klein group
    KleinEdge,
    /// Maximum resonance case
    MaxResonance,
    /// Minimum resonance case
    MinResonance,
}

impl TestCategory {
    /// Generate bit pattern for this category and given n
    pub fn generate_pattern(&self, n: usize) -> Vec<u8> {
        let bytes_needed = n.div_ceil(8);
        let mut result = vec![0u8; bytes_needed];

        match self {
            TestCategory::AllZeros => {
                // Already zeros
            }
            TestCategory::AllOnes => {
                result.fill(0xFF);
                // Mask off unused bits in last byte
                if n % 8 != 0 {
                    let mask = (1u8 << (n % 8)) - 1;
                    if let Some(last) = result.last_mut() {
                        *last &= mask;
                    }
                }
            }
            TestCategory::Alternating => {
                for (i, byte) in result.iter_mut().enumerate() {
                    *byte = if i % 2 == 0 { 0xAA } else { 0x55 };
                }
                // Mask off unused bits
                if n % 8 != 0 {
                    let mask = (1u8 << (n % 8)) - 1;
                    if let Some(last) = result.last_mut() {
                        *last &= mask;
                    }
                }
            }
            TestCategory::SingleBit(pos) => {
                if *pos < n {
                    let byte_idx = pos / 8;
                    let bit_idx = pos % 8;
                    if byte_idx < result.len() {
                        result[byte_idx] |= 1u8 << bit_idx;
                    }
                }
            }
            TestCategory::PowerOfTwo(power) => {
                let value = 1u64 << power;
                for (i, byte) in result.iter_mut().enumerate() {
                    if i < 8 {
                        *byte = ((value >> (i * 8)) & 0xFF) as u8;
                    }
                }
            }
            TestCategory::Random(seed) => {
                // Simple PRNG for reproducible patterns
                let mut state = *seed;
                for byte in &mut result {
                    state = state
                        .wrapping_mul(6364136223846793005)
                        .wrapping_add(1442695040888963407);
                    *byte = (state >> 32) as u8;
                }
                // Mask off unused bits
                if n % 8 != 0 {
                    let mask = (1u8 << (n % 8)) - 1;
                    if let Some(last) = result.last_mut() {
                        *last &= mask;
                    }
                }
            }
            TestCategory::KleinEdge => {
                // Set the last two bits (Klein group control bits)
                if n >= 2 {
                    let last_byte_idx = (n - 1) / 8;
                    if last_byte_idx < result.len() {
                        result[last_byte_idx] |= 0b11 << ((n - 2) % 8);
                    }
                }
            }
            TestCategory::MaxResonance => {
                // Pattern that maximizes resonance depends on alpha values
                // For now, use all ones
                result.fill(0xFF);
                if n % 8 != 0 {
                    let mask = (1u8 << (n % 8)) - 1;
                    if let Some(last) = result.last_mut() {
                        *last &= mask;
                    }
                }
            }
            TestCategory::MinResonance => {
                // Pattern that minimizes resonance
                // Typically all zeros or specific pattern based on alphas
                // Already zeros by default
            }
        }

        result
    }
}

/// Standard alpha vectors for different n values
pub mod standard_alphas {
    use crate::{AlphaVec, Float};

    /// Create standard alpha vector for n=3
    pub fn alpha_n3<P: Float>() -> AlphaVec<P> {
        // Minimal set with unity constraint
        AlphaVec::try_from(vec![
            P::from(1.618_033_988_749_895).unwrap(), // φ (golden ratio)
            P::from(std::f64::consts::E).unwrap(),   // e
            P::from(0.3678794411714423).unwrap(),    // 1/e (unity: e * 1/e = 1)
        ])
        .expect("Valid alpha for n=3")
    }

    /// Create standard alpha vector for n=4
    pub fn alpha_n4<P: Float>() -> AlphaVec<P> {
        AlphaVec::try_from(vec![
            P::from(2.0).unwrap(),
            P::from(std::f64::consts::SQRT_2).unwrap(), // √2
            P::from(std::f64::consts::PI).unwrap(),
            P::from(1.0 / std::f64::consts::PI).unwrap(), // 1/π (unity)
        ])
        .expect("Valid alpha for n=4")
    }

    /// Create standard alpha vector for n=8
    pub fn alpha_n8<P: Float + num_traits::FromPrimitive>() -> AlphaVec<P> {
        AlphaVec::for_bit_length(8).expect("Valid alpha for n=8")
    }

    /// Create standard alpha vector for n=10
    pub fn alpha_n10<P: Float>() -> AlphaVec<P> {
        AlphaVec::try_from(vec![
            P::from(std::f64::consts::E).unwrap(),
            P::from(1.8392867552141612).unwrap(), // Tribonacci
            P::from(1.618_033_988_749_895).unwrap(), // φ
            P::from(std::f64::consts::PI).unwrap(),
            P::from(3.0_f64.sqrt()).unwrap(), // √3
            P::from(2.0).unwrap(),
            P::from(2.0_f64.powf(1.0 / 3.0)).unwrap(), // ∛2
            P::from(std::f64::consts::SQRT_2).unwrap(), // √2
            P::from(std::f64::consts::FRAC_PI_2).unwrap(),
            P::from(std::f64::consts::FRAC_2_PI).unwrap(), // Unity
        ])
        .expect("Valid alpha for n=10")
    }

    /// Create standard alpha vector for n=16
    pub fn alpha_n16<P: Float>() -> AlphaVec<P> {
        AlphaVec::try_from(vec![
            P::from(std::f64::consts::E).unwrap(),
            P::from(1.8392867552141612).unwrap(),
            P::from(1.618_033_988_749_895).unwrap(),
            P::from(std::f64::consts::PI).unwrap(),
            P::from(3.0_f64.sqrt()).unwrap(),
            P::from(2.0).unwrap(),
            P::from(2.0_f64.powf(1.0 / 3.0)).unwrap(),
            P::from(std::f64::consts::SQRT_2).unwrap(),
            P::from(5.0_f64.sqrt()).unwrap(),     // √5
            P::from(2.0_f64.powf(0.25)).unwrap(), // ∜2
            P::from(7.0_f64.sqrt()).unwrap(),     // √7
            P::from(3.0).unwrap(),
            P::from(1.324_717_957_244_746).unwrap(), // Plastic number
            P::from(1.202_056_903_159_594).unwrap(), // Apéry's constant^(1/3)
            P::from(std::f64::consts::FRAC_PI_4).unwrap(),
            P::from(4.0 / std::f64::consts::PI).unwrap(), // Unity
        ])
        .expect("Valid alpha for n=16")
    }

    /// Create standard alpha vector for n=32
    pub fn alpha_n32<P: Float>() -> AlphaVec<P> {
        let mut values = vec![
            P::from(std::f64::consts::E).unwrap(),
            P::from(1.8392867552141612).unwrap(),
            P::from(1.618_033_988_749_895).unwrap(),
            P::from(std::f64::consts::PI).unwrap(),
            P::from(3.0_f64.sqrt()).unwrap(),
            P::from(2.0).unwrap(),
            P::from(2.0_f64.powf(1.0 / 3.0)).unwrap(),
            P::from(std::f64::consts::SQRT_2).unwrap(),
        ];

        // Add more mathematical constants
        for i in 0..22 {
            let val = match i {
                0 => 5.0_f64.sqrt(),                 // √5
                1 => 6.0_f64.sqrt(),                 // √6
                2 => 7.0_f64.sqrt(),                 // √7
                3 => 2.0 * std::f64::consts::SQRT_2, // 2√2
                4 => 3.0,
                5 => 10.0_f64.sqrt(),                       // √10
                6 => 2.0_f64.powf(0.25),                    // ∜2
                7 => 3.0_f64.powf(0.25),                    // ∜3
                8 => 5.0_f64.powf(0.25),                    // ∜5
                9 => 1.515_716_566_510_398,                 // ζ(3)^(1/3)
                10 => std::f64::consts::E.sqrt(),           // √e
                11 => std::f64::consts::PI.sqrt(),          // √π
                12 => std::f64::consts::E.powf(2.0 / 3.0),  // e^(2/3)
                13 => std::f64::consts::PI.powf(2.0 / 3.0), // π^(2/3)
                14 => 17.0_f64.sqrt().sqrt(),               // √(√17)
                15 => std::f64::consts::LN_10,              // ln(10)
                16 => (2.0 * std::f64::consts::PI).sqrt(),  // √(2π)
                17 => std::f64::consts::E.powf(std::f64::consts::PI / 4.0), // e^(π/4)
                18 => std::f64::consts::E,                  // e again for variety
                19 => (std::f64::consts::E * std::f64::consts::PI).sqrt(), // √(e*π)
                _ => 1.5,
            };
            values.push(P::from(val).unwrap());
        }

        // Last two must satisfy unity constraint
        values.push(P::from(std::f64::consts::FRAC_PI_6).unwrap());
        values.push(P::from(6.0 / std::f64::consts::PI).unwrap());

        AlphaVec::try_from(values).expect("Valid alpha for n=32")
    }

    /// Create standard alpha vector for n=64
    pub fn alpha_n64<P: Float>() -> AlphaVec<P> {
        let mut values = Vec::with_capacity(64);

        // Start with well-known constants
        values.extend_from_slice(&[
            P::from(std::f64::consts::E).unwrap(),
            P::from(std::f64::consts::PI).unwrap(),
            P::from(1.618_033_988_749_895).unwrap(), // φ
            P::from(1.8392867552141612).unwrap(),    // Tribonacci
        ]);

        // Add square roots
        for i in 2..20 {
            values.push(P::from((i as f64).sqrt()).unwrap());
        }

        // Add cube roots
        for i in 2..15 {
            values.push(P::from((i as f64).powf(1.0 / 3.0)).unwrap());
        }

        // Add some ratios and special values
        for i in 0..25 {
            let val = match i {
                0 => std::f64::consts::LN_2,
                1 => std::f64::consts::LN_10,
                2 => std::f64::consts::LOG2_E,
                3 => std::f64::consts::LOG10_E,
                4 => std::f64::consts::SQRT_2,
                5 => 1.202_056_903_159_594, // Apéry's constant
                6 => 1.324_717_957_244_746, // Plastic number
                7 => 2.0,                   // 2
                8 => (2.0 * std::f64::consts::PI).sqrt(), // √(2π)
                9 => 0.577_215_664_901_533, // Euler-Mascheroni
                10 => 1.282_427_129_100_623, // ζ(2)^(1/2)
                11 => std::f64::consts::E.sqrt(), // √e
                12 => std::f64::consts::PI.sqrt(), // √π
                13 => 2.685_452_001_065_306, // φ²
                14 => std::f64::consts::E.powf(0.25), // ∜e
                15 => std::f64::consts::PI.powf(0.25), // ∜π
                16 => std::f64::consts::LOG2_E, // log(e)/log(2)
                17 => std::f64::consts::LN_2, // ln(2)
                18 => std::f64::consts::LN_10, // ln(10)
                19 => std::f64::consts::FRAC_PI_2, // π/2
                20 => std::f64::consts::FRAC_PI_4, // π/4
                21 => std::f64::consts::FRAC_PI_6, // π/6
                22 => std::f64::consts::FRAC_PI_3, // π/3
                23 => 2.094_395_102_393_195, // 2π/3
                _ => 1.5 + (i as f64) * 0.1,
            };
            values.push(P::from(val).unwrap());
        }

        // Ensure we have exactly 64 values
        while values.len() < 62 {
            values.push(P::from(1.1 + (values.len() as f64) * 0.05).unwrap());
        }

        // Last two satisfy unity constraint
        values.push(P::from(std::f64::consts::FRAC_PI_8).unwrap());
        values.push(P::from(8.0 / std::f64::consts::PI).unwrap());

        AlphaVec::try_from(values).expect("Valid alpha for n=64")
    }

    /// Get standard alpha for any supported n
    pub fn get_standard_alpha<P: Float + num_traits::FromPrimitive>(n: u8) -> Option<AlphaVec<P>> {
        match n {
            3 => Some(alpha_n3()),
            4 => Some(alpha_n4()),
            8 => Some(alpha_n8()),
            10 => Some(alpha_n10()),
            16 => Some(alpha_n16()),
            32 => Some(alpha_n32()),
            64 => Some(alpha_n64()),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_standard_alphas_unity_constraint() {
        // Test all standard alpha vectors satisfy unity constraint
        for n in &[3u8, 4, 8, 10, 16, 32, 64] {
            let alpha = standard_alphas::get_standard_alpha::<f64>(*n)
                .expect(&format!("Should have alpha for n={}", n));

            let len = alpha.len();
            let product = alpha[len - 2] * alpha[len - 1];

            assert!(
                (product - 1.0).abs() < 1e-10,
                "Unity constraint failed for n={}: {} * {} = {}",
                n,
                alpha[len - 2],
                alpha[len - 1],
                product
            );
        }
    }

    #[test]
    fn test_pattern_generation() {
        // Test various pattern generation categories
        let categories = vec![
            TestCategory::AllZeros,
            TestCategory::AllOnes,
            TestCategory::Alternating,
            TestCategory::SingleBit(0),
            TestCategory::SingleBit(7),
            TestCategory::PowerOfTwo(3),
            TestCategory::Random(12345),
            TestCategory::KleinEdge,
        ];

        for cat in categories {
            let pattern = cat.generate_pattern(8);
            assert_eq!(pattern.len(), 1); // 8 bits = 1 byte

            match cat {
                TestCategory::AllZeros => assert_eq!(pattern[0], 0x00),
                TestCategory::AllOnes => assert_eq!(pattern[0], 0xFF),
                TestCategory::Alternating => assert_eq!(pattern[0], 0xAA),
                TestCategory::SingleBit(0) => assert_eq!(pattern[0], 0x01),
                TestCategory::SingleBit(7) => assert_eq!(pattern[0], 0x80),
                TestCategory::PowerOfTwo(3) => assert_eq!(pattern[0], 0x08),
                TestCategory::KleinEdge => assert_eq!(pattern[0] & 0xC0, 0xC0),
                _ => {} // Random patterns vary
            }
        }
    }
}
