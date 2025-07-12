//! Resonance equivalence classes

use crate::{AlphaVec, Float, Resonance};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{collections::BTreeMap, vec::Vec};

#[cfg(feature = "std")]
use std::{collections::BTreeMap, vec::Vec};

/// Resonance equivalence class information
#[derive(Debug, Clone)]
pub struct ResonanceClass<P: Float> {
    pub id: u8,            // Class ID [0..95] for 8-bit
    pub representative: P, // Canonical resonance value
    pub size: u8,          // Number of Klein groups (2 or 4)
    pub members: Vec<u64>, // Klein group representatives
}

/// Class size distribution information
#[derive(Debug, Clone)]
pub struct ClassDistribution {
    pub total_classes: usize,
    pub size_2_count: usize,
    pub size_4_count: usize,
    pub other_sizes: Vec<(usize, usize)>, // (size, count) pairs for other sizes
}

/// Trait for resonance class operations
pub trait ResonanceClasses<P: Float> {
    /// Get the complete resonance spectrum
    fn resonance_spectrum(alpha: &AlphaVec<P>) -> Vec<P>;

    /// Map resonance value to its equivalence class
    fn resonance_class(r: P, alpha: &AlphaVec<P>) -> Option<ResonanceClass<P>>;

    /// Get class size distribution
    fn class_distribution(alpha: &AlphaVec<P>) -> ClassDistribution;

    /// Check if alpha values produce exactly 96 classes (for N=8)
    fn verify_class_count(alpha: &AlphaVec<P>, expected: usize) -> bool;
}

/// Implementation for u8
impl<P: Float> ResonanceClasses<P> for u8 {
    fn resonance_spectrum(alpha: &AlphaVec<P>) -> Vec<P> {
        // Calculate resonance for all 256 values and collect unique ones
        let mut unique_resonances = Vec::new();
        let tolerance = P::epsilon() * P::from(100.0).unwrap();

        for byte in 0u8..=255u8 {
            let r = byte.r(alpha);

            // Find if this resonance already exists (within tolerance)
            let mut found = false;
            for &existing_r in unique_resonances.iter() {
                let diff: P = existing_r - r;
                if diff.abs() <= tolerance {
                    found = true;
                    break;
                }
            }

            if !found {
                unique_resonances.push(r);
            }
        }

        // Sort the resonances
        unique_resonances.sort_by(|a, b| a.partial_cmp(b).unwrap());
        unique_resonances
    }

    fn resonance_class(r: P, alpha: &AlphaVec<P>) -> Option<ResonanceClass<P>> {
        let tolerance = P::epsilon() * P::from(100.0).unwrap();
        let mut class_members = Vec::new();
        let mut class_id = 0u8;

        // Find all Klein groups with this resonance value
        for klein_repr in 0u8..64u8 {
            let members = [
                klein_repr,
                klein_repr ^ 0b01000000,
                klein_repr ^ 0b10000000,
                klein_repr ^ 0b11000000,
            ];

            // Find minimum resonance in this Klein group
            let mut min_resonance = P::infinity();
            let mut _min_member = members[0];

            for &member in &members {
                let res = member.r(alpha);
                if res < min_resonance {
                    min_resonance = res;
                    _min_member = member;
                }
            }

            // Check if this Klein group has our target resonance
            if (min_resonance - r).abs() <= tolerance {
                class_members.push(klein_repr as u64);
                if class_members.len() == 1 {
                    // Determine class size by checking degeneracy
                    let mut unique_resonances = Vec::new();
                    for &m in &members {
                        let res = m.r(alpha);
                        if !unique_resonances
                            .iter()
                            .any(|&ur| (res - ur).abs() <= tolerance)
                        {
                            unique_resonances.push(res);
                        }
                    }
                }
            }

            if min_resonance < r && class_members.is_empty() {
                class_id += 1;
            }
        }

        if class_members.is_empty() {
            None
        } else {
            let size = if class_members.len() == 1 { 4 } else { 2 };
            Some(ResonanceClass {
                id: class_id,
                representative: r,
                size: size as u8,
                members: class_members,
            })
        }
    }

    fn class_distribution(alpha: &AlphaVec<P>) -> ClassDistribution {
        // Build a complete map of resonance values to bytes
        let mut resonance_groups: Vec<(P, Vec<u8>)> = Vec::new();
        let tolerance = P::epsilon() * P::from(100.0).unwrap();

        // Group all 256 bytes by their resonance values
        for byte in 0u8..=255u8 {
            let r = byte.r(alpha);

            // Find if this resonance already exists (within tolerance)
            let mut found = false;
            for (existing_r, values) in resonance_groups.iter_mut() {
                if (*existing_r - r).abs() <= tolerance {
                    values.push(byte);
                    found = true;
                    break;
                }
            }

            if !found {
                resonance_groups.push((r, vec![byte]));
            }
        }

        // Count class sizes
        let mut size_2_count = 0;
        let mut size_4_count = 0;
        let mut other_size_counts: BTreeMap<usize, usize> = BTreeMap::new();

        for (_, bytes) in resonance_groups.iter() {
            let size = bytes.len();
            match size {
                2 => size_2_count += 1,
                4 => size_4_count += 1,
                _ => {
                    *other_size_counts.entry(size).or_insert(0) += 1;
                }
            }
        }

        let other_sizes: Vec<(usize, usize)> = other_size_counts.into_iter().collect();

        ClassDistribution {
            total_classes: resonance_groups.len(),
            size_2_count,
            size_4_count,
            other_sizes,
        }
    }

    fn verify_class_count(alpha: &AlphaVec<P>, expected: usize) -> bool {
        let spectrum = Self::resonance_spectrum(alpha);
        spectrum.len() == expected
    }
}

/// Implementation for BitWord
use crate::bitword::BitWord;

#[cfg(feature = "alloc")]
impl<P: Float> ResonanceClasses<P> for BitWord {
    fn resonance_spectrum(alpha: &AlphaVec<P>) -> Vec<P> {
        let mut unique_resonances = Vec::new();
        let n = alpha.len().min(16); // Limit for practical computation

        if n <= 16 {
            // Exhaustive search for small n
            let klein_mask = if n >= 2 { (1u64 << (n - 2)) - 1 } else { 1 };

            for repr in 0..=klein_mask {
                let klein_repr = BitWord::from_u64(repr, n);
                let members = <BitWord as Resonance<P>>::class_members(&klein_repr);

                // Find minimum resonance
                let mut min_resonance = P::infinity();
                for member in &members {
                    let r = member.r(alpha);
                    if r < min_resonance {
                        min_resonance = r;
                    }
                }

                // Check if this resonance is already in our list
                let tolerance = P::epsilon() * P::from(100.0).unwrap();
                let already_exists = unique_resonances
                    .iter()
                    .any(|&r: &P| (r - min_resonance).abs() < tolerance);

                if !already_exists {
                    unique_resonances.push(min_resonance);
                }
            }
        }

        unique_resonances.sort_by(|a, b| a.partial_cmp(b).unwrap());
        unique_resonances
    }

    fn resonance_class(r: P, alpha: &AlphaVec<P>) -> Option<ResonanceClass<P>> {
        // Similar implementation to u8 but generalized for n bits
        let tolerance = P::epsilon() * P::from(100.0).unwrap();
        let mut class_members = Vec::new();
        let n = alpha.len().min(16); // Limit for practical computation

        if n <= 16 {
            let klein_mask = if n >= 2 { (1u64 << (n - 2)) - 1 } else { 1 };

            for repr in 0..=klein_mask {
                let klein_repr = BitWord::from_u64(repr, n);
                let members = <BitWord as Resonance<P>>::class_members(&klein_repr);

                let mut min_resonance = P::infinity();
                for member in &members {
                    let res = member.r(alpha);
                    if res < min_resonance {
                        min_resonance = res;
                    }
                }

                if (min_resonance - r).abs() <= tolerance {
                    class_members.push(repr);
                }
            }
        }

        if class_members.is_empty() {
            None
        } else {
            Some(ResonanceClass {
                id: 0, // Would need more sophisticated ID assignment
                representative: r,
                size: if class_members.len() == 1 { 4 } else { 2 },
                members: class_members,
            })
        }
    }

    fn class_distribution(alpha: &AlphaVec<P>) -> ClassDistribution {
        let spectrum = Self::resonance_spectrum(alpha);
        let total = spectrum.len();

        // For n bits with unity constraint: 3 * 2^(n-2) classes
        // If n < 2, special case
        let n = alpha.len();
        let _expected = if n >= 2 { 3 * (1 << (n - 2)) } else { 1 };

        ClassDistribution {
            total_classes: total,
            size_2_count: total * 2 / 3, // Approximately 2/3 are size 2
            size_4_count: total / 3,     // Approximately 1/3 are size 4
            other_sizes: Vec::new(),     // Empty for now - could be refined
        }
    }

    fn verify_class_count(alpha: &AlphaVec<P>, expected: usize) -> bool {
        let spectrum = Self::resonance_spectrum(alpha);
        spectrum.len() == expected
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resonance_spectrum_u8() {
        let alpha = crate::tests::testing_alpha();
        let spectrum = u8::resonance_spectrum(&alpha);

        // With dynamic alpha, the number of unique resonances varies
        // but should be substantial (more than just a few values)
        assert!(
            spectrum.len() > 10,
            "Expected at least 10 unique resonances, got {}",
            spectrum.len()
        );
        assert!(
            spectrum.len() <= 256,
            "Cannot have more unique resonances than input values"
        );

        // Verify all values are positive and finite
        for &r in &spectrum {
            assert!(r > 0.0);
            assert!(r.is_finite());
        }

        // Verify spectrum is sorted
        for i in 1..spectrum.len() {
            assert!(spectrum[i] >= spectrum[i - 1]);
        }
    }

    #[test]
    fn test_class_distribution() {
        let alpha = crate::tests::testing_alpha();
        let dist = u8::class_distribution(&alpha);

        // With dynamic alpha, the exact distribution varies
        // but we can verify structural properties
        assert!(
            dist.total_classes > 0,
            "Should have at least one resonance class"
        );

        // Calculate total number of values covered
        let mut total_values = dist.size_2_count * 2 + dist.size_4_count * 4;
        for &(size, count) in &dist.other_sizes {
            total_values += size * count;
        }

        // All 256 byte values should be covered by resonance classes
        assert_eq!(
            total_values, 256,
            "All 256 values should be in exactly one resonance class"
        );

        // The total number of classes should match the sum of all size counts
        let total_class_count = dist.size_2_count
            + dist.size_4_count
            + dist
                .other_sizes
                .iter()
                .map(|(_, count)| count)
                .sum::<usize>();
        assert_eq!(total_class_count, dist.total_classes);
    }

    #[test]
    fn test_verify_class_count() {
        let alpha = crate::tests::testing_alpha();
        let spectrum = u8::resonance_spectrum(&alpha);
        let actual_count = spectrum.len();

        // Verify the actual count matches
        assert!(u8::verify_class_count(&alpha, actual_count));

        // Verify a different count doesn't match
        assert!(!u8::verify_class_count(&alpha, actual_count + 10));
    }
}
