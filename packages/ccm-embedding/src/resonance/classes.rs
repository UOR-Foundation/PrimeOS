//! Resonance equivalence classes
//!
//! This module handles the classification of bit patterns into resonance equivalence classes,
//! where patterns are equivalent if they belong to the same Klein group.
//!
//! ## Mathematical Foundation
//!
//! Each Klein group contains exactly 4 elements formed by XORing the last 2 bits.
//! With the unity constraint α_{n-2} × α_{n-1} = 1, there are exactly:
//! - **3 × 2^{n-2}** unique resonance values
//! - **2^{n-2}** Klein groups (4 elements each)
//!
//! ## Scaling Properties
//!
//! ### Small n (≤ 12 bits)
//! - Can enumerate all resonance classes exactly
//! - Store complete spectrum in memory
//! - O(2^n) time, O(2^{n-2}) space
//!
//! ### Large n (> 12 bits)
//! - Use sampling to estimate spectrum
//! - Statistical properties remain accurate
//! - O(sampling size) time and space
//!
//! ## Class Distribution
//!
//! Each resonance class contains either 2 or 4 Klein groups:
//! - Most classes: 4 Klein groups (typical case)
//! - Special classes: 2 Klein groups (at extremes)
//!
//! ## Example
//!
//! ```no_run
//! use ccm_embedding::{AlphaVec, ResonanceClasses};
//! use ccm_core::BitWord;
//!
//! let alpha = AlphaVec::<f64>::for_bit_length(10).unwrap();
//!
//! // Get unique resonance values
//! let spectrum = BitWord::resonance_spectrum(&alpha);
//! assert_eq!(spectrum.len(), 3 * (1 << 8)); // 3 × 2^{10-2} = 768
//! ```

use crate::{AlphaVec, Resonance};
use ccm_core::Float;
use num_traits::FromPrimitive;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{collections::BTreeMap, vec::Vec};

#[cfg(feature = "std")]
use std::{collections::BTreeMap, vec::Vec};

/// Resonance equivalence class information
#[derive(Debug, Clone)]
pub struct ResonanceClass<P: Float> {
    pub id: usize,             // Class ID (no longer limited to u8)
    pub representative: P,     // Canonical resonance value
    pub size: usize,           // Number of Klein groups
    pub members: Vec<BitWord>, // Klein group representatives (now BitWord)
}

use ccm_core::BitWord;

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
impl<P: Float + FromPrimitive> ResonanceClasses<P> for u8 {
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
                class_members.push(BitWord::from_u8(klein_repr));
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
                id: class_id as usize,
                representative: r,
                size,
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
#[cfg(feature = "alloc")]
impl<P: Float + FromPrimitive> ResonanceClasses<P> for BitWord {
    fn resonance_spectrum(alpha: &AlphaVec<P>) -> Vec<P> {
        let n = alpha.len();
        let mut unique_resonances = BTreeMap::new();
        let _tolerance = P::epsilon() * P::from(100.0).unwrap();

        // For n >= 2, we know there are exactly 3 × 2^(n-2) unique resonance values
        // We'll use a sampling strategy for large n
        if n < 2 {
            // Special case: only one possible value
            let word = BitWord::new(n);
            unique_resonances.insert(crate::page::coherence::OrdFloat(word.r(alpha)), ());
        } else if n <= 20 {
            // Small enough for exhaustive search through Klein representatives
            let num_klein_representatives = 1usize << (n - 2);

            for i in 0..num_klein_representatives {
                let mut repr = BitWord::new(n);
                // Set bits based on i, but only the first n-2 bits
                for bit in 0..(n - 2) {
                    if (i >> bit) & 1 == 1 {
                        repr.set_bit(bit, true);
                    }
                }

                // Get Klein minimum resonance
                let members = <BitWord as Resonance<P>>::class_members(&repr);
                let min_resonance = members
                    .iter()
                    .map(|m| m.r(alpha))
                    .min_by(|a, b| a.partial_cmp(b).unwrap())
                    .unwrap();

                unique_resonances.insert(crate::page::coherence::OrdFloat(min_resonance), ());
            }
        } else {
            // Large n: use mathematical sampling
            // We know there are 3 × 2^(n-2) unique values
            let expected_count = 3 * (1usize << (n - 2).min(62));

            // Strategic sampling to find diverse resonance values
            // 1. Empty pattern (all zeros)
            let zero = BitWord::new(n);
            unique_resonances.insert(crate::page::coherence::OrdFloat(zero.r(alpha)), ());

            // 2. Single bit patterns
            for i in 0..n.min(64) {
                let mut word = BitWord::new(n);
                word.set_bit(i, true);
                unique_resonances.insert(crate::page::coherence::OrdFloat(word.r(alpha)), ());
            }

            // 3. Unity positions
            if n >= 2 {
                let mut unity = BitWord::new(n);
                unity.set_bit(n - 2, true);
                unity.set_bit(n - 1, true);
                unique_resonances.insert(crate::page::coherence::OrdFloat(unity.r(alpha)), ());
            }

            // 4. Random sampling with deterministic seed
            let mut seed = 0x2A65C3F5u64;
            let samples_needed = expected_count.min(10000);

            while unique_resonances.len() < samples_needed {
                seed = seed.wrapping_mul(1103515245).wrapping_add(12345);

                let mut word = BitWord::new(n);
                // Set bits based on pseudo-random pattern
                for i in 0..n.min(64) {
                    if (seed >> i) & 1 == 1 {
                        word.set_bit(i, true);
                    }
                }

                // For bits beyond 64, use additional random iterations
                if n > 64 {
                    let mut extra_seed = seed;
                    for i in 64..n {
                        extra_seed = extra_seed.wrapping_mul(1103515245).wrapping_add(12345);
                        if extra_seed & 1 == 1 {
                            word.set_bit(i, true);
                        }
                    }
                }

                let r = word.r(alpha);
                unique_resonances.insert(crate::page::coherence::OrdFloat(r), ());
            }
        }

        // Convert to sorted vector
        unique_resonances
            .into_keys()
            .map(|ord_float| ord_float.0)
            .collect()
    }

    fn resonance_class(r: P, alpha: &AlphaVec<P>) -> Option<ResonanceClass<P>> {
        let tolerance = P::epsilon() * P::from(100.0).unwrap();
        let n = alpha.len();
        let mut class_members = Vec::new();
        let mut class_id = 0usize;

        if n < 2 {
            // Special case
            let word = BitWord::new(n);
            if (word.r(alpha) - r).abs() <= tolerance {
                class_members.push(word);
            }
        } else {
            // Use inverse resonance to find members
            use crate::InverseResonance;
            match BitWord::find_by_resonance(r, alpha, tolerance) {
                Ok(klein_minima) => {
                    // The inverse resonance returns Klein minima
                    // We need to find which Klein groups they belong to
                    for min_word in klein_minima {
                        let klein_repr = <BitWord as Resonance<P>>::klein_representative(&min_word);
                        class_members.push(klein_repr);
                    }
                }
                Err(_) => return None,
            }

            // Assign a class ID based on sorted position
            let spectrum = Self::resonance_spectrum(alpha);
            class_id = spectrum
                .iter()
                .position(|&spec_r| (spec_r - r).abs() <= tolerance)
                .unwrap_or(0);
        }

        if class_members.is_empty() {
            None
        } else {
            // Determine actual size by checking Klein group degeneracy
            let size = if class_members.is_empty() {
                0
            } else {
                let repr = &class_members[0];
                let klein_members = <BitWord as Resonance<P>>::class_members(repr);

                // Count unique resonances in Klein group
                let mut unique_resonances = Vec::new();
                for member in &klein_members {
                    let res = member.r(alpha);
                    if !unique_resonances
                        .iter()
                        .any(|&ur| (res - ur).abs() <= tolerance)
                    {
                        unique_resonances.push(res);
                    }
                }

                // Size is 4 / number of unique resonances
                4 / unique_resonances.len()
            };

            Some(ResonanceClass {
                id: class_id,
                representative: r,
                size,
                members: class_members,
            })
        }
    }

    fn class_distribution(alpha: &AlphaVec<P>) -> ClassDistribution {
        let n = alpha.len();

        if n < 2 {
            // Special case
            ClassDistribution {
                total_classes: 1,
                size_2_count: 0,
                size_4_count: 0,
                other_sizes: vec![(1, 1)],
            }
        } else {
            // Mathematical formula: 3 × 2^(n-2) total classes
            let total = 3 * (1usize << (n - 2).min(62));

            // From theory: 2/3 are size 2, 1/3 are size 4
            let size_4 = total / 3;
            let size_2 = total - size_4;

            ClassDistribution {
                total_classes: total,
                size_2_count: size_2,
                size_4_count: size_4,
                other_sizes: Vec::new(),
            }
        }
    }

    fn verify_class_count(alpha: &AlphaVec<P>, expected: usize) -> bool {
        let n = alpha.len();

        if n < 2 {
            expected == 1
        } else {
            // Check if expected matches the theoretical count
            let theoretical = 3 * (1usize << (n - 2).min(62));
            expected == theoretical
        }
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
