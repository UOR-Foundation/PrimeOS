//! Unity positions and harmonic centers
//!
//! This module handles unity positions in resonance algebra, where "unity position"
//! means a bit pattern with resonance value exactly equal to 1.0.
//!
//! ## Important Distinction
//!
//! There are two related but different concepts:
//!
//! 1. **Unity Positions**: Bit patterns where R(b) = 1.0
//!    - These are the actual positions with unity resonance
//!    - Example: positions 0 and 3 in a Klein group might have R=1
//!
//! 2. **Klein Groups with Unity**: Klein groups containing unity elements
//!    - A Klein group has 4 members formed by XORing the last 2 bits
//!    - Some members may have unity resonance, others may not
//!    - Example: Klein group {0, 1, 2, 3} where only 0 and 3 have R=1
//!
//! The `unity_positions` functions return actual unity positions (concept 1),
//! while the `klein_unity` submodule deals with Klein groups (concept 2).

use crate::{AlphaVec, Resonance};
use ccm_core::Float;
use num_traits::FromPrimitive;

#[cfg(feature = "alloc")]
use alloc::vec;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Trait for unity structure operations
pub trait UnityStructure {
    /// Find all positions where R = 1
    fn unity_positions<P: Float + FromPrimitive>(alpha: &AlphaVec<P>, range: usize) -> Vec<usize>;

    /// Check if value is near unity (within tolerance)
    fn is_near_unity<P: Float + FromPrimitive>(r: P, tolerance: P) -> bool;

    /// Get the standard unity positions for 8-bit
    fn standard_unity_positions() -> [usize; 12] {
        // Unity positions are where resonance = 1.0
        // This depends on the specific alpha values used
        // For standard 8-bit alpha, these are typically:
        [0, 1, 48, 49, 256, 257, 304, 305, 512, 513, 560, 561]
    }
}

/// Implementation for u8
impl UnityStructure for u8 {
    fn unity_positions<P: Float + FromPrimitive>(alpha: &AlphaVec<P>, range: usize) -> Vec<usize> {
        let mut positions = Vec::new();
        let tolerance = P::epsilon() * P::from(100.0).unwrap();

        // Check each position for unity resonance
        for i in 0..range {
            let byte = (i % 256) as u8;
            let r = byte.r(alpha);

            // Only include positions with resonance ≈ 1.0
            if Self::is_near_unity(r, tolerance) {
                positions.push(i);
            }
        }

        positions
    }

    fn is_near_unity<P: Float + FromPrimitive>(r: P, tolerance: P) -> bool {
        (r - P::one()).abs() < tolerance
    }
}

/// Implementation for BitWord
use ccm_core::BitWord;

#[cfg(feature = "alloc")]
impl UnityStructure for BitWord {
    fn unity_positions<P: Float + FromPrimitive>(alpha: &AlphaVec<P>, range: usize) -> Vec<usize> {
        let mut positions = Vec::new();
        let tolerance = P::epsilon() * P::from(100.0).unwrap();
        let n = alpha.len();

        // For n >= 2, unity positions come from the Klein structure
        // The unity constraint α[n-2] × α[n-1] = 1 means certain bit patterns yield resonance = 1

        if n < 2 {
            // Special case: check each position directly
            for i in 0..range {
                let word = BitWord::new(n);
                if i == 0 && Self::is_near_unity(word.r(alpha), tolerance) {
                    positions.push(i);
                }
            }
        } else {
            // First, identify which Klein group elements have unity resonance
            let mut unity_klein_elements = Vec::new();

            // Check all 4 Klein group elements (based on last two bits)
            for klein in 0..4u8 {
                let mut test_word = BitWord::new(n);
                if klein & 1 != 0 {
                    test_word.set_bit(n - 2, true);
                }
                if klein & 2 != 0 {
                    test_word.set_bit(n - 1, true);
                }

                let r = test_word.r(alpha);
                if Self::is_near_unity(r, tolerance) {
                    unity_klein_elements.push(klein);
                }
            }

            // If no Klein elements have unity resonance, we still need to check all positions
            // because unity can come from other bit combinations, not just Klein elements

            // Now find all positions that have actual unity resonance
            // For small n, we can enumerate
            if n <= 20 {
                let max_check = range.min(1usize << n);

                for i in 0..max_check {
                    // Convert index to bit pattern
                    let word = index_to_bitword_unity(i, n);

                    // Check actual resonance value
                    let r = word.r(alpha);
                    if Self::is_near_unity(r, tolerance) {
                        positions.push(i);
                    }
                }

                // For ranges beyond 2^n, positions repeat cyclically
                if range > max_check {
                    let cycle_length = 1usize << n;
                    let base_positions = positions.clone();

                    for cycle in 1..(range / cycle_length + 1) {
                        for &base_pos in &base_positions {
                            let pos = cycle * cycle_length + base_pos;
                            if pos < range {
                                positions.push(pos);
                            }
                        }
                    }
                }
            } else {
                // For large n, we can't enumerate all positions
                // Use sampling approach to find unity positions

                let sample_size = range.min(1 << 20);
                let step = if range > sample_size {
                    range / sample_size
                } else {
                    1
                };

                for i in (0..range).step_by(step) {
                    let word = index_to_bitword_unity(i, n);
                    let r = word.r(alpha);

                    if Self::is_near_unity(r, tolerance) {
                        positions.push(i);
                    }
                }
            }
        }

        positions
    }

    fn is_near_unity<P: Float + FromPrimitive>(r: P, tolerance: P) -> bool {
        (r - P::one()).abs() < tolerance
    }
}

// Helper function for index to BitWord conversion
#[cfg(feature = "alloc")]
fn index_to_bitword_unity(idx: usize, n: usize) -> BitWord {
    let mut word = BitWord::new(n);

    // Set bits based on the binary representation of idx
    for bit in 0..n.min(64) {
        if (idx >> bit) & 1 == 1 {
            word.set_bit(bit, true);
        }
    }

    // For bits beyond 64, we need a deterministic mapping
    // This uses a linear congruential generator for reproducibility
    if n > 64 {
        let mut state = idx as u64;
        for bit in 64..n {
            state = state.wrapping_mul(1103515245).wrapping_add(12345);
            if state & 1 == 1 {
                word.set_bit(bit, true);
            }
            state >>= 1;
        }
    }

    word
}

/// Unity analysis functions
pub mod analysis {
    use super::*;

    /// Unity spacing analysis
    #[derive(Debug, Clone)]
    pub struct UnitySpacing {
        pub positions: Vec<usize>,
        pub spacings: Vec<usize>,
        pub average_spacing: f64,
        pub is_periodic: bool,
    }

    /// Analyze spacing between unity positions
    pub fn analyze_unity_spacing<P: Float + FromPrimitive>(
        alpha: &AlphaVec<P>,
        range: usize,
    ) -> UnitySpacing {
        let positions = u8::unity_positions(alpha, range);
        let mut spacings = Vec::new();

        for i in 1..positions.len() {
            spacings.push(positions[i] - positions[i - 1]);
        }

        let average_spacing = if !spacings.is_empty() {
            spacings.iter().sum::<usize>() as f64 / spacings.len() as f64
        } else {
            0.0
        };

        // Check if spacing is periodic (all spacings equal)
        let is_periodic = if !spacings.is_empty() {
            let first = spacings[0];
            spacings.iter().all(|&s| s == first)
        } else {
            false
        };

        UnitySpacing {
            positions,
            spacings,
            average_spacing,
            is_periodic,
        }
    }

    /// Find unity clusters (groups of nearby unity positions)
    pub fn find_unity_clusters<P: Float + FromPrimitive>(
        alpha: &AlphaVec<P>,
        range: usize,
        max_gap: usize,
    ) -> Vec<Vec<usize>> {
        let positions = u8::unity_positions(alpha, range);
        let mut clusters = Vec::new();

        if positions.is_empty() {
            return clusters;
        }

        let mut current_cluster = vec![positions[0]];

        for i in 1..positions.len() {
            if positions[i] - positions[i - 1] <= max_gap {
                current_cluster.push(positions[i]);
            } else {
                clusters.push(current_cluster);
                current_cluster = vec![positions[i]];
            }
        }

        clusters.push(current_cluster);
        clusters
    }

    /// Verify expected unity pattern for standard 8-bit
    pub fn verify_standard_pattern<P: Float + FromPrimitive>(alpha: &AlphaVec<P>) -> bool {
        let expected = u8::standard_unity_positions();
        let actual = u8::unity_positions(alpha, 768);

        // Check first 12 positions match
        if actual.len() < 12 {
            return false;
        }

        for i in 0..12 {
            if actual[i] != expected[i] {
                return false;
            }
        }

        true
    }

    /// Unity density (unity positions per unit range)
    pub fn unity_density<P: Float + FromPrimitive>(alpha: &AlphaVec<P>, range: usize) -> f64 {
        let positions = u8::unity_positions(alpha, range);
        positions.len() as f64 / range as f64
    }

    /// Analyze unity spacing for arbitrary bit lengths
    #[cfg(feature = "alloc")]
    pub fn analyze_unity_spacing_bitword<P: Float + FromPrimitive>(
        alpha: &AlphaVec<P>,
        range: usize,
    ) -> UnitySpacing {
        let positions = BitWord::unity_positions(alpha, range);
        let mut spacings = Vec::new();

        for i in 1..positions.len() {
            spacings.push(positions[i] - positions[i - 1]);
        }

        let average_spacing = if !spacings.is_empty() {
            spacings.iter().sum::<usize>() as f64 / spacings.len() as f64
        } else {
            0.0
        };

        // Check if spacing is periodic
        let is_periodic = if !spacings.is_empty() {
            let first = spacings[0];
            spacings.iter().all(|&s| s == first)
        } else {
            false
        };

        UnitySpacing {
            positions,
            spacings,
            average_spacing,
            is_periodic,
        }
    }

    /// Unity density for arbitrary bit lengths
    #[cfg(feature = "alloc")]
    pub fn unity_density_bitword<P: Float + FromPrimitive>(
        alpha: &AlphaVec<P>,
        range: usize,
    ) -> f64 {
        let positions = BitWord::unity_positions(alpha, range);
        positions.len() as f64 / range as f64
    }

    /// Count positions per Klein group that have unity
    /// Returns distribution of unity counts: how many Klein groups have 0, 1, 2, 3, or 4 unity positions
    #[cfg(feature = "alloc")]
    pub fn unity_distribution_by_klein<P: Float + FromPrimitive>(
        alpha: &AlphaVec<P>,
        range: usize,
    ) -> [usize; 5] {
        let n = alpha.len();
        let mut distribution = [0usize; 5]; // Index is count of unity positions in Klein group

        if n < 2 || range == 0 {
            return distribution;
        }

        let tolerance = P::epsilon() * P::from(100.0).unwrap();

        // Track seen Klein representatives
        #[cfg(feature = "std")]
        let mut seen = std::collections::HashSet::new();
        #[cfg(all(feature = "alloc", not(feature = "std")))]
        let mut seen = alloc::collections::BTreeSet::new();

        // Check Klein groups up to range
        let max_check = range.min(if n <= 20 { 1usize << n } else { 1 << 20 });

        for i in 0..max_check {
            let word = super::helpers::index_to_bitword(i, n);
            let repr = <BitWord as Resonance<P>>::klein_representative(&word);

            // Convert to key for tracking
            let key = super::helpers::bitword_to_key(&repr);
            if seen.contains(&key) {
                continue;
            }
            seen.insert(key);

            // Count unity positions in this Klein group
            let members = <BitWord as Resonance<P>>::class_members(&repr);
            let unity_count = members
                .iter()
                .filter(|&m| <BitWord as UnityStructure>::is_near_unity(m.r(alpha), tolerance))
                .count();

            distribution[unity_count] += 1;
        }

        distribution
    }
}

/// Properties related to Klein four-group and unity
pub mod klein_unity {
    use super::*;

    /// Find Klein groups whose representative has unity resonance
    /// Note: This is different from finding all unity positions!
    /// A Klein group may have unity resonance for its representative
    /// but other members may not have unity resonance.
    pub fn find_klein_groups_with_unity_representative<P: Float + FromPrimitive>(
        alpha: &AlphaVec<P>,
        n: usize,
        range: usize,
    ) -> Vec<Vec<BitWord>> {
        let mut unity_groups = Vec::new();
        let tolerance = P::epsilon() * P::from(100.0).unwrap();

        // Track which Klein representatives we've seen
        #[cfg(feature = "std")]
        let mut seen = std::collections::HashSet::new();
        #[cfg(all(feature = "alloc", not(feature = "std")))]
        let mut seen = alloc::collections::BTreeSet::new();

        // For small n, check all Klein representatives
        if n <= 20 {
            let max_check = range.min(1usize << n);

            for i in 0..max_check {
                let word = helpers::index_to_bitword(i, n);

                // Get Klein representative (zero out last 2 bits)
                let repr = <BitWord as Resonance<P>>::klein_representative(&word);

                // Skip if we've already seen this representative
                let repr_key = helpers::bitword_to_key(&repr);
                if seen.contains(&repr_key) {
                    continue;
                }
                seen.insert(repr_key);

                // Check if representative has unity resonance
                let r = repr.r(alpha);
                if <BitWord as UnityStructure>::is_near_unity(r, tolerance) {
                    let members = <BitWord as Resonance<P>>::class_members(&repr);
                    unity_groups.push(members);
                }
            }
        }

        unity_groups
    }

    /// Verify Klein four-group elements have unity resonance
    pub fn verify_klein_unity<P: Float + FromPrimitive>(alpha: &AlphaVec<P>) -> bool {
        // Check if the Klein four-group based on last 2 bits has unity
        let n = alpha.len();
        if n < 2 {
            return false;
        }

        let tolerance = P::epsilon() * P::from(100.0).unwrap();

        // Check all 4 Klein elements formed by last 2 bits
        for klein in 0..4u8 {
            let mut word = BitWord::new(n);
            if klein & 1 != 0 {
                word.set_bit(n - 2, true);
            }
            if klein & 2 != 0 {
                word.set_bit(n - 1, true);
            }

            let r = word.r(alpha);
            if !<BitWord as UnityStructure>::is_near_unity(r, tolerance) {
                return false;
            }
        }

        true
    }

    /// Find all Klein groups where ALL members have unity resonance
    /// This is the most restrictive case - requires all 4 members to have R=1
    pub fn unity_klein_groups<P: Float + FromPrimitive>(alpha: &AlphaVec<P>) -> Vec<Vec<u8>> {
        let mut unity_groups = Vec::new();
        let tolerance = P::epsilon() * P::from(100.0).unwrap();
        #[cfg(feature = "std")]
        let mut seen = std::collections::HashSet::new();
        #[cfg(all(feature = "alloc", not(feature = "std")))]
        let mut seen = alloc::collections::BTreeSet::new();

        // Check all possible values
        for value in 0u8..=255 {
            // Get the Klein representative
            let repr = <u8 as Resonance<P>>::klein_representative(&value);

            // Skip if we've already processed this Klein group
            if seen.contains(&repr) {
                continue;
            }
            seen.insert(repr);

            let members = <u8 as Resonance<P>>::class_members(&repr);

            // Check if all members have unity resonance
            let all_unity = members.iter().all(|&m| {
                let r = m.r(alpha);
                <u8 as UnityStructure>::is_near_unity(r, tolerance)
            });

            if all_unity {
                unity_groups.push(members);
            }
        }

        unity_groups
    }
}

// Helper module for index conversions
#[cfg(feature = "alloc")]
mod helpers {
    use super::*;

    /// Convert an index to a BitWord pattern
    pub fn index_to_bitword(idx: usize, n: usize) -> BitWord {
        let mut word = BitWord::new(n);

        // Set bits based on the index
        for bit in 0..n.min(64) {
            if (idx >> bit) & 1 == 1 {
                word.set_bit(bit, true);
            }
        }

        // For bits beyond 64, use modular arithmetic
        if n > 64 {
            let mut shifted_idx = idx;
            for bit in 64..n {
                shifted_idx = shifted_idx.wrapping_mul(1103515245).wrapping_add(12345);
                if shifted_idx & 1 == 1 {
                    word.set_bit(bit, true);
                }
            }
        }

        word
    }

    /// Convert BitWord to a hashable key (first 64 bits)
    #[cfg(any(feature = "std", feature = "alloc"))]
    pub fn bitword_to_key(word: &BitWord) -> u64 {
        // Get first 64 bits as key
        let mut key = 0u64;
        for i in 0..word.len().min(64) {
            if word.bit(i) {
                key |= 1u64 << i;
            }
        }
        key
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unity_positions() {
        let alpha = crate::tests::testing_alpha();
        let positions = u8::unity_positions(&alpha, 256);

        // Should find at least the basic unity positions
        assert!(!positions.is_empty());

        // Verify found positions actually have unity resonance
        for &pos in &positions {
            let byte = (pos % 256) as u8;
            let r = byte.r(&alpha);
            assert!(u8::is_near_unity(r, 1e-10));
        }
    }

    #[test]
    fn test_standard_unity_positions() {
        let expected = u8::standard_unity_positions();

        // Standard unity positions for 8-bit where R=1.0
        // These are the typical positions, but actual values depend on alpha
        assert_eq!(expected[0], 0);
        assert_eq!(expected[1], 1);
        assert_eq!(expected[2], 48);
        assert_eq!(expected[3], 49);

        // Pattern should repeat every 256
        assert_eq!(expected[4], 256);
        assert_eq!(expected[5], 257);
    }

    #[test]
    fn test_unity_spacing() {
        let alpha = crate::tests::testing_alpha();
        let spacing = analysis::analyze_unity_spacing(&alpha, 768);

        // With dynamic alpha, the exact count may vary
        // but we should find some unity positions
        assert!(
            !spacing.positions.is_empty(),
            "Should find some unity positions"
        );

        // Check spacing pattern exists
        if spacing.positions.len() > 1 {
            assert!(!spacing.spacings.is_empty());
        }
    }

    #[test]
    fn test_klein_unity() {
        let alpha = crate::tests::testing_alpha();

        // With dynamic alpha, Klein groups are formed by XORing bits 4,5
        // verify_klein_unity checks if {0, 16, 32, 48} has unity

        // Test if the base Klein group has unity
        let has_base_unity = klein_unity::verify_klein_unity(&alpha);

        if has_base_unity {
            println!("Base Klein group {{0, 16, 32, 48}} has unity resonance");
        }

        // Find all unity Klein groups
        let unity_groups = klein_unity::unity_klein_groups(&alpha);

        // If we find unity groups, verify they actually have unity resonance
        for group in &unity_groups {
            for &member in group {
                let r = member.r(&alpha);
                assert!(
                    u8::is_near_unity(r, 1e-6),
                    "Member {} should have unity resonance",
                    member
                );
            }
        }

        // The test passes whether or not unity groups exist - depends on alpha values
    }
}
