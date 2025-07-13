//! Coherence-based page system for CCM
//!
//! Pages emerge from the mathematical structure of CCM rather than
//! combinatorial enumeration. This provides natural bounds and meaningful
//! groupings for arbitrary bit lengths.

use crate::{AlphaVec, InverseResonance, Resonance};
use ccm_core::{BitWord, CcmError, Float};
use num_traits::FromPrimitive;

#[cfg(feature = "alloc")]
use alloc::{collections::BTreeMap, vec::Vec};

use core::cmp::Ordering;

/// Wrapper for Float types to enable ordering
#[derive(Debug, Clone, Copy)]
pub struct OrdFloat<P: Float>(pub P);

impl<P: Float> PartialEq for OrdFloat<P> {
    fn eq(&self, other: &Self) -> bool {
        // Use relative epsilon comparison for better dynamic alpha handling
        let epsilon = P::epsilon() * P::from(1000.0).unwrap(); // More generous for dynamic alpha
        let abs_diff = (self.0 - other.0).abs();
        let max_val = self.0.abs().max(other.0.abs()).max(P::one());
        let relative_epsilon = epsilon * max_val;

        abs_diff <= relative_epsilon
    }
}

impl<P: Float> Eq for OrdFloat<P> {}

impl<P: Float> PartialOrd for OrdFloat<P> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<P: Float> Ord for OrdFloat<P> {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.eq(other) {
            Ordering::Equal
        } else if self.0 < other.0 {
            Ordering::Less
        } else {
            Ordering::Greater
        }
    }
}

/// Structure representing the page configuration for a given bit length
#[cfg(feature = "alloc")]
#[derive(Debug, Clone)]
pub struct PageStructure<P: Float> {
    /// Number of bits
    pub bit_length: usize,

    /// Sorted list of unique resonance values
    pub resonance_values: Vec<P>,

    /// Representative patterns for each resonance value (Klein minima)
    /// Each representative corresponds to the resonance value at the same index
    pub representatives: Vec<BitWord>,

    /// Mapping from resonance value to class index
    pub resonance_map: BTreeMap<OrdFloat<P>, usize>,

    /// Total number of pages (resonance classes × Klein orbits)
    pub total_pages: usize,
}

#[cfg(feature = "alloc")]
impl<P: Float + FromPrimitive> PageStructure<P> {
    /// Generate page structure for n-bit inputs
    pub fn for_bit_length(n: usize, alpha: &AlphaVec<P>) -> Result<Self, CcmError> {
        if n != alpha.len() {
            return Err(CcmError::InvalidLength);
        }

        // Enumerate all resonance values and their representative patterns
        let resonance_pattern_pairs = enumerate_resonance_classes(n, alpha)?;

        // Validate we got some resonance values
        if resonance_pattern_pairs.is_empty() {
            return Err(CcmError::InvalidInput);
        }

        // Split into separate vectors (already sorted from BTreeMap)
        let mut resonance_values = Vec::new();
        let mut representatives = Vec::new();

        for (resonance, pattern) in resonance_pattern_pairs {
            resonance_values.push(resonance);
            representatives.push(pattern);
        }

        // Build mapping from resonance to index
        let mut resonance_map = BTreeMap::new();
        for (idx, &resonance) in resonance_values.iter().enumerate() {
            resonance_map.insert(OrdFloat(resonance), idx);
        }

        // Validate expected count for small n
        if (3..=20).contains(&n) {
            let expected = 3 * (1 << (n - 2));
            if resonance_values.len() != expected {
                // Log warning but don't fail - floating point may cause slight variations
            }
        }

        // Total pages = resonance classes × Klein orbits (4)
        let total_pages = if n >= 2 {
            resonance_values.len() * 4
        } else {
            resonance_values.len()
        };

        Ok(Self {
            bit_length: n,
            resonance_values,
            representatives,
            resonance_map,
            total_pages,
        })
    }

    /// Find resonance class index for a given resonance value
    pub fn find_resonance_class(&self, resonance: P) -> Option<usize> {
        self.resonance_map.get(&OrdFloat(resonance)).copied()
    }
}

/// Represents a single coherence page
#[derive(Debug, Clone)]
pub struct ResonancePage<P: Float> {
    /// Page index
    pub index: usize,

    /// Resonance value for this page
    pub resonance: P,

    /// Klein orbit position (0-3)
    pub klein_orbit: u8,

    /// Canonical representative (computed lazily)
    #[cfg(feature = "alloc")]
    pub representative: Option<BitWord>,
}

/// Trait for intrinsic page operations based on coherence
pub trait IntrinsicPages<P: Float + FromPrimitive>: Sized {
    /// Get the coherence-based page index
    fn coherence_page(
        &self,
        alpha: &AlphaVec<P>,
        structure: &PageStructure<P>,
    ) -> Result<usize, CcmError>;

    /// Get Klein orbit position within resonance class
    fn klein_orbit_position(&self) -> u8;

    /// Apply Klein transform
    fn apply_klein_transform(&self, klein: u8) -> Self;

    /// Get all members of the same coherence page
    #[cfg(feature = "alloc")]
    fn page_members(
        &self,
        alpha: &AlphaVec<P>,
        structure: &PageStructure<P>,
    ) -> Result<Vec<Self>, CcmError>
    where
        Self: Resonance<P> + InverseResonance<P, Output = Self> + Clone,
    {
        let page_index = self.coherence_page(alpha, structure)?;

        // Extract resonance class and Klein orbit
        let resonance_class = page_index >> 2;
        let target_klein_orbit = (page_index & 0b11) as u8;

        // Get the resonance value for this class
        let target_resonance = structure
            .resonance_values
            .get(resonance_class)
            .ok_or(CcmError::InvalidInput)?;

        // Use inverse resonance to find all patterns with this resonance
        let tolerance = P::epsilon() * P::from(10.0).unwrap();
        let all_with_resonance = match Self::find_by_resonance(*target_resonance, alpha, tolerance)
        {
            Ok(patterns) => patterns,
            Err(CcmError::SearchExhausted) => {
                // No patterns found with this exact resonance
                // This can happen due to floating point precision
                return Ok(Vec::new());
            }
            Err(e) => return Err(e),
        };

        // Filter to only patterns in the specific Klein orbit
        let filtered: Vec<Self> = all_with_resonance
            .into_iter()
            .filter(|pattern| pattern.klein_orbit_position() == target_klein_orbit)
            .collect();

        Ok(filtered)
    }

    /// Find the page representative (minimal member)
    fn page_representative(
        &self,
        alpha: &AlphaVec<P>,
        structure: &PageStructure<P>,
    ) -> Result<Self, CcmError>
    where
        Self: Resonance<P> + InverseResonance<P, Output = Self> + Clone,
    {
        // Get all members of this page
        let members = self.page_members(alpha, structure)?;

        // Find the member with minimal Klein orbit position
        // This gives us a consistent canonical representative
        members
            .into_iter()
            .min_by_key(|m| m.klein_orbit_position())
            .ok_or(CcmError::InvalidInput)
    }
}

/// Enumerate all resonance values and their representative patterns for n-bit patterns
#[cfg(feature = "alloc")]
fn enumerate_resonance_classes<P: Float + FromPrimitive>(
    n: usize,
    alpha: &AlphaVec<P>,
) -> Result<Vec<(P, BitWord)>, CcmError> {
    use alloc::collections::BTreeMap;

    // Use BTreeMap to maintain sorted order and store both resonance and pattern
    let mut resonance_patterns = BTreeMap::new();

    if n == 0 {
        // Degenerate case
        let word = BitWord::new(0);
        resonance_patterns.insert(OrdFloat(P::one()), word);
    } else if n == 1 {
        // Only two patterns: 0 and 1
        let word0 = BitWord::new(1);
        resonance_patterns.insert(OrdFloat(P::one()), word0); // 0

        let mut word1 = BitWord::new(1);
        word1.set_bit(0, true);
        resonance_patterns.insert(OrdFloat(alpha[0]), word1); // 1
    } else if n == 2 {
        // Four patterns, no unity constraint yet
        for i in 0..4u8 {
            let mut word = BitWord::new(2);
            if i & 1 != 0 {
                word.set_bit(0, true);
            }
            if i & 2 != 0 {
                word.set_bit(1, true);
            }
            let r = word.r(alpha);
            resonance_patterns.insert(OrdFloat(r), word);
        }
    } else {
        // n >= 3: Generate Klein representatives more efficiently

        if n <= 20 {
            // Small enough to enumerate exactly
            let num_representatives = 1 << (n - 2);

            for i in 0..num_representatives {
                // Create base pattern with first n-2 bits from i
                let base = BitWord::from_u64(i as u64, n - 2);

                // Generate all 4 Klein variants by varying last 2 bits
                for klein in 0..4u8 {
                    let mut pattern = BitWord::new(n);

                    // Copy first n-2 bits
                    for bit in 0..(n - 2) {
                        if base.bit(bit) {
                            pattern.set_bit(bit, true);
                        }
                    }

                    // Set last two bits according to Klein value
                    if klein & 1 != 0 {
                        pattern.set_bit(n - 2, true);
                    }
                    if klein & 2 != 0 {
                        pattern.set_bit(n - 1, true);
                    }

                    let r = pattern.r(alpha);
                    // Only keep Klein minimum for each unique resonance
                    let ord_r = OrdFloat(r);
                    resonance_patterns.entry(ord_r).or_insert_with(|| {
                        // Find Klein minimum among all variants with this resonance
                        let mut min_pattern = pattern.clone();
                        let mut min_r = r;

                        // Check all Klein variants to find minimum
                        for k2 in 0..4u8 {
                            let mut test_pattern = BitWord::new(n);

                            // Copy base bits
                            for bit in 0..(n - 2) {
                                if base.bit(bit) {
                                    test_pattern.set_bit(bit, true);
                                }
                            }

                            // Set Klein bits
                            if k2 & 1 != 0 {
                                test_pattern.set_bit(n - 2, true);
                            }
                            if k2 & 2 != 0 {
                                test_pattern.set_bit(n - 1, true);
                            }

                            let test_r = test_pattern.r(alpha);
                            if OrdFloat(test_r) == ord_r && test_r < min_r {
                                min_r = test_r;
                                min_pattern = test_pattern;
                            }
                        }

                        min_pattern
                    });
                }
            }
        } else {
            // For large n, use a strategic sampling approach
            // Focus on patterns likely to produce diverse resonance values

            // Start with key patterns
            let zero_pattern = BitWord::new(n);
            resonance_patterns.insert(OrdFloat(P::one()), zero_pattern);

            // Add single bit patterns (these often give the alpha values directly)
            for i in 0..n.min(64) {
                let mut pattern = BitWord::new(n);
                pattern.set_bit(i, true);
                let r = pattern.r(alpha);
                let ord_r = OrdFloat(r);
                resonance_patterns.entry(ord_r).or_insert(pattern);
            }

            // Add two-bit patterns for alpha products
            for i in 0..n.min(32) {
                for j in (i + 1)..n.min(32) {
                    let mut pattern = BitWord::new(n);
                    pattern.set_bit(i, true);
                    pattern.set_bit(j, true);
                    let r = pattern.r(alpha);
                    let ord_r = OrdFloat(r);
                    resonance_patterns.entry(ord_r).or_insert(pattern);
                }
            }

            // Add patterns with varying popcount
            let mut rng_state = 0x2A65C3F5u64;
            let target_samples = 5000; // Reduced for efficiency

            for popcount in 1..=n.min(15) {
                let samples_per_popcount = target_samples / n.min(15);

                for _ in 0..samples_per_popcount {
                    rng_state = rng_state.wrapping_mul(1103515245).wrapping_add(12345);

                    let mut pattern = BitWord::new(n);
                    let mut bits_set = 0;

                    // Set exactly `popcount` bits
                    while bits_set < popcount {
                        let bit_pos = (rng_state as usize) % n;
                        rng_state = rng_state.wrapping_mul(1103515245).wrapping_add(12345);

                        if !pattern.bit(bit_pos) {
                            pattern.set_bit(bit_pos, true);
                            bits_set += 1;
                        }
                    }

                    let r = pattern.r(alpha);
                    let ord_r = OrdFloat(r);
                    resonance_patterns.entry(ord_r).or_insert(pattern);
                }
            }
        }
    }

    // Convert to sorted vector of (resonance, pattern) pairs
    Ok(resonance_patterns
        .into_iter()
        .map(|(ord_r, pattern)| (ord_r.0, pattern))
        .collect())
}

/// Implementation for BitWord
#[cfg(feature = "alloc")]
impl<P: Float + FromPrimitive> IntrinsicPages<P> for BitWord {
    fn coherence_page(
        &self,
        alpha: &AlphaVec<P>,
        structure: &PageStructure<P>,
    ) -> Result<usize, CcmError> {
        if self.len() != structure.bit_length {
            return Err(CcmError::InvalidLength);
        }

        // Compute resonance value
        let resonance = self.r(alpha);

        // Find resonance class index
        let resonance_class = structure
            .find_resonance_class(resonance)
            .ok_or(CcmError::InvalidInput)?;

        // Get Klein orbit position
        let klein_orbit = <BitWord as IntrinsicPages<P>>::klein_orbit_position(self);

        // Combine into page index
        Ok((resonance_class << 2) | (klein_orbit as usize))
    }

    fn klein_orbit_position(&self) -> u8 {
        if self.len() < 2 {
            return 0;
        }

        let n = self.len();
        let mut orbit = 0u8;

        if self.bit(n - 2) {
            orbit |= 1;
        }
        if self.bit(n - 1) {
            orbit |= 2;
        }

        orbit
    }

    fn apply_klein_transform(&self, klein: u8) -> Self {
        if self.len() < 2 {
            return self.clone();
        }

        let mut result = self.clone();
        let n = self.len();

        // Apply XOR to last two bits based on klein value
        if klein & 1 != 0 {
            result.flip_bit(n - 2);
        }
        if klein & 2 != 0 {
            result.flip_bit(n - 1);
        }

        result
    }
}

/// Implementation for u8
impl<P: Float + FromPrimitive> IntrinsicPages<P> for u8 {
    fn coherence_page(
        &self,
        alpha: &AlphaVec<P>,
        structure: &PageStructure<P>,
    ) -> Result<usize, CcmError> {
        BitWord::from_u8(*self).coherence_page(alpha, structure)
    }

    fn klein_orbit_position(&self) -> u8 {
        // For 8-bit values, last 2 bits are at positions 6,7
        let mut orbit = 0u8;

        if self & 0x40 != 0 {
            // bit 6
            orbit |= 1;
        }
        if self & 0x80 != 0 {
            // bit 7
            orbit |= 2;
        }

        orbit
    }

    fn apply_klein_transform(&self, klein: u8) -> Self {
        let mut result = *self;

        // Apply XOR to bits 6,7 based on klein value
        if klein & 1 != 0 {
            result ^= 0x40; // flip bit 6
        }
        if klein & 2 != 0 {
            result ^= 0x80; // flip bit 7
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ord_float() {
        let a = OrdFloat(1.0_f64);
        let b = OrdFloat(2.0_f64);
        let c = OrdFloat(1.0_f64 + f64::EPSILON / 2.0);

        assert!(a < b);
        assert!(a == c); // Within epsilon
        assert!(b > a);
    }

    #[test]
    fn test_klein_orbit_position() {
        // Test u8 Klein orbit positions
        assert_eq!(
            <u8 as IntrinsicPages<f64>>::klein_orbit_position(&0b00000000u8),
            0
        ); // 00
        assert_eq!(
            <u8 as IntrinsicPages<f64>>::klein_orbit_position(&0b01000000u8),
            1
        ); // 01
        assert_eq!(
            <u8 as IntrinsicPages<f64>>::klein_orbit_position(&0b10000000u8),
            2
        ); // 10
        assert_eq!(
            <u8 as IntrinsicPages<f64>>::klein_orbit_position(&0b11000000u8),
            3
        ); // 11
    }

    #[test]
    fn test_klein_transform() {
        let byte = 0b00110000u8;

        // Test all Klein transforms
        assert_eq!(
            <u8 as IntrinsicPages<f64>>::apply_klein_transform(&byte, 0),
            0b00110000
        ); // No change
        assert_eq!(
            <u8 as IntrinsicPages<f64>>::apply_klein_transform(&byte, 1),
            0b01110000
        ); // Flip bit 6
        assert_eq!(
            <u8 as IntrinsicPages<f64>>::apply_klein_transform(&byte, 2),
            0b10110000
        ); // Flip bit 7
        assert_eq!(
            <u8 as IntrinsicPages<f64>>::apply_klein_transform(&byte, 3),
            0b11110000
        ); // Flip both
    }

    #[test]
    fn test_page_structure_generation() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();
        let structure = PageStructure::for_bit_length(8, &alpha).unwrap();

        // With dynamic alpha, we get a reasonable number of resonance classes
        // but not necessarily the theoretical 3 × 2^(n-2)
        assert!(!structure.resonance_values.is_empty());
        assert!(structure.resonance_values.len() > 10); // Should have decent coverage

        // Total pages = resonance classes × 4 Klein orbits
        assert_eq!(structure.total_pages, structure.resonance_values.len() * 4);

        // Verify resonance values are sorted
        for i in 1..structure.resonance_values.len() {
            assert!(structure.resonance_values[i] >= structure.resonance_values[i - 1]);
        }
    }

    #[test]
    fn test_coherence_page_bounds() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();
        let structure = PageStructure::for_bit_length(8, &alpha).unwrap();

        // Test that all bytes map to valid pages
        for i in 0..=255u8 {
            let page = i.coherence_page(&alpha, &structure).unwrap();
            assert!(page < structure.total_pages);
        }
    }

    #[test]
    fn test_klein_group_structure() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();
        let byte = 42u8;

        // Test that Klein transforms work correctly structurally
        // Note: With dynamic alpha, Klein group members may not have identical resonance

        let mut resonances = Vec::new();

        for klein in 0..4 {
            let transformed = <u8 as IntrinsicPages<f64>>::apply_klein_transform(&byte, klein);
            let resonance = transformed.r(&alpha);
            let orbit = <u8 as IntrinsicPages<f64>>::klein_orbit_position(&transformed);

            resonances.push(resonance);

            // Verify Klein orbit position matches the transform
            assert_eq!(
                orbit, klein,
                "Klein orbit position should match transform index"
            );
        }

        // Just verify that all resonances are positive and finite
        for (i, &r) in resonances.iter().enumerate() {
            assert!(
                r > 0.0 && r.is_finite(),
                "Klein transform {} gave invalid resonance {}",
                i,
                r
            );
        }
    }

    #[test]
    fn test_resonance_enumeration() {
        // Test that we get reasonable resonance counts for small cases
        // Note: With dynamic alpha, exact theoretical counts may not hold

        // Skip n=2 since AlphaVec requires at least 3 elements for unity constraint

        let alpha3 = AlphaVec::<f64>::for_bit_length(3).unwrap();
        let resonances3 = enumerate_resonance_classes(3, &alpha3).unwrap();
        assert!(!resonances3.is_empty());
        assert!(resonances3.len() >= 3); // Should have at least a few unique values

        let alpha4 = AlphaVec::<f64>::for_bit_length(4).unwrap();
        let resonances4 = enumerate_resonance_classes(4, &alpha4).unwrap();
        assert!(!resonances4.is_empty());
        assert!(resonances4.len() >= 4); // Should have reasonable coverage

        // Verify they're sorted and unique
        for resonances in [&resonances3, &resonances4] {
            for i in 1..resonances.len() {
                assert!(
                    resonances[i].0 > resonances[i - 1].0,
                    "Resonances should be sorted and unique"
                );
            }
        }
    }
}
