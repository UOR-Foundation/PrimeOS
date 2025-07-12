//! CCM Embedding - Minimal embedding and resonance algebra
//!
//! This crate implements Axiom A2 of Coherence-Centric Mathematics:
//! the minimal embedding principle, including alpha generation and
//! resonance algebra.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

// Import core types from ccm-core
use ccm_core::{BitWord, CcmError, Float};

// Modules
pub mod alpha;
pub mod page;
pub mod resonance;

// Re-export key types
pub use alpha::{AlphaError, AlphaVec};
pub use page::{inject_page, page_of};
pub use resonance::{
    HomomorphicResonance, InverseResonance, Resonance, ResonanceClasses, ResonanceConservation,
    ResonanceGradient, UnityStructure,
};

/// Embedding operations for mathematical objects
pub mod embed {
    use super::*;

    /// Find the minimal embedding of a BitWord
    pub fn minimal_embedding<P: Float + num_traits::FromPrimitive>(
        object: &BitWord,
        alpha: &AlphaVec<P>,
    ) -> Result<BitWord, CcmError> {
        use crate::Resonance;

        // Get all Klein group members
        let members = <BitWord as Resonance<P>>::class_members(object);

        // Find the member with minimum resonance
        let mut min_resonance = object.r(alpha);
        let mut min_member = object.clone();

        for member in members {
            let resonance = member.r(alpha);
            if resonance < min_resonance {
                min_resonance = resonance;
                min_member = member;
            }
        }

        Ok(min_member)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::Resonance;

    #[test]
    fn test_alpha_generation() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();
        assert_eq!(alpha.len(), 8);
        assert!(alpha.verify_unity_constraint());
    }

    #[test]
    fn test_minimal_embedding() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Test with a byte that's not a Klein minimum
        let test_byte = 0b11010101u8; // bits 6,7 = 11
        let word = BitWord::from_u8(test_byte);

        let min_embedding = embed::minimal_embedding(&word, &alpha).unwrap();

        // The result should be a Klein minimum
        assert!(min_embedding.is_klein_minimum(&alpha));

        // It should be in the same Klein group as the input
        let klein_members = <BitWord as Resonance<f64>>::class_members(&word);
        assert!(
            klein_members.iter().any(|m| m == &min_embedding),
            "Minimal embedding should be in the same Klein group"
        );

        // Its resonance should be minimal among Klein members
        let min_resonance = min_embedding.r(&alpha);
        for member in klein_members {
            assert!(
                member.r(&alpha) >= min_resonance - 1e-10,
                "Minimal embedding should have the smallest resonance"
            );
        }
    }

    #[test]
    fn test_klein_group_properties() {
        let _alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Test Klein group for various bytes
        for test_byte in [0u8, 1, 42, 128, 255] {
            let members = <u8 as Resonance<f64>>::class_members(&test_byte);

            // Klein group should have exactly 4 members
            assert_eq!(members.len(), 4);

            // All members should differ only in last two bits
            for i in 0..4 {
                for j in 0..4 {
                    if i != j {
                        // XOR should only affect bits 6,7
                        let diff = members[i] ^ members[j];
                        assert!(
                            diff & 0b00111111 == 0,
                            "Klein members should only differ in bits 6,7"
                        );
                    }
                }
            }

            // Verify Klein group structure (XOR operation)
            let base = test_byte & 0b00111111;
            let expected_members = [
                base,
                base | 0b01000000,
                base | 0b10000000,
                base | 0b11000000,
            ];

            for expected in expected_members {
                assert!(
                    members.contains(&expected),
                    "Klein group should contain byte {}",
                    expected
                );
            }
        }
    }

    #[test]
    fn test_conservation_laws() {
        use crate::resonance::conservation::ResonanceConservation;

        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Test 768-cycle conservation
        let sum_768 = <u8 as ResonanceConservation<f64>>::resonance_sum(0, 768, &alpha);

        // The sum should be approximately 3 times the sum of 256 values
        // since we cycle through all 256 values 3 times
        let sum_256 = <u8 as ResonanceConservation<f64>>::resonance_sum(0, 256, &alpha);
        let expected = sum_256 * 3.0;

        assert!(
            (sum_768 - expected).abs() < 1e-10,
            "768-cycle should equal 3 × 256-cycle: {} vs {}",
            sum_768,
            expected
        );

        // Test that conservation sum is positive and finite
        assert!(sum_768 > 0.0 && sum_768.is_finite());
    }

    /// Helper function to create a test alpha vector for 8-bit values
    pub fn testing_alpha() -> AlphaVec<f64> {
        // Use mathematical generation for consistency in tests
        AlphaVec::<f64>::mathematical(8).unwrap()
    }
}
