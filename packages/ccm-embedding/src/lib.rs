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

        // Find Klein minimum for minimal resonance
        object.is_klein_minimum(alpha);

        // For now, return the object itself
        // TODO: Implement full Klein minimum search
        Ok(object.clone())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_alpha_generation() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();
        assert_eq!(alpha.len(), 8);
        assert!(alpha.verify_unity_constraint());
    }

    /// Helper function to create a test alpha vector for 8-bit values
    pub fn testing_alpha() -> AlphaVec<f64> {
        // Use mathematical generation for consistency in tests
        AlphaVec::<f64>::mathematical(8).unwrap()
    }
}
