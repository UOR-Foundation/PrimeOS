//! Complete integrated implementation of Coherence-Centric Mathematics
//!
//! This crate provides the unified CCM system that applications should use.
//! It integrates the three fundamental mathematical structures:
//! - Embedding (Axiom A2): Minimal norm representations via resonance
//! - Coherence (Axiom A1): Clifford algebra and coherence metric
//! - Symmetry (Axiom A3): Group actions preserving CCM structure

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

// Module structure
pub mod cache;
pub mod engines;
pub mod standard;

// Re-export the main implementation
pub use standard::StandardCCM;

// Re-export core types from ccm-core
pub use ccm_core::{BitWord, CCMCore, CcmError, Float};

// Re-export key types from mathematical packages
pub use ccm_coherence::{CliffordElement, Section};
pub use ccm_embedding::AlphaVec;
pub use ccm_symmetry::GroupElement;

// Re-export traits that users need
pub use ccm_coherence::{Coherence, Graded};
pub use ccm_embedding::Resonance;
pub use ccm_symmetry::GroupAction;

/// Prelude module for convenient imports
pub mod prelude {
    pub use crate::{CCMCore, StandardCCM};
    pub use ccm_coherence::CliffordElement;
    pub use ccm_core::{BitWord, CcmError, Float};
    pub use ccm_embedding::AlphaVec;
    pub use ccm_symmetry::GroupElement;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ccm_integration() {
        // Create CCM instance
        let ccm = StandardCCM::<f64>::new(8).unwrap();

        // Generate alpha values
        let alpha = ccm.generate_alpha().unwrap();

        // Create test input
        let input = BitWord::from_u8(42);

        // Find minimal resonance
        let minimal = ccm.find_minimum_resonance(&input, &alpha).unwrap();

        // Embed into Clifford algebra
        let section = ccm.embed(&minimal, &alpha).unwrap();

        // Check coherence norm is positive
        let norm = ccm.coherence_norm(&section);
        assert!(norm > 0.0);
    }

    #[test]
    fn test_axiom_integration() {
        let ccm = StandardCCM::<f64>::new(8).unwrap();
        let alpha = ccm.generate_alpha().unwrap();

        // Test that embedding respects Klein group structure
        let word = BitWord::from_u8(0b11001100);
        let klein_members = ccm.klein_members(&word);
        assert_eq!(klein_members.len(), 4);

        // Test that all Klein members have different resonances but same minimal
        let minimal = ccm.find_minimum_resonance(&word, &alpha).unwrap();
        for member in &klein_members {
            let member_minimal = ccm.find_minimum_resonance(member, &alpha).unwrap();
            assert_eq!(minimal, member_minimal);
        }
    }
}
