//! CCM Coherence - Clifford algebra and coherence metric
//!
//! This crate implements Axiom A1 of Coherence-Centric Mathematics:
//! the coherence inner product, including Clifford algebra generation
//! and grade decomposition.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

// Import core types

// Include existing modules
mod coherence;
pub use coherence::{Coherence, Graded};

// Core modules
pub mod clifford;
pub mod element;
pub mod embedding;
pub mod grade;
pub mod metric;

// Re-export key types
pub use clifford::CliffordAlgebra;
pub use element::{CliffordElement, Section};
pub use embedding::{bitword_to_clifford, embed_with_resonance, u8_to_clifford};
pub use metric::{coherence_norm, coherence_product};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clifford_generation() {
        let algebra = CliffordAlgebra::<f64>::generate(8).unwrap();
        assert_eq!(algebra.dimension(), 8);
    }
}
