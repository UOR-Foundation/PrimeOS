//! CCM Coherence - Clifford algebra and coherence metric
//!
//! This crate implements Axiom A1 of Coherence-Centric Mathematics:
//! the coherence inner product, including Clifford algebra generation
//! and grade decomposition.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

// Import core types
use ccm_core::{CcmError, Float};

// Include the existing coherence module
mod coherence;
pub use coherence::{Coherence, Graded};

// Additional modules to be implemented
pub mod clifford;
pub mod grade;
pub mod metric;

/// Clifford algebra structure for n dimensions
pub struct CliffordAlgebra<P: Float> {
    dimension: usize,
    _phantom: core::marker::PhantomData<P>,
}

impl<P: Float> CliffordAlgebra<P> {
    /// Generate Clifford algebra for n dimensions
    pub fn generate(n: usize) -> Result<Self, CcmError> {
        Ok(Self {
            dimension: n,
            _phantom: core::marker::PhantomData,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clifford_generation() {
        let algebra = CliffordAlgebra::<f64>::generate(8).unwrap();
        assert_eq!(algebra.dimension, 8);
    }
}
