//! CCM Symmetry - Group actions and invariant theory
//!
//! This crate implements Axiom A3 of Coherence-Centric Mathematics:
//! symmetry group actions that preserve CCM structure.

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

#[cfg(feature = "alloc")]
extern crate alloc;

// Import core types
use ccm_core::CcmError;

// Module structure
pub mod actions;
pub mod discrete;
pub mod group;
pub mod invariants;
pub mod lie_algebra;
pub mod matrix_group;
pub mod orbits;
pub mod special_subgroups;
pub mod verification;

// Re-export main types
pub use actions::{CliffordAction, GroupAction};
pub use discrete::{KleinSymmetry, ResonanceAutomorphism};
pub use group::{GroupElement, SymmetryGroup};
pub use invariants::{ConservedQuantity, Invariant};
pub use lie_algebra::{LieAlgebra, LieAlgebraElement};
pub use orbits::{Orbit, StabilizerSubgroup};
pub use special_subgroups::{
    grade_preserving_subgroup, klein_subgroup, maximal_resonance_subgroup,
    resonance_preserving_subgroup, unity_stabilizer,
};
pub use verification::{ActionVerifier, CCMInvarianceVerifier, GroupAxiomVerifier};

/// Symmetry-specific error types
#[derive(Debug, Clone, PartialEq)]
pub enum SymmetryError {
    /// Group operation failed
    InvalidGroupOperation,
    /// Element not in group
    NotInGroup,
    /// Action does not preserve structure
    InvarianceViolation,
    /// Lie algebra operation failed
    LieAlgebraError,
    /// Orbit computation failed
    OrbitComputationFailed,
}

impl From<SymmetryError> for CcmError {
    fn from(err: SymmetryError) -> Self {
        match err {
            SymmetryError::InvalidGroupOperation => CcmError::InvalidInput,
            SymmetryError::NotInGroup => CcmError::InvalidInput,
            SymmetryError::InvarianceViolation => CcmError::Custom("Invariance violation"),
            SymmetryError::LieAlgebraError => CcmError::Custom("Lie algebra error"),
            SymmetryError::OrbitComputationFailed => CcmError::Custom("Orbit computation failed"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_symmetry_group_creation() {
        let group = SymmetryGroup::<f64>::generate(8).unwrap();
        // Group was created successfully for dimension 8
    }
}
