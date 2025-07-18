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
pub use coherence::Coherence;
pub use grade::Graded;

// Core modules
pub mod arbitrary_support;
pub mod clifford;
pub mod coherence_gradient;
pub mod decomposition;
pub mod element;
pub mod embedding;
pub mod grade;
pub mod lazy;
pub mod metric;
pub mod optimization;
pub mod rotor;
pub mod sparse;
pub mod unified;
pub mod single_blade;
pub mod scalable;
pub mod sparse_big;
pub mod optimizations;

#[cfg(test)]
mod arbitrary_tests;

#[cfg(test)]
mod grade_orthogonality_test;

// Re-export key types
pub use clifford::CliffordAlgebra;
pub use decomposition::{CoherentDecomposition, GradeComponent, CoherenceBoundary, CoherenceBoundaryType};
pub use element::{CliffordElement, Section};
pub use embedding::{bitword_to_clifford, embed_with_resonance, u8_to_clifford};
pub use metric::{coherence_norm, coherence_product};

// Re-export unified API
pub use unified::{CliffordAlgebraTrait, CliffordAlgebraFactory, UnifiedCliffordAlgebra};
pub use arbitrary_support::{ArbitraryCliffordAlgebra, ArbitraryDimensionConfig};
pub use lazy::LazyCliffordAlgebra;
pub use sparse::SparseCliffordElement;

// Re-export new embedding functions
pub use embedding::{bitword_to_clifford_trait, u8_to_clifford_trait, embed_bitword_lazy};

// Re-export scalable API
pub use scalable::{ScalableCliffordAlgebraTrait, ScalableAlgebra, LazyElement, GradeIterator};
pub use single_blade::{SingleBlade, LazySingleBlade};
pub use arbitrary_support::BigIndex;
pub use sparse_big::SparseBigElement;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clifford_generation() {
        let algebra = CliffordAlgebra::<f64>::generate(8).unwrap();
        assert_eq!(algebra.dimension(), 8);
    }
}
