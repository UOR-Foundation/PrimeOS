//! Symmetry group module
//! 
//! This module provides symmetry group implementations for CCM.
//! Groups are fundamental to Axiom A3 (Symmetry Group Action) and
//! represent transformations that preserve coherence structure.
//! 
//! # Module Organization
//! 
//! - `element` - Group element representation
//! - `types` - Group type classification
//! - `symmetry_group` - Main group structure
//! - `finite` - Finite group implementations
//! - `infinite` - Infinite discrete group implementations
//! - `continuous` - Continuous group implementations
//! - `discrete` - Discrete group implementations
//! - `stabilizer` - Stabilizer subgroup computations
//! - `operations` - Group operations (multiply, inverse, etc.)
//! - `generators` - Generator management
//! - `representations` - Various group representations

// Core types
mod element;
mod types;
mod symmetry_group;

// Group implementations
mod finite;
mod infinite;
mod continuous;
mod discrete;

// Functionality
mod stabilizer;
mod operations;
mod generators;
mod representations;
mod invariants;
mod orbits;

// Refactored modules from symmetry_group
mod word_search;
mod matrix_operations;
mod manifold_checks;
mod group_validation;
mod schreier_sims;
mod matrix_logarithm;

// Re-export main types for public API
pub use element::GroupElement;
pub use types::{GroupType, StabilizerSubgroup, GroupRelation, GroupPresentation};
pub use symmetry_group::SymmetryGroup;
pub use representations::{FiniteGroupRep, ContinuousGroupRep};
pub use orbits::Orbit;

// Re-export commonly used items
pub use operations::GroupOperations;
pub use stabilizer::StabilizerComputation;

// For backward compatibility, re-export DiscreteInfinite as both Discrete and Infinite
pub use types::GroupType::DiscreteInfinite as Discrete;
pub use types::GroupType::DiscreteInfinite as Infinite;