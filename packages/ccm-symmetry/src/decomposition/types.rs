//! Core types for symmetry decomposition
//!
//! This module contains the fundamental data structures used throughout
//! the decomposition system.

use crate::SymmetryType;

/// A component corresponding to a group orbit
///
/// Represents an element and its orbit under group action, along with
/// information about the stabilizer subgroup and preserved symmetries.
#[derive(Clone, Debug)]
pub struct OrbitComponent<T> {
    /// Representative element of the orbit
    pub representative: T,
    /// Size of the orbit
    pub orbit_size: usize,
    /// Stabilizer subgroup generators
    pub stabilizer_generators: Vec<usize>,
    /// Symmetries preserved by this orbit
    pub preserved_symmetries: Vec<SymmetryType>,
}

/// A natural boundary in symmetry space
///
/// Represents a position where the symmetry structure of a mathematical
/// object changes. These boundaries emerge naturally from the group action
/// and indicate transitions in mathematical structure.
#[derive(Clone, Debug)]
pub struct SymmetryBoundary {
    /// Position where the boundary occurs
    pub position: usize,
    /// Symmetry that is broken at this boundary
    pub broken_symmetry: SymmetryType,
    /// Magnitude of symmetry breaking
    pub breaking_strength: f64,
    /// Type of boundary
    pub boundary_type: SymmetryBoundaryType,
}

/// Types of boundaries that can occur in symmetry space
/// 
/// These boundaries represent points where the symmetry structure
/// of a mathematical object changes in some fundamental way.
#[derive(Clone, Debug, PartialEq)]
pub enum SymmetryBoundaryType {
    /// Transition between different orbits
    /// 
    /// Occurs when moving from one group orbit to another.
    /// This indicates a fundamental change in how the group acts on elements.
    OrbitTransition,
    
    /// Point where stabilizer changes
    /// 
    /// The stabilizer subgroup (elements that fix a point) changes size or structure.
    /// This often indicates a change in the symmetry properties of the element.
    StabilizerChange,
    
    /// Loss of invariant
    /// 
    /// A conserved quantity or invariant property is no longer preserved.
    /// This is often associated with symmetry breaking.
    InvariantBreak,
    
    /// Composite of multiple indicators
    /// 
    /// Multiple types of symmetry changes occur at the same boundary.
    /// This typically indicates a major structural transition.
    Composite,
    
    /// Pattern break in periodic structure
    /// 
    /// Used for cyclic and permutation symmetries where expected
    /// patterns are violated.
    PatternBreak,
    
    /// Gradient jump in continuous measures
    /// 
    /// Used for continuous symmetries (Linear, Orthogonal) where
    /// derivatives show discontinuities.
    GradientJump,
    
    /// Composite break from multiple symmetry types
    /// 
    /// Used for compound symmetries like Dihedral where multiple
    /// component symmetries are broken.
    CompositeBreak,
}