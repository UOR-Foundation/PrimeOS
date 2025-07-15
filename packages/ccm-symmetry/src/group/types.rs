//! Group type classification and related types
//! 
//! This module defines the classification of symmetry groups
//! and associated type definitions.

use num_traits::Float;
use crate::group::GroupElement;

/// Classification of symmetry groups by mathematical structure
/// 
/// Groups are classified by their properties:
/// - Finite: Groups with finitely many elements
/// - Continuous: Groups with manifold structure (Lie groups)
/// - DiscreteInfinite: Discrete groups with infinitely many elements
#[derive(Debug, Clone)]
pub enum GroupType<P: Float> {
    /// Finite group with explicit element list
    /// 
    /// Contains all group elements explicitly. This allows for:
    /// - Exact orbit calculations
    /// - Complete stabilizer enumeration
    /// - Exhaustive symmetry checking
    /// 
    /// Examples: Klein group V₄, cyclic groups C_n, dihedral groups D_n
    Finite { 
        /// Complete list of all group elements
        elements: Vec<GroupElement<P>> 
    },
    
    /// Continuous Lie group
    /// 
    /// Infinite group with smooth manifold structure.
    /// Operations are typically done via Lie algebra or generators.
    /// 
    /// Examples: SO(n), SU(n), general linear groups
    Continuous,
    
    /// Discrete but infinite group
    /// 
    /// Countably infinite group without continuous structure.
    /// Usually handled via generators and relations.
    /// 
    /// Examples: Integer groups ℤ, discrete Heisenberg group
    DiscreteInfinite,
}

/// Represents a stabilizer subgroup
/// 
/// The stabilizer of an element x under group G is:
/// Stab_G(x) = {g ∈ G : g·x = x}
#[derive(Debug, Clone)]
pub struct StabilizerSubgroup<P: Float> {
    /// Generators of the stabilizer subgroup
    pub generators: Vec<GroupElement<P>>,
}

/// Represents a relation in a group presentation
/// 
/// A relation is an equation of the form: word = identity
/// where word is a product of generators and their inverses
#[derive(Debug, Clone)]
pub struct GroupRelation {
    /// Word on the left-hand side of the relation
    /// Each element is (generator_index, power)
    pub word: Vec<(usize, i32)>,
    /// Optional name/description of the relation
    pub name: Option<String>,
}

/// Represents a complete group presentation
/// 
/// A group presentation consists of generators and relations:
/// <g1, g2, ... | r1, r2, ...>
#[derive(Debug, Clone)]
pub struct GroupPresentation<P: Float> {
    /// Generator names (for display purposes)
    pub generator_names: Vec<String>,
    /// The actual generator elements
    pub generators: Vec<GroupElement<P>>,
    /// Relations between generators
    pub relations: Vec<GroupRelation>,
}