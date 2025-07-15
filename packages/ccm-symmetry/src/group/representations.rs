//! Various group representations
//! 
//! This module defines different ways to represent groups:
//! - Abstract (generators and relations)
//! - Matrix representations
//! - Permutation representations
//! - Character tables (for finite groups)

use num_traits::Float;

/// Finite group representations
pub enum FiniteGroupRep<P: Float> {
    /// Permutation group
    PermutationGroup {
        /// Degree of permutation
        degree: usize,
        /// Generating permutations
        generators: Vec<Vec<usize>>,
    },
    /// Matrix group
    MatrixGroup {
        /// Dimension of matrices
        dimension: usize,
        /// Generating matrices (row-major)
        generators: Vec<Vec<P>>,
    },
}

/// Continuous group representations
pub enum ContinuousGroupRep<P: Float> {
    /// Lie group with manifold structure
    LieGroup {
        /// Dimension of the manifold
        manifold_dimension: usize,
        /// Lie algebra dimension
        algebra_dimension: usize,
        /// Phantom data for P
        _phantom: core::marker::PhantomData<P>,
    },
    /// Algebraic group defined by equations
    AlgebraicGroup {
        /// Number of variables
        variables: usize,
        /// Number of equations
        equations: usize,
        /// Phantom data for P
        _phantom: core::marker::PhantomData<P>,
    },
}