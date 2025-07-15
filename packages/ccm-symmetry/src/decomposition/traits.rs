//! Trait definitions for symmetry-based decomposition
//!
//! This module defines the core trait that enables decomposition of mathematical
//! objects based on their symmetry structure.

use crate::{SymmetryGroup, SymmetryType};
use crate::decomposition::types::{OrbitComponent, SymmetryBoundary};
use ccm_core::{Float, CcmError};

/// Natural decomposition based on symmetry structure
///
/// This trait provides methods for decomposing mathematical objects according
/// to their symmetry properties. The decomposition respects the group action
/// and preserves important invariants.
///
/// ## Mathematical Foundation
///
/// Decomposition in symmetry space is based on:
/// 1. **Orbit Decomposition**: Natural splitting by group orbits
/// 2. **Stabilizer Factorization**: Decomposition via stabilizer subgroups
/// 3. **Invariant Preservation**: Splits that preserve conservation laws
///
/// ## Key Properties
///
/// - Orbit elements share the same invariants
/// - Stabilizer subgroups provide natural boundaries
/// - Symmetry-preserving decompositions are unique modulo group action
/// - Boundaries emerge from symmetry breaking points
pub trait SymmetricDecomposition<P: Float>: Sized {
    /// Decompose by group orbits
    ///
    /// Splits the object into components corresponding to different group orbits.
    /// Each component represents elements that can be transformed into each other
    /// by the group action.
    ///
    /// # Arguments
    ///
    /// * `group` - The symmetry group to use for decomposition
    ///
    /// # Returns
    ///
    /// A vector of orbit components, each containing a representative element
    /// and information about the orbit structure.
    fn orbit_decompose(&self, group: &SymmetryGroup<P>) -> Vec<OrbitComponent<Self>>;
    
    /// Find natural boundaries based on symmetry breaking
    ///
    /// Identifies positions where the symmetry structure changes. These boundaries
    /// indicate natural splitting points for decomposition.
    ///
    /// # Arguments
    ///
    /// * `group` - The symmetry group to analyze
    ///
    /// # Returns
    ///
    /// A vector of symmetry boundaries, sorted by position.
    fn find_symmetry_boundaries(&self, group: &SymmetryGroup<P>) -> Vec<SymmetryBoundary>;
    
    /// Decompose while preserving specified symmetries
    ///
    /// Performs decomposition that maintains certain symmetries in each part.
    /// This is useful when specific invariants must be preserved.
    ///
    /// # Arguments
    ///
    /// * `group` - The symmetry group to use
    /// * `preserve` - List of symmetry types that must be preserved in each part
    ///
    /// # Returns
    ///
    /// A vector of decomposed parts, each preserving the specified symmetries,
    /// or an error if such decomposition is impossible.
    fn symmetry_preserving_decompose(
        &self,
        group: &SymmetryGroup<P>,
        preserve: &[SymmetryType],
    ) -> Result<Vec<Self>, CcmError>;
    
    /// Verify that a decomposition preserves symmetry properties
    ///
    /// Checks whether a proposed decomposition maintains the required
    /// mathematical relationships between the whole and its parts.
    ///
    /// # Arguments
    ///
    /// * `parts` - The proposed decomposition
    /// * `group` - The symmetry group to verify against
    ///
    /// # Returns
    ///
    /// `true` if the decomposition is valid, `false` otherwise.
    ///
    /// # Verification Criteria
    ///
    /// A valid decomposition must satisfy:
    /// 1. Parts reconstruct to the whole (up to group action)
    /// 2. Stabilizer compatibility: Stab(whole) ⊆ ∩ Stab(part_i)
    /// 3. Conservation laws are preserved
    /// 4. No information is lost or gained
    fn verify_symmetric_decomposition(
        &self,
        parts: &[Self],
        group: &SymmetryGroup<P>,
    ) -> bool;
}