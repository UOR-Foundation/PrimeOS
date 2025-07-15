//! Conservation laws specific to symmetry decomposition
//!
//! This module provides functionality for verifying that decompositions
//! preserve important mathematical properties and conservation laws.

use crate::SymmetryGroup;
use crate::decomposition::{stabilizer::{calculate_orbit_size, verify_stabilizer_compatibility}, utils::{parts_sum, invariants_equal}};
use ccm_coherence::CliffordElement;
use ccm_core::Float;
use num_traits::FromPrimitive;

/// Symmetry conservation modes
///
/// Different types of conservation laws that can be verified
/// during decomposition.
#[derive(Clone, Debug, PartialEq)]
pub enum SymmetryConservationMode {
    /// Orbit size is preserved
    ///
    /// The sum of orbit sizes of parts equals the orbit size of the whole
    OrbitSize,
    
    /// Stabilizer structure is preserved
    ///
    /// Stabilizers of parts are compatible with the stabilizer of the whole
    StabilizerStructure,
    
    /// Invariants are preserved
    ///
    /// Group invariants are conserved across decomposition
    Invariants,
}

/// Verify symmetry conservation for a decomposition
///
/// Checks that a decomposition preserves the specified conservation law.
///
/// # Arguments
///
/// * `whole` - The complete element before decomposition
/// * `parts` - The decomposed parts
/// * `group` - The symmetry group
/// * `mode` - Which conservation law to verify
///
/// # Returns
///
/// `true` if the conservation law is satisfied, `false` otherwise
pub fn verify_symmetry_conservation<P: Float + FromPrimitive>(
    whole: &CliffordElement<P>,
    parts: &[CliffordElement<P>],
    group: &SymmetryGroup<P>,
    mode: SymmetryConservationMode,
) -> bool {
    match mode {
        SymmetryConservationMode::OrbitSize => {
            // Check that total orbit size is preserved
            let whole_orbit_size = calculate_orbit_size(whole, group);
            let parts_orbit_sum: usize = parts.iter()
                .map(|p| calculate_orbit_size(p, group))
                .sum();
            whole_orbit_size == parts_orbit_sum
        }
        SymmetryConservationMode::StabilizerStructure => {
            // Check that stabilizer subgroups are compatible
            verify_stabilizer_compatibility(whole, parts, group)
        }
        SymmetryConservationMode::Invariants => {
            // Check that all invariants are preserved
            verify_invariant_preservation(whole, parts, group)
        }
    }
}

/// Verify that group invariants are preserved in decomposition
///
/// # Arguments
///
/// * `whole` - The complete element
/// * `parts` - The decomposed parts
/// * `group` - The symmetry group
///
/// # Returns
///
/// `true` if invariants are preserved within tolerance
fn verify_invariant_preservation<P: Float + FromPrimitive>(
    whole: &CliffordElement<P>,
    parts: &[CliffordElement<P>],
    group: &SymmetryGroup<P>,
) -> bool {
    // Check that group invariants are preserved
    let whole_invariants = group.compute_invariants(whole);
    let parts_invariants = group.compute_invariants(&parts_sum(parts));
    
    // Compare invariants within tolerance
    invariants_equal(&whole_invariants, &parts_invariants)
}