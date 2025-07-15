//! Strategies for symmetry-based decomposition
//!
//! This module provides various strategies for decomposing Clifford elements
//! based on their symmetry properties.

use crate::{SymmetryGroup, SymmetricDecomposition};
use ccm_coherence::{CliffordElement, CoherentDecomposition};
use ccm_core::Float;
use num_traits::FromPrimitive;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Decompose along orbit boundaries
///
/// This strategy decomposes an element by finding its group orbits and
/// extracting the representative from each orbit.
///
/// # Arguments
///
/// * `element` - The Clifford element to decompose
/// * `group` - The symmetry group
///
/// # Returns
///
/// A vector of representative elements, one from each orbit
pub fn orbit_boundary_decomposition<P: Float + FromPrimitive>(
    element: &CliffordElement<P>,
    group: &SymmetryGroup<P>,
) -> Vec<CliffordElement<P>> {
    let orbits = element.orbit_decompose(group);
    orbits.into_iter()
        .map(|orbit| orbit.representative)
        .collect()
}

/// Decompose by maximal symmetric components
///
/// This strategy iteratively extracts parts with maximal symmetry
/// (largest stabilizer subgroups) until the element is fully decomposed.
///
/// # Arguments
///
/// * `element` - The Clifford element to decompose
/// * `group` - The symmetry group
///
/// # Returns
///
/// A vector of components ordered by decreasing symmetry
pub fn maximal_symmetric_decomposition<P: Float + FromPrimitive>(
    element: &CliffordElement<P>,
    group: &SymmetryGroup<P>,
) -> Vec<CliffordElement<P>> {
    // Find components with maximal symmetry
    let mut components = Vec::new();
    let mut remainder = element.clone();
    
    // Iteratively extract maximally symmetric parts
    while remainder.coherence_norm() > P::epsilon() {
        if let Some(symmetric_part) = extract_maximal_symmetric(&remainder, group) {
            components.push(symmetric_part.clone());
            remainder = remainder - symmetric_part;
        } else {
            // No more symmetric parts - add remainder
            components.push(remainder);
            break;
        }
    }
    
    components
}

/// Extract the part with maximal symmetry from an element
///
/// Finds the orbit component with the largest stabilizer subgroup.
///
/// # Arguments
///
/// * `element` - The element to analyze
/// * `group` - The symmetry group
///
/// # Returns
///
/// The component with the largest stabilizer, or None if decomposition fails
fn extract_maximal_symmetric<P: Float + FromPrimitive>(
    element: &CliffordElement<P>,
    group: &SymmetryGroup<P>,
) -> Option<CliffordElement<P>> {
    // Find the part with the largest stabilizer
    let orbit_components = element.orbit_decompose(group);
    
    orbit_components.into_iter()
        .max_by_key(|comp| comp.stabilizer_generators.len())
        .map(|comp| comp.representative)
}

/// Decompose by extracting Klein-symmetric (even grade) components
///
/// This strategy separates even-grade components (which have Klein symmetry)
/// from odd-grade components.
///
/// # Arguments
///
/// * `element` - The Clifford element to decompose
///
/// # Returns
///
/// A vector containing the even-grade component (if non-zero) followed by
/// the odd-grade component (if non-zero)
pub fn klein_symmetric_decomposition<P: Float + FromPrimitive>(
    element: &CliffordElement<P>,
) -> Vec<CliffordElement<P>> {
    // Klein symmetry is associated with even grades
    let grades = element.grade_decompose();
    
    let mut components = Vec::new();
    
    // Group even-grade components
    let mut even_component = CliffordElement::zero(element.dimension());
    let mut odd_component = CliffordElement::zero(element.dimension());
    
    for gc in grades {
        if gc.grade % 2 == 0 {
            // Even grade - Klein symmetric
            even_component = even_component + gc.component;
        } else {
            // Odd grade - not Klein symmetric
            odd_component = odd_component + gc.component;
        }
    }
    
    // Add non-zero components
    if even_component.coherence_norm() > P::epsilon() {
        components.push(even_component);
    }
    if odd_component.coherence_norm() > P::epsilon() {
        components.push(odd_component);
    }
    
    components
}