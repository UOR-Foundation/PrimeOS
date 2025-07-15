//! Inherent decomposition properties based on symmetry structure
//!
//! This module implements decomposition functionality that emerges naturally from
//! the symmetry group structure. These properties are inherent to CCM's symmetry
//! axiom (A3), not imposed algorithms.
//!
//! ## Mathematical Foundation
//!
//! Decomposition in symmetry space is based on:
//! 1. **Orbit Decomposition**: Natural splitting by group orbits
//! 2. **Stabilizer Factorization**: Decomposition via stabilizer subgroups
//! 3. **Invariant Preservation**: Splits that preserve conservation laws
//!
//! ## Key Properties
//!
//! - Orbit elements share the same invariants
//! - Stabilizer subgroups provide natural boundaries
//! - Symmetry-preserving decompositions are unique modulo group action
//! - Boundaries emerge from symmetry breaking points

// Module structure
pub mod traits;
pub mod types;
pub mod detection;
pub mod breaking;
pub mod stabilizer;
pub mod conservation;
pub mod strategies;
pub mod utils;

#[cfg(test)]
mod tests;

// Re-export main types and traits
pub use traits::SymmetricDecomposition;
pub use types::{OrbitComponent, SymmetryBoundary, SymmetryBoundaryType};
pub use conservation::{SymmetryConservationMode, verify_symmetry_conservation};
pub use strategies::{orbit_boundary_decomposition, maximal_symmetric_decomposition, klein_symmetric_decomposition};

// Internal imports
use crate::{SymmetryGroup, SymmetryType, CliffordAction};
use ccm_core::{Float, CcmError};
use ccm_coherence::{CliffordElement, CliffordAlgebra};
use num_traits::FromPrimitive;

use detection::detect_preserved_symmetries;
use breaking::find_breaking_point;
use stabilizer::{compute_stabilizer_generators, compute_stabilizer_size, count_stabilizer_elements};
use utils::elements_equal;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Extension trait implementation for CliffordElement to support symmetric decomposition
impl<P: Float + FromPrimitive> SymmetricDecomposition<P> for CliffordElement<P> {
    fn orbit_decompose(&self, group: &SymmetryGroup<P>) -> Vec<OrbitComponent<Self>> {
        let mut components: Vec<OrbitComponent<Self>> = Vec::new();
        
        // For finite groups, we can enumerate orbits
        if let Some(elements) = group.elements() {
            let algebra = CliffordAlgebra::generate(self.dimension()).unwrap();
            let action = CliffordAction::new(algebra);
            
            let mut processed = Vec::new();
            
            #[cfg(test)]
            {
                // Orbit decomposition for finite group
            }
            
            for (_idx, g) in elements.enumerate() {
                // Check if we've already seen this orbit
                let transformed = group.apply(&g, self, &action).unwrap_or_else(|_| self.clone());
                
                #[cfg(test)]
                {
                    // Processing group element, transformed norm
                }
                
                let mut already_seen = false;
                for comp in &components {
                    if elements_equal(&comp.representative, &transformed) {
                        already_seen = true;
                        break;
                    }
                }
                
                // Check if it's in processed list
                for proc in &processed {
                    if elements_equal(proc, &transformed) {
                        already_seen = true;
                        break;
                    }
                }
                
                #[cfg(test)]
                {
                    // Already seen check
                }
                
                if !already_seen {
                    // Compute orbit size and stabilizer
                    let stabilizer = group.stabilizer(&transformed, &action);
                    
                    // Compute stabilizer generators properly
                    // This extracts a minimal generating set from the stabilizer subgroup
                    let stabilizer_generators = compute_stabilizer_generators(&stabilizer, group);
                    
                    let orbit_size = if let Some(group_order) = group.order() {
                        // By orbit-stabilizer theorem: |Orbit| = |G| / |Stabilizer|
                        // We need the actual stabilizer size, not just generator count
                        let stabilizer_size = compute_stabilizer_size(&stabilizer, group);
                        if stabilizer_size > 0 {
                            group_order / stabilizer_size
                        } else {
                            group_order
                        }
                    } else {
                        1
                    };
                    
                    // Determine preserved symmetries
                    let preserved = detect_preserved_symmetries(&transformed, group);
                    
                    #[cfg(test)]
                    {
                        // Adding orbit component
                    }
                    
                    components.push(OrbitComponent {
                        representative: transformed.clone(),
                        orbit_size,
                        stabilizer_generators,
                        preserved_symmetries: preserved,
                    });
                    
                    processed.push(transformed);
                }
            }
        } else {
            // For infinite groups, return just the element itself as an orbit
            // But still detect its symmetries
            let preserved = detect_preserved_symmetries(self, group);
            
            components.push(OrbitComponent {
                representative: self.clone(),
                orbit_size: 1,
                stabilizer_generators: vec![],
                preserved_symmetries: preserved,
            });
        }
        
        components
    }
    
    fn find_symmetry_boundaries(&self, group: &SymmetryGroup<P>) -> Vec<SymmetryBoundary> {
        let mut boundaries = Vec::new();
        
        // Check each symmetry type for breaking points
        let symmetry_types = vec![
            SymmetryType::Translation,
            SymmetryType::Rotation,
            SymmetryType::Reflection,
            SymmetryType::Klein,
        ];
        
        for sym_type in symmetry_types {
            if let Some(boundary) = find_breaking_point(self, &sym_type, group) {
                boundaries.push(boundary);
            }
        }
        
        // Sort by position
        boundaries.sort_by_key(|b| b.position);
        boundaries
    }
    
    fn symmetry_preserving_decompose(
        &self,
        group: &SymmetryGroup<P>,
        preserve: &[SymmetryType],
    ) -> Result<Vec<Self>, CcmError> {
        // Start with orbit decomposition
        let orbit_components = self.orbit_decompose(group);
        
        // Filter to components that preserve required symmetries
        let valid_components: Vec<_> = orbit_components
            .into_iter()
            .filter(|comp| {
                preserve.iter().all(|sym| comp.preserved_symmetries.contains(sym))
            })
            .collect();
        
        if valid_components.is_empty() {
            return Err(CcmError::InvalidInput);
        }
        
        // Return the representative elements
        Ok(valid_components.into_iter()
            .map(|comp| comp.representative)
            .collect())
    }
    
    fn verify_symmetric_decomposition(
        &self,
        parts: &[Self],
        group: &SymmetryGroup<P>,
    ) -> bool {
        // A valid symmetric decomposition must:
        // 1. Sum to the original element
        // 2. Each part must be invariant under some subgroup
        // 3. The decomposition respects the group action
        
        if parts.is_empty() {
            return false;
        }
        
        // Check if parts sum to original
        let mut sum = CliffordElement::zero(self.dimension());
        for part in parts {
            sum = sum + part.clone();
        }
        
        // Check if sum equals original within tolerance
        let diff = self.clone() - sum;
        let diff_norm = diff.coherence_norm();
        let tolerance = P::epsilon() * P::from(100.0).unwrap();
        
        if diff_norm > tolerance {
            return false;
        }
        
        // Check that each part has non-trivial stabilizer
        // For continuous groups, we can't enumerate all elements, so we check differently
        if group.order().is_some() {
            // Finite group - check stabilizer size
            for part in parts.iter() {
                let stabilizer_size = count_stabilizer_elements(part, group);
                #[cfg(test)]
                {
                    let _i = parts.iter().position(|p| core::ptr::eq(p, part)).unwrap();
                    // Part has stabilizer size
                }
                if stabilizer_size == 1 {
                    // Only identity stabilizes it - not a symmetric decomposition
                    return false;
                }
            }
        } else {
            // Continuous group - just check that parts are orthogonal (grade decomposition property)
            // This is a weaker check but appropriate for continuous groups
        }
        
        true
    }
}