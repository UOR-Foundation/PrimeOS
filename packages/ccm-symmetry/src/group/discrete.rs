//! Discrete group implementations
//! 
//! This module handles discrete groups that don't fit neatly
//! into finite or infinite categories, such as:
//! - Crystallographic groups
//! - Wallpaper groups
//! - Space groups

use num_traits::Float;
use crate::group::{GroupElement, SymmetryGroup};

/// Trait for discrete group operations
pub trait DiscreteGroup<P: Float> {
    /// Get the point group component
    fn point_group(&self) -> SymmetryGroup<P>;
    
    /// Get the translation subgroup
    fn translation_subgroup(&self) -> Option<SymmetryGroup<P>>;
    
    /// Check if element preserves discreteness
    fn preserves_lattice(&self, element: &GroupElement<P>) -> bool;
}

impl<P: Float> DiscreteGroup<P> for SymmetryGroup<P> {
    /// Get the point group component
    fn point_group(&self) -> SymmetryGroup<P> {
        // For discrete groups, extract the finite point group component
        // This is the subgroup of elements that fix the origin
        
        match &self.group_type {
            crate::group::GroupType::Finite { .. } => {
                // Already a point group
                self.clone()
            }
            _ => {
                // Extract elements that don't translate
                let mut point_elements = Vec::new();
                
                // Always include identity
                point_elements.push(self.identity());
                
                // For discrete groups, check which generators are pure rotations/reflections
                for gen in &self.generators {
                    if self.is_point_transformation(gen) {
                        point_elements.push(gen.clone());
                    }
                }
                
                SymmetryGroup {
                    dimension: self.dimension,
                    generators: point_elements.clone(),
                    group_type: crate::group::GroupType::Finite { elements: point_elements },
                    cached_order: None,
                }
            }
        }
    }
    
    /// Get the translation subgroup
    fn translation_subgroup(&self) -> Option<SymmetryGroup<P>> {
        // Extract pure translations
        let mut translation_generators = Vec::new();
        
        for gen in &self.generators {
            if self.is_pure_translation(gen) {
                translation_generators.push(gen.clone());
            }
        }
        
        if translation_generators.is_empty() {
            None
        } else {
            Some(SymmetryGroup {
                dimension: self.dimension,
                generators: translation_generators,
                group_type: crate::group::GroupType::DiscreteInfinite,
                cached_order: None,
            })
        }
    }
    
    /// Check if element preserves discreteness
    fn preserves_lattice(&self, element: &GroupElement<P>) -> bool {
        // Check if the element maps lattice points to lattice points
        // For integer lattices, this means integer coefficients
        
        element.params.iter().all(|&p| {
            let rounded = p.round();
            (p - rounded).abs() < P::epsilon()
        })
    }
}

impl<P: Float> SymmetryGroup<P> {
    /// Check if transformation is a point transformation (no translation)
    fn is_point_transformation(&self, element: &GroupElement<P>) -> bool {
        // A point transformation fixes the origin
        // For our representation, check if it's orthogonal/unitary
        
        // Simple heuristic: check if det = ±1 and preserves distances
        // For now, check if all parameters have magnitude close to 0 or 1
        element.params.iter().all(|&p| {
            let abs_p = p.abs();
            (abs_p - P::zero()).abs() < P::epsilon() || 
            (abs_p - P::one()).abs() < P::epsilon()
        })
    }
    
    /// Check if transformation is a pure translation
    fn is_pure_translation(&self, element: &GroupElement<P>) -> bool {
        // A pure translation has the form x → x + v
        // In matrix form, it's the identity plus a translation vector
        
        // For our simplified representation, check if it looks like
        // adding a constant vector
        let identity = self.identity();
        
        // Check if element - identity gives a valid translation vector
        let diff: Vec<P> = element.params.iter()
            .zip(identity.params.iter())
            .map(|(e, i)| *e - *i)
            .collect();
            
        // All components should be either 0 or the same non-zero value
        let non_zero_values: Vec<P> = diff.iter()
            .filter(|&&x| x.abs() > P::epsilon())
            .cloned()
            .collect();
            
        if non_zero_values.is_empty() {
            false // Identity is not a pure translation
        } else {
            // Check if all non-zero values are the same (up to sign)
            let first = non_zero_values[0].abs();
            non_zero_values.iter().all(|&x| (x.abs() - first).abs() < P::epsilon())
        }
    }
}