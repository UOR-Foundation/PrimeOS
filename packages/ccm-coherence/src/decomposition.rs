//! Inherent decomposition properties based on coherence structure
//!
//! This module implements decomposition functionality that emerges naturally from
//! the coherence metric and Clifford algebra structure. These properties are
//! inherent to CCM's coherence axiom (A1), not imposed algorithms.
//!
//! ## Mathematical Foundation
//!
//! Decomposition in coherence space is based on:
//! 1. **Grade Decomposition**: Natural splitting by Clifford grades
//! 2. **Coherence Minimization**: Finding optimal splits that minimize total coherence
//! 3. **Orthogonality**: Grade-wise orthogonality provides natural boundaries
//!
//! ## Key Properties
//!
//! - Grade components are orthogonal under coherence inner product
//! - Coherence norm satisfies triangle inequality
//! - Minimal coherence decompositions are unique
//! - Boundaries emerge from coherence gradient discontinuities

use crate::{CliffordElement, Coherence};
use ccm_core::{Float, CcmError};
use num_traits::FromPrimitive;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Natural decomposition based on coherence structure
pub trait CoherentDecomposition<P: Float>: Coherence<P> + Sized {
    /// Decompose by grade components
    fn grade_decompose(&self) -> Vec<GradeComponent<Self>>;
    
    /// Find natural boundaries based on coherence discontinuities
    fn find_coherence_boundaries(&self) -> Vec<CoherenceBoundary>;
    
    /// Decompose to minimize total coherence norm
    fn coherence_optimal_decompose(&self, target_parts: usize) -> Result<Vec<Self>, CcmError>;
    
    /// Verify that a decomposition preserves coherence properties
    fn verify_coherence_decomposition(&self, parts: &[Self]) -> bool;
}

/// A component of a specific grade
#[derive(Clone, Debug)]
pub struct GradeComponent<T> {
    /// The grade of this component
    pub grade: usize,
    /// The component itself
    pub component: T,
    /// Coherence norm of this component
    pub coherence_norm: f64,
}

/// A natural boundary in coherence space
#[derive(Clone, Debug)]
pub struct CoherenceBoundary {
    /// Grade where the boundary occurs
    pub grade: usize,
    /// Magnitude of coherence discontinuity
    pub discontinuity: f64,
    /// Type of boundary
    pub boundary_type: CoherenceBoundaryType,
}

#[derive(Clone, Debug, PartialEq)]
pub enum CoherenceBoundaryType {
    /// Transition between grades
    GradeTransition,
    /// Large gradient in coherence
    CoherenceGradientJump,
    /// Orthogonality boundary
    OrthogonalSplit,
    /// Composite of multiple indicators
    Composite,
}

/// Implementation for CliffordElement
impl<P: Float + FromPrimitive> CoherentDecomposition<P> for CliffordElement<P> {
    fn grade_decompose(&self) -> Vec<GradeComponent<Self>> {
        let mut components = Vec::new();
        
        // Get the maximum grade present
        let max_grade = self.max_grade();
        
        // Extract each grade component
        for k in 0..=max_grade {
            let component = self.grade(k);
            
            // Only include non-zero components
            let norm = component.coherence_norm();
            if norm > P::epsilon() {
                components.push(GradeComponent {
                    grade: k,
                    component,
                    coherence_norm: norm.to_f64().unwrap_or(0.0),
                });
            }
        }
        
        components
    }
    
    fn find_coherence_boundaries(&self) -> Vec<CoherenceBoundary> {
        let mut boundaries = Vec::new();
        let grade_components = self.grade_decompose();
        
        if grade_components.len() <= 1 {
            return boundaries;
        }
        
        // Find boundaries between grade components
        for i in 0..grade_components.len() - 1 {
            let current = &grade_components[i];
            let next = &grade_components[i + 1];
            
            // Grade transition boundary
            if next.grade != current.grade + 1 {
                boundaries.push(CoherenceBoundary {
                    grade: current.grade,
                    discontinuity: 0.0, // Exact boundary
                    boundary_type: CoherenceBoundaryType::GradeTransition,
                });
            }
            
            // Coherence gradient jump
            let norm_ratio = next.coherence_norm / current.coherence_norm;
            if norm_ratio > 10.0 || norm_ratio < 0.1 {
                boundaries.push(CoherenceBoundary {
                    grade: current.grade,
                    discontinuity: (norm_ratio.ln()).abs(),
                    boundary_type: CoherenceBoundaryType::CoherenceGradientJump,
                });
            }
        }
        
        // Orthogonal splits occur naturally between all grades
        for component in &grade_components {
            boundaries.push(CoherenceBoundary {
                grade: component.grade,
                discontinuity: 0.0,
                boundary_type: CoherenceBoundaryType::OrthogonalSplit,
            });
        }
        
        boundaries.sort_by_key(|b| b.grade);
        boundaries
    }
    
    fn coherence_optimal_decompose(&self, target_parts: usize) -> Result<Vec<Self>, CcmError> {
        // Start with grade decomposition
        let grade_components = self.grade_decompose();
        
        if grade_components.len() >= target_parts {
            // We have enough grade components
            // Return the target_parts components with highest coherence norms
            let mut sorted = grade_components;
            sorted.sort_by(|a, b| b.coherence_norm.partial_cmp(&a.coherence_norm).unwrap());
            
            Ok(sorted.into_iter()
                .take(target_parts)
                .map(|gc| gc.component)
                .collect())
        } else {
            // Need to subdivide some components
            // For now, return grade components
            // Future: implement finer subdivision strategies
            Ok(grade_components.into_iter()
                .map(|gc| gc.component)
                .collect())
        }
    }
    
    fn verify_coherence_decomposition(&self, parts: &[Self]) -> bool {
        // A valid coherence decomposition must:
        // 1. Preserve total coherence norm (with tolerance)
        // 2. Maintain grade orthogonality
        // 3. Sum to original element
        
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
        
        // Check grade orthogonality
        // Parts with different grades should be orthogonal
        for i in 0..parts.len() {
            for j in i+1..parts.len() {
                let part_i = &parts[i];
                let part_j = &parts[j];
                
                // If parts have different dominant grades, inner product should be near zero
                let inner = part_i.coherence_inner_product(part_j);
                if inner.abs() > tolerance {
                    // Check if they share grades
                    let i_grades = part_i.grade_decompose();
                    let j_grades = part_j.grade_decompose();
                    
                    let mut shares_grade = false;
                    for gi in &i_grades {
                        for gj in &j_grades {
                            if gi.grade == gj.grade {
                                shares_grade = true;
                                break;
                            }
                        }
                    }
                    
                    if !shares_grade {
                        // Different grades but non-zero inner product
                        return false;
                    }
                }
            }
        }
        
        true
    }
}

/// Conservation laws specific to coherence
pub mod conservation {
    use super::*;
    
    /// Coherence conservation modes
    #[derive(Clone, Debug, PartialEq)]
    pub enum CoherenceConservationMode {
        /// Sum of norms equals norm of sum (rare)
        Additive,
        /// Pythagorean theorem for orthogonal components
        Pythagorean,
        /// General triangle inequality
        TriangleInequality,
    }
    
    /// Verify coherence conservation for a decomposition
    pub fn verify_coherence_conservation<P: Float + FromPrimitive>(
        whole: &CliffordElement<P>,
        parts: &[CliffordElement<P>],
        mode: CoherenceConservationMode,
    ) -> bool {
        let whole_norm = whole.coherence_norm();
        let tolerance = P::epsilon() * P::from(100.0).unwrap();
        
        match mode {
            CoherenceConservationMode::Additive => {
                let parts_sum: P = parts.iter()
                    .map(|p| p.coherence_norm())
                    .fold(P::zero(), |a, b| a + b);
                (whole_norm - parts_sum).abs() < tolerance
            }
            CoherenceConservationMode::Pythagorean => {
                // Check if parts are orthogonal
                for i in 0..parts.len() {
                    for j in i+1..parts.len() {
                        let inner = parts[i].coherence_inner_product(&parts[j]);
                        if inner.abs() > tolerance {
                            return false; // Not orthogonal
                        }
                    }
                }
                
                // Verify Pythagorean theorem
                let parts_sum_squared: P = parts.iter()
                    .map(|p| {
                        let norm = p.coherence_norm();
                        norm * norm
                    })
                    .fold(P::zero(), |a, b| a + b);
                
                (whole_norm * whole_norm - parts_sum_squared).abs() < tolerance
            }
            CoherenceConservationMode::TriangleInequality => {
                // Verify triangle inequality: ||whole|| ≤ Σ||parts||
                let parts_sum: P = parts.iter()
                    .map(|p| p.coherence_norm())
                    .fold(P::zero(), |a, b| a + b);
                whole_norm <= parts_sum + tolerance
            }
        }
    }
}

/// Strategies for coherence-based decomposition
pub mod strategies {
    use super::*;
    
    /// Decompose at coherence gradient discontinuities
    pub fn decompose_at_gradient_jumps<P: Float + FromPrimitive>(
        element: &CliffordElement<P>,
        threshold: P,
    ) -> Vec<CliffordElement<P>> {
        let boundaries = element.find_coherence_boundaries();
        let mut parts = Vec::new();
        
        // Group by significant boundaries
        let significant: Vec<_> = boundaries.into_iter()
            .filter(|b| b.discontinuity > threshold.to_f64().unwrap_or(0.1))
            .collect();
        
        if significant.is_empty() {
            // No significant boundaries, return grade decomposition
            element.grade_decompose().into_iter()
                .map(|gc| gc.component)
                .collect()
        } else {
            // Split at significant boundaries
            let grades = element.grade_decompose();
            let mut current_part = CliffordElement::zero(element.dimension());
            
            for grade_comp in grades {
                let is_boundary = significant.iter()
                    .any(|b| b.grade == grade_comp.grade);
                
                if is_boundary && !current_part.is_zero() {
                    parts.push(current_part);
                    current_part = grade_comp.component;
                } else {
                    current_part = current_part + grade_comp.component;
                }
            }
            
            if !current_part.is_zero() {
                parts.push(current_part);
            }
            
            parts
        }
    }
    
    /// Find the decomposition that minimizes total coherence
    pub fn minimal_coherence_decomposition<P: Float + FromPrimitive>(
        element: &CliffordElement<P>,
        max_parts: usize,
    ) -> Vec<CliffordElement<P>> {
        // This is an optimization problem
        // For now, use grade decomposition as it's naturally minimal
        let grade_parts = element.grade_decompose();
        
        if grade_parts.len() <= max_parts {
            grade_parts.into_iter()
                .map(|gc| gc.component)
                .collect()
        } else {
            // Merge smallest components
            let mut sorted = grade_parts;
            sorted.sort_by(|a, b| a.coherence_norm.partial_cmp(&b.coherence_norm).unwrap());
            
            let mut result = Vec::new();
            let mut accumulated = CliffordElement::zero(element.dimension());
            let merge_count = sorted.len() - max_parts + 1;
            
            // Merge the smallest components
            for (i, gc) in sorted.into_iter().enumerate() {
                if i < merge_count {
                    accumulated = accumulated + gc.component;
                } else {
                    result.push(gc.component);
                }
            }
            
            if !accumulated.is_zero() {
                result.push(accumulated);
            }
            
            result
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    
    #[test]
    fn test_grade_decomposition() {
        // Create element with multiple grades
        let mut element = CliffordElement::<f64>::zero(3);
        
        // Set components for different grades
        // Grade 0: scalar (index 0)
        element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap();
        // Grade 1: vectors (indices 1, 2, 4)
        element.set_component(1, num_complex::Complex::new(2.0, 0.0)).unwrap();
        element.set_component(2, num_complex::Complex::new(3.0, 0.0)).unwrap();
        // Grade 2: bivector (index 3 = e1e2)
        element.set_component(3, num_complex::Complex::new(4.0, 0.0)).unwrap();
        
        let decomposition = element.grade_decompose();
        
        // Should have components with non-zero norms
        assert!(!decomposition.is_empty());
        // Check that we found components for different grades
        let grades: Vec<_> = decomposition.iter().map(|gc| gc.grade).collect();
        assert!(grades.contains(&0) || grades.contains(&1) || grades.contains(&2));
    }
    
    #[test]
    fn test_coherence_boundaries() {
        // Create element with distinct grade components
        let mut element = CliffordElement::<f64>::zero(3);
        
        // Grade 0: large scalar
        element.set_component(0, num_complex::Complex::new(10.0, 0.0)).unwrap();
        // Skip grade 1 to create a gap
        // Grade 2: large bivector  
        element.set_component(3, num_complex::Complex::new(100.0, 0.0)).unwrap();
        // Grade 3: trivector
        element.set_component(7, num_complex::Complex::new(5.0, 0.0)).unwrap();
        
        let boundaries = element.find_coherence_boundaries();
        
        // Should find boundaries between grades
        assert!(!boundaries.is_empty());
        assert!(boundaries.iter().any(|b| 
            matches!(b.boundary_type, CoherenceBoundaryType::GradeTransition)
        ));
    }
    
    #[test]
    fn test_verify_decomposition() {
        // Create a simple element
        let mut element = CliffordElement::<f64>::zero(3);
        element.set_component(1, num_complex::Complex::new(1.0, 0.0)).unwrap(); // e1
        element.set_component(2, num_complex::Complex::new(2.0, 0.0)).unwrap(); // e2
        
        // Create the parts
        let mut e1 = CliffordElement::<f64>::zero(3);
        e1.set_component(1, num_complex::Complex::new(1.0, 0.0)).unwrap();
        
        let mut e2 = CliffordElement::<f64>::zero(3);
        e2.set_component(2, num_complex::Complex::new(2.0, 0.0)).unwrap();
        
        // Valid decomposition: grade components
        assert!(element.verify_coherence_decomposition(&[e1.clone(), e2.clone()]));
        
        // Invalid: doesn't sum to original
        assert!(!element.verify_coherence_decomposition(&[e1.clone()]));
        
        // Invalid: empty decomposition
        assert!(!element.verify_coherence_decomposition(&[]));
    }
}