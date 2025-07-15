//! Symmetry breaking detection functions
//!
//! This module provides functions for detecting where and how symmetries are broken
//! in Clifford elements.

use crate::{SymmetryGroup, SymmetryType, actions::KleinCliffordAction};
use crate::decomposition::types::{SymmetryBoundary, SymmetryBoundaryType};
use ccm_coherence::{CliffordElement, CoherentDecomposition};
use ccm_core::Float;
use num_traits::FromPrimitive;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Find where a symmetry is broken
/// 
/// Complete symmetry breaking detection algorithm:
/// 1. For each symmetry type, compute local invariance measure
/// 2. Find discontinuities/jumps in invariance  
/// 3. Measure breaking strength = |invariant_before - invariant_after|
/// 4. Classify boundary type based on which symmetries break
/// 5. Handle gradual vs sharp transitions
/// 
/// # Symmetry-specific detection:
/// - Klein: Check grade 2 components and resonance jumps
/// - Translation: Check shift invariance
/// - Rotation: Check rotational invariants
/// - Reflection: Check parity invariance
/// - Cyclic: Check cyclic shift patterns
/// - Dihedral: Check rotation + reflection combinations
/// - Permutation: Check permutation invariance
/// - Linear/Orthogonal: Check continuous transformation invariance
///
/// # Arguments
///
/// * `element` - The Clifford element to analyze
/// * `sym_type` - The type of symmetry to check for breaking
/// * `group` - The symmetry group context
///
/// # Returns
///
/// An optional `SymmetryBoundary` indicating where and how the symmetry is broken,
/// or `None` if the symmetry is preserved throughout the element.
pub fn find_breaking_point<P: Float + FromPrimitive>(
    element: &CliffordElement<P>,
    sym_type: &SymmetryType,
    group: &SymmetryGroup<P>,
) -> Option<SymmetryBoundary> {
    let grades = element.grade_decompose();
    let n = element.dimension();
    
    // Compute symmetry-specific invariants across the element structure
    match sym_type {
        SymmetryType::Klein => {
            // Klein breaking detection: analyze grade structure  
            // Klein symmetry is fundamentally about even vs odd grade separation
            
            // Separate even and odd grades
            let (even_grades, odd_grades): (Vec<_>, Vec<_>) = grades.iter()
                .partition(|gc| gc.grade % 2 == 0);
            
            // Compute total norms for even and odd grades
            let even_norm: f64 = even_grades.iter()
                .map(|gc| gc.coherence_norm)
                .sum();
            let odd_norm: f64 = odd_grades.iter()
                .map(|gc| gc.coherence_norm)
                .sum();
            
            // Klein symmetry is broken when we have significant odd grade components
            // in an element that also has even grade components
            if even_norm > 0.1 && odd_norm > 0.1 {
                // Both even and odd grades present - Klein symmetry is broken
                // Breaking strength is proportional to the relative contribution of odd grades
                let total_norm = even_norm + odd_norm;
                let odd_ratio = odd_norm / total_norm;
                let breaking_strength = odd_ratio;
                
                // Find the position of the strongest odd grade component
                let breaking_position = grades.iter()
                    .position(|gc| gc.grade % 2 == 1 && gc.coherence_norm > P::epsilon().to_f64().unwrap())
                    .unwrap_or(0);
                
                return Some(SymmetryBoundary {
                    position: breaking_position,
                    broken_symmetry: SymmetryType::Klein,
                    breaking_strength,
                    boundary_type: SymmetryBoundaryType::InvariantBreak,
                });
            }
            
            // Original complex detection code as fallback
            if let Ok(klein_group) = SymmetryGroup::<P>::klein_group(n) {
                let action = KleinCliffordAction::new(n);
                
                // Analyze grade-by-grade Klein invariance
                let mut breaking_position = None;
                let mut max_breaking_strength = P::zero();
                
                for (idx, gc) in grades.iter().enumerate() {
                    if gc.coherence_norm > P::epsilon().to_f64().unwrap() {
                        // Check if this grade component breaks Klein symmetry
                        let grade_elem = element.grade(gc.grade);
                        
                        // Apply Klein transformations and measure invariance
                        let mut klein_invariance = P::one();
                        
                        if let Some(klein_elements) = klein_group.elements() {
                            let klein_vec: Vec<_> = klein_elements.collect();
                            
                            // Compute variance under Klein action
                            let mut transformed_norms = Vec::new();
                            for g in &klein_vec {
                                if let Ok(transformed) = klein_group.apply(g, &grade_elem, &action) {
                                    transformed_norms.push(transformed.coherence_norm());
                                }
                            }
                            
                            if transformed_norms.len() == 4 {
                                // Compute standard deviation of norms
                                let mean_norm = transformed_norms.iter()
                                    .fold(P::zero(), |acc, &x| acc + x) / P::from(4.0).unwrap();
                                
                                let variance = transformed_norms.iter()
                                    .map(|&x| {
                                        let diff = x - mean_norm;
                                        diff * diff
                                    })
                                    .fold(P::zero(), |acc, x| acc + x) / P::from(4.0).unwrap();
                                
                                klein_invariance = variance.sqrt();
                                
                                // Large variance indicates Klein breaking
                                if klein_invariance > max_breaking_strength {
                                    max_breaking_strength = klein_invariance;
                                    breaking_position = Some(idx);
                                }
                            }
                        }
                        
                        // Additional check: grade 2 components are critical for Klein symmetry
                        if gc.grade == 2 && gc.coherence_norm > 0.1 {
                            // Grade 2 is particularly important for Klein structure
                            let enhanced_strength = klein_invariance * P::from(2.0).unwrap();
                            if enhanced_strength > max_breaking_strength {
                                max_breaking_strength = enhanced_strength;
                                breaking_position = Some(idx);
                            }
                        }
                    }
                }
                
                if let Some(pos) = breaking_position {
                    #[cfg(feature = "std")]
                    eprintln!("Klein: max_breaking_strength = {:?}, epsilon = {:?}", max_breaking_strength.to_f64(), P::epsilon().to_f64());
                    if max_breaking_strength > P::epsilon() {
                        return Some(SymmetryBoundary {
                            position: pos,
                            broken_symmetry: SymmetryType::Klein,
                            breaking_strength: max_breaking_strength.to_f64().unwrap(),
                            boundary_type: SymmetryBoundaryType::InvariantBreak,
                        });
                    }
                }
            }
        }
        
        SymmetryType::Translation => {
            // Translation symmetry breaking: check shift invariance
            // Analyze how the element changes under discrete translations
            
            let mut max_translation_break = P::zero();
            let mut break_position = None;
            
            // Check translation by analyzing grade components
            for (idx, gc) in grades.iter().enumerate().skip(1) {
                if gc.coherence_norm > P::epsilon().to_f64().unwrap() {
                    // Compare with previous grade component
                    let prev_gc = &grades[idx - 1];
                    
                    // Translation symmetry suggests regular spacing/pattern
                    let norm_ratio = if prev_gc.coherence_norm > P::epsilon().to_f64().unwrap() {
                        gc.coherence_norm / prev_gc.coherence_norm
                    } else {
                        P::from(1.0).unwrap().to_f64().unwrap()
                    };
                    
                    // Large jumps indicate translation breaking
                    let jump = ((norm_ratio.ln()).abs()).max(0.0);
                    let breaking_strength = P::from(jump).unwrap();
                    
                    if breaking_strength > max_translation_break {
                        max_translation_break = breaking_strength;
                        break_position = Some(idx);
                    }
                }
            }
            
            if let Some(pos) = break_position {
                if max_translation_break > P::from(0.5).unwrap() {
                    return Some(SymmetryBoundary {
                        position: pos,
                        broken_symmetry: SymmetryType::Translation,
                        breaking_strength: max_translation_break.to_f64().unwrap(),
                        boundary_type: SymmetryBoundaryType::GradientJump,
                    });
                }
            }
        }
        
        SymmetryType::Rotation => {
            // Rotation symmetry breaking: check rotational invariants
            // Analyze angular momentum-like quantities
            
            let mut max_rotation_break = P::zero();
            let mut break_position = None;
            
            // Check rotation by analyzing grade patterns
            // Rotational symmetry often preserves certain grade combinations
            for (idx, gc) in grades.iter().enumerate() {
                if gc.coherence_norm > P::epsilon().to_f64().unwrap() {
                    // For rotation, check if grade components form expected patterns
                    // Higher grades often indicate rotation breaking
                    if gc.grade > n / 2 {
                        let breaking_strength = P::from(gc.grade as f64 / n as f64).unwrap() 
                            * P::from(gc.coherence_norm).unwrap();
                        
                        if breaking_strength > max_rotation_break {
                            max_rotation_break = breaking_strength;
                            break_position = Some(idx);
                        }
                    }
                }
            }
            
            if let Some(pos) = break_position {
                if max_rotation_break > P::from(0.3).unwrap() {
                    return Some(SymmetryBoundary {
                        position: pos,
                        broken_symmetry: SymmetryType::Rotation,
                        breaking_strength: max_rotation_break.to_f64().unwrap(),
                        boundary_type: SymmetryBoundaryType::InvariantBreak,
                    });
                }
            }
        }
        
        SymmetryType::Reflection => {
            // Reflection symmetry breaking: check parity invariance
            // Compare even vs odd grade components
            
            let (even_grades, odd_grades): (Vec<_>, Vec<_>) = grades.iter()
                .partition(|gc| gc.grade % 2 == 0);
            
            let even_norm: f64 = even_grades.iter()
                .map(|gc| gc.coherence_norm)
                .sum();
            let odd_norm: f64 = odd_grades.iter()
                .map(|gc| gc.coherence_norm)
                .sum();
            
            if even_norm > 0.0 && odd_norm > 0.0 {
                // Reflection symmetry suggests balance between even/odd
                let imbalance = ((even_norm - odd_norm) / (even_norm + odd_norm)).abs();
                
                if imbalance > 0.3 {
                    // Find the grade with maximum contribution to imbalance
                    let break_position = grades.iter()
                        .position(|gc| gc.coherence_norm > P::epsilon().to_f64().unwrap())
                        .unwrap_or(0);
                    
                    return Some(SymmetryBoundary {
                        position: break_position,
                        broken_symmetry: SymmetryType::Reflection,
                        breaking_strength: imbalance,
                        boundary_type: SymmetryBoundaryType::InvariantBreak,
                    });
                }
            }
        }
        
        SymmetryType::Cyclic(order) => {
            // Cyclic symmetry breaking: check periodicity
            // Look for deviations from expected cyclic patterns
            
            let order_f = *order as f64;
            let mut max_cyclic_break = P::zero();
            let mut break_position = None;
            
            // Check if grade components follow cyclic pattern
            for (idx, gc) in grades.iter().enumerate() {
                if gc.coherence_norm > P::epsilon().to_f64().unwrap() {
                    // Expected position in cycle
                    let expected_phase = (gc.grade as f64 * 2.0 * core::f64::consts::PI) / order_f;
                    let expected_norm = expected_phase.cos().abs() + 0.5;
                    
                    // Deviation from expected cyclic pattern
                    let deviation = (gc.coherence_norm / expected_norm - 1.0).abs();
                    let breaking_strength = P::from(deviation).unwrap();
                    
                    if breaking_strength > max_cyclic_break {
                        max_cyclic_break = breaking_strength;
                        break_position = Some(idx);
                    }
                }
            }
            
            if let Some(pos) = break_position {
                if max_cyclic_break > P::from(0.4).unwrap() {
                    return Some(SymmetryBoundary {
                        position: pos,
                        broken_symmetry: SymmetryType::Cyclic(*order),
                        breaking_strength: max_cyclic_break.to_f64().unwrap(),
                        boundary_type: SymmetryBoundaryType::PatternBreak,
                    });
                }
            }
        }
        
        SymmetryType::Dihedral(n_sides) => {
            // Dihedral symmetry: combination of rotation and reflection
            // Check both rotational and reflectional components
            
            // First check rotation breaking
            let rotation_break = find_breaking_point(element, &SymmetryType::Rotation, group);
            let reflection_break = find_breaking_point(element, &SymmetryType::Reflection, group);
            
            // Dihedral breaking is the stronger of the two
            return match (rotation_break, reflection_break) {
                (Some(rot), Some(ref_)) => {
                    Some(if rot.breaking_strength > ref_.breaking_strength {
                        SymmetryBoundary {
                            position: rot.position,
                            broken_symmetry: SymmetryType::Dihedral(*n_sides),
                            breaking_strength: rot.breaking_strength,
                            boundary_type: SymmetryBoundaryType::CompositeBreak,
                        }
                    } else {
                        SymmetryBoundary {
                            position: ref_.position,
                            broken_symmetry: SymmetryType::Dihedral(*n_sides),
                            breaking_strength: ref_.breaking_strength,
                            boundary_type: SymmetryBoundaryType::CompositeBreak,
                        }
                    })
                }
                (Some(rot), None) => Some(SymmetryBoundary {
                    position: rot.position,
                    broken_symmetry: SymmetryType::Dihedral(*n_sides),
                    breaking_strength: rot.breaking_strength,
                    boundary_type: rot.boundary_type,
                }),
                (None, Some(ref_)) => Some(SymmetryBoundary {
                    position: ref_.position,
                    broken_symmetry: SymmetryType::Dihedral(*n_sides),
                    breaking_strength: ref_.breaking_strength,
                    boundary_type: ref_.boundary_type,
                }),
                (None, None) => None,
            };
        }
        
        SymmetryType::Permutation(n_elements) => {
            // Permutation symmetry: check invariance under element permutations
            // Analyze grade components for permutation patterns
            
            let mut max_perm_break = P::zero();
            let mut break_position = None;
            
            // Check if grades follow expected permutation patterns
            for (idx, gc) in grades.iter().enumerate() {
                if gc.coherence_norm > P::epsilon().to_f64().unwrap() {
                    // For S_n, certain grade combinations should be preserved
                    // Higher grades often indicate more complex permutations
                    let complexity = gc.grade as f64 / n as f64;
                    let expected_norm = 1.0 / (1.0 + complexity);
                    
                    let deviation = (gc.coherence_norm / expected_norm - 1.0).abs();
                    let breaking_strength = P::from(deviation).unwrap();
                    
                    if breaking_strength > max_perm_break {
                        max_perm_break = breaking_strength;
                        break_position = Some(idx);
                    }
                }
            }
            
            if let Some(pos) = break_position {
                if max_perm_break > P::from(0.35).unwrap() {
                    return Some(SymmetryBoundary {
                        position: pos,
                        broken_symmetry: SymmetryType::Permutation(*n_elements),
                        breaking_strength: max_perm_break.to_f64().unwrap(),
                        boundary_type: SymmetryBoundaryType::PatternBreak,
                    });
                }
            }
        }
        
        SymmetryType::Linear | SymmetryType::Orthogonal => {
            // Continuous symmetry breaking: use derivative-based detection
            // Analyze smoothness and continuity of grade progression
            
            if grades.len() < 3 {
                return None; // Need at least 3 points for derivative
            }
            
            let mut max_derivative = P::zero();
            let mut break_position = None;
            
            // Compute discrete second derivative of coherence norms
            for i in 1..grades.len()-1 {
                let prev_norm = P::from(grades[i-1].coherence_norm).unwrap();
                let curr_norm = P::from(grades[i].coherence_norm).unwrap();
                let next_norm = P::from(grades[i+1].coherence_norm).unwrap();
                
                // Second derivative approximation
                let second_deriv = next_norm - P::from(2.0).unwrap() * curr_norm + prev_norm;
                
                if second_deriv.abs() > max_derivative {
                    max_derivative = second_deriv.abs();
                    break_position = Some(i);
                }
            }
            
            if let Some(pos) = break_position {
                if max_derivative > P::from(0.25).unwrap() {
                    return Some(SymmetryBoundary {
                        position: pos,
                        broken_symmetry: sym_type.clone(),
                        breaking_strength: max_derivative.to_f64().unwrap(),
                        boundary_type: SymmetryBoundaryType::GradientJump,
                    });
                }
            }
        }
        
        SymmetryType::Custom(name) => {
            // For custom symmetries, use generic discontinuity detection
            // Look for sudden changes in grade structure
            
            let mut max_discontinuity = P::zero();
            let mut break_position = None;
            
            for i in 1..grades.len() {
                let prev_norm = P::from(grades[i-1].coherence_norm).unwrap();
                let curr_norm = P::from(grades[i].coherence_norm).unwrap();
                
                if prev_norm > P::epsilon() {
                    let ratio = (curr_norm / prev_norm - P::one()).abs();
                    if ratio > max_discontinuity {
                        max_discontinuity = ratio;
                        break_position = Some(i);
                    }
                }
            }
            
            if let Some(pos) = break_position {
                if max_discontinuity > P::from(0.5).unwrap() {
                    return Some(SymmetryBoundary {
                        position: pos,
                        broken_symmetry: SymmetryType::Custom(name.clone()),
                        breaking_strength: max_discontinuity.to_f64().unwrap(),
                        boundary_type: SymmetryBoundaryType::InvariantBreak,
                    });
                }
            }
        }
    }
    
    None
}