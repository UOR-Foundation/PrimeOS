//! Symmetry detection functions
//!
//! This module provides functions for detecting various types of symmetries
//! in Clifford elements.

use crate::{SymmetryGroup, SymmetryType, CliffordAction, actions::KleinCliffordAction};
use ccm_coherence::{CliffordElement, CliffordAlgebra, CoherentDecomposition};
use ccm_core::Float;
use num_traits::FromPrimitive;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Detect which symmetries are preserved by an element
///
/// Analyzes a Clifford element to determine which symmetries it possesses.
/// This function checks for various symmetry types and returns a list of
/// all detected symmetries.
///
/// # Arguments
///
/// * `element` - The Clifford element to analyze
/// * `group` - The symmetry group context
///
/// # Returns
///
/// A vector of symmetry types that the element preserves.
pub fn detect_preserved_symmetries<P: Float + FromPrimitive>(
    element: &CliffordElement<P>,
    group: &SymmetryGroup<P>,
) -> Vec<SymmetryType> {
    let mut preserved = Vec::new();
    
    // Check Klein symmetry (most common in CCM)
    if has_klein_symmetry(element) {
        preserved.push(SymmetryType::Klein);
    }
    
    // Check if this element has high symmetry (large stabilizer)
    if let Ok(algebra) = CliffordAlgebra::generate(element.dimension()) {
        let action = CliffordAction::new(algebra);
        let stabilizer = group.stabilizer(element, &action);
        
        // If stabilizer is non-trivial, element has symmetry
        if !stabilizer.generators.is_empty() {
            // Try to identify the type of symmetry
            if stabilizer.generators.len() == 1usize {
                preserved.push(SymmetryType::Reflection);
            } else if stabilizer.generators.len() >= 2usize {
                // Already added Klein if detected above
                if !preserved.contains(&SymmetryType::Klein) {
                    preserved.push(SymmetryType::Klein);
                }
            }
        }
    }
    
    preserved
}

/// Check if element has Klein V₄ symmetry
/// 
/// Klein symmetry detection checks multiple conditions:
/// 1. Invariance under bit flips on unity positions (n-2, n-1)
/// 2. Resonance preservation: R(k*x) = R(x) for all k in V_4
/// 3. Grade pattern: specific relationship between even grades
/// 4. Coherence structure: Klein orbits have equal coherence
/// 
/// # Mathematical foundation:
/// - Unity constraint: alpha[n-2] * alpha[n-1] = 1
/// - XOR homomorphism: R(a XOR b) = R(a) * R(b) for Klein elements
/// - Grade preservation under Klein action
///
/// # Arguments
///
/// * `element` - The Clifford element to check
///
/// # Returns
///
/// `true` if the element has Klein symmetry, `false` otherwise.
pub fn has_klein_symmetry<P: Float + FromPrimitive>(element: &CliffordElement<P>) -> bool {
    let n = element.dimension();
    
    #[cfg(test)]
    {
        // Checking Klein symmetry for element
        // Number of components
        for i in 0..element.num_components() {
            if let Some(c) = element.component(i) {
                if c.norm_sqr() > P::epsilon() {
                    // Component has non-zero value
                }
            }
        }
    }
    
    // Klein group requires at least 2 dimensions
    if n < 2 {
        return false;
    }
    
    // Check 1: Grade structure analysis
    // Klein-symmetric elements have specific grade patterns
    let grades = element.grade_decompose();
    
    #[cfg(test)]
    {
        // Grade decomposition
        for gc in &grades {
            if gc.coherence_norm > P::epsilon().to_f64().unwrap() {
                // Grade and norm
            }
        }
    }
    
    // Separate even and odd grade components
    let (even_grades, odd_grades): (Vec<_>, Vec<_>) = grades.iter()
        .partition(|gc| gc.grade % 2 == 0);
    
    // Klein symmetry requires non-trivial even grade components
    let has_even_content = even_grades.iter()
        .any(|gc| gc.coherence_norm > P::epsilon().to_f64().unwrap_or(1e-10));
    
    if !has_even_content {
        #[cfg(test)]
        // No significant even grade content
        return false;
    }
    
    // Check 2: Verify Klein action preserves coherence structure
    // For true Klein symmetry, the action of V_4 should preserve certain properties
    
    // Create a Klein group for testing
    if let Ok(klein_group) = SymmetryGroup::<P>::klein_group(n) {
        // Get the Klein group elements and action
        let action = KleinCliffordAction::new(n);
        
        // Check invariance under Klein group action
        // Element has Klein symmetry if g*element has same structure for all g in V_4
        if let Some(klein_elements) = klein_group.elements() {
                let klein_vec: Vec<_> = klein_elements.collect();
                
                // Check 2a: Coherence norm preservation
                let original_norm = element.coherence_norm();
                let mut norm_preserved = true;
                
                #[cfg(test)]
                // Checking Klein action norm preservation
                
                #[allow(unused_variables)]
                for (idx, g) in klein_vec.iter().enumerate() {
                    if let Ok(transformed) = klein_group.apply(g, element, &action) {
                        let transformed_norm = transformed.coherence_norm();
                        
                        #[cfg(test)]
                        {
                            // Klein element
                            // Check which components changed
                            let mut changes = 0;
                            for i in 0..element.num_components() {
                                if let (Some(orig), Some(trans)) = (element.component(i), transformed.component(i)) {
                                    if (orig - trans).norm_sqr() > P::epsilon() {
                                        changes += 1;
                                    }
                                }
                            }
                            // Components changed
                            // Norm preserved check
                        }
                        
                        if (transformed_norm - original_norm).abs() > P::epsilon() {
                            #[cfg(test)]
                            {
                                // Klein action doesn't preserve norm
                                // Norms differ by more than epsilon
                            }
                            norm_preserved = false;
                            break;
                        }
                    }
                }
                
                if !norm_preserved {
                    return false;
                }
                
                // Check 2b: Grade structure preservation under Klein action
                // Apply each Klein element and verify grade decomposition is compatible
                let mut grade_signatures = Vec::new();
                
                for g in &klein_vec {
                    if let Ok(transformed) = klein_group.apply(g, element, &action) {
                        let trans_grades = transformed.grade_decompose();
                        
                        // Create grade signature: which grades are present with significant norm
                        let signature: Vec<(usize, bool)> = (0..=n).map(|k| {
                            let has_grade = trans_grades.iter()
                                .any(|gc| gc.grade == k && P::from_f64(gc.coherence_norm).unwrap_or(P::zero()) > P::epsilon());
                            (k, has_grade)
                        }).collect();
                        
                        grade_signatures.push(signature);
                    }
                }
                
                // For Klein symmetry, certain grade patterns must be preserved
                // Check if all Klein transforms produce compatible grade signatures
                if grade_signatures.len() == 4usize { // V_4 has 4 elements
                    #[cfg(test)]
                    {
                        // Grade signatures analysis
                        for (_i, sig) in grade_signatures.iter().enumerate() {
                            // Klein element grades present
                            let _grades_present: Vec<_> = sig.iter()
                                .filter_map(|&(grade, present)| if present { Some(grade) } else { None })
                                .collect();
                        }
                    }
                    
                    // The identity element's signature
                    // let identity_sig = &grade_signatures[0];  // Not needed with new approach
                    
                    // Check Klein symmetry pattern:
                    // For n=8, XORing bits 6,7 can flip grade parity
                    // The pattern should be: identity and one element preserve grade parity,
                    // while two elements flip grade parity
                    let mut even_preserving = 0;
                    let mut odd_mapping = 0;
                    
                    for sig in &grade_signatures {
                        // Check if this signature has even grades
                        let has_even = (0..=n).step_by(2).any(|j| sig[j].1);
                        let has_odd = (1..=n).step_by(2).any(|j| sig[j].1);
                        
                        if has_even && !has_odd {
                            even_preserving += 1;
                        } else if has_odd && !has_even {
                            odd_mapping += 1;
                        }
                    }
                    
                    // For Klein symmetry of even elements, we expect:
                    // 2 elements preserve even grades, 2 elements map to odd grades
                    // For mixed elements, check if the Klein action shows systematic behavior
                    let pure_even_klein = even_preserving == 2 && odd_mapping == 2;
                    let all_even_klein = even_preserving == 4 && odd_mapping == 0;
                    
                    // For mixed elements, check if there's a consistent pattern
                    // All 4 Klein elements should have non-empty grade content
                    let all_have_content = grade_signatures.iter()
                        .all(|sig| sig.iter().any(|(_, present)| *present));
                    
                    let valid_klein_pattern = pure_even_klein || all_even_klein || 
                                            (all_have_content && norm_preserved);
                    
                    if !valid_klein_pattern {
                        // Invalid Klein symmetry pattern
                        return false;
                    }
                    
                    // Check 2c: Verify resonance-like properties
                    // Klein symmetry is deeply connected to resonance through unity positions
                    // Check if the element respects the Klein group's XOR-homomorphic structure
                    
                    // For elements with Klein symmetry, the sum of norms over Klein orbit
                    // should satisfy specific relationships
                    let mut orbit_norms = Vec::new();
                    for g in &klein_vec {
                        if let Ok(transformed) = klein_group.apply(g, element, &action) {
                            orbit_norms.push(transformed.coherence_norm());
                        }
                    }
                    
                    // Klein symmetric elements have equal norms across the orbit
                    // or norms that follow a specific pattern
                    if orbit_norms.len() == 4usize {
                        let first_norm = orbit_norms[0];
                        let all_equal = orbit_norms.iter().all(|&norm| {
                            (norm - first_norm).abs() < P::epsilon()
                        });
                        
                        if !all_equal {
                            // Check for pairwise equality pattern (characteristic of Klein group)
                            let pair1_equal = (orbit_norms[0] - orbit_norms[1]).abs() < P::epsilon() &&
                                             (orbit_norms[2] - orbit_norms[3]).abs() < P::epsilon();
                            let pair2_equal = (orbit_norms[0] - orbit_norms[2]).abs() < P::epsilon() &&
                                             (orbit_norms[1] - orbit_norms[3]).abs() < P::epsilon();
                            
                            if !pair1_equal && !pair2_equal {
                                return false;
                            }
                        }
                    }
                }
                
                // Check 3: Final verification - all checks must pass
                // We've verified:
                // - Coherence norm preservation under Klein action
                // - Grade structure compatibility
                // - Orbit norm patterns
                
                // Additionally check for characteristic Klein patterns in grade structure
                let has_klein_grade_pattern = {
                    // Klein symmetric elements often have:
                    // 1. Strong even-grade components
                    // 2. Grade structure that respects the 2^k pattern
                    // 3. Special relationships between grades differing by 2
                    
                    let even_norm_sq: f64 = even_grades.iter()
                        .map(|gc| gc.coherence_norm * gc.coherence_norm)
                        .sum();
                    let odd_norm_sq: f64 = odd_grades.iter()
                        .map(|gc| gc.coherence_norm * gc.coherence_norm)
                        .sum();
                    
                    #[cfg(test)]
                    {
                        // Grade pattern analysis
                        // Even norm squared
                        // Odd norm squared
                    }
                    
                    // Even grades should be significant for Klein symmetry
                    // For purely even elements (odd_norm_sq = 0), check even_norm_sq > 0
                    // For mixed elements, even grades should dominate
                    if odd_norm_sq.abs() < 1e-10 {
                        even_norm_sq > 1e-10  // Purely even element
                    } else {
                        even_norm_sq > odd_norm_sq * 0.1  // Mixed element with dominant even grades
                    }
                };
                
                #[cfg(test)]
                {
                    // has_klein_symmetry: Final results
                    // Grade components
                    // Even grades
                    // Odd grades
                    // Norm preservation
                    // Klein grade pattern test
                    // Final result
                }
                
                // Element has Klein symmetry if it passes all checks
                return has_klein_grade_pattern;
            }
    }
    
    // Fallback: just check for significant even grade content
    has_even_content
}