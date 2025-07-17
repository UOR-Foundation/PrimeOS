//! Invariant quantities under group action

use crate::{discrete::ResonanceAutomorphism, group::SymmetryGroup, lie_algebra::LieAlgebraElement};
use ccm_coherence::{coherence_norm, CliffordElement};
use ccm_core::Float;

#[cfg(feature = "alloc")]
use alloc::{boxed::Box, format, string::String, vec, vec::Vec};

/// Type alias for invariant functions
pub type InvariantFunction<P> = Box<dyn Fn(&CliffordElement<P>) -> P>;

/// Trait for invariant quantities
pub trait Invariant<P: Float> {
    /// Check if quantity is invariant under group action
    fn is_invariant(&self, group: &SymmetryGroup<P>) -> bool;

    /// Find generating invariants
    fn generating_invariants(&self) -> Vec<InvariantFunction<P>>;
}

/// A conserved quantity from Noether's theorem
pub struct ConservedQuantity<P: Float> {
    /// Name of the conserved quantity
    pub name: String,
    /// The symmetry generator
    pub symmetry: LieAlgebraElement<P>,
    /// Function computing the conserved quantity
    pub quantity: InvariantFunction<P>,
}

impl<P: Float> ConservedQuantity<P> {
    /// Create a new conserved quantity
    pub fn new(
        name: String,
        symmetry: LieAlgebraElement<P>,
        quantity: InvariantFunction<P>,
    ) -> Self {
        Self {
            name,
            symmetry,
            quantity,
        }
    }

    /// Evaluate the conserved quantity
    pub fn evaluate(&self, element: &CliffordElement<P>) -> P {
        (self.quantity)(element)
    }
}

/// Coherence norm is invariant under symmetry action
pub struct CoherenceInvariant;

impl<P: Float> Invariant<P> for CoherenceInvariant {
    fn is_invariant(&self, _group: &SymmetryGroup<P>) -> bool {
        // Coherence norm is always invariant by Axiom A3
        true
    }

    fn generating_invariants(&self) -> Vec<Box<dyn Fn(&CliffordElement<P>) -> P>> {
        vec![Box::new(|x| x.coherence_norm())]
    }
}

/// Grade components are invariant under symmetry action
pub struct GradeInvariant {
    /// Which grade to check
    pub grade: usize,
}

impl<P: Float> Invariant<P> for GradeInvariant {
    fn is_invariant(&self, _group: &SymmetryGroup<P>) -> bool {
        // Grade structure is preserved by Axiom A3
        true
    }

    fn generating_invariants(&self) -> Vec<Box<dyn Fn(&CliffordElement<P>) -> P>> {
        let grade = self.grade;
        vec![Box::new(move |x| {
            // Return norm of grade component
            let grade_comp = x.grade(grade);
            coherence_norm(&grade_comp)
        })]
    }
}

/// Resonance values are invariant under certain automorphisms
pub struct ResonanceInvariant;

impl<P: Float + num_traits::FromPrimitive> Invariant<P> for ResonanceInvariant {
    fn is_invariant(&self, group: &SymmetryGroup<P>) -> bool {
        // Check if this group preserves resonance values
        // For resonance to be invariant, the group must:
        // 1. Preserve the Klein group structure
        // 2. Act as automorphisms of (Z/48Z × Z/256Z)
        // 3. Preserve the unity constraint α[n-2] × α[n-1] = 1
        
        // Check if this is a Klein group or subgroup thereof
        if let Some(order) = group.order() {
            // Klein group has order 4, and its subgroups have orders 1, 2, 4
            order == 1 || order == 2 || order == 4
        } else {
            // For infinite groups, need more sophisticated check
            false
        }
    }

    fn generating_invariants(&self) -> Vec<Box<dyn Fn(&CliffordElement<P>) -> P>> {
        use ccm_coherence::embedding::{extract_dominant_pattern, index_to_bitword};
        use ccm_embedding::{AlphaVec, Resonance};
        
        vec![
            // Invariant 1: Resonance of dominant component
            Box::new(|x: &CliffordElement<P>| -> P {
                // Extract the dominant bit pattern
                let (index, coeff) = extract_dominant_pattern(x);
                
                // Convert to BitWord
                let word = index_to_bitword(index, x.dimension());
                
                // Compute resonance (requires alpha vector)
                // For invariant functions, we use mathematical alpha
                let alpha: AlphaVec<P> = match AlphaVec::<P>::mathematical(x.dimension()) {
                    Ok(a) => a,
                    Err(_) => return P::zero(),
                };
                
                // Return resonance weighted by coefficient magnitude
                word.r(&alpha) * P::from(coeff.norm()).unwrap_or(P::one())
            }),
            
            // Invariant 2: Sum of resonances over Klein orbit
            Box::new(|x: &CliffordElement<P>| -> P {
                let dimension = x.dimension();
                if dimension < 2 {
                    return P::zero();
                }
                
                let alpha: AlphaVec<P> = match AlphaVec::<P>::mathematical(dimension) {
                    Ok(a) => a,
                    Err(_) => return P::zero(),
                };
                
                let mut sum = P::zero();
                
                // For each significant component, sum resonances over its Klein orbit
                for i in 0..x.num_components() {
                    if let Some(coeff) = x.component(i) {
                        if coeff.norm_sqr() > P::epsilon() {
                            let word = index_to_bitword(i, dimension);
                            
                            // Klein orbit: XOR with {0, 2^(n-2), 2^(n-1), 2^(n-2)+2^(n-1)}
                            let klein_xor = [0, 1 << (dimension - 2), 1 << (dimension - 1), 
                                           (1 << (dimension - 2)) | (1 << (dimension - 1))];
                            
                            for &xor_val in &klein_xor {
                                let orbit_index = i ^ xor_val;
                                if orbit_index < x.num_components() {
                                    let orbit_word = index_to_bitword(orbit_index, dimension);
                                    sum = sum + orbit_word.r(&alpha) * P::from(coeff.norm()).unwrap_or(P::zero());
                                }
                            }
                        }
                    }
                }
                
                // Normalize by Klein group size
                sum / P::from(4.0).unwrap()
            }),
            
            // Invariant 3: Resonance-weighted coherence norm
            Box::new(|x: &CliffordElement<P>| -> P {
                let dimension = x.dimension();
                let alpha: AlphaVec<P> = match AlphaVec::<P>::mathematical(dimension) {
                    Ok(a) => a,
                    Err(_) => return P::zero(),
                };
                
                let mut weighted_norm = P::zero();
                
                // Sum over all components weighted by their resonance
                for i in 0..x.num_components() {
                    if let Some(coeff) = x.component(i) {
                        let norm_sq = coeff.norm_sqr();
                        if norm_sq > P::epsilon() {
                            let word = index_to_bitword(i, dimension);
                            let resonance: P = word.r(&alpha);
                            weighted_norm = weighted_norm + norm_sq * resonance;
                        }
                    }
                }
                
                weighted_norm.sqrt()
            }),
            
            // Invariant 4: Resonance spectrum entropy
            Box::new(|x: &CliffordElement<P>| -> P {
                let dimension = x.dimension();
                let alpha: AlphaVec<P> = match AlphaVec::<P>::mathematical(dimension) {
                    Ok(a) => a,
                    Err(_) => return P::zero(),
                };
                
                // Compute resonance distribution
                let mut resonance_bins = vec![P::zero(); 96]; // 96 possible resonance values
                let mut total = P::zero();
                
                for i in 0..x.num_components().min(256) {
                    if let Some(coeff) = x.component(i) {
                        let norm_sq = coeff.norm_sqr();
                        if norm_sq > P::epsilon() {
                            let word = index_to_bitword(i, dimension);
                            let resonance: P = word.r(&alpha);
                            
                            // Map resonance to bin (0-95)
                            // This is approximate - in practice would need resonance class mapping
                            let scaled_resonance: P = resonance * P::from(95.0).unwrap();
                            let bin = (scaled_resonance.to_f64().unwrap_or(0.0) as usize).min(95);
                            resonance_bins[bin] = resonance_bins[bin] + norm_sq;
                            total = total + norm_sq;
                        }
                    }
                }
                
                // Compute entropy
                let mut entropy = P::zero();
                if total > P::epsilon() {
                    for &bin_val in &resonance_bins {
                        if bin_val > P::epsilon() {
                            let p = bin_val / total;
                            entropy = entropy - p * p.ln();
                        }
                    }
                }
                
                entropy
            }),
        ]
    }
}

/// Map symmetry to conserved quantity via Noether's theorem
pub fn noether_correspondence<P: Float>(symmetry: &LieAlgebraElement<P>) -> ConservedQuantity<P> {
    // Determine the type of symmetry and corresponding conserved quantity
    let dimension = symmetry.dimension;

    // Check if this is a translation generator
    let is_translation = symmetry
        .coefficients
        .iter()
        .enumerate()
        .filter(|(_, &c)| c.abs() > P::epsilon())
        .count()
        == 1;

    if is_translation {
        // Translation symmetry -> momentum conservation
        let direction = symmetry
            .coefficients
            .iter()
            .position(|&c| c.abs() > P::epsilon())
            .unwrap_or(0);

        ConservedQuantity::new(
            format!("Momentum_{direction}"),
            symmetry.clone(),
            Box::new(move |x| {
                // Momentum is the coefficient of the translation generator
                // in the expansion of the element
                // Get component at direction index
                x.component(direction).map(|c| c.re).unwrap_or(P::zero())
            }),
        )
    } else if dimension == 3 {
        // Check for rotation generators in so(3)
        // These have 2 non-zero entries with opposite signs
        let non_zero: Vec<_> = symmetry
            .coefficients
            .iter()
            .enumerate()
            .filter(|(_, &c)| c.abs() > P::epsilon())
            .collect();

        if non_zero.len() == 2 && (*non_zero[0].1 + *non_zero[1].1).abs() < P::epsilon() {
            // Rotation symmetry -> angular momentum conservation
            let axis = if non_zero[0].0 == 0 && non_zero[1].0 == 1 {
                2 // z-axis rotation
            } else if non_zero[0].0 == 0 && non_zero[1].0 == 2 {
                1 // y-axis rotation
            } else {
                0 // x-axis rotation
            };

            ConservedQuantity::new(
                format!("AngularMomentum_{axis}"),
                symmetry.clone(),
                Box::new(move |x| {
                    // Angular momentum component
                    // L_i = ∑_{jk} ε_{ijk} x_j p_k
                    // For Clifford elements, use bivector components
                    // Get grade-2 (bivector) component norm
                    let bivector = x.grade(2);
                    coherence_norm(&bivector)
                }),
            )
        } else {
            // General transformation -> energy conservation
            ConservedQuantity::new(
                String::from("Energy"),
                symmetry.clone(),
                Box::new(|x| coherence_norm(x).powi(2)),
            )
        }
    } else {
        // For higher dimensions, default to coherence norm squared
        ConservedQuantity::new(
            String::from("CoherenceEnergy"),
            symmetry.clone(),
            Box::new(|x| coherence_norm(x).powi(2)),
        )
    }
}

/// Resonance current conservation from translation symmetry
pub fn resonance_current_conservation<P: Float>() -> ConservedQuantity<P> {
    // Translation by n: b ↦ (b + n) mod 256
    // Conserved: sum of resonance currents

    // Create translation generator (shift in byte space)
    let mut translation_coeffs = vec![P::zero(); 8];
    translation_coeffs[0] = P::one(); // Translation in bit 0 direction
    let symmetry = LieAlgebraElement::from_coefficients(translation_coeffs);

    ConservedQuantity::new(
        String::from("Resonance Current"),
        symmetry,
        Box::new(|x| {
            // For resonance current conservation, we need to track
            // the flow of resonance through the system
            // This is related to the grade-0 (scalar) component
            let scalar_part = x.grade(0);
            // The conserved quantity is the sum of currents
            // J(n) = R(n+1) - R(n), and ∑J(n) = 0
            // This manifests as the imaginary part being zero
            scalar_part
                .component(0)
                .map(|c| c.im.abs())
                .unwrap_or(P::zero())
        }),
    )
}

/// Create conserved quantity for Klein symmetry
pub fn klein_symmetry_conservation<P: Float>() -> ConservedQuantity<P> {
    // Klein V₄ symmetry preserves resonance
    let mut klein_coeffs = vec![P::zero(); 4];
    klein_coeffs[0] = P::one(); // First Klein generator
    let symmetry = LieAlgebraElement::from_coefficients(klein_coeffs);

    ConservedQuantity::new(
        String::from("Klein Invariant"),
        symmetry,
        Box::new(|x| {
            // Klein symmetry preserves the sum of squares of
            // components related to unity positions
            let mut sum = P::zero();
            // Check last 4 components (Klein group dimension)
            // Check last 4 components (Klein group dimension)
            let n = x.num_components();
            let start = n.saturating_sub(4);
            for i in start..n {
                if let Some(c) = x.component(i) {
                    sum = sum + c.norm_sqr();
                }
            }
            sum
        }),
    )
}

/// Create conserved quantity for grade preservation
pub fn grade_preservation_conservation<P: Float>(grade: usize) -> ConservedQuantity<P> {
    // Grade-preserving transformations conserve grade norms
    let dimension = 2_usize.pow(grade as u32); // Appropriate dimension for grade
    let symmetry = LieAlgebraElement::zero(dimension);

    ConservedQuantity::new(
        format!("Grade {grade} Norm"),
        symmetry,
        Box::new(move |x| {
            let grade_component = x.grade(grade);
            coherence_norm(&grade_component).powi(2)
        }),
    )
}

/// Verify if a group action preserves resonance invariants
pub fn verify_resonance_preservation<P: Float + num_traits::FromPrimitive>(
    group: &SymmetryGroup<P>,
    test_element: &CliffordElement<P>,
    action: &dyn crate::actions::GroupAction<P, Target = CliffordElement<P>>,
) -> bool {
    use ccm_embedding::AlphaVec;
    
    // Get mathematical alpha for testing
    let _alpha = match AlphaVec::<P>::mathematical(test_element.dimension()) {
        Ok(a) => a,
        Err(_) => return false,
    };
    
    // Create resonance invariant
    let invariant = ResonanceInvariant;
    let invariant_functions = invariant.generating_invariants();
    
    // Test preservation for each generator
    for g in group.generators() {
        // Apply group action
        let transformed = match action.apply(g, test_element) {
            Ok(t) => t,
            Err(_) => return false,
        };
        
        // Check each invariant function
        for inv_fn in &invariant_functions {
            let orig_val = inv_fn(test_element);
            let trans_val = inv_fn(&transformed);
            
            // Check if preserved within tolerance
            if (orig_val - trans_val).abs() > P::epsilon() * P::from(10.0).unwrap() {
                return false;
            }
        }
    }
    
    true
}

/// Create a resonance-preserving group from automorphisms
#[cfg(feature = "alloc")]
pub fn resonance_preserving_group<P: Float + num_traits::FromPrimitive>(
    dimension: usize,
) -> Result<SymmetryGroup<P>, crate::SymmetryError> {
    use crate::group::{GroupElement, GroupType};
    
    let mut group = SymmetryGroup::generate(dimension)
        .map_err(|_| crate::SymmetryError::InvalidGroupOperation)?;
    
    // Generate resonance-preserving automorphisms
    let automorphisms = crate::discrete::resonance_preserving_automorphisms();
    
    // Convert automorphisms to group elements
    let mut elements = Vec::new();
    for auto in automorphisms.iter().take(10) { // Limit for practicality
        // Create group element from automorphism parameters
        let mut params = vec![P::zero(); 4];
        params[0] = P::from(auto.factor_48 as f64).unwrap_or(P::one());
        params[1] = P::from(auto.factor_256 as f64).unwrap_or(P::one());
        params[2] = P::from(auto.offset_48 as f64).unwrap_or(P::zero());
        params[3] = P::from(auto.offset_256 as f64).unwrap_or(P::zero());
        
        let element = GroupElement {
            params,
            cached_order: None,
        };
        elements.push(element);
    }
    
    // Set group type to finite with these elements
    group.group_type = GroupType::Finite { elements };
    
    Ok(group)
}

/// Check if a given automorphism preserves resonance structure
pub fn check_automorphism_resonance_preservation<P: Float + num_traits::FromPrimitive>(
    automorphism: &ResonanceAutomorphism,
    alpha: &ccm_embedding::AlphaVec<P>,
) -> bool {
    automorphism.preserves_resonance(alpha)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ccm_coherence::{CliffordAlgebra, CliffordElement};
    use ccm_embedding::AlphaVec;
    
    #[test]
    fn test_resonance_invariant_is_invariant() {
        let invariant = ResonanceInvariant;
        let group = SymmetryGroup::<f64>::klein_group(8).unwrap();
        
        // Klein group should preserve resonance
        assert!(invariant.is_invariant(&group));
        
        // Test with larger groups
        let cyclic = SymmetryGroup::<f64>::cyclic_group(8, 8).unwrap();
        assert!(!invariant.is_invariant(&cyclic)); // Cyclic of order 8 doesn't preserve resonance
    }
    
    #[test]
    fn test_resonance_generating_invariants() {
        let invariant = ResonanceInvariant;
        let inv_funcs: Vec<Box<dyn Fn(&CliffordElement<f64>) -> f64>> = invariant.generating_invariants();
        
        // Should have 4 generating invariants
        assert_eq!(inv_funcs.len(), 4);
        
        // Test on a simple element
        let mut elem = CliffordElement::<f64>::zero(8);
        elem.set_component(42, num_complex::Complex::new(1.5, 0.0)).unwrap();
        
        // Each invariant should return a finite value
        for inv_fn in &inv_funcs {
            let val = inv_fn(&elem);
            assert!(val.is_finite(), "Invariant returned non-finite value");
        }
    }
    
    #[test]
    fn test_verify_resonance_preservation() {
        // Klein group needs Klein action, not general Clifford action
        let action = crate::actions::KleinCliffordAction::new(8);
        let group = SymmetryGroup::<f64>::klein_group(8).unwrap();
        
        // Create test element that has components in a complete Klein orbit
        // Use indices that form a Klein orbit under bit flips at positions 6,7
        let mut test_elem = CliffordElement::<f64>::zero(8);
        
        // Create an element with all 4 components of a Klein orbit
        // Orbit of 0: {0, 64, 128, 192} (flipping bits 6 and/or 7)
        test_elem.set_component(0, num_complex::Complex::new(0.5, 0.0)).unwrap();
        test_elem.set_component(64, num_complex::Complex::new(0.5, 0.0)).unwrap();
        test_elem.set_component(128, num_complex::Complex::new(0.5, 0.0)).unwrap();
        test_elem.set_component(192, num_complex::Complex::new(0.5, 0.0)).unwrap();
        
        // Klein group should preserve resonance invariants for this symmetric element
        assert!(verify_resonance_preservation(&group, &test_elem, &action));
    }
    
    #[test]
    #[cfg(feature = "alloc")]
    fn test_resonance_preserving_group_creation() {
        let group = resonance_preserving_group::<f64>(8).unwrap();
        
        // Should have finite elements
        if let crate::group::GroupType::Finite { ref elements } = group.group_type {
            assert!(!elements.is_empty(), "Resonance preserving group should have elements");
            assert!(elements.len() <= 10, "Limited to 10 elements for practicality");
        } else {
            panic!("Expected finite group");
        }
    }
    
    #[test]
    fn test_resonance_automorphism_preservation() {
        let alpha = AlphaVec::<f64>::mathematical(8).unwrap();
        let auto = ResonanceAutomorphism::identity();
        
        // Identity automorphism should preserve resonance
        assert!(check_automorphism_resonance_preservation(&auto, &alpha));
        
        // Translation automorphisms also preserve resonance
        let translation = ResonanceAutomorphism {
            factor_48: 1,
            factor_256: 1,
            offset_48: 5,
            offset_256: 10,
        };
        assert!(check_automorphism_resonance_preservation(&translation, &alpha));
    }
    
    #[test]
    fn test_klein_orbit_invariant() {
        let invariant = ResonanceInvariant;
        let inv_funcs: Vec<Box<dyn Fn(&CliffordElement<f64>) -> f64>> = invariant.generating_invariants();
        
        // Second invariant is Klein orbit sum
        let klein_orbit_inv = &inv_funcs[1];
        
        // Create element with known Klein structure
        let mut elem = CliffordElement::<f64>::zero(8);
        elem.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap(); // Identity
        elem.set_component(192, num_complex::Complex::new(1.0, 0.0)).unwrap(); // Klein partner
        
        let orbit_sum = klein_orbit_inv(&elem);
        assert!(orbit_sum > 0.0, "Klein orbit sum should be positive");
    }
}
