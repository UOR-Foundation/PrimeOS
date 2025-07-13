//! Invariant quantities under group action

use crate::{group::SymmetryGroup, lie_algebra::LieAlgebraElement};
use ccm_core::Float;
use ccm_coherence::{CliffordElement, coherence_norm};

#[cfg(feature = "alloc")]
use alloc::{boxed::Box, string::String, vec::Vec};

/// Trait for invariant quantities
pub trait Invariant<P: Float> {
    /// Check if quantity is invariant under group action
    fn is_invariant(&self, group: &SymmetryGroup<P>) -> bool;
    
    /// Find generating invariants
    fn generating_invariants(&self) -> Vec<Box<dyn Fn(&CliffordElement<P>) -> P>>;
}

/// A conserved quantity from Noether's theorem
pub struct ConservedQuantity<P: Float> {
    /// Name of the conserved quantity
    pub name: String,
    /// The symmetry generator
    pub symmetry: LieAlgebraElement<P>,
    /// Function computing the conserved quantity
    pub quantity: Box<dyn Fn(&CliffordElement<P>) -> P>,
}

impl<P: Float> ConservedQuantity<P> {
    /// Create a new conserved quantity
    pub fn new(
        name: String,
        symmetry: LieAlgebraElement<P>,
        quantity: Box<dyn Fn(&CliffordElement<P>) -> P>,
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
        vec![
            Box::new(|x| x.coherence_norm()),
        ]
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
        vec![
            Box::new(move |x| {
                // Return norm of grade component
                let grade_comp = x.grade(grade);
                coherence_norm(&grade_comp)
            }),
        ]
    }
}

/// Resonance values are invariant under certain automorphisms
pub struct ResonanceInvariant;

impl<P: Float> Invariant<P> for ResonanceInvariant {
    fn is_invariant(&self, _group: &SymmetryGroup<P>) -> bool {
        // Only certain subgroups preserve resonance
        // This would need to check the specific group
        true
    }
    
    fn generating_invariants(&self) -> Vec<Box<dyn Fn(&CliffordElement<P>) -> P>> {
        // Resonance-based invariants would go here
        vec![]
    }
}

/// Map symmetry to conserved quantity via Noether's theorem
pub fn noether_correspondence<P: Float>(
    symmetry: &LieAlgebraElement<P>,
) -> ConservedQuantity<P> {
    // Determine the type of symmetry and corresponding conserved quantity
    let dimension = symmetry.dimension;
    
    // Check if this is a translation generator
    let is_translation = symmetry.coefficients.iter()
        .enumerate()
        .filter(|(_, &c)| c.abs() > P::epsilon())
        .count() == 1;
    
    if is_translation {
        // Translation symmetry -> momentum conservation
        let direction = symmetry.coefficients.iter()
            .position(|&c| c.abs() > P::epsilon())
            .unwrap_or(0);
        
        ConservedQuantity::new(
            format!("Momentum_{}", direction),
            symmetry.clone(),
            Box::new(move |x| {
                // Momentum is the coefficient of the translation generator
                // in the expansion of the element
                // Get component at direction index
                x.component(direction)
                    .map(|c| c.re)
                    .unwrap_or(P::zero())
            }),
        )
    } else if dimension == 3 {
        // Check for rotation generators in so(3)
        // These have 2 non-zero entries with opposite signs
        let non_zero: Vec<_> = symmetry.coefficients.iter()
            .enumerate()
            .filter(|(_, &c)| c.abs() > P::epsilon())
            .collect();
        
        if non_zero.len() == 2 && 
           (*non_zero[0].1 + *non_zero[1].1).abs() < P::epsilon() {
            // Rotation symmetry -> angular momentum conservation
            let axis = if non_zero[0].0 == 0 && non_zero[1].0 == 1 {
                2 // z-axis rotation
            } else if non_zero[0].0 == 0 && non_zero[1].0 == 2 {
                1 // y-axis rotation
            } else {
                0 // x-axis rotation
            };
            
            ConservedQuantity::new(
                format!("AngularMomentum_{}", axis),
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
            scalar_part.component(0)
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
        format!("Grade {} Norm", grade),
        symmetry,
        Box::new(move |x| {
            let grade_component = x.grade(grade);
            coherence_norm(&grade_component).powi(2)
        }),
    )
}
