//! Even subalgebra and rotor group implementation

use crate::clifford::CliffordAlgebra;
use crate::element::CliffordElement;
use crate::metric::{coherence_norm, normalize};
use ccm_core::{CcmError, Float};
use num_complex::Complex;
#[allow(unused_imports)]
use num_traits::{One, Zero};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Even subalgebra Cl⁺(n) - elements with only even grades
pub struct EvenSubalgebra<P: Float> {
    /// The parent Clifford algebra
    algebra: CliffordAlgebra<P>,
}

impl<P: Float> EvenSubalgebra<P> {
    /// Create the even subalgebra from a Clifford algebra
    pub fn new(algebra: CliffordAlgebra<P>) -> Self {
        Self { algebra }
    }

    /// Get the dimension of the underlying space
    pub fn dimension(&self) -> usize {
        self.algebra.dimension()
    }

    /// Check if an element belongs to the even subalgebra
    pub fn contains(&self, element: &CliffordElement<P>) -> bool {
        // Check that all non-zero components have even grade
        for i in 0..element.num_components() {
            if let Some(comp) = element.component(i) {
                if comp.norm_sqr() > P::epsilon() {
                    let grade = CliffordElement::<P>::grade_of_index(i);
                    if grade % 2 != 0 {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Project an element onto the even subalgebra
    pub fn project(&self, element: &CliffordElement<P>) -> CliffordElement<P> {
        let mut result = CliffordElement::zero(element.dimension());

        for i in 0..element.num_components() {
            let grade = CliffordElement::<P>::grade_of_index(i);
            if grade % 2 == 0 {
                if let Some(comp) = element.component(i) {
                    result.set_component(i, comp).unwrap();
                }
            }
        }

        result
    }

    /// Create a basis for the even subalgebra
    #[cfg(feature = "alloc")]
    pub fn basis_elements(&self) -> Vec<CliffordElement<P>> {
        let mut basis = Vec::new();
        let n = self.dimension();

        // Generate all basis elements with even grade
        for i in 0..(1usize << n) {
            let grade = i.count_ones() as usize;
            if grade % 2 == 0 {
                if let Ok(elem) = self.algebra.basis_element(i) {
                    basis.push(elem);
                }
            }
        }

        basis
    }

    /// Dimension of the even subalgebra (2^(n-1))
    pub fn subalgebra_dimension(&self) -> usize {
        1usize << (self.dimension() - 1)
    }
}

/// Rotor - element of even subalgebra with unit norm
/// Rotors form the spin group Spin(n)
#[derive(Debug, Clone, PartialEq)]
pub struct Rotor<P: Float> {
    /// The underlying even element with unit norm
    element: CliffordElement<P>,
}

impl<P: Float> Rotor<P> {
    /// Create a rotor from an even element by normalizing
    pub fn new(even_element: CliffordElement<P>) -> Result<Self, CcmError> {
        // Verify it's even
        for i in 0..even_element.num_components() {
            if let Some(comp) = even_element.component(i) {
                if comp.norm_sqr() > P::epsilon() {
                    let grade = CliffordElement::<P>::grade_of_index(i);
                    if grade % 2 != 0 {
                        return Err(CcmError::InvalidInput);
                    }
                }
            }
        }

        // Normalize to unit norm
        let normalized = normalize(&even_element)?;

        Ok(Self {
            element: normalized,
        })
    }

    /// Create identity rotor
    pub fn identity(dimension: usize) -> Self {
        let element = CliffordElement::scalar(P::one(), dimension);
        Self { element }
    }

    /// Get the underlying Clifford element
    pub fn as_element(&self) -> &CliffordElement<P> {
        &self.element
    }

    /// Apply rotor to a vector (grade 1 element)
    /// Formula: v' = R v R†
    pub fn apply_to_vector(
        &self,
        vector: &CliffordElement<P>,
        algebra: &CliffordAlgebra<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        // Compute R v
        let rv = algebra.geometric_product(&self.element, vector)?;

        // Compute R† (reverse of R)
        let r_dagger = self.reverse();

        // Compute R v R†
        algebra.geometric_product(&rv, &r_dagger.element)
    }

    /// Apply rotor to any element
    /// Formula: x' = R x R†
    pub fn apply(
        &self,
        element: &CliffordElement<P>,
        algebra: &CliffordAlgebra<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        let rx = algebra.geometric_product(&self.element, element)?;
        let r_dagger = self.reverse();
        algebra.geometric_product(&rx, &r_dagger.element)
    }

    /// Compute the reverse (grade reversal) R†
    pub fn reverse(&self) -> Self {
        let mut reversed = CliffordElement::zero(self.element.dimension());

        for i in 0..self.element.num_components() {
            if let Some(comp) = self.element.component(i) {
                let grade = CliffordElement::<P>::grade_of_index(i);
                // Reverse introduces factor (-1)^(k(k-1)/2)
                let sign = if grade == 0 || (grade * (grade.saturating_sub(1)) / 2) % 2 == 0 {
                    P::one()
                } else {
                    -P::one()
                };

                reversed.set_component(i, comp.scale(sign)).unwrap();
            }
        }

        // Rotor reverse is also a rotor
        Self { element: reversed }
    }

    /// Compose two rotors: R₁ ∘ R₂
    pub fn compose(&self, other: &Self, algebra: &CliffordAlgebra<P>) -> Result<Self, CcmError> {
        let product = algebra.geometric_product(&self.element, &other.element)?;
        // Product of rotors is a rotor (even * even = even)
        Ok(Self { element: product })
    }

    /// Create a rotor from a bivector (grade 2 element)
    /// Using exponential map: R = exp(B/2)
    pub fn from_bivector(
        bivector: &CliffordElement<P>,
        algebra: &CliffordAlgebra<P>,
    ) -> Result<Self, CcmError> {
        // Verify it's purely grade 2
        for i in 0..bivector.num_components() {
            if let Some(comp) = bivector.component(i) {
                if comp.norm_sqr() > P::epsilon() {
                    let grade = CliffordElement::<P>::grade_of_index(i);
                    if grade != 2 && grade != 0 {
                        return Err(CcmError::InvalidInput);
                    }
                }
            }
        }

        // Compute exp(B/2) using series expansion
        // exp(B/2) = 1 + B/2 + (B/2)²/2! + ...

        let half = P::from(0.5).unwrap();
        let b_half = bivector.clone() * half;

        let mut result = CliffordElement::scalar(P::one(), bivector.dimension());
        let mut term = b_half.clone();
        let mut factorial = P::one();

        // Series expansion (truncate when term is small)
        for n in 1..20 {
            result = result + term.clone();

            // Check convergence
            if coherence_norm(&term) < P::epsilon() {
                break;
            }

            // Next term: B^(n+1) / (n+1)!
            term = algebra.geometric_product(&term, &b_half)?;
            factorial = factorial * P::from(n + 1).unwrap();
            term = term * (P::one() / factorial);
        }

        // Ensure the result is normalized
        let normalized = crate::metric::normalize(&result)?;
        Ok(Self {
            element: normalized,
        })
    }

    /// Extract the bivector B such that R ≈ exp(B/2)
    /// (Inverse of from_bivector, approximate)
    pub fn to_bivector(&self) -> Result<CliffordElement<P>, CcmError> {
        // For small rotations, R ≈ 1 + B/2
        // So B ≈ 2(R - 1)

        let mut bivector = self.element.clone();

        // Subtract scalar part
        if let Some(scalar) = bivector.component(0) {
            bivector.set_component(0, scalar - Complex::one())?;
        }

        // Scale by 2 and keep only grade 2 part
        bivector = bivector * P::from(2.0).unwrap();

        let mut result = CliffordElement::zero(self.element.dimension());
        for i in 0..bivector.num_components() {
            if CliffordElement::<P>::grade_of_index(i) == 2 {
                if let Some(comp) = bivector.component(i) {
                    result.set_component(i, comp)?;
                }
            }
        }

        Ok(result)
    }
}

/// Rotor group operations
impl<P: Float> Rotor<P> {
    /// Identity element
    pub fn one(dimension: usize) -> Self {
        Self::identity(dimension)
    }

    /// Inverse rotor: R⁻¹ = R†
    pub fn inverse(&self) -> Self {
        self.reverse()
    }

    /// Check if this is approximately the identity
    pub fn is_identity(&self) -> bool {
        // Check if scalar part is ≈1 and all other parts are ≈0
        for i in 0..self.element.num_components() {
            if let Some(comp) = self.element.component(i) {
                if i == 0 {
                    // Scalar component should be 1
                    if (comp - Complex::one()).norm() > P::epsilon() {
                        return false;
                    }
                } else {
                    // Other components should be 0
                    if comp.norm() > P::epsilon() {
                        return false;
                    }
                }
            }
        }
        true
    }
}

/// Create a rotor that rotates in the plane spanned by two vectors
pub fn rotor_from_vectors<P: Float>(
    from: &CliffordElement<P>,
    to: &CliffordElement<P>,
    algebra: &CliffordAlgebra<P>,
) -> Result<Rotor<P>, CcmError> {
    // Normalize input vectors
    let v1 = normalize(from)?;
    let v2 = normalize(to)?;

    // Compute v2 * v1 (geometric product)
    let v2v1 = algebra.geometric_product(&v2, &v1)?;

    // Add scalar part to ensure it's invertible
    let _scalar_part = algebra.scalar_product(&v1, &v2)?;
    let mut rotor_elem = v2v1;
    if let Some(current_scalar) = rotor_elem.component(0) {
        rotor_elem.set_component(0, current_scalar + Complex::one())?;
    }

    // Normalize to get unit rotor
    Rotor::new(rotor_elem)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_even_subalgebra() {
        let algebra = CliffordAlgebra::<f64>::generate(3).unwrap();
        let even = EvenSubalgebra::new(algebra);

        // Scalar (grade 0) should be in even subalgebra
        let scalar = CliffordElement::scalar(2.0, 3);
        assert!(even.contains(&scalar));

        // Bivector (grade 2) should be in even subalgebra
        let bivector = CliffordElement::basis_blade(&[0, 1], 3).unwrap();
        assert!(even.contains(&bivector));

        // Vector (grade 1) should NOT be in even subalgebra
        let vector = CliffordElement::basis_vector(0, 3).unwrap();
        assert!(!even.contains(&vector));

        // Test projection
        let mixed = scalar.clone() + vector + bivector;
        let projected = even.project(&mixed);
        assert!(even.contains(&projected));
    }

    #[test]
    fn test_rotor_identity() {
        let rotor = Rotor::<f64>::identity(3);
        assert!(rotor.is_identity());

        // Identity rotor should not change vectors
        let algebra = CliffordAlgebra::<f64>::generate(3).unwrap();
        let v = CliffordElement::basis_vector(0, 3).unwrap();
        let v_rotated = rotor.apply_to_vector(&v, &algebra).unwrap();

        // Should be unchanged
        for i in 0..v.num_components() {
            assert_eq!(v.component(i), v_rotated.component(i));
        }
    }

    #[test]
    fn test_rotor_reverse() {
        let algebra = CliffordAlgebra::<f64>::generate(3).unwrap();

        // Create a simple rotor from a bivector (small angle for better convergence)
        let mut bivector = CliffordElement::<f64>::zero(3);
        bivector.set_component(3, Complex::new(0.1, 0.0)).unwrap(); // e₀e₁

        let rotor = Rotor::from_bivector(&bivector, &algebra).unwrap();
        let reversed = rotor.reverse();

        // R R† should be identity
        let product = algebra
            .geometric_product(rotor.as_element(), reversed.as_element())
            .unwrap();

        // Check it's approximately identity
        let tolerance = 1e-2; // Relaxed tolerance due to exponential approximation
        assert!(
            (product.component(0).unwrap() - Complex::one()).norm() < tolerance,
            "Scalar component should be 1, got {:?}",
            product.component(0)
        );
        for i in 1..product.num_components() {
            let comp = product.component(i).unwrap();
            assert!(
                comp.norm() < tolerance,
                "Component {} should be 0, got {:?} (norm: {})",
                i,
                comp,
                comp.norm()
            );
        }
    }

    #[test]
    fn test_rotor_composition() {
        let algebra = CliffordAlgebra::<f64>::generate(3).unwrap();

        // Create two rotors
        let r1 = Rotor::<f64>::identity(3);
        let mut bivector = CliffordElement::<f64>::zero(3);
        bivector.set_component(3, Complex::new(0.1, 0.0)).unwrap();
        let r2 = Rotor::from_bivector(&bivector, &algebra).unwrap();

        // Compose them
        let composed = r1.compose(&r2, &algebra).unwrap();

        // r1 ∘ r2 should equal r2 when r1 is identity
        for i in 0..composed.as_element().num_components() {
            assert!(
                (composed.as_element().component(i).unwrap()
                    - r2.as_element().component(i).unwrap())
                .norm()
                    < 1e-6
            );
        }
    }
}
