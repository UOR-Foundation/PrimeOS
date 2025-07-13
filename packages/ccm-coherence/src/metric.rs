//! Coherence inner product and norm implementation

use crate::element::CliffordElement;
use ccm_core::{CcmError, Float};
use num_complex::Complex;
#[allow(unused_imports)]
use num_traits::{One, Zero};

/// Compute the coherence inner product ⟨⟨a, b⟩⟩
///
/// This implements Axiom A1 with:
/// - Positive-definiteness
/// - Conjugate symmetry
/// - Linearity
/// - Grade orthogonality
pub fn coherence_product<P: Float>(a: &CliffordElement<P>, b: &CliffordElement<P>) -> Complex<P> {
    if a.dimension != b.dimension {
        return Complex::zero();
    }

    let mut result = Complex::zero();

    // Grade orthogonality: only components of the same grade contribute
    // This is already enforced because components at index i have grade = count_ones(i)
    // When we do component-wise multiplication, we automatically get grade orthogonality
    for i in 0..a.components.len() {
        // Complex inner product: conj(a) * b
        result = result + a.components[i].conj() * b.components[i];
    }

    result
}

/// Compute the coherence norm ‖x‖_c = √⟨⟨x, x⟩⟩
pub fn coherence_norm<P: Float>(x: &CliffordElement<P>) -> P {
    let norm_squared = coherence_product(x, x);
    // Since x is real, the inner product with itself is real and positive
    norm_squared.re.sqrt()
}

/// Compute the squared coherence norm (more efficient)
pub fn coherence_norm_squared<P: Float>(x: &CliffordElement<P>) -> P {
    let mut sum = P::zero();

    for i in 0..x.components.len() {
        sum = sum + x.components[i].norm_sqr();
    }

    sum
}

/// Grade-wise inner product (only considers grade k components)
pub fn grade_inner_product<P: Float>(
    a: &CliffordElement<P>,
    b: &CliffordElement<P>,
    k: usize,
) -> Complex<P> {
    if a.dimension != b.dimension {
        return Complex::zero();
    }

    let mut result = Complex::zero();

    // Sum only over components of grade k
    for i in 0..a.components.len() {
        if CliffordElement::<P>::grade_of_index(i) == k {
            result = result + a.components[i].conj() * b.components[i];
        }
    }

    result
}

/// Check if two elements are orthogonal under coherence product
pub fn are_orthogonal<P: Float>(a: &CliffordElement<P>, b: &CliffordElement<P>) -> bool {
    let product = coherence_product(a, b);
    product.norm_sqr() < P::epsilon()
}

/// Normalize an element to unit coherence norm
pub fn normalize<P: Float>(x: &CliffordElement<P>) -> Result<CliffordElement<P>, CcmError> {
    let norm = coherence_norm(x);

    if norm < P::epsilon() {
        return Err(CcmError::InvalidInput);
    }

    let mut result = x.clone();
    let inv_norm = P::one() / norm;

    for i in 0..result.components.len() {
        result.components[i] = result.components[i].scale(inv_norm);
    }

    Ok(result)
}

/// Project b onto a (in the direction of a)
pub fn project<P: Float>(
    a: &CliffordElement<P>,
    b: &CliffordElement<P>,
) -> Result<CliffordElement<P>, CcmError> {
    let norm_a_sq = coherence_norm_squared(a);

    if norm_a_sq < P::epsilon() {
        return Err(CcmError::InvalidInput);
    }

    let proj_coeff = coherence_product(a, b) / Complex::new(norm_a_sq, P::zero());

    let mut result = a.clone();
    for i in 0..result.components.len() {
        result.components[i] = result.components[i] * proj_coeff;
    }

    Ok(result)
}

/// Gram-Schmidt orthogonalization for a set of elements
#[cfg(feature = "alloc")]
pub fn gram_schmidt<P: Float>(
    elements: &[CliffordElement<P>],
) -> Result<alloc::vec::Vec<CliffordElement<P>>, CcmError> {
    use alloc::vec::Vec;

    if elements.is_empty() {
        return Ok(Vec::new());
    }

    let mut orthogonal = Vec::with_capacity(elements.len());

    for elem in elements.iter() {
        let mut orth = elem.clone();

        // Subtract projections onto all previous orthogonal elements
        for orth_elem in orthogonal.iter() {
            if let Ok(proj) = project(orth_elem, elem) {
                for k in 0..orth.components.len() {
                    orth.components[k] = orth.components[k] - proj.components[k];
                }
            }
        }

        // Normalize if non-zero
        if coherence_norm_squared(&orth) > P::epsilon() {
            orth = normalize(&orth)?;
            orthogonal.push(orth);
        }
    }

    Ok(orthogonal)
}

impl<P: Float> CliffordElement<P> {
    /// Compute coherence norm of this element
    pub fn coherence_norm(&self) -> P {
        coherence_norm(self)
    }

    /// Compute squared coherence norm (more efficient)
    pub fn coherence_norm_squared(&self) -> P {
        coherence_norm_squared(self)
    }

    /// Normalize to unit coherence norm
    pub fn normalize(&self) -> Result<Self, CcmError> {
        normalize(self)
    }

    /// Check if this element has unit norm
    pub fn is_unit_norm(&self) -> bool {
        (self.coherence_norm() - P::one()).abs() < P::epsilon()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_coherence_product_basic() {
        // Test with basis vectors
        let e1 = CliffordElement::<f64>::basis_vector(0, 3).unwrap();
        let e2 = CliffordElement::<f64>::basis_vector(1, 3).unwrap();

        // Basis vectors should be orthonormal
        let prod11 = coherence_product(&e1, &e1);
        assert!((prod11.re - 1.0).abs() < 1e-10);
        assert!(prod11.im.abs() < 1e-10);

        let prod12 = coherence_product(&e1, &e2);
        assert!(prod12.norm() < 1e-10); // orthogonal
    }

    #[test]
    fn test_grade_orthogonality() {
        let mut a = CliffordElement::<f64>::zero(3);
        let mut b = CliffordElement::<f64>::zero(3);

        // a has grade 1 component
        a.set_component(1, Complex::new(2.0, 0.0)).unwrap(); // e₀

        // b has grade 2 component
        b.set_component(3, Complex::new(3.0, 0.0)).unwrap(); // e₀e₁

        // Different grades should be orthogonal
        let prod = coherence_product(&a, &b);
        assert!(prod.norm() < 1e-10);
    }

    #[test]
    fn test_coherence_norm() {
        let mut elem = CliffordElement::<f64>::zero(3);
        elem.set_component(0, Complex::new(3.0, 0.0)).unwrap();
        elem.set_component(1, Complex::new(4.0, 0.0)).unwrap();

        // Norm should be sqrt(3² + 4²) = 5
        let norm = coherence_norm(&elem);
        assert!((norm - 5.0).abs() < 1e-10);
    }

    #[test]
    fn test_normalize() {
        let mut elem = CliffordElement::<f64>::zero(3);
        elem.set_component(0, Complex::new(3.0, 0.0)).unwrap();
        elem.set_component(1, Complex::new(4.0, 0.0)).unwrap();

        let normalized = normalize(&elem).unwrap();
        let norm = coherence_norm(&normalized);
        assert!((norm - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_projection() {
        let e1 = CliffordElement::<f64>::basis_vector(0, 3).unwrap();
        let mut v = CliffordElement::<f64>::zero(3);
        v.set_component(1, Complex::new(1.0, 0.0)).unwrap(); // e₀
        v.set_component(2, Complex::new(1.0, 0.0)).unwrap(); // e₁

        let proj = project(&e1, &v).unwrap();
        // Projection of v onto e₀ should give just the e₀ component
        assert!((proj.component(1).unwrap().re - 1.0).abs() < 1e-10);
        assert!(proj.component(2).unwrap().norm() < 1e-10);
    }

    #[test]
    fn test_conjugate_symmetry() {
        let mut a = CliffordElement::<f64>::zero(3);
        let mut b = CliffordElement::<f64>::zero(3);

        a.set_component(0, Complex::new(1.0, 2.0)).unwrap();
        b.set_component(0, Complex::new(3.0, 4.0)).unwrap();

        let prod_ab = coherence_product(&a, &b);
        let prod_ba = coherence_product(&b, &a);

        // Should have ⟨⟨a,b⟩⟩ = ⟨⟨b,a⟩⟩*
        assert!((prod_ab - prod_ba.conj()).norm() < 1e-10);
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn test_gram_schmidt() {
        // Create linearly dependent vectors
        let mut v1 = CliffordElement::<f64>::zero(3);
        v1.set_component(1, Complex::new(1.0, 0.0)).unwrap();
        v1.set_component(2, Complex::new(1.0, 0.0)).unwrap();

        let mut v2 = CliffordElement::<f64>::zero(3);
        v2.set_component(1, Complex::new(2.0, 0.0)).unwrap();
        v2.set_component(2, Complex::new(0.0, 0.0)).unwrap();

        let orthogonal = gram_schmidt(&[v1, v2]).unwrap();

        // Should produce orthonormal vectors
        assert_eq!(orthogonal.len(), 2);
        assert!(orthogonal[0].is_unit_norm());
        assert!(orthogonal[1].is_unit_norm());
        assert!(are_orthogonal(&orthogonal[0], &orthogonal[1]));
    }
}
