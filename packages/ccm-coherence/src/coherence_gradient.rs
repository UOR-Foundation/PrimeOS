//! Coherence gradient implementation for optimization

use crate::element::CliffordElement;
use crate::metric::coherence_product;
use ccm_core::Float;

/// Compute the gradient of the coherence norm squared
///
/// For ‖x‖²_c = ⟨⟨x, x⟩⟩, the gradient is:
/// ∇‖x‖²_c = 2x (in the coherence inner product)
pub fn coherence_gradient<P: Float>(x: &CliffordElement<P>) -> CliffordElement<P> {
    // The gradient of ‖x‖²_c with respect to x is 2x
    x.clone() * P::from(2.0).unwrap()
}

/// Compute the gradient of the coherence norm (not squared)
///
/// For ‖x‖_c = √⟨⟨x, x⟩⟩, the gradient is:
/// ∇‖x‖_c = x / ‖x‖_c
pub fn coherence_norm_gradient<P: Float>(x: &CliffordElement<P>) -> CliffordElement<P> {
    let norm = crate::metric::coherence_norm(x);

    if norm < P::epsilon() {
        // Gradient undefined at zero
        CliffordElement::zero(x.dimension())
    } else {
        x.clone() * (P::one() / norm)
    }
}

/// Compute directional derivative of coherence norm in direction v
pub fn coherence_directional_derivative<P: Float>(
    x: &CliffordElement<P>,
    v: &CliffordElement<P>,
) -> P {
    let grad = coherence_norm_gradient(x);
    coherence_product(&grad, v).re
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_complex::Complex;

    #[test]
    fn test_coherence_gradient() {
        let mut x = CliffordElement::<f64>::zero(3);
        x.set_component(0, Complex::new(3.0, 0.0)).unwrap();
        x.set_component(1, Complex::new(4.0, 0.0)).unwrap();

        let grad = coherence_gradient(&x);

        // Gradient should be 2x
        assert_eq!(grad.component(0), Some(Complex::new(6.0, 0.0)));
        assert_eq!(grad.component(1), Some(Complex::new(8.0, 0.0)));
    }

    #[test]
    fn test_norm_gradient() {
        let mut x = CliffordElement::<f64>::zero(3);
        x.set_component(0, Complex::new(3.0, 0.0)).unwrap();
        x.set_component(1, Complex::new(4.0, 0.0)).unwrap();

        let grad = coherence_norm_gradient(&x);
        let norm = crate::metric::coherence_norm(&x);

        // Gradient should be x/‖x‖
        assert!((grad.component(0).unwrap().re - 3.0 / norm).abs() < 1e-10);
        assert!((grad.component(1).unwrap().re - 4.0 / norm).abs() < 1e-10);
    }
}
