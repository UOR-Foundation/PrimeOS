//! Internal math utilities, especially log-domain operations

use crate::Float;
use num_traits::FromPrimitive;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Compute log₂ of a value
pub fn log2<P: Float + FromPrimitive>(x: P) -> P {
    x.ln() / P::from_f64(core::f64::consts::LN_2).unwrap()
}

/// Compute 2^x
pub fn exp2<P: Float + FromPrimitive>(x: P) -> P {
    (x * P::from_f64(core::f64::consts::LN_2).unwrap()).exp()
}

/// Precompute logarithms of alpha values
#[cfg(feature = "alloc")]
pub fn precompute_logs<P: Float>(alpha: &[P]) -> Vec<P> {
    alpha.iter().map(|&a| a.ln()).collect()
}

/// Safe multiplication with overflow checking
pub fn safe_mul<P: Float>(a: P, b: P) -> Option<P> {
    let result = a * b;
    if result.is_finite() {
        Some(result)
    } else {
        None
    }
}

/// Check if a value is close to another within relative tolerance
pub fn approx_eq<P: Float>(a: P, b: P, rel_tol: P) -> bool {
    if a == b {
        return true;
    }

    let diff = (a - b).abs();
    let larger = if a.abs() > b.abs() { a.abs() } else { b.abs() };

    diff <= larger * rel_tol
}

/// Compute ulp (unit in last place) difference between two floats
pub fn ulp_diff(a: f64, b: f64) -> u64 {
    let a_bits = a.to_bits();
    let b_bits = b.to_bits();

    a_bits.abs_diff(b_bits)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_log2_exp2() {
        let x = 10.0_f64;
        let log2_x = log2(x);
        let recovered = exp2(log2_x);
        assert!((recovered - x).abs() < 1e-10);
    }

    #[test]
    fn test_approx_eq() {
        assert!(approx_eq(1.0, 1.0, 1e-10));
        assert!(approx_eq(1.0, 1.0 + 1e-11, 1e-10));
        assert!(!approx_eq(1.0, 1.0 + 1e-9, 1e-10));
    }

    #[test]
    fn test_ulp_diff() {
        let a = 1.0_f64;
        let b = f64::from_bits(a.to_bits() + 1);
        assert_eq!(ulp_diff(a, b), 1);
    }
}
