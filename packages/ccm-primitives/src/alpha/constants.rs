//! Standard alpha constants for CCM primitives
//!
//! These alpha values ensure unique minimum resonances per Klein group,
//! which is required for BJC codec bijectivity.

use crate::{AlphaVec, Float};

/// Create the standard CCM alpha vector
///
/// The values are carefully chosen to:
/// 1. Avoid any α = 1.0 (except as part of unity constraint)
/// 2. Ensure unique minimum resonances per Klein group
/// 3. Satisfy the unity constraint: α[n-2] * α[n-1] = 1
/// 4. Use well-known mathematical constants for reproducibility
pub fn standard_alpha<P: Float>() -> AlphaVec<P> {
    AlphaVec::try_from(vec![
        P::from(std::f64::consts::E).unwrap(),   // α₀ = e ≈ 2.71828
        P::from(1.8392867552141612).unwrap(),    // α₁ = tribonacci constant
        P::from(1.618_033_988_749_895).unwrap(), // α₂ = φ (golden ratio)
        P::from(std::f64::consts::PI).unwrap(),  // α₃ = π ≈ 3.14159
        P::from(3.0_f64.sqrt()).unwrap(),        // α₄ = √3 ≈ 1.73205
        P::from(2.0).unwrap(),                   // α₅ = 2
        P::from(std::f64::consts::PI / 2.0).unwrap(), // α₆ = π/2 ≈ 1.57080
        P::from(2.0 / std::f64::consts::PI).unwrap(), // α₇ = 2/π ≈ 0.63662
    ])
    .expect("Standard alpha values should always be valid")
}

/// The standard alpha values as f64 constants
pub mod f64_constants {
    pub const ALPHA_0: f64 = std::f64::consts::E; // e
    pub const ALPHA_1: f64 = 1.8392867552141612; // tribonacci
    pub const ALPHA_2: f64 = 1.618_033_988_749_895; // φ
    pub const ALPHA_3: f64 = std::f64::consts::PI; // π
    pub const ALPHA_4: f64 = 1.732_050_807_568_877; // √3
    pub const ALPHA_5: f64 = 2.0; // 2
    pub const ALPHA_6: f64 = std::f64::consts::FRAC_PI_2; // π/2
    pub const ALPHA_7: f64 = std::f64::consts::FRAC_2_PI; // 2/π

    /// Verify unity constraint
    pub const UNITY_PRODUCT: f64 = ALPHA_6 * ALPHA_7; // Should be 1.0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_standard_alpha_unity() {
        let alpha = standard_alpha::<f64>();
        let n = alpha.len();
        let product = alpha[n - 2] * alpha[n - 1];
        assert!(
            (product - 1.0).abs() < 1e-10,
            "Unity constraint failed: {} * {} = {}",
            alpha[n - 2],
            alpha[n - 1],
            product
        );
    }

    #[test]
    fn test_f64_constants_unity() {
        use f64_constants::*;
        assert!(
            (UNITY_PRODUCT - 1.0).abs() < 1e-10,
            "Unity constant check failed: {} * {} = {}",
            ALPHA_6,
            ALPHA_7,
            UNITY_PRODUCT
        );
    }
}
