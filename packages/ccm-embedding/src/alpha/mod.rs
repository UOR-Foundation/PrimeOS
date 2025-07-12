//! Alpha vector representation and validation

use ccm_core::{CcmError, Float};

pub mod generator;

#[cfg(feature = "alloc")]
use alloc::{boxed::Box, vec::Vec};

/// Error type specific to AlphaVec operations
#[derive(Debug, Clone, PartialEq)]
pub enum AlphaError {
    /// Vector length must be between 3 and 64 (or 512 with binary128)
    InvalidLength(usize),
    /// Alpha values must be positive
    NonPositiveValue(usize),
    /// Unity constraint not satisfied: α[n-2] * α[n-1] ≠ 1
    UnityConstraintViolation,
}

impl From<AlphaError> for CcmError {
    fn from(e: AlphaError) -> Self {
        match e {
            AlphaError::InvalidLength(_) => CcmError::InvalidLength,
            AlphaError::NonPositiveValue(_) => CcmError::AlphaConstraint,
            AlphaError::UnityConstraintViolation => CcmError::AlphaConstraint,
        }
    }
}

/// Positive real constants α₀ … αₙ₋₁ with αₙ₋₂·αₙ₋₁ ≈ 1.
#[derive(Debug, Clone)]
pub struct AlphaVec<P: Float> {
    /// The alpha values, length n where 3 ≤ n ≤ 64 (or 512 with binary128)
    pub values: Box<[P]>,
}

impl<P: Float> AlphaVec<P> {
    /// Maximum length for performance testing
    /// Note: The implementation supports arbitrary sizes, but for
    /// practical testing we may limit to smaller values
    pub const MAX_LEN_TESTING: usize = 4096;

    /// Get the maximum allowed length
    /// This is not a hard limit of the implementation, but a practical
    /// limit for testing and validation purposes
    pub fn max_len() -> usize {
        // In principle, AlphaVec can support arbitrary sizes
        // Limited only by available memory and numerical precision
        usize::MAX
    }

    /// Validate the unity constraint: α[n-2] * α[n-1] = 1
    fn validate_unity_constraint(values: &[P]) -> Result<(), AlphaError> {
        let n = values.len();
        if n < 3 {
            // We need at least 3 values for unity constraint
            return Err(AlphaError::InvalidLength(n));
        }

        // Unity constraint is always at positions (n-2, n-1) for Klein groups
        let (u1, u2) = (n - 2, n - 1);

        let product = values[u1] * values[u2];
        let one = P::one();
        let epsilon = P::epsilon();

        // Check relative tolerance: |product - 1| / |1| ≤ epsilon
        let relative_error = ((product - one) / one).abs();
        if relative_error > epsilon {
            return Err(AlphaError::UnityConstraintViolation);
        }

        Ok(())
    }

    /// Create a new AlphaVec from a boxed slice, validating all constraints
    pub fn new(values: Box<[P]>) -> Result<Self, AlphaError> {
        let n = values.len();

        // Check length constraints
        if n < 3 || n > Self::max_len() {
            return Err(AlphaError::InvalidLength(n));
        }

        // Check all values meet constraints: 0 < αᵢ ≤ 2^128 and |log₂ αᵢ| ≤ 20
        for (i, &value) in values.iter().enumerate() {
            // Check positive
            if value <= P::zero() {
                return Err(AlphaError::NonPositiveValue(i));
            }

            // Check |log₂ αᵢ| ≤ 20 (which implicitly bounds the value)
            let log2_value = value.log2();
            if log2_value.abs() > P::from(20.0).unwrap() {
                return Err(AlphaError::NonPositiveValue(i));
            }

            // Note: 2^20 < 2^128, so the log constraint is actually more restrictive
            // than the 2^128 bound, making an explicit check unnecessary
        }

        // Validate unity constraint
        Self::validate_unity_constraint(&values)?;

        Ok(Self { values })
    }

    /// Get the number of alpha values
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Check if the vector is empty (always false for valid AlphaVec)
    pub fn is_empty(&self) -> bool {
        false // Valid AlphaVec always has at least 3 elements
    }

    /// Verify that the unity constraint is satisfied
    pub fn verify_unity_constraint(&self) -> bool {
        let n = self.values.len();
        if n < 3 {
            return false;
        }

        let (u1, u2) = (n - 2, n - 1);
        let product = self.values[u1] * self.values[u2];
        let one = P::one();
        let epsilon = P::epsilon();

        let relative_error = ((product - one) / one).abs();
        relative_error <= epsilon
    }

    /// Generate alpha values dynamically for N-bit inputs
    #[cfg(any(feature = "alloc", feature = "std"))]
    pub fn for_bit_length(n: usize) -> Result<Self, AlphaError>
    where
        P: num_traits::FromPrimitive,
    {
        let config = generator::AlphaConfig::for_bits(n);
        generator::generate_alpha(config)
    }

    /// Generate alpha values using mathematical constants
    #[cfg(any(feature = "alloc", feature = "std"))]
    pub fn mathematical(bit_length: usize) -> Result<Self, AlphaError>
    where
        P: num_traits::FromPrimitive,
    {
        generator::generate_mathematical_alpha(bit_length)
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
impl<P: Float> TryFrom<Vec<P>> for AlphaVec<P> {
    type Error = AlphaError;

    fn try_from(vec: Vec<P>) -> Result<Self, Self::Error> {
        Self::new(vec.into_boxed_slice())
    }
}

impl<P: Float> AsRef<[P]> for AlphaVec<P> {
    fn as_ref(&self) -> &[P] {
        &self.values
    }
}

impl<P: Float> core::ops::Deref for AlphaVec<P> {
    type Target = [P];

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

// Float trait is already implemented for f64 in num-traits
// f32 is explicitly NOT recommended as it lacks sufficient precision for CCM

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alpha_vec_creation() {
        // Valid case
        let values = vec![1.0, 2.0, 0.5].into_boxed_slice();
        let alpha = AlphaVec::new(values).unwrap();
        assert_eq!(alpha.len(), 3);

        // Unity constraint satisfied: 2.0 * 0.5 = 1.0
        assert_eq!(alpha[1] * alpha[2], 1.0);
    }

    #[test]
    fn test_unity_constraint_violation() {
        let values = vec![1.0, 2.0, 3.0].into_boxed_slice();
        let result = AlphaVec::new(values);
        assert!(matches!(result, Err(AlphaError::UnityConstraintViolation)));
    }

    #[test]
    fn test_invalid_length() {
        // Too short
        let values = vec![1.0, 2.0].into_boxed_slice();
        let result = AlphaVec::<f64>::new(values);
        assert!(matches!(result, Err(AlphaError::InvalidLength(2))));

        // Since we support arbitrary sizes limited only by memory,
        // we can't test "too long" without causing overflow
    }
}
