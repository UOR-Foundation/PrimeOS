//! Alpha vector representation and validation

use crate::{error::CcmError, Float};

pub mod constants;

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
    /// Maximum length without binary128 feature
    pub const MAX_LEN_STANDARD: usize = 64;

    /// Maximum length with binary128 feature
    #[cfg(feature = "binary128")]
    pub const MAX_LEN_EXTENDED: usize = 512;

    /// Get the maximum allowed length based on features
    pub fn max_len() -> usize {
        #[cfg(feature = "binary128")]
        {
            Self::MAX_LEN_EXTENDED
        }
        #[cfg(not(feature = "binary128"))]
        {
            Self::MAX_LEN_STANDARD
        }
    }

    /// Validate the unity constraint: α[n-2] * α[n-1] = 1
    fn validate_unity_constraint(values: &[P]) -> Result<(), AlphaError> {
        let n = values.len();
        if n < 2 {
            return Err(AlphaError::InvalidLength(n));
        }

        let product = values[n - 2] * values[n - 1];
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

// Float trait implementations for types that meet CCM precision requirements
// f32 is explicitly NOT implemented as it lacks sufficient precision
impl Float for f64 {}

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

        // Too long
        let max_len = AlphaVec::<f64>::max_len();
        let mut values = Vec::new();
        for i in 0..(max_len + 1) {
            values.push((i + 1) as f64);
        }
        // Ensure unity constraint for last two values
        let n = values.len();
        values[n - 2] = 2.0;
        values[n - 1] = 0.5;
        let result = AlphaVec::new(values.into_boxed_slice());
        assert!(matches!(result, Err(AlphaError::InvalidLength(_))));
    }
}
