//! Resonance function implementation

use crate::{AlphaVec, CcmError, Float};

/// Trait for types that can compute their resonance value
pub trait Resonance<P: Float> {
    /// Compute the resonance value R(b) = ∏ α_i^{b_i}
    fn r(&self, alpha: &AlphaVec<P>) -> Result<P, CcmError>;

    /// Get all class members (up to 4 elements with same resonance)
    fn class_members(&self) -> Vec<Self>
    where
        Self: Sized;
}

/// Implementation for u8 (most common case)
impl<P: Float> Resonance<P> for u8 {
    fn r(&self, alpha: &AlphaVec<P>) -> Result<P, CcmError> {
        if alpha.len() < 8 {
            return Err(CcmError::InvalidLength);
        }

        let popcount = self.count_ones();

        // Use log-domain for large popcounts or when overflow is likely
        if popcount > 32 || should_use_log_domain::<P>(*self, alpha) {
            compute_resonance_log_domain(*self, alpha)
        } else {
            compute_resonance_direct(*self, alpha)
        }
    }

    fn class_members(&self) -> Vec<Self> {
        // For now, just return self
        // Full implementation would find all bytes with same resonance
        vec![*self]
    }
}

/// Direct product computation (ascending index order)
fn compute_resonance_direct<P: Float>(byte: u8, alpha: &AlphaVec<P>) -> Result<P, CcmError> {
    let mut result = P::one();

    for i in 0..8 {
        if (byte >> i) & 1 == 1 {
            let factor = alpha[i];

            // Check for overflow before multiplication
            if would_overflow(result, factor) {
                return Err(CcmError::FpRange);
            }

            result = result * factor;

            // Check for underflow/overflow after multiplication
            if !result.is_finite() {
                return Err(CcmError::FpRange);
            }
        }
    }

    Ok(result)
}

/// Log-domain computation for better numerical stability
fn compute_resonance_log_domain<P: Float>(byte: u8, alpha: &AlphaVec<P>) -> Result<P, CcmError> {
    let mut log_sum = P::zero();

    for i in 0..8 {
        if (byte >> i) & 1 == 1 {
            let log_alpha = alpha[i].ln();

            if !log_alpha.is_finite() {
                return Err(CcmError::FpRange);
            }

            log_sum = log_sum + log_alpha;
        }
    }

    // Check if result would be in valid range
    if log_sum.abs() > <P as num_traits::FromPrimitive>::from_f64(1024.0).unwrap() {
        return Err(CcmError::FpRange);
    }

    let result = log_sum.exp();

    if !result.is_finite() || result <= P::zero() {
        return Err(CcmError::FpRange);
    }

    Ok(result)
}

/// Heuristic to determine if log-domain computation should be used
fn should_use_log_domain<P: Float>(byte: u8, alpha: &AlphaVec<P>) -> bool {
    // Estimate the log magnitude of the result
    let mut log_estimate = P::zero();

    for i in 0..8 {
        if (byte >> i) & 1 == 1 {
            let val = alpha[i];
            if val > P::one() {
                log_estimate = log_estimate + val.ln();
            } else if val < P::one() {
                log_estimate = log_estimate - (-val.ln());
            }
        }
    }

    // Use log domain if the result might be very large or very small
    log_estimate.abs() > <P as num_traits::FromPrimitive>::from_f64(100.0).unwrap()
}

/// Check if multiplication would overflow
fn would_overflow<P: Float>(a: P, b: P) -> bool {
    if a == P::zero() || b == P::zero() {
        return false;
    }

    // Conservative check: if log(a) + log(b) > log(MAX)
    let max_exp = <P as num_traits::FromPrimitive>::from_f64(700.0).unwrap(); // Conservative for f64

    if a > P::one() && b > P::one() {
        a.ln() + b.ln() > max_exp
    } else {
        false
    }
}

/// Extension for BitWord types
use crate::bitword::BitWord;

impl<P: Float, const N: usize> Resonance<P> for BitWord<N> {
    fn r(&self, alpha: &AlphaVec<P>) -> Result<P, CcmError> {
        if alpha.len() < N {
            return Err(CcmError::InvalidLength);
        }

        let mut result = P::one();

        for i in 0..N {
            if self.bit(i) {
                result = result * alpha[i];

                if !result.is_finite() {
                    return Err(CcmError::FpRange);
                }
            }
        }

        Ok(result)
    }

    fn class_members(&self) -> Vec<Self> {
        vec![*self]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alpha::AlphaVec;

    #[test]
    fn test_resonance_u8() {
        // Create PrimeOS alpha vector
        let alpha = AlphaVec::try_from(vec![
            1.0,
            1.8392867552141612, // Tribonacci
            1.6180339887498950, // Golden ratio
            0.5,
            0.15915494309189535, // 1/(2π)
            6.283185307179586,   // 2π
            0.19961197478400415,
            0.014134725141734695,
        ])
        .unwrap();

        // Test byte 0 (empty product = 1)
        let r0 = 0u8.r(&alpha).unwrap();
        assert!((r0 - 1.0).abs() < 1e-10);

        // Test byte 48 = 0b00110000 (bits 4,5 set)
        // Should give α₄ * α₅ = 1/(2π) * 2π = 1
        let r48 = 48u8.r(&alpha).unwrap();
        assert!((r48 - 1.0).abs() < 1e-10);

        // Test byte with single bit
        let r1 = 1u8.r(&alpha).unwrap();
        assert!((r1 - 1.0).abs() < 1e-10); // α₀ = 1

        let r2 = 2u8.r(&alpha).unwrap();
        assert!((r2 - 1.8392867552141612).abs() < 1e-10);
    }

    #[test]
    fn test_overflow_protection() {
        // Create alpha vector with large values
        let mut values = vec![1e100; 8];
        values[6] = 1e-100;
        values[7] = 1e-100; // Satisfy unity constraint

        let alpha = AlphaVec::try_from(values).unwrap();

        // Byte with many bits set should trigger overflow protection
        let result = 0b11111111u8.r(&alpha);
        assert!(matches!(result, Err(CcmError::FpRange)));
    }
}
