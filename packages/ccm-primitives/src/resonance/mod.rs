//! Resonance function implementation

use crate::{AlphaVec, CcmError, Float};

// Submodules
pub mod inverse;
pub mod classes;
pub mod conservation;
pub mod homomorphic;
pub mod gradient;
pub mod unity;

// Re-export key traits
pub use inverse::InverseResonance;
pub use classes::{ResonanceClasses, ResonanceClass, ClassDistribution};
pub use conservation::{ResonanceConservation, ConservationResult, CurrentExtrema};
pub use homomorphic::{HomomorphicResonance, HomomorphicSubgroup};
pub use gradient::ResonanceGradient;
pub use unity::UnityStructure;

/// Trait for types that can compute their resonance value
pub trait Resonance<P: Float> {
    /// Compute the resonance value R(b) = ∏ α_i^{b_i}
    fn r(&self, alpha: &AlphaVec<P>) -> P;

    /// Get all class members (up to 4 elements with same resonance)
    fn class_members(&self) -> [Self; 4]
    where
        Self: Sized + Copy;
    
    /// Get Klein group representative (first N-2 bits)
    fn klein_representative(&self) -> Self
    where
        Self: Sized + Copy;
    
    /// Check if this is the Klein minimum
    fn is_klein_minimum(&self, alpha: &AlphaVec<P>) -> bool
    where
        Self: Sized + Copy;
}

/// Implementation for u8 (most common case)
impl<P: Float> Resonance<P> for u8 {
    fn r(&self, alpha: &AlphaVec<P>) -> P {
        if alpha.len() < 8 {
            // Cannot panic per spec, return 1.0 as safe default
            return P::one();
        }

        let popcount = self.count_ones();

        // Use log-domain for large popcounts or when overflow is likely
        let result = if popcount > 32 || should_use_log_domain::<P>(*self, alpha) {
            compute_resonance_log_domain(*self, alpha)
        } else {
            compute_resonance_direct(*self, alpha)
        };

        // Return the result or 1.0 on error (spec requires no errors)
        result.unwrap_or(P::one())
    }

    fn class_members(&self) -> [Self; 4] {
        // With dynamic alpha, unity constraint is at positions (4,5)
        // So Klein groups are formed by XORing bits 4,5
        let b = *self;

        // The four members are: b ⊕ 00, b ⊕ 01, b ⊕ 10, b ⊕ 11 on bits 4,5
        [
            b,              // b ⊕ 00 (no change)
            b ^ 0b00010000, // b ⊕ 01 on bits 4,5
            b ^ 0b00100000, // b ⊕ 10 on bits 4,5
            b ^ 0b00110000, // b ⊕ 11 on bits 4,5
        ]
    }
    
    fn klein_representative(&self) -> Self {
        // Clear bits 4,5 to get Klein representative
        self & 0b11001111
    }
    
    fn is_klein_minimum(&self, alpha: &AlphaVec<P>) -> bool {
        let members = <Self as Resonance<P>>::class_members(self);
        let my_resonance = self.r(alpha);
        
        // Check if this has the minimum resonance among Klein group members
        for &member in &members {
            if member.r(alpha) < my_resonance {
                return false;
            }
        }
        true
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
    fn r(&self, alpha: &AlphaVec<P>) -> P {
        if alpha.len() < N {
            return P::one();
        }

        let mut result = P::one();

        // Direct product in ascending index order per spec
        for i in 0..N {
            if self.bit(i) {
                result = result * alpha[i];

                if !result.is_finite() {
                    // Return 1.0 on numerical issues
                    return P::one();
                }
            }
        }

        result
    }

    fn class_members(&self) -> [Self; 4] {
        if N < 6 {
            // Cannot form Klein groups without at least 6 bits (positions 4,5)
            [*self, *self, *self, *self]
        } else {
            // With dynamic alpha, unity is at positions 4,5
            // XOR with patterns on bits 4,5
            let bit_4 = 1u64 << 4;
            let bit_5 = 1u64 << 5;

            [
                *self,                                    // b ⊕ 00
                self.xor(&BitWord::from(bit_4)),         // b ⊕ 01
                self.xor(&BitWord::from(bit_5)),         // b ⊕ 10
                self.xor(&BitWord::from(bit_4 | bit_5)), // b ⊕ 11
            ]
        }
    }
    
    fn klein_representative(&self) -> Self {
        if N < 6 {
            *self
        } else {
            // Clear bits 4,5 to get Klein representative
            let mask = !(0b11u64 << 4);  // Create mask with bits 4,5 clear
            BitWord::from(self.to_usize() as u64 & mask)
        }
    }
    
    fn is_klein_minimum(&self, alpha: &AlphaVec<P>) -> bool {
        let members = <Self as Resonance<P>>::class_members(self);
        let my_resonance = self.r(alpha);
        
        for &member in &members {
            if member.r(alpha) < my_resonance {
                return false;
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alpha::AlphaVec;

    #[test]
    #[allow(clippy::approx_constant, clippy::excessive_precision)]
    fn test_resonance_u8() {
        // Use the testing alpha which has dynamic values
        let alpha = crate::tests::testing_alpha();

        // Test byte 0 (empty product = 1)
        let r0 = 0u8.r(&alpha);
        assert!((r0 - 1.0).abs() < 1e-10);

        // Test byte with single bit set
        let r1 = 1u8.r(&alpha);
        assert_eq!(r1, alpha[0]); // Should equal α₀

        let r2 = 2u8.r(&alpha);
        assert_eq!(r2, alpha[1]); // Should equal α₁

        // Test byte with multiple bits
        let r3 = 3u8.r(&alpha); // bits 0,1 set
        assert!((r3 - alpha[0] * alpha[1]).abs() < 1e-10);

        // Test that resonance is always positive
        for byte in 0..=255u8 {
            let r = byte.r(&alpha);
            assert!(r > 0.0, "Resonance for byte {} should be positive", byte);
            assert!(r.is_finite(), "Resonance for byte {} should be finite", byte);
        }
    }

    #[test]
    fn test_overflow_protection() {
        // Create an alpha vector that will produce very large products
        // For 8 values, unity constraint is at positions 4,5: α[4] * α[5] = 1
        let mut values = vec![2.0f64.powf(19.0); 8]; // Near the limit of |log₂| ≤ 20
        values[4] = 2.0f64.powf(-19.0);
        values[5] = 2.0f64.powf(19.0); // Satisfy unity constraint: 2^(-19) * 2^19 = 1

        let alpha = AlphaVec::try_from(values).unwrap();

        // Test that computation doesn't panic and returns a valid result
        let result = 0b11111111u8.r(&alpha);
        assert!(result.is_finite());

        // With all bits set: 2^19 * 2^19 * 2^19 * 2^19 * 2^-19 * 2^19 * 2^19 * 2^19
        // = 2^(19*6 + (-19) + 19) = 2^(114 - 19 + 19) = 2^114
        // This demonstrates that the implementation correctly handles large values without overflow
        let expected = 2.0f64.powf(114.0);
        assert!((result - expected).abs() / expected < 1e-10);
    }

    #[test]
    fn test_class_members() {
        let b = 0b00110101u8; // Example byte
        let members = <u8 as Resonance<f64>>::class_members(&b);

        // Should produce 4 members by XORing with patterns on bits 4,5
        assert_eq!(members[0], b); // No change (b ^ 0 = b)
        assert_eq!(members[1], b ^ 0b00010000); // Flip bit 4
        assert_eq!(members[2], b ^ 0b00100000); // Flip bit 5
        assert_eq!(members[3], b ^ 0b00110000); // Flip both bits 4,5

        // All members should be distinct unless the original has specific patterns
        let unique_count = members
            .iter()
            .collect::<std::collections::HashSet<_>>()
            .len();
        assert!((1..=4).contains(&unique_count));
    }
}
