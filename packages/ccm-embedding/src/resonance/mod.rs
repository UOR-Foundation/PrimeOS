//! Resonance function implementation
//!
//! This module provides a complete implementation of resonance algebra supporting
//! arbitrary bit lengths from 8 bits to theoretical infinity.
//!
//! ## Overview
//!
//! The resonance function R: {0,1}^n → ℝ⁺ computes a positive real value for
//! any bit pattern based on field constants α = (α₀, α₁, ..., α_{n-1}).
//!
//! ## Key Features
//!
//! - **Arbitrary precision**: Supports bit patterns of any length via BitWord
//! - **Numerical stability**: Automatic log-domain computation for large values  
//! - **Klein group structure**: 4-element equivalence classes via XOR on last 2 bits
//! - **Unity constraint**: α_{n-2} × α_{n-1} = 1 enables special properties
//! - **Conservation laws**: Resonance sums are conserved over specific cycles
//!
//! ## Klein Group Structure
//!
//! For n-bit patterns, Klein groups are formed by XORing bits at positions (n-2, n-1):
//!
//! - Each Klein group contains exactly 4 members: {b, b⊕01, b⊕10, b⊕11}
//! - The unity constraint ensures these positions have special algebraic properties
//! - For 8-bit values, this corresponds to bits 6,7
//! - The Klein minimum is the member with the smallest resonance value
//! - All resonance operations preserve Klein group membership
//!
//! ## Submodules
//!
//! - [`classes`]: Resonance equivalence classes and spectrum analysis
//! - [`conservation`]: Conservation laws and resonance currents
//! - [`gradient`]: Gradient-based optimization in resonance space
//! - [`homomorphic`]: XOR-homomorphic subgroups and properties
//! - [`inverse`]: Finding bit patterns with target resonance values
//! - [`unity`]: Unity positions where R(b) = 1
//!
//! ## Example
//!
//! ```no_run
//! use ccm_embedding::{AlphaVec, Resonance};
//! use ccm_core::BitWord;
//!
//! // Generate alpha for 64-bit system
//! let alpha = AlphaVec::<f64>::for_bit_length(64).unwrap();
//!
//! // Compute resonance for a bit pattern
//! let word = BitWord::from_u64(0xDEADBEEF, 64);
//! let r = word.r(&alpha);
//! println!("Resonance: {}", r);
//!
//! // Find Klein group members
//! let members = <BitWord as Resonance<f64>>::class_members(&word);
//! assert_eq!(members.len(), 4);
//! ```
//!
//! ## Performance
//!
//! Operations scale efficiently with bit length:
//! - O(n) for basic resonance computation
//! - O(1) for Klein group operations  
//! - O(sampling) for large-scale analysis
//!
//! See README.md for detailed scaling properties and algorithm complexities.

use crate::AlphaVec;
use ccm_core::{CcmError, Float};
use num_traits::FromPrimitive;

// Submodules
pub mod classes;
pub mod conservation;
pub mod decomposition;
pub mod gradient;
pub mod homomorphic;
pub mod inverse;
pub mod unity;

#[cfg(test)]
pub mod bitword_tests;

// Re-export key traits
pub use classes::{ClassDistribution, ResonanceClass, ResonanceClasses};
pub use conservation::{ConservationResult, CurrentExtrema, ResonanceConservation, DecompositionConservationResult};
pub use decomposition::{ResonanceDecomposable, KleinPartition, ResonanceBoundary, ResonanceBoundaryType};
pub use gradient::ResonanceGradient;
pub use homomorphic::{HomomorphicResonance, HomomorphicSubgroup};
pub use inverse::InverseResonance;
pub use unity::UnityStructure;

/// Trait for types that can compute their resonance value
pub trait Resonance<P: Float> {
    /// Compute the resonance value R(b) = ∏ α_i^{b_i}
    fn r(&self, alpha: &AlphaVec<P>) -> P;

    /// Get all class members (up to 4 elements with same resonance)
    #[cfg(feature = "alloc")]
    fn class_members(&self) -> alloc::vec::Vec<Self>
    where
        Self: Sized + Clone;

    /// Get Klein group representative (first N-2 bits)
    fn klein_representative(&self) -> Self
    where
        Self: Sized + Clone;

    /// Check if this is the Klein minimum
    #[cfg(feature = "alloc")]
    fn is_klein_minimum(&self, alpha: &AlphaVec<P>) -> bool
    where
        Self: Sized + Clone;
}

/// Implementation for u8 (most common case)
impl<P: Float + FromPrimitive> Resonance<P> for u8 {
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

    #[cfg(feature = "alloc")]
    fn class_members(&self) -> alloc::vec::Vec<Self> {
        // Klein groups are formed by XORing the last two bits
        // These correspond to unity constraint positions (N-2, N-1)
        let b = *self;

        // For u8 (N=8), Klein group uses bits 6,7
        alloc::vec![
            b,              // b ⊕ 00 (no change)
            b ^ 0b01000000, // b ⊕ 01 on bits 6,7
            b ^ 0b10000000, // b ⊕ 10 on bits 6,7
            b ^ 0b11000000, // b ⊕ 11 on bits 6,7
        ]
    }

    fn klein_representative(&self) -> Self {
        // Clear bits 6,7 to get Klein representative (N-2, N-1 for N=8)
        self & 0b00111111
    }

    #[cfg(feature = "alloc")]
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

/// Direct product computation for u8 (ascending index order)
fn compute_resonance_direct<P: Float + FromPrimitive>(
    byte: u8,
    alpha: &AlphaVec<P>,
) -> Result<P, CcmError> {
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

/// Log-domain computation for u8 for better numerical stability
fn compute_resonance_log_domain<P: Float + FromPrimitive>(
    byte: u8,
    alpha: &AlphaVec<P>,
) -> Result<P, CcmError> {
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
    if log_sum.abs() > P::from_f64(1024.0).unwrap() {
        return Err(CcmError::FpRange);
    }

    let result = log_sum.exp();

    if !result.is_finite() || result <= P::zero() {
        return Err(CcmError::FpRange);
    }

    Ok(result)
}

/// Heuristic to determine if log-domain computation should be used for u8
fn should_use_log_domain<P: Float + FromPrimitive>(byte: u8, alpha: &AlphaVec<P>) -> bool {
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
    log_estimate.abs() > P::from_f64(100.0).unwrap()
}

/// Direct product computation for BitWord (ascending index order)
#[cfg(feature = "alloc")]
fn compute_resonance_direct_bitword<P: Float + FromPrimitive>(
    word: &BitWord,
    alpha: &AlphaVec<P>,
) -> Result<P, CcmError> {
    let mut result = P::one();
    let max_bits = word.len().min(alpha.len());

    for i in 0..max_bits {
        if word.bit(i) {
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

/// Log-domain computation for BitWord for better numerical stability
#[cfg(feature = "alloc")]
fn compute_resonance_log_domain_bitword<P: Float + FromPrimitive>(
    word: &BitWord,
    alpha: &AlphaVec<P>,
) -> Result<P, CcmError> {
    let mut log_sum = P::zero();
    let max_bits = word.len().min(alpha.len());

    for i in 0..max_bits {
        if word.bit(i) {
            let log_alpha = alpha[i].ln();

            if !log_alpha.is_finite() {
                return Err(CcmError::FpRange);
            }

            log_sum = log_sum + log_alpha;
        }
    }

    // Check if result would be in valid range
    if log_sum.abs() > P::from_f64(1024.0).unwrap() {
        return Err(CcmError::FpRange);
    }

    let result = log_sum.exp();

    if !result.is_finite() || result <= P::zero() {
        return Err(CcmError::FpRange);
    }

    Ok(result)
}

/// Heuristic to determine if log-domain computation should be used for BitWord
#[cfg(feature = "alloc")]
fn should_use_log_domain_bitword<P: Float + FromPrimitive>(
    word: &BitWord,
    alpha: &AlphaVec<P>,
) -> bool {
    let popcount = word.popcount();

    // Use log domain for large popcounts
    if popcount > 32 {
        return true;
    }

    // Estimate the log magnitude of the result
    let mut log_estimate = P::zero();
    let max_bits = word.len().min(alpha.len());

    for i in 0..max_bits {
        if word.bit(i) {
            let val = alpha[i];
            if val > P::one() {
                log_estimate = log_estimate + val.ln();
            } else if val < P::one() {
                log_estimate = log_estimate - (-val.ln());
            }
        }
    }

    // Use log domain if the result might be very large or very small
    log_estimate.abs() > P::from_f64(100.0).unwrap()
}

/// Check if multiplication would overflow
fn would_overflow<P: Float + FromPrimitive>(a: P, b: P) -> bool {
    if a == P::zero() || b == P::zero() {
        return false;
    }

    // Conservative check: if log(a) + log(b) > log(MAX)
    let max_exp = P::from_f64(700.0).unwrap(); // Conservative for f64

    if a > P::one() && b > P::one() {
        a.ln() + b.ln() > max_exp
    } else {
        false
    }
}

/// Extension for BitWord types
use ccm_core::BitWord;

/// Implementation for BitWord (arbitrary size)
#[cfg(feature = "alloc")]
impl<P: Float + FromPrimitive> Resonance<P> for BitWord {
    fn r(&self, alpha: &AlphaVec<P>) -> P {
        if alpha.len() < self.len() {
            // Cannot panic per spec, return 1.0 as safe default
            return P::one();
        }

        let popcount = self.popcount();

        // Use log-domain for large popcounts or when overflow is likely
        let result = if popcount > 32 || should_use_log_domain_bitword::<P>(self, alpha) {
            compute_resonance_log_domain_bitword(self, alpha)
        } else {
            compute_resonance_direct_bitword(self, alpha)
        };

        // Return the result or 1.0 on error (spec requires no errors)
        result.unwrap_or(P::one())
    }

    fn class_members(&self) -> alloc::vec::Vec<Self> {
        let n = self.len();
        if n < 2 {
            // Cannot form Klein groups without at least 2 bits
            alloc::vec![self.clone()]
        } else {
            // Klein groups are formed by XORing the last two bits (n-2, n-1)
            let mut member1 = self.clone();
            let mut member2 = self.clone();
            let mut member3 = self.clone();

            // Flip bit n-2
            member1.flip_bit(n - 2);

            // Flip bit n-1
            member2.flip_bit(n - 1);

            // Flip both bits n-2 and n-1
            member3.flip_bit(n - 2);
            member3.flip_bit(n - 1);

            alloc::vec![
                self.clone(), // b ⊕ 00
                member1,      // b ⊕ 01
                member2,      // b ⊕ 10
                member3,      // b ⊕ 11
            ]
        }
    }

    fn klein_representative(&self) -> Self {
        let n = self.len();
        if n < 2 {
            self.clone()
        } else {
            // Clear the last two bits (n-2, n-1) to get Klein representative
            let mut repr = self.clone();
            repr.set_bit(n - 2, false);
            repr.set_bit(n - 1, false);
            repr
        }
    }

    fn is_klein_minimum(&self, alpha: &AlphaVec<P>) -> bool {
        let members = <Self as Resonance<P>>::class_members(self);
        let my_resonance = self.r(alpha);

        for member in &members {
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
            assert!(
                r.is_finite(),
                "Resonance for byte {} should be finite",
                byte
            );
        }
    }

    #[test]
    fn test_overflow_protection() {
        // Create an alpha vector that will produce very large products
        // For 8 values, unity constraint is at positions 6,7 (n-2, n-1)
        let mut values = vec![2.0f64.powf(19.0); 8]; // Near the limit of |log₂| ≤ 20
        values[6] = 2.0f64.powf(-19.0);
        values[7] = 2.0f64.powf(19.0); // Satisfy unity constraint: 2^(-19) * 2^19 = 1

        let alpha = AlphaVec::try_from(values).unwrap();

        // Test that computation doesn't panic and returns a valid result
        let result = 0b11111111u8.r(&alpha);
        assert!(result.is_finite());

        // With all bits set: 2^19 * 2^19 * 2^19 * 2^19 * 2^19 * 2^19 * 2^-19 * 2^19
        // = 2^(19*7 + (-19)) = 2^(133 - 19) = 2^114
        // This demonstrates that the implementation correctly handles large values without overflow
        let expected = 2.0f64.powf(114.0);
        assert!((result - expected).abs() / expected < 1e-10);
    }

    #[test]
    fn test_class_members() {
        let b = 0b00110101u8; // Example byte
        let members = <u8 as Resonance<f64>>::class_members(&b);

        // Should produce 4 members by XORing with patterns on bits 6,7
        assert_eq!(members[0], b); // No change (b ^ 0 = b)
        assert_eq!(members[1], b ^ 0b01000000); // Flip bit 6
        assert_eq!(members[2], b ^ 0b10000000); // Flip bit 7
        assert_eq!(members[3], b ^ 0b11000000); // Flip both bits 6,7

        // All members should be distinct unless the original has specific patterns
        let unique_count = members
            .iter()
            .collect::<std::collections::HashSet<_>>()
            .len();
        assert!((1..=4).contains(&unique_count));
    }

    #[test]
    fn test_resonance_large_bit_lengths() {
        // Test that resonance calculation works for large N values
        for n in [64, 128, 256, 512, 1024, 2048, 4096] {
            // Generate alpha values for N bits
            let alpha = AlphaVec::<f64>::for_bit_length(n).unwrap();
            test_resonance_n(n, &alpha);
        }
    }

    fn test_resonance_n(n: usize, alpha: &AlphaVec<f64>) {
        // Test empty value (all bits 0)
        let zero = BitWord::from_u64(0u64, n);
        let r_zero = zero.r(alpha);
        assert_eq!(r_zero, 1.0, "Empty product should be 1.0 for n={}", n);

        // Test single bit set at position 0
        let one = BitWord::from_u64(1u64, n);
        let r_one = one.r(alpha);
        assert_eq!(r_one, alpha[0], "Single bit 0 should give α₀ for n={}", n);

        // Test Klein group formation for n >= 2
        if n >= 2 {
            let test_val = BitWord::from_u64(42u64, n);
            let members = <BitWord as Resonance<f64>>::class_members(&test_val);

            // Verify Klein group has 4 members
            assert_eq!(
                members.len(),
                4,
                "Klein group should have 4 members for n={}",
                n
            );

            // Verify Klein group uses bits (n-2, n-1)
            if n <= 64 {
                let bit_n_minus_2 = 1u64 << (n - 2);
                let bit_n_minus_1 = 1u64 << (n - 1);

                assert_eq!(members[0].to_usize(), test_val.to_usize());
                assert_eq!(
                    members[1].to_usize(),
                    test_val.to_usize() ^ bit_n_minus_2 as usize
                );
                assert_eq!(
                    members[2].to_usize(),
                    test_val.to_usize() ^ bit_n_minus_1 as usize
                );
                assert_eq!(
                    members[3].to_usize(),
                    test_val.to_usize() ^ (bit_n_minus_2 | bit_n_minus_1) as usize
                );
            }

            // Verify unity constraint positions create unity resonance
            let mut unity_val = BitWord::new(n);
            unity_val.set_bit(n - 2, true);
            unity_val.set_bit(n - 1, true);
            let r_unity = unity_val.r(alpha);
            assert!(
                (r_unity - 1.0).abs() < 1e-10,
                "Unity positions ({},{}) should give resonance 1.0 for n={}, got {}",
                n - 2,
                n - 1,
                n,
                r_unity
            );
        }

        // Test that resonance is always positive and finite
        for i in 0..10 {
            let test_val = if n < 64 {
                BitWord::from_u64((i * 137u64) % (1u64 << n), n)
            } else {
                // For n >= 64, create a pattern without causing shift overflow
                let mut word = BitWord::new(n);
                // Set some bits in a pattern
                for j in 0..n.min(10) {
                    if (i + j as u64) % 3 == 0 {
                        word.set_bit(j, true);
                    }
                }
                word
            };
            let r = test_val.r(alpha);
            assert!(
                r > 0.0 && r.is_finite(),
                "Resonance should be positive and finite for n={}",
                n
            );
        }
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn test_bitword_large_resonance() {
        // Test BitWord with various sizes including large ones
        for n in [8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096] {
            let alpha = AlphaVec::<f64>::for_bit_length(n).unwrap();

            // Test empty value (all bits 0)
            let zero = BitWord::new(n);
            let r_zero = zero.r(&alpha);
            assert_eq!(r_zero, 1.0, "Empty product should be 1.0 for n={}", n);

            // Test single bit set at position 0
            let mut one = BitWord::new(n);
            one.set_bit(0, true);
            let r_one = one.r(&alpha);
            assert_eq!(r_one, alpha[0], "Single bit 0 should give α₀ for n={}", n);

            // Test Klein group formation for n >= 2
            if n >= 2 {
                let test_val = BitWord::from_u64(42, n);
                let members = <BitWord as Resonance<f64>>::class_members(&test_val);

                // Verify Klein group has 4 members
                assert_eq!(
                    members.len(),
                    4,
                    "Klein group should have 4 members for n={}",
                    n
                );

                // Verify unity constraint positions create unity resonance
                let mut unity_val = BitWord::new(n);
                unity_val.set_bit(n - 2, true);
                unity_val.set_bit(n - 1, true);
                let r_unity = unity_val.r(&alpha);
                assert!(
                    (r_unity - 1.0).abs() < 1e-10,
                    "Unity positions ({},{}) should give resonance 1.0 for n={}, got {}",
                    n - 2,
                    n - 1,
                    n,
                    r_unity
                );
            }

            // Test that resonance is always positive and finite
            for i in 0..10.min(n) {
                let mut test_val = BitWord::new(n);
                test_val.set_bit(i, true);
                let r = test_val.r(&alpha);
                assert!(
                    r > 0.0 && r.is_finite(),
                    "Resonance should be positive and finite for n={}",
                    n
                );
            }
        }
    }
}
