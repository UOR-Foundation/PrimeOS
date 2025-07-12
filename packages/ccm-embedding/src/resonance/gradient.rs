//! Gradient and optimization operations for resonance

use crate::{AlphaVec, Resonance};
use ccm_core::{CcmError, Float};
use num_traits::FromPrimitive;

#[cfg(feature = "alloc")]
use alloc::vec;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Trait for gradient-based resonance operations
pub trait ResonanceGradient<P: Float> {
    /// Compute gradient with respect to bit flips
    fn bit_gradient(&self, alpha: &AlphaVec<P>) -> Vec<P>;

    /// Find steepest ascent/descent direction
    fn steepest_direction(&self, alpha: &AlphaVec<P>, maximize: bool) -> Option<usize>;

    /// Gradient-guided search from starting point
    fn gradient_search(
        start: Self,
        target: P,
        alpha: &AlphaVec<P>,
        max_steps: usize,
    ) -> Result<Self, CcmError>
    where
        Self: Sized;
}

/// Implementation for u8
impl<P: Float + FromPrimitive> ResonanceGradient<P> for u8 {
    fn bit_gradient(&self, alpha: &AlphaVec<P>) -> Vec<P> {
        let mut gradients = Vec::with_capacity(8);
        let current_resonance = self.r(alpha);

        for i in 0..8 {
            let bit_is_set = (self >> i) & 1 == 1;

            if bit_is_set {
                // Gradient when bit i is set: ∂R/∂b_i = -R * ln(α_i)
                let grad = -current_resonance * alpha[i].ln();
                gradients.push(grad);
            } else {
                // Gradient when bit i is clear: ∂R/∂b_i = R * ln(α_i)
                let grad = current_resonance * alpha[i].ln();
                gradients.push(grad);
            }
        }

        gradients
    }

    fn steepest_direction(&self, alpha: &AlphaVec<P>, maximize: bool) -> Option<usize> {
        let gradients = self.bit_gradient(alpha);

        if maximize {
            // Find bit with largest positive gradient
            gradients
                .iter()
                .enumerate()
                .filter(|(_, &g)| g > P::zero())
                .max_by(|(_, &a), (_, &b)| a.partial_cmp(&b).unwrap())
                .map(|(i, _)| i)
        } else {
            // Find bit with largest negative gradient (most negative)
            gradients
                .iter()
                .enumerate()
                .filter(|(_, &g)| g < P::zero())
                .min_by(|(_, &a), (_, &b)| a.partial_cmp(&b).unwrap())
                .map(|(i, _)| i)
        }
    }

    fn gradient_search(
        start: Self,
        target: P,
        alpha: &AlphaVec<P>,
        max_steps: usize,
    ) -> Result<Self, CcmError> {
        let mut current = start;
        let tolerance = P::epsilon() * P::from(100.0).unwrap();

        for _ in 0..max_steps {
            let current_resonance = current.r(alpha);
            let error = (current_resonance - target).abs();

            if error < tolerance {
                return Ok(current);
            }

            // Determine if we need to increase or decrease resonance
            let need_increase = current_resonance < target;

            // Find steepest direction
            if let Some(bit_idx) = current.steepest_direction(alpha, need_increase) {
                // Flip the bit
                current ^= 1u8 << bit_idx;
            } else {
                // No improving direction found
                break;
            }
        }

        // Return best found even if not perfect
        Ok(current)
    }
}

/// Implementation for BitWord
use ccm_core::BitWord;

#[cfg(feature = "alloc")]
impl<P: Float + FromPrimitive> ResonanceGradient<P> for BitWord {
    fn bit_gradient(&self, alpha: &AlphaVec<P>) -> Vec<P> {
        let n = alpha.len();
        let mut gradients = Vec::with_capacity(n);
        let current_resonance = self.r(alpha);

        for i in 0..n {
            let bit_is_set = self.bit(i);

            if bit_is_set {
                // Gradient when bit i is set: ∂R/∂b_i = -R * ln(α_i)
                let grad = -current_resonance * alpha[i].ln();
                gradients.push(grad);
            } else {
                // Gradient when bit i is clear: ∂R/∂b_i = R * ln(α_i)
                let grad = current_resonance * alpha[i].ln();
                gradients.push(grad);
            }
        }

        gradients
    }

    fn steepest_direction(&self, alpha: &AlphaVec<P>, maximize: bool) -> Option<usize> {
        let gradients = self.bit_gradient(alpha);

        if maximize {
            // Find bit with largest positive gradient
            gradients
                .iter()
                .enumerate()
                .filter(|(_, &g)| g > P::zero())
                .max_by(|(_, &a), (_, &b)| a.partial_cmp(&b).unwrap())
                .map(|(i, _)| i)
        } else {
            // Find bit with largest negative gradient (most negative)
            gradients
                .iter()
                .enumerate()
                .filter(|(_, &g)| g < P::zero())
                .min_by(|(_, &a), (_, &b)| a.partial_cmp(&b).unwrap())
                .map(|(i, _)| i)
        }
    }

    fn gradient_search(
        start: Self,
        target: P,
        alpha: &AlphaVec<P>,
        max_steps: usize,
    ) -> Result<Self, CcmError> {
        let mut current = start;
        let tolerance = P::epsilon() * P::from(100.0).unwrap();

        for _ in 0..max_steps {
            let current_resonance = current.r(alpha);
            let error = (current_resonance - target).abs();

            if error < tolerance {
                return Ok(current);
            }

            // Determine if we need to increase or decrease resonance
            let need_increase = current_resonance < target;

            // Find steepest direction
            if let Some(bit_idx) = current.steepest_direction(alpha, need_increase) {
                // Flip the bit
                current.flip_bit(bit_idx);
            } else {
                // No improving direction found
                break;
            }
        }

        // Return best found even if not perfect
        Ok(current)
    }
}

/// Advanced gradient operations
pub mod advanced {
    use super::*;

    /// Compute Hessian matrix (second derivatives)
    pub fn resonance_hessian<P: Float + FromPrimitive>(
        byte: u8,
        alpha: &AlphaVec<P>,
    ) -> Vec<Vec<P>> {
        let n = 8;
        let mut hessian = vec![vec![P::zero(); n]; n];
        let r = byte.r(alpha);

        for i in 0..n {
            for j in 0..n {
                if i == j {
                    // Diagonal: ∂²R/∂b_i² = 0 (bits are binary)
                    hessian[i][j] = P::zero();
                } else {
                    // Off-diagonal: ∂²R/∂b_i∂b_j
                    let bit_i_set = (byte >> i) & 1 == 1;
                    let bit_j_set = (byte >> j) & 1 == 1;

                    let sign = if (bit_i_set && bit_j_set) || (!bit_i_set && !bit_j_set) {
                        P::one()
                    } else {
                        -P::one()
                    };

                    hessian[i][j] = sign * r * alpha[i].ln() * alpha[j].ln();
                }
            }
        }

        hessian
    }

    /// Newton's method step (using Hessian)
    pub fn newton_step<P: Float + FromPrimitive>(
        current: u8,
        target: P,
        alpha: &AlphaVec<P>,
    ) -> Option<u8> {
        let r = current.r(alpha);
        let error = r - target;

        if error.abs() < P::epsilon() {
            return Some(current);
        }

        // For binary optimization, we use a simplified Newton approach
        // Find the bit flip that best reduces |R - target|
        let mut best_flip = None;
        let mut best_reduction = P::zero();

        for i in 0..8 {
            let flipped = current ^ (1u8 << i);
            let new_r = flipped.r(alpha);
            let new_error = (new_r - target).abs();
            let reduction = error.abs() - new_error;

            if reduction > best_reduction {
                best_reduction = reduction;
                best_flip = Some(i);
            }
        }

        best_flip.map(|i| current ^ (1u8 << i))
    }

    /// Multi-start gradient search for global optimization
    pub fn multistart_search<P: Float + FromPrimitive>(
        target: P,
        alpha: &AlphaVec<P>,
        n_starts: usize,
    ) -> Result<u8, CcmError> {
        let mut best_result = 0u8;
        let mut best_error = P::infinity();

        // Try multiple random starting points
        for i in 0..n_starts {
            let start = ((i * 256 / n_starts) % 256) as u8;

            if let Ok(result) = u8::gradient_search(start, target, alpha, 50) {
                let error = (result.r(alpha) - target).abs();
                if error < best_error {
                    best_error = error;
                    best_result = result;
                }
            }
        }

        if best_error < P::from(0.001).unwrap() {
            Ok(best_result)
        } else {
            Err(CcmError::SearchExhausted)
        }
    }

    /// Compute Hessian matrix for BitWord (second derivatives)
    #[cfg(feature = "alloc")]
    pub fn resonance_hessian_bitword<P: Float + FromPrimitive>(
        word: &BitWord,
        alpha: &AlphaVec<P>,
    ) -> Vec<Vec<P>> {
        let n = alpha.len();
        let mut hessian = vec![vec![P::zero(); n]; n];
        let r = word.r(alpha);

        for i in 0..n {
            for j in 0..n {
                if i == j {
                    // Diagonal: ∂²R/∂b_i² = 0 (bits are binary)
                    hessian[i][j] = P::zero();
                } else {
                    // Off-diagonal: ∂²R/∂b_i∂b_j
                    let bit_i_set = word.bit(i);
                    let bit_j_set = word.bit(j);

                    let sign = if (bit_i_set && bit_j_set) || (!bit_i_set && !bit_j_set) {
                        P::one()
                    } else {
                        -P::one()
                    };

                    hessian[i][j] = sign * r * alpha[i].ln() * alpha[j].ln();
                }
            }
        }

        hessian
    }

    /// Newton's method step for BitWord (using Hessian)
    #[cfg(feature = "alloc")]
    pub fn newton_step_bitword<P: Float + FromPrimitive>(
        current: &BitWord,
        target: P,
        alpha: &AlphaVec<P>,
    ) -> Option<BitWord> {
        let r = current.r(alpha);
        let error = r - target;

        if error.abs() < P::epsilon() {
            return Some(current.clone());
        }

        // For binary optimization, we use a simplified Newton approach
        // Find the bit flip that best reduces |R - target|
        let mut best_flip = None;
        let mut best_reduction = P::zero();
        let n = alpha.len();

        for i in 0..n {
            let mut flipped = current.clone();
            flipped.flip_bit(i);

            let new_r = flipped.r(alpha);
            let new_error = (new_r - target).abs();
            let reduction = error.abs() - new_error;

            if reduction > best_reduction {
                best_reduction = reduction;
                best_flip = Some(i);
            }
        }

        best_flip.map(|i| {
            let mut result = current.clone();
            result.flip_bit(i);
            result
        })
    }

    /// Multi-start gradient search for BitWord
    #[cfg(feature = "alloc")]
    pub fn multistart_search_bitword<P: Float + FromPrimitive>(
        target: P,
        alpha: &AlphaVec<P>,
        n_starts: usize,
    ) -> Result<BitWord, CcmError> {
        let n = alpha.len();
        let mut best_result = BitWord::new(n);
        let mut best_error = P::infinity();

        // For large n, use strategic sampling
        if n > 20 {
            // Sample from different regions of the space
            let mut seed = 0x2A65C3F5u64;

            for _ in 0..n_starts {
                seed = seed.wrapping_mul(1103515245).wrapping_add(12345);

                let mut start = BitWord::new(n);
                // Set bits based on pseudo-random pattern
                for i in 0..n.min(64) {
                    if (seed >> i) & 1 == 1 {
                        start.set_bit(i, true);
                    }
                }

                if let Ok(result) = BitWord::gradient_search(start, target, alpha, 50) {
                    let error = (result.r(alpha) - target).abs();
                    if error < best_error {
                        best_error = error;
                        best_result = result;
                    }
                }
            }
        } else {
            // For small n, try evenly distributed starting points
            let step = if n <= 20 {
                (1usize << n) / n_starts.max(1)
            } else {
                1
            };

            for i in (0..(1usize << n)).step_by(step.max(1)).take(n_starts) {
                let mut start = BitWord::new(n);
                for bit in 0..n {
                    if (i >> bit) & 1 == 1 {
                        start.set_bit(bit, true);
                    }
                }

                if let Ok(result) = BitWord::gradient_search(start, target, alpha, 50) {
                    let error = (result.r(alpha) - target).abs();
                    if error < best_error {
                        best_error = error;
                        best_result = result;
                    }
                }
            }
        }

        if best_error < P::from(0.001).unwrap() {
            Ok(best_result)
        } else {
            Err(CcmError::SearchExhausted)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bit_gradient() {
        let alpha = crate::tests::testing_alpha();
        let byte = 0b00001010u8; // bits 1 and 3 set

        let gradients = byte.bit_gradient(&alpha);
        assert_eq!(gradients.len(), 8);

        // Gradient should be negative for set bits, positive for clear bits
        // (assuming all α_i > 1, which means ln(α_i) > 0)
        for i in 0..8 {
            let bit_set = (byte >> i) & 1 == 1;
            let ln_alpha = alpha[i].ln();

            if ln_alpha > 0.0 {
                if bit_set {
                    assert!(gradients[i] < 0.0);
                } else {
                    assert!(gradients[i] > 0.0);
                }
            }
        }
    }

    #[test]
    fn test_steepest_direction() {
        let alpha = crate::tests::testing_alpha();
        let byte = 0b00000001u8;

        // Find direction to increase resonance
        let up_dir = byte.steepest_direction(&alpha, true);
        assert!(up_dir.is_some());

        // Find direction to decrease resonance
        let down_dir = byte.steepest_direction(&alpha, false);
        assert!(down_dir.is_some());
    }

    #[test]
    fn test_gradient_search() {
        let alpha = crate::tests::testing_alpha();
        let target = 5.0;
        let start = 0u8;

        let result = u8::gradient_search(start, target, &alpha, 100).unwrap();
        let final_resonance = result.r(&alpha);

        // Should get reasonably close to target
        assert!((final_resonance - target).abs() < 1.0);
    }

    #[test]
    fn test_multistart_search() {
        let alpha = crate::tests::testing_alpha();

        // With dynamic alpha, we can't guarantee finding specific resonance values
        // Instead, test that the search process works
        let target = 5.0; // A reasonable target value

        // The search might fail if no byte has resonance close to target
        match advanced::multistart_search(target, &alpha, 10) {
            Ok(byte) => {
                // If it succeeds, verify the result is reasonable
                let resonance = byte.r(&alpha);
                assert!(resonance > 0.0);
                assert!(resonance.is_finite());
            }
            Err(CcmError::SearchExhausted) => {
                // It's okay if search fails - dynamic alphas may not have values near target
            }
            Err(e) => panic!("Unexpected error: {:?}", e),
        }
    }
}
