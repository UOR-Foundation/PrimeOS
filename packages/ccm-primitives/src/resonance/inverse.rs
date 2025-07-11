//! Inverse resonance mapping operations

use crate::{AlphaVec, CcmError, Float, Resonance};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Trait for inverse resonance operations
pub trait InverseResonance<P: Float> {
    type Output;

    /// Find all values with given resonance that are Klein minima
    fn find_by_resonance(
        target: P,
        alpha: &AlphaVec<P>,
        tolerance: P,
    ) -> Result<Vec<Self::Output>, CcmError>;

    /// Decompose resonance into constituent alpha factors
    fn factor_resonance(
        r: P,
        alpha: &AlphaVec<P>,
    ) -> Result<Vec<Vec<usize>>, CcmError>;

    /// Solve the subset sum problem in log domain
    fn solve_log_subset_sum(
        target_log: P,
        log_alphas: &[P],
        tolerance: P,
    ) -> Vec<Vec<usize>>;
}

/// Implementation for u8
impl<P: Float> InverseResonance<P> for u8 {
    type Output = u8;

    fn find_by_resonance(
        target: P,
        alpha: &AlphaVec<P>,
        tolerance: P,
    ) -> Result<Vec<Self::Output>, CcmError> {
        let mut results = Vec::new();
        
        // For 8-bit, we can do exhaustive search efficiently
        for klein_repr in 0u8..64u8 {  // Only need first 6 bits (Klein representatives)
            // Get all 4 Klein group members
            let members = [
                klein_repr,
                klein_repr ^ 0b01000000,
                klein_repr ^ 0b10000000,
                klein_repr ^ 0b11000000,
            ];
            
            // Find the one with minimum resonance
            let mut min_resonance = P::infinity();
            let mut min_member = members[0];
            
            for &member in &members {
                let r = member.r(alpha);
                if r < min_resonance {
                    min_resonance = r;
                    min_member = member;
                }
            }
            
            // Check if this Klein minimum matches our target
            if (min_resonance - target).abs() <= tolerance {
                results.push(min_member);
            }
        }
        
        if results.is_empty() {
            Err(CcmError::SearchExhausted)
        } else {
            Ok(results)
        }
    }

    fn factor_resonance(
        r: P,
        alpha: &AlphaVec<P>,
    ) -> Result<Vec<Vec<usize>>, CcmError> {
        if alpha.len() < 8 {
            return Err(CcmError::InvalidInput);
        }
        
        let target_log = r.ln();
        let log_alphas: Vec<P> = alpha.values[..8]
            .iter()
            .map(|&a| a.ln())
            .collect();
        
        let solutions = Self::solve_log_subset_sum(
            target_log,
            &log_alphas,
            P::epsilon() * P::from(10.0).unwrap(),
        );
        
        Ok(solutions)
    }

    fn solve_log_subset_sum(
        target_log: P,
        log_alphas: &[P],
        tolerance: P,
    ) -> Vec<Vec<usize>> {
        let mut solutions = Vec::new();
        let n = log_alphas.len().min(8);
        
        // Exhaustive search for 8-bit case
        // Use u16 to avoid overflow when n = 8
        let max_mask = 1u16 << n;
        for mask in 0u16..max_mask {
            let mut sum = P::zero();
            let mut indices = Vec::new();
            
            for (i, &log_alpha) in log_alphas.iter().enumerate().take(n) {
                if ((mask >> i) & 1) == 1 {
                    sum = sum + log_alpha;
                    indices.push(i);
                }
            }
            
            if (sum - target_log).abs() <= tolerance {
                solutions.push(indices);
            }
        }
        
        solutions
    }
}

/// Implementation for BitWord
use crate::bitword::BitWord;

impl<P: Float, const N: usize> InverseResonance<P> for BitWord<N> {
    type Output = BitWord<N>;

    fn find_by_resonance(
        target: P,
        alpha: &AlphaVec<P>,
        tolerance: P,
    ) -> Result<Vec<Self::Output>, CcmError> {
        let mut results = Vec::new();
        
        if N <= 16 {
            // Exhaustive search for small N
            let klein_mask = if N >= 2 { (1u64 << (N - 2)) - 1 } else { 1 };
            
            for repr in 0..=klein_mask {
                let klein_repr = BitWord::<N>::from(repr);
                let members = <BitWord<N> as Resonance<P>>::class_members(&klein_repr);
                
                // Find Klein minimum
                let mut min_resonance = P::infinity();
                let mut min_member = members[0];
                
                for &member in &members {
                    let r = member.r(alpha);
                    if r < min_resonance {
                        min_resonance = r;
                        min_member = member;
                    }
                }
                
                if (min_resonance - target).abs() <= tolerance {
                    results.push(min_member);
                }
            }
        } else {
            // For larger N, use heuristics or return error
            return Err(CcmError::UnsupportedPrecision);
        }
        
        if results.is_empty() {
            Err(CcmError::SearchExhausted)
        } else {
            Ok(results)
        }
    }

    fn factor_resonance(
        r: P,
        alpha: &AlphaVec<P>,
    ) -> Result<Vec<Vec<usize>>, CcmError> {
        if alpha.len() < N {
            return Err(CcmError::InvalidInput);
        }
        
        let target_log = r.ln();
        let log_alphas: Vec<P> = alpha.values[..N]
            .iter()
            .map(|&a| a.ln())
            .collect();
        
        let solutions = Self::solve_log_subset_sum(
            target_log,
            &log_alphas,
            P::epsilon() * P::from(10.0).unwrap(),
        );
        
        Ok(solutions)
    }

    fn solve_log_subset_sum(
        target_log: P,
        log_alphas: &[P],
        tolerance: P,
    ) -> Vec<Vec<usize>> {
        let mut solutions = Vec::new();
        
        if log_alphas.len() <= 20 {
            // Exhaustive search for reasonable sizes
            let n = log_alphas.len();
            let max_mask = 1u64 << n;
            
            for mask in 0..max_mask {
                let mut sum = P::zero();
                let mut indices = Vec::new();
                
                for (i, &log_alpha) in log_alphas.iter().enumerate().take(n) {
                    if (mask >> i) & 1 == 1 {
                        sum = sum + log_alpha;
                        indices.push(i);
                    }
                }
                
                if (sum - target_log).abs() <= tolerance {
                    solutions.push(indices);
                }
            }
        }
        // For larger N, could implement dynamic programming or approximation algorithms
        
        solutions
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_find_by_resonance_u8() {
        let alpha = crate::tests::testing_alpha();
        
        // Find bytes with resonance close to 1.0
        let candidates = u8::find_by_resonance(1.0, &alpha, 1e-10).unwrap();
        
        // Should find unity positions (0, 1, 48, 49 for standard alpha)
        assert!(!candidates.is_empty());
        
        // Verify all found values have correct resonance
        for &byte in &candidates {
            let r = byte.r(&alpha);
            assert!((r - 1.0).abs() < 1e-10);
        }
    }
    
    #[test]
    fn test_factor_resonance() {
        let alpha = crate::tests::testing_alpha();
        
        // Factor a known resonance value
        let byte = 0b00000101u8;  // bits 0 and 2 set
        let r = byte.r(&alpha);
        
        let factors = u8::factor_resonance(r, &alpha).unwrap();
        
        // Should find at least one factorization
        assert!(!factors.is_empty());
        
        // Check that [0, 2] is among the solutions
        let expected = vec![0, 2];
        assert!(factors.iter().any(|f| f == &expected));
    }
    
    #[test]
    fn test_subset_sum() {
        let log_alphas = vec![0.5, 0.3, 0.2, 0.1];
        let target = 0.8;  // 0.5 + 0.3
        
        let solutions = u8::solve_log_subset_sum(target, &log_alphas, 1e-10);
        
        assert!(!solutions.is_empty());
        assert!(solutions.iter().any(|s| s == &vec![0, 1]));
    }
}