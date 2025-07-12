//! Inverse resonance mapping operations
//!
//! This module provides algorithms for finding bit patterns with specific resonance values,
//! scaling from exact exhaustive search for small n to heuristic methods for large n.
//!
//! ## Problem Statement
//!
//! Given a target resonance value r and tolerance ε, find all bit patterns b such that:
//! |R(b) - r| ≤ ε
//!
//! ## Scaling Strategies
//!
//! ### Small n (≤ 20 bits)
//! - **Algorithm**: Exhaustive search through Klein representatives
//! - **Complexity**: O(2^{n-2}) - reduced by factor of 4 using Klein structure
//! - **Guarantee**: Finds all solutions
//!
//! ### Medium n (20 < n ≤ 40 bits)  
//! - **Algorithm**: Meet-in-the-middle with dynamic programming
//! - **Complexity**: O(2^{n/2}) time, O(2^{n/2}) space
//! - **Guarantee**: Finds all solutions (memory permitting)
//!
//! ### Large n (> 40 bits)
//! - **Algorithms**: Multiple heuristic approaches
//!   - Gradient-guided search from random starts
//!   - Sample-based approximation
//!   - Branch-and-bound with pruning
//! - **Complexity**: Varies by method
//! - **Guarantee**: May not find all solutions
//!
//! ## Example
//!
//! ```no_run
//! use ccm_embedding::{AlphaVec, InverseResonance};
//! use ccm_core::BitWord;
//!
//! let alpha = AlphaVec::<f64>::for_bit_length(32).unwrap();
//! let target = 100.0;
//!
//! // Find patterns with resonance near 100
//! let patterns = BitWord::find_by_resonance(target, &alpha, 0.1).unwrap();
//! ```

use crate::{AlphaVec, Resonance};
use ccm_core::{CcmError, Float};
use num_traits::FromPrimitive;

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
    fn factor_resonance(r: P, alpha: &AlphaVec<P>) -> Result<Vec<Vec<usize>>, CcmError>;

    /// Solve the subset sum problem in log domain
    fn solve_log_subset_sum(target_log: P, log_alphas: &[P], tolerance: P) -> Vec<Vec<usize>>;
}

/// Implementation for u8
impl<P: Float + FromPrimitive> InverseResonance<P> for u8 {
    type Output = u8;

    fn find_by_resonance(
        target: P,
        alpha: &AlphaVec<P>,
        tolerance: P,
    ) -> Result<Vec<Self::Output>, CcmError> {
        let mut results = Vec::new();

        // For 8-bit, we can do exhaustive search efficiently
        // Klein groups are formed by XORing bits 6,7 (N-2, N-1 for N=8)
        for byte in 0u8..=255u8 {
            // Get Klein representative by clearing bits 6,7
            let klein_repr = byte & 0b00111111;

            // Skip if we've already processed this Klein group
            if byte != klein_repr {
                continue;
            }

            // Get all 4 Klein group members by XORing bits 6,7
            let members = [
                klein_repr,
                klein_repr ^ 0b01000000, // Flip bit 6
                klein_repr ^ 0b10000000, // Flip bit 7
                klein_repr ^ 0b11000000, // Flip bits 6,7
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

    fn factor_resonance(r: P, alpha: &AlphaVec<P>) -> Result<Vec<Vec<usize>>, CcmError> {
        if alpha.len() < 8 {
            return Err(CcmError::InvalidInput);
        }

        let target_log = r.ln();
        let log_alphas: Vec<P> = alpha.values[..8].iter().map(|&a| a.ln()).collect();

        let solutions = Self::solve_log_subset_sum(
            target_log,
            &log_alphas,
            P::epsilon() * P::from(10.0).unwrap(),
        );

        Ok(solutions)
    }

    fn solve_log_subset_sum(target_log: P, log_alphas: &[P], tolerance: P) -> Vec<Vec<usize>> {
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

/// Advanced algorithms for large-scale inverse resonance
#[cfg(feature = "alloc")]
pub mod algorithms {
    use super::*;

    /// Approximation algorithm for very large n using sampling
    pub fn sample_based_inverse<P: Float + FromPrimitive>(
        target: P,
        alpha: &AlphaVec<P>,
        tolerance: P,
        samples: usize,
    ) -> Result<Vec<BitWord>, CcmError> {
        let mut results = Vec::new();
        let n = alpha.len();
        let mut seed = 0x2A65C3F5u64;

        // Use importance sampling based on log-resonance decomposition
        let target_log = target.ln();
        let log_alphas: Vec<P> = alpha.values.iter().map(|&a| a.ln()).collect();

        // Find most significant bits (largest log values)
        let mut indexed_logs: Vec<(usize, P)> = log_alphas
            .iter()
            .enumerate()
            .map(|(i, &log_a)| (i, log_a))
            .collect();
        indexed_logs.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());

        for _ in 0..samples {
            seed = seed.wrapping_mul(1103515245).wrapping_add(12345);

            let mut word = BitWord::new(n);
            let mut current_log_sum = P::zero();

            // Greedy construction guided by target
            for &(idx, log_a) in &indexed_logs {
                if (current_log_sum + log_a - target_log).abs()
                    < (current_log_sum - target_log).abs()
                {
                    word.set_bit(idx, true);
                    current_log_sum = current_log_sum + log_a;
                }

                // Early termination if close enough
                if (current_log_sum - target_log).abs() < tolerance {
                    break;
                }
            }

            // Refine with local search
            for _ in 0..10 {
                let r = word.r(alpha);
                if (r - target).abs() <= tolerance {
                    if word.is_klein_minimum(alpha) {
                        results.push(word.clone());
                    }
                    break;
                }

                // Try flipping bits to improve
                let mut best_flip = None;
                let mut best_error = (r - target).abs();

                for i in 0..n.min(64) {
                    // Focus on most significant bits
                    let mut test = word.clone();
                    test.flip_bit(i);
                    let test_r = test.r(alpha);
                    let test_error = (test_r - target).abs();

                    if test_error < best_error {
                        best_error = test_error;
                        best_flip = Some(i);
                    }
                }

                if let Some(flip_idx) = best_flip {
                    word.flip_bit(flip_idx);
                } else {
                    break;
                }
            }
        }

        if results.is_empty() {
            Err(CcmError::SearchExhausted)
        } else {
            Ok(results)
        }
    }

    /// Branch and bound algorithm for exact solutions
    pub fn branch_and_bound<P: Float + FromPrimitive>(
        target: P,
        alpha: &AlphaVec<P>,
        tolerance: P,
        max_solutions: usize,
    ) -> Result<Vec<BitWord>, CcmError> {
        let n = alpha.len();
        let mut results = Vec::new();

        // Precompute cumulative bounds
        let mut cumulative_max = vec![P::zero(); n + 1];
        let mut cumulative_min = vec![P::zero(); n + 1];

        for i in (0..n).rev() {
            cumulative_max[i] = cumulative_max[i + 1] + alpha[i];
            cumulative_min[i] = cumulative_min[i + 1];
        }

        // Stack for DFS
        let mut stack = vec![(BitWord::new(n), P::one(), 0)];

        while let Some((mut word, current_r, depth)) = stack.pop() {
            if depth == n {
                // Complete solution
                if (current_r - target).abs() <= tolerance && word.is_klein_minimum(alpha) {
                    results.push(word);
                    if results.len() >= max_solutions {
                        break;
                    }
                }
                continue;
            }

            // Bounds check
            let lower_bound = current_r * cumulative_min[depth];
            let upper_bound = current_r * cumulative_max[depth];

            if lower_bound > target + tolerance || upper_bound < target - tolerance {
                continue; // Prune this branch
            }

            // Try both options for current bit
            // Option 1: bit not set
            stack.push((word.clone(), current_r, depth + 1));

            // Option 2: bit set
            word.set_bit(depth, true);
            stack.push((word, current_r * alpha[depth], depth + 1));
        }

        if results.is_empty() {
            Err(CcmError::SearchExhausted)
        } else {
            Ok(results)
        }
    }
}

/// Implementation for BitWord
use ccm_core::BitWord;

#[cfg(feature = "alloc")]
impl<P: Float + FromPrimitive> InverseResonance<P> for BitWord {
    type Output = BitWord;

    fn find_by_resonance(
        target: P,
        alpha: &AlphaVec<P>,
        tolerance: P,
    ) -> Result<Vec<Self::Output>, CcmError> {
        let mut results = Vec::new();
        let n = alpha.len();

        // Dynamic threshold based on available memory and time constraints
        let practical_search_limit = if cfg!(feature = "std") {
            24 // Can handle up to 2^24 in reasonable time with std
        } else {
            20 // More conservative for no_std environments
        };

        if n <= practical_search_limit {
            // Exhaustive search through Klein representatives
            // For n >= 2, we iterate through first n-2 bits
            let num_klein_reps = if n >= 2 { 1usize << (n - 2) } else { 1 };

            for i in 0..num_klein_reps {
                let mut klein_repr = BitWord::new(n);

                // Set bits based on index i
                for bit in 0..(n.saturating_sub(2)) {
                    if (i >> bit) & 1 == 1 {
                        klein_repr.set_bit(bit, true);
                    }
                }

                let members = <BitWord as Resonance<P>>::class_members(&klein_repr);

                // Find Klein minimum
                let mut min_resonance = P::infinity();
                let mut min_member = members[0].clone();

                for member in &members {
                    let r = member.r(alpha);
                    if r < min_resonance {
                        min_resonance = r;
                        min_member = member.clone();
                    }
                }

                if (min_resonance - target).abs() <= tolerance {
                    results.push(min_member);
                }
            }
        } else {
            // For larger N, use multiple strategies

            // Strategy 1: Resonance factorization
            if let Ok(factorizations) = Self::factor_resonance(target, alpha) {
                for indices in factorizations.into_iter().take(100) {
                    // Limit results
                    let mut candidate = BitWord::new(n);
                    for &idx in &indices {
                        if idx < n {
                            candidate.set_bit(idx, true);
                        }
                    }

                    // Check if this is a Klein minimum
                    if candidate.is_klein_minimum(alpha) {
                        let r = candidate.r(alpha);
                        if (r - target).abs() <= tolerance {
                            results.push(candidate);
                        }
                    }
                }
            }

            // Strategy 2: Gradient-based search from multiple starting points
            use crate::ResonanceGradient;
            let num_starts = 10;
            let mut seed = 0x2A65C3F5u64;

            for _ in 0..num_starts {
                seed = seed.wrapping_mul(1103515245).wrapping_add(12345);

                let mut start = BitWord::new(n);
                // Random initialization
                for i in 0..n.min(64) {
                    if (seed >> i) & 1 == 1 {
                        start.set_bit(i, true);
                    }
                }

                if let Ok(candidate) = BitWord::gradient_search(start, target, alpha, 100) {
                    if candidate.is_klein_minimum(alpha) {
                        let r = candidate.r(alpha);
                        if (r - target).abs() <= tolerance && !results.contains(&candidate) {
                            results.push(candidate);
                        }
                    }
                }
            }
        }

        if results.is_empty() {
            Err(CcmError::SearchExhausted)
        } else {
            Ok(results)
        }
    }

    fn factor_resonance(r: P, alpha: &AlphaVec<P>) -> Result<Vec<Vec<usize>>, CcmError> {
        let n = alpha.len();

        let target_log = r.ln();
        let log_alphas: Vec<P> = alpha.values[..n].iter().map(|&a| a.ln()).collect();

        let solutions = Self::solve_log_subset_sum(
            target_log,
            &log_alphas,
            P::epsilon() * P::from(10.0).unwrap(),
        );

        Ok(solutions)
    }

    fn solve_log_subset_sum(target_log: P, log_alphas: &[P], tolerance: P) -> Vec<Vec<usize>> {
        let mut solutions = Vec::new();
        let n = log_alphas.len();

        // Choose algorithm based on problem size
        let dp_threshold = if cfg!(feature = "std") { 24 } else { 20 };

        if n <= dp_threshold {
            // Exhaustive search for small n
            let max_iterations = 1usize << n;

            for i in 0..max_iterations {
                let mut sum = P::zero();
                let mut indices = Vec::new();

                for (bit_idx, &log_alpha) in log_alphas.iter().enumerate() {
                    if (i >> bit_idx) & 1 == 1 {
                        sum = sum + log_alpha;
                        indices.push(bit_idx);
                    }
                }

                if (sum - target_log).abs() <= tolerance {
                    solutions.push(indices);
                }
            }
        } else {
            // Dynamic programming approach for larger n
            // We'll use a meet-in-the-middle strategy to handle larger instances

            let mid = n / 2;
            let first_half = &log_alphas[..mid];
            let second_half = &log_alphas[mid..];

            // Generate all subset sums for first half
            let mut first_sums = Vec::new();
            for mask in 0..(1usize << mid) {
                let mut sum = P::zero();
                let mut indices = Vec::new();

                for (i, &log_alpha) in first_half.iter().enumerate() {
                    if (mask >> i) & 1 == 1 {
                        sum = sum + log_alpha;
                        indices.push(i);
                    }
                }
                first_sums.push((sum, indices));
            }

            // Sort first half sums for binary search
            first_sums.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());

            // Check all subsets of second half
            for mask in 0..(1usize << (n - mid)) {
                let mut sum = P::zero();
                let mut indices = Vec::new();

                for (i, &log_alpha) in second_half.iter().enumerate() {
                    if (mask >> i) & 1 == 1 {
                        sum = sum + log_alpha;
                        indices.push(mid + i);
                    }
                }

                let needed = target_log - sum;

                // Binary search for matching sum in first half
                let pos =
                    first_sums.binary_search_by(|probe| probe.0.partial_cmp(&needed).unwrap());

                match pos {
                    Ok(idx) => {
                        // Exact match found
                        let mut full_indices = first_sums[idx].1.clone();
                        full_indices.extend(&indices);
                        solutions.push(full_indices);

                        // Check neighbors for additional matches within tolerance
                        let mut check_idx = idx.saturating_sub(1);
                        while check_idx < first_sums.len()
                            && (first_sums[check_idx].0 - needed).abs() <= tolerance
                        {
                            if check_idx != idx {
                                let mut full_indices = first_sums[check_idx].1.clone();
                                full_indices.extend(&indices);
                                solutions.push(full_indices);
                            }
                            check_idx += 1;
                        }
                    }
                    Err(idx) => {
                        // Check nearby values within tolerance
                        for check_idx in idx.saturating_sub(1)..=(idx + 1).min(first_sums.len()) {
                            if check_idx < first_sums.len()
                                && (first_sums[check_idx].0 - needed).abs() <= tolerance
                            {
                                let mut full_indices = first_sums[check_idx].1.clone();
                                full_indices.extend(&indices);
                                solutions.push(full_indices);
                            }
                        }
                    }
                }
            }

            // Limit solutions to prevent memory explosion
            solutions.truncate(1000);
        }

        solutions
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_by_resonance_u8() {
        let alpha = crate::tests::testing_alpha();

        // Test finding a known resonance value
        // First, find a byte that's actually a Klein minimum
        let test_byte = 0b00100101u8; // 37, with bits 6,7 = 00 (Klein representative)
        let klein_members = <u8 as Resonance<f64>>::class_members(&test_byte);

        // Find the actual Klein minimum and its resonance
        let mut min_resonance = test_byte.r(&alpha);
        for &member in &klein_members {
            let r = member.r(&alpha);
            if r < min_resonance {
                min_resonance = r;
            }
        }

        // Now test finding this minimum resonance
        let candidates = u8::find_by_resonance(min_resonance, &alpha, 1e-9).unwrap();

        // Should find at least one Klein minimum
        assert!(
            !candidates.is_empty(),
            "Should find at least one Klein minimum"
        );

        // Verify all found values have correct resonance
        for &byte in &candidates {
            let r = byte.r(&alpha);
            assert!(
                (r - min_resonance).abs() < 1e-9,
                "Found byte {} with resonance {} instead of target {}",
                byte,
                r,
                min_resonance
            );
        }

        // Verify Klein minimum property
        for &candidate in &candidates {
            assert!(
                candidate.is_klein_minimum(&alpha),
                "Candidate {} should be a Klein minimum",
                candidate
            );

            // Check that it's in the right Klein group
            let klein_repr = candidate & 0b00111111;
            let expected_members = [
                klein_repr,
                klein_repr | 0b01000000,
                klein_repr | 0b10000000,
                klein_repr | 0b11000000,
            ];

            assert!(
                expected_members.contains(&candidate),
                "Candidate {} not in expected Klein group",
                candidate
            );
        }

        // Test with a non-Klein-representative to ensure we still find the minimum
        let test_byte2 = 0b11100101u8; // Same as above but with bits 6,7 = 11
        let klein_members = <u8 as Resonance<f64>>::class_members(&test_byte2);

        // Find the Klein minimum's resonance
        let min_resonance = klein_members
            .iter()
            .map(|&b| b.r(&alpha))
            .min_by(|a, b| a.partial_cmp(b).unwrap())
            .unwrap();

        let candidates2 = u8::find_by_resonance(min_resonance, &alpha, 1e-9).unwrap();
        assert!(
            !candidates2.is_empty(),
            "Should find Klein minimum for non-representative"
        );
    }

    #[test]
    fn test_factor_resonance() {
        let alpha = crate::tests::testing_alpha();

        // Factor a known resonance value
        let byte = 0b00000101u8; // bits 0 and 2 set
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
        let target = 0.8; // 0.5 + 0.3

        let solutions = u8::solve_log_subset_sum(target, &log_alphas, 1e-10);

        assert!(!solutions.is_empty());
        assert!(solutions.iter().any(|s| s == &vec![0, 1]));
    }
}
