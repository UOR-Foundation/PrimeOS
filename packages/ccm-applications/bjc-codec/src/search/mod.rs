//! Generic b_min search backend

use ccm_core::{BitWord, CcmError, Float};
use ccm_embedding::{AlphaVec, Resonance};

#[cfg(feature = "alloc")]
use alloc::vec;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Search for the bit pattern with minimum resonance
pub fn search_b_min<P: Float>(
    target: &BitWord,
    alpha: &AlphaVec<P>,
    search_space: Option<Vec<BitWord>>,
) -> Result<BitWord, CcmError> {
    let candidates = search_space.unwrap_or_else(|| {
        // Default: search Klein group transformations
        // Klein group is formed by XORing bits (n-2, n-1)
        let n = target.len();

        if n >= 2 {
            let mut result = Vec::new();

            // Generate Klein group members by flipping bits (n-2, n-1)
            result.push(target.clone()); // 00

            let mut member1 = target.clone();
            member1.flip_bit(n - 2); // 01
            result.push(member1);

            let mut member2 = target.clone();
            member2.flip_bit(n - 1); // 10
            result.push(member2);

            let mut member3 = target.clone();
            member3.flip_bit(n - 2);
            member3.flip_bit(n - 1); // 11
            result.push(member3);

            result
        } else {
            vec![target.clone()]
        }
    });

    if candidates.is_empty() {
        return Err(CcmError::SearchExhausted);
    }

    let mut min_resonance = P::infinity();
    let mut best_candidate = candidates[0].clone();

    for candidate in candidates {
        let resonance = candidate.r(alpha);
        if resonance < min_resonance {
            min_resonance = resonance;
            best_candidate = candidate.clone();
        } else if resonance == min_resonance {
            // Tie-break: choose lexicographically smallest
            let n = candidate.len();
            if n <= 64 && candidate.to_usize() < best_candidate.to_usize() {
                best_candidate = candidate.clone();
            }
        }
    }

    if min_resonance.is_infinite() {
        Err(CcmError::SearchExhausted)
    } else {
        Ok(best_candidate)
    }
}

/// Advanced search strategies for larger search spaces
pub mod strategies {
    use super::*;

    /// Binary search in ordered resonance space
    pub fn binary_search<P: Float>(
        target_resonance: P,
        alpha: &AlphaVec<P>,
        tolerance: P,
        n: usize,
    ) -> Result<BitWord, CcmError> {
        // This is a placeholder for more sophisticated search
        // In practice, would implement efficient binary search
        // over the resonance-ordered space

        let max_iterations = if n >= 64 { 1_000_000 } else { 1usize << n };

        for i in 0..max_iterations.min(1_000_000) {
            let candidate = BitWord::from_u64(i as u64, n);

            let resonance = candidate.r(alpha);
            let diff = (resonance - target_resonance).abs();
            if diff <= tolerance {
                return Ok(candidate);
            }
        }

        Err(CcmError::SearchExhausted)
    }

    /// Gradient-based search using resonance derivatives
    pub fn gradient_search<P: Float>(
        start: BitWord,
        alpha: &AlphaVec<P>,
        target: P,
    ) -> Result<BitWord, CcmError> {
        let mut current = start;
        let n = current.len();
        let mut current_resonance = current.r(alpha);

        // Simple hill-climbing approach
        for _ in 0..100 {
            if (current_resonance - target).abs() < P::epsilon() {
                return Ok(current);
            }

            // Try flipping each bit and see which improves
            let mut best_improvement = P::infinity();
            let mut best_flip = None;

            for bit_idx in 0..n {
                let mut candidate = current.clone();
                candidate.flip_bit(bit_idx);

                let new_resonance = candidate.r(alpha);
                let improvement = (new_resonance - target).abs();
                if improvement < best_improvement {
                    best_improvement = improvement;
                    best_flip = Some(bit_idx);
                }
            }

            match best_flip {
                Some(bit_idx) => {
                    current.flip_bit(bit_idx);
                    current_resonance = current.r(alpha);
                }
                None => break,
            }
        }

        Ok(current)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_search_b_min() {
        // Use dynamic alpha which guarantees unity constraint
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        let target = BitWord::from_u8(0b10110010u8);
        let result = search_b_min(&target, &alpha, None).unwrap();

        // Should find one of the Klein group transformations
        // For N=8, Klein group uses bits 6 and 7 (N-2, N-1)
        let klein_values = [
            target.to_usize(),
            target.to_usize() ^ 0b01000000, // bit 6
            target.to_usize() ^ 0b10000000, // bit 7
            target.to_usize() ^ 0b11000000, // bits 6 and 7
        ];

        assert!(klein_values.contains(&result.to_usize()));
    }
}
