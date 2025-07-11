//! Generic b_min search backend

use crate::{AlphaVec, BitWord, CcmError, Float, Resonance};

#[cfg(feature = "alloc")]
use alloc::vec;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Search for the bit pattern with minimum resonance
pub fn search_b_min<P: Float, const N: usize>(
    target: &BitWord<N>,
    alpha: &AlphaVec<P>,
    search_space: Option<Vec<BitWord<N>>>,
) -> Result<BitWord<N>, CcmError> {
    let candidates = search_space.unwrap_or_else(|| {
        // Default: search Klein group transformations
        // For N-bit words, Klein group is formed by XORing bits N-2 and N-1
        let klein_masks = if N >= 2 {
            let bit_n_minus_2 = 1u64 << (N - 2);
            let bit_n_minus_1 = 1u64 << (N - 1);
            vec![
                0,                             // 00
                bit_n_minus_2,                 // 01
                bit_n_minus_1,                 // 10
                bit_n_minus_2 | bit_n_minus_1, // 11
            ]
        } else {
            vec![0]
        };
        let target_value = target.to_usize() as u64;

        klein_masks
            .into_iter()
            .map(|mask| BitWord::from(target_value ^ mask))
            .collect()
    });

    if candidates.is_empty() {
        return Err(CcmError::SearchExhausted);
    }

    let mut min_resonance = P::infinity();
    let mut best_candidate = candidates[0];

    for candidate in candidates {
        let resonance = candidate.r(alpha);
        if resonance < min_resonance {
            min_resonance = resonance;
            best_candidate = candidate;
        } else if resonance == min_resonance {
            // Tie-break: choose lexicographically smallest
            if candidate.to_usize() < best_candidate.to_usize() {
                best_candidate = candidate;
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
    pub fn binary_search<P: Float, const N: usize>(
        target_resonance: P,
        alpha: &AlphaVec<P>,
        tolerance: P,
    ) -> Result<BitWord<N>, CcmError> {
        // This is a placeholder for more sophisticated search
        // In practice, would implement efficient binary search
        // over the resonance-ordered space

        let max_iterations = 1 << N;

        for i in 0..max_iterations.min(1_000_000) {
            let candidate = BitWord::<N>::from(i as u64);

            let resonance = candidate.r(alpha);
            let diff = (resonance - target_resonance).abs();
            if diff <= tolerance {
                return Ok(candidate);
            }
        }

        Err(CcmError::SearchExhausted)
    }

    /// Gradient-based search using resonance derivatives
    pub fn gradient_search<P: Float, const N: usize>(
        start: BitWord<N>,
        alpha: &AlphaVec<P>,
        target: P,
    ) -> Result<BitWord<N>, CcmError> {
        let mut current = start;
        let mut current_resonance = current.r(alpha);

        // Simple hill-climbing approach
        for _ in 0..100 {
            if (current_resonance - target).abs() < P::epsilon() {
                return Ok(current);
            }

            // Try flipping each bit and see which improves
            let mut best_improvement = P::infinity();
            let mut best_flip = None;

            for bit_idx in 0..N {
                let mut candidate = current;
                candidate.set_bit(bit_idx, !candidate.bit(bit_idx));

                let new_resonance = candidate.r(alpha);
                let improvement = (new_resonance - target).abs();
                if improvement < best_improvement {
                    best_improvement = improvement;
                    best_flip = Some(bit_idx);
                }
            }

            match best_flip {
                Some(bit_idx) => {
                    current.set_bit(bit_idx, !current.bit(bit_idx));
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
        let alpha = AlphaVec::try_from(vec![
            std::f64::consts::E,        // e
            1.8392867552141612,         // Tribonacci
            1.6180339887498950,         // Golden ratio
            std::f64::consts::PI,       // π
            3.0_f64.sqrt(),             // √3
            2.0,                        // 2
            std::f64::consts::PI / 2.0, // π/2
            2.0 / std::f64::consts::PI, // 2/π (unity)
        ])
        .unwrap();

        let target = BitWord::<8>::from(0b10110010u8);
        let result = search_b_min(&target, &alpha, None).unwrap();

        // Should find one of the Klein group transformations
        // For 8-bit, Klein group uses bits 6 and 7
        let klein_values = [
            target.to_usize(),
            target.to_usize() ^ 0b01000000, // bit 6
            target.to_usize() ^ 0b10000000, // bit 7
            target.to_usize() ^ 0b11000000, // bits 6 and 7
        ];

        assert!(klein_values.contains(&result.to_usize()));
    }
}
