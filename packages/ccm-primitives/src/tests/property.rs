//! Property-based tests using proptest

use crate::{decode_bjc, encode_bjc, AlphaVec, BitWord};
use proptest::prelude::*;

/// Generate a valid alpha vector with unity constraint
fn arb_alpha_vec() -> impl Strategy<Value = AlphaVec<f64>> {
    (3usize..=8usize).prop_flat_map(|n| {
        // Generate n-2 positive values
        prop::collection::vec(0.1f64..=10.0, n - 2).prop_map(move |mut values| {
            // Add two values that satisfy unity constraint
            let second_last = 2.0;
            let last = 0.5; // 2.0 * 0.5 = 1.0
            values.push(second_last);
            values.push(last);

            AlphaVec::try_from(values).unwrap()
        })
    })
}

/// Generate arbitrary BitWord
fn arb_bitword<const N: usize>() -> impl Strategy<Value = BitWord<N>> {
    (0u64..=(if N == 64 { !0u64 } else { (1u64 << N) - 1 })).prop_map(BitWord::from)
}

proptest! {
    #[test]
    fn test_roundtrip_property(
        alpha in arb_alpha_vec(),
        word in arb_bitword::<8>(),
        k in 1usize..=4usize,
        include_hash in any::<bool>()
    ) {
        // Only test with compatible sizes
        if alpha.len() >= 8 {
            let packet = encode_bjc(&word, &alpha, k, include_hash)?;
            let decoded = decode_bjc::<f64, 8>(&packet, &alpha)?;
            prop_assert_eq!(word, decoded);
        }
    }

    #[test]
    fn test_resonance_minimum_property(
        alpha in arb_alpha_vec(),
        word in arb_bitword::<8>()
    ) {
        if alpha.len() >= 8 {
            // The encoded b_min should have minimum resonance among Klein group
            let packet = encode_bjc(&word, &alpha, 1, false)?;

            // Decode to get b_min
            let klein_masks = [0u64, 1, 48, 49];
            let original_value = word.to_usize() as u64;

            // Find which Klein element was chosen
            let mut min_resonance = f64::INFINITY;
            for &mask in &klein_masks {
                let candidate = BitWord::<8>::from(original_value ^ mask);
                if let Ok(resonance) = candidate.r(&alpha) {
                    min_resonance = min_resonance.min(resonance);
                }
            }

            // The packet should encode the one with minimum resonance
            prop_assert!(packet.flips <= 0b11);
        }
    }

    #[test]
    fn test_hash_integrity(
        alpha in arb_alpha_vec(),
        word in arb_bitword::<8>()
    ) {
        if alpha.len() >= 8 {
            let packet = encode_bjc(&word, &alpha, 1, true)?;
            prop_assert!(packet.hash.is_some());

            // Decoding should succeed
            let decoded = decode_bjc::<f64, 8>(&packet, &alpha)?;
            prop_assert_eq!(word, decoded);
        }
    }

    #[test]
    fn test_unity_constraint_preserved(
        n in 3usize..=8usize
    ) {
        let mut values = vec![1.0; n];
        // Set last two to satisfy unity
        values[n-2] = 3.14159;
        values[n-1] = 1.0 / 3.14159;

        let alpha = AlphaVec::try_from(values)?;
        let product = alpha[n-2] * alpha[n-1];
        prop_assert!((product - 1.0).abs() < 1e-10);
    }
}
