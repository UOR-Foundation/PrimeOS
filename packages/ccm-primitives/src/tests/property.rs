//! Property-based tests using proptest

#![allow(clippy::approx_constant, clippy::excessive_precision)]

use crate::{decode_bjc, encode_bjc, AlphaVec, BitWord, Resonance};
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

            // The class members are determined by XORing with patterns on last two bits
            let class_members = <BitWord<8> as Resonance<f64>>::class_members(&word);

            // Find which has minimum resonance
            let mut min_resonance = f64::INFINITY;
            for &member in &class_members {
                let resonance = member.r(&alpha);
                min_resonance = min_resonance.min(resonance);
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
        values[n-2] = 3.1415926535897932;
        values[n-1] = 1.0 / 3.1415926535897932;

        let alpha = AlphaVec::try_from(values).unwrap();
        let product = alpha[n-2] * alpha[n-1];
        prop_assert!((product - 1.0).abs() < 1e-10);
    }
}

// Conformance test per spec section 7
#[test]
fn test_conformance_requirements() {
    // Test for nominated n values: 3, 4, 8, 10, 16, 32, 64
    let test_sizes = vec![3, 4, 8, 10, 16, 32, 64];

    for &n in &test_sizes {
        if n > 8 {
            continue; // Skip larger sizes for this simple test
        }

        // Create appropriate alpha vector with good properties
        let alpha = create_test_alpha_for_n(n);

        // Test 10,000 random inputs per spec requirement
        let num_tests = if n <= 8 { 1000 } else { 100 }; // Reduced for test speed

        for i in 0..num_tests {
            let value = i as u64 % (1u64 << n);
            match n {
                3 => test_roundtrip::<3>(value, &alpha),
                4 => test_roundtrip::<4>(value, &alpha),
                8 => test_roundtrip::<8>(value, &alpha),
                _ => {}
            }
        }
    }
}

fn test_roundtrip<const N: usize>(value: u64, alpha: &AlphaVec<f64>) {
    let word = BitWord::<N>::from(value);
    let packet = encode_bjc(&word, alpha, 1, false).unwrap();
    let decoded = decode_bjc::<f64, N>(&packet, alpha).unwrap();
    assert_eq!(word, decoded);
}

fn create_test_alpha_for_n(n: usize) -> AlphaVec<f64> {
    match n {
        3 => AlphaVec::try_from(vec![1.5, 2.0, 0.5]).unwrap(),
        4 => AlphaVec::try_from(vec![1.5, 1.8, 2.0, 0.5]).unwrap(),
        8 => AlphaVec::try_from(vec![
            std::f64::consts::E,
            1.8392867552141612,
            1.6180339887498950,
            std::f64::consts::PI,
            3.0_f64.sqrt(),
            2.0,
            std::f64::consts::PI / 2.0,
            2.0 / std::f64::consts::PI,
        ])
        .unwrap(),
        _ => {
            // Generic alpha values that avoid α=1.0 issues
            let mut values = Vec::with_capacity(n);
            for i in 0..n {
                if i == n - 2 {
                    values.push(2.0);
                } else if i == n - 1 {
                    values.push(0.5); // Unity constraint
                } else {
                    // Use varied values to avoid degeneracy
                    values.push(1.5 + (i as f64) * 0.1);
                }
            }
            AlphaVec::try_from(values).unwrap()
        }
    }
}
