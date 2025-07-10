//! Test vectors for conformance testing

#![allow(clippy::approx_constant, clippy::excessive_precision)]

use crate::{decode_bjc, encode_bjc, AlphaVec, BitWord, Resonance};

/// Standard test alpha vector (PrimeOS configuration)
fn test_alpha() -> AlphaVec<f64> {
    AlphaVec::try_from(vec![
        1.0,                  // α₀
        1.8392867552141612,   // α₁ (tribonacci)
        1.6180339887498950,   // α₂ (golden ratio) - exact value from spec
        0.5,                  // α₃
        0.15915494309189535,  // α₄ (1/2π)
        6.283185307179586,    // α₅ (2π) - exact value from spec
        0.19961197478400415,  // α₆
        0.014134725141734695, // α₇
    ])
    .unwrap()
}

#[test]
fn test_known_vectors() {
    let alpha = test_alpha();

    // Test vector 1: Simple byte
    let input1 = BitWord::<8>::from(0x42u8);
    let packet1 = encode_bjc(&input1, &alpha, 1, false).unwrap();
    let decoded1 = decode_bjc::<f64, 8>(&packet1, &alpha).unwrap();
    assert_eq!(input1, decoded1);

    // Test vector 2: Klein group member
    let input2 = BitWord::<8>::from(48u8); // Binary: 00110000
    let packet2 = encode_bjc(&input2, &alpha, 1, false).unwrap();
    let decoded2 = decode_bjc::<f64, 8>(&packet2, &alpha).unwrap();
    assert_eq!(input2, decoded2);

    // Test vector 3: All bits set
    let input3 = BitWord::<8>::from(0xFFu8);
    let packet3 = encode_bjc(&input3, &alpha, 1, false).unwrap();
    let decoded3 = decode_bjc::<f64, 8>(&packet3, &alpha).unwrap();
    assert_eq!(input3, decoded3);
}

#[test]
fn test_unity_constraint_vectors() {
    let alpha = test_alpha();

    // Verify unity constraint
    assert!((alpha[4] * alpha[5] - 1.0).abs() < f64::EPSILON);

    // Test bytes that utilize the unity property
    let unity_bytes = vec![0u8, 1, 48, 49]; // Klein four-group

    for &byte in &unity_bytes {
        let word = BitWord::<8>::from(byte);
        let resonance = word.r(&alpha);

        // Klein group members should have specific resonance patterns
        if byte == 0 || byte == 1 {
            assert!((resonance - 1.0).abs() < 1e-10);
        } else if byte == 48 {
            // bits 4,5 set: α₄ * α₅ = 1
            assert!((resonance - 1.0).abs() < 1e-10);
        } else if byte == 49 {
            // bits 0,4,5 set: α₀ * α₄ * α₅ = 1 * 1 = 1
            assert!((resonance - 1.0).abs() < 1e-10);
        }
    }
}

#[test]
fn test_hash_verification() {
    let alpha = test_alpha();

    let input = BitWord::<8>::from(0xABu8);

    // Encode with hash
    let packet_with_hash = encode_bjc(&input, &alpha, 1, true).unwrap();
    assert!(packet_with_hash.hash.is_some());

    // Decode should verify hash automatically
    let decoded = decode_bjc::<f64, 8>(&packet_with_hash, &alpha).unwrap();
    assert_eq!(input, decoded);

    // Corrupt the packet
    let mut corrupted = packet_with_hash.clone();
    corrupted.flips ^= 1; // Flip a bit

    // Decoding should fail due to hash mismatch
    let result = decode_bjc::<f64, 8>(&corrupted, &alpha);
    assert!(result.is_err());
}

#[test]
fn test_edge_cases() {
    let _alpha = test_alpha();

    // Minimum valid size (n=3 for alpha vector)
    let small_alpha = AlphaVec::try_from(vec![1.0, 2.0, 0.5]).unwrap();
    let small_input = BitWord::<3>::from(0b101u8);
    let small_packet = encode_bjc(&small_input, &small_alpha, 1, false).unwrap();
    let small_decoded = decode_bjc::<f64, 3>(&small_packet, &small_alpha).unwrap();
    assert_eq!(small_input, small_decoded);
}

#[test]
fn test_spec_conformance_vectors() {
    // Test vectors from spec section 5.4
    let n3_alpha = AlphaVec::try_from(vec![1.0, 1.618033988749895, 0.618033988749895]).unwrap();

    // n=3, α=(1,φ,1/φ), k=1
    let test_cases = vec![
        (
            0b000u8,
            vec![0x03, 0x00, 0x3F, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
        ), // b=000
        (
            0b101u8,
            vec![0x03, 0x00, 0x3F, 0xE1, 0xF4, 0xA8, 0x00, 0x00, 0x00, 0x00],
        ), // b=101
    ];

    for (input_bits, expected_r_min_start) in test_cases {
        let word = BitWord::<3>::from(input_bits);
        let packet = encode_bjc(&word, &n3_alpha, 1, false).unwrap();

        // Check n_bits
        assert_eq!(packet.n_bits, 3);

        // Check log2_k
        assert_eq!(packet.log2_k, 0); // k=1 means log2(k)=0

        // Check r_min starts with expected bytes (partial check)
        for (i, &expected_byte) in expected_r_min_start.iter().enumerate() {
            if i < packet.r_min.len() {
                assert_eq!(
                    packet.r_min[i], expected_byte,
                    "r_min[{i}] mismatch for input {input_bits:03b}"
                );
            }
        }
    }
}

#[test]
fn test_exhaustive_small_n() {
    // Exhaustive test for n=3 as a sanity check
    let alpha = AlphaVec::try_from(vec![1.0, 2.0, 0.5]).unwrap();

    for i in 0u8..8 {
        let word = BitWord::<3>::from(i);
        let packet = encode_bjc(&word, &alpha, 1, false).unwrap();
        let decoded = decode_bjc::<f64, 3>(&packet, &alpha).unwrap();

        assert_eq!(word, decoded, "Round-trip failed for {i:03b}");

        // Verify packet structure
        assert_eq!(packet.n_bits, 3);
        assert_eq!(packet.log2_k, 0);
        assert!(packet.flips <= 0b11);
        assert_eq!(packet.page.len(), 0); // No page data when k=1
        assert!(packet.hash.is_none()); // No hash when include_hash=false

        // Verify r_min is properly encoded
        assert_eq!(packet.r_min.len(), 8); // f64 is 8 bytes
    }
}

#[test]
#[cfg(feature = "sha2")]
fn test_packet_structure_with_hash() {
    let alpha = test_alpha();
    let word = BitWord::<8>::from(0x42u8);

    // Test with hash
    let packet = encode_bjc(&word, &alpha, 1, true).unwrap();

    // Verify packet structure
    assert_eq!(packet.n_bits, 8);
    assert_eq!(packet.log2_k, 0);
    assert!(packet.flips <= 0b11);
    assert_eq!(packet.page.len(), 0);
    assert_eq!(packet.hash.as_ref().unwrap().len(), 32); // SHA-256 is 32 bytes

    // Verify the packet can be decoded
    let decoded = decode_bjc::<f64, 8>(&packet, &alpha).unwrap();
    assert_eq!(word, decoded);
}

// Note: Full 256KB test vectors from Appendix A would be loaded from external file
// This is a placeholder for the actual implementation that would read from tests/data/
