//! Test vectors for conformance testing

use crate::{decode_bjc, encode_bjc, AlphaVec, BitWord};

/// Standard test alpha vector (PrimeOS configuration)
fn test_alpha() -> AlphaVec<f64> {
    AlphaVec::try_from(vec![
        1.0,                  // α₀
        1.8392867552141612,   // α₁ (tribonacci)
        1.6180339887498950,   // α₂ (golden ratio)
        0.5,                  // α₃
        0.15915494309189535,  // α₄ (1/2π)
        6.283185307179586,    // α₅ (2π)
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
        let resonance = word.r(&alpha).unwrap();

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
    let alpha = test_alpha();

    // Minimum valid size (n=3 for alpha vector)
    let small_alpha = AlphaVec::try_from(vec![1.0, 2.0, 0.5]).unwrap();
    let small_input = BitWord::<3>::from(0b101u8);
    let small_packet = encode_bjc(&small_input, &small_alpha, 1, false).unwrap();
    let small_decoded = decode_bjc::<f64, 3>(&small_packet, &small_alpha).unwrap();
    assert_eq!(small_input, small_decoded);
}

// Additional test vectors would be loaded from tests/data/ in a real implementation
