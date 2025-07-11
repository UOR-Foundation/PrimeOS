//! Comprehensive correctness tests for BJC codec
//! These tests ensure the encoder and decoder implement the spec correctly

use crate::{decode_bjc, encode_bjc, AlphaVec, BitWord, Resonance};

/// Verify that the encoder correctly implements the 6-step algorithm from spec section 2.6
#[test]
fn test_encoder_algorithm_steps() {
    let alpha = create_test_alpha();

    // Test a specific input to trace through the algorithm
    let input = BitWord::<8>::from(0x42u8); // 01000010

    // Step 1: Generate Klein group (XOR with 00,01,10,11 on bits 6,7)
    let class_members = <BitWord<8> as Resonance<f64>>::class_members(&input);
    println!("Klein group members:");
    for (i, m) in class_members.iter().enumerate() {
        println!("  [{}] 0x{:02X} = {:08b}", i, m.to_usize(), m.to_usize());
    }

    // According to the implementation in resonance/mod.rs:
    // [0] = b           = 0x42 = 01000010
    // [1] = b ^ 0x40    = 0x02 = 00000010 (flip bit 6)
    // [2] = b ^ 0x80    = 0xC2 = 11000010 (flip bit 7)
    // [3] = b ^ 0xC0    = 0x82 = 10000010 (flip both)
    assert_eq!(class_members[0].to_usize(), 0x42); // original
    assert_eq!(class_members[1].to_usize(), 0x02); // flip bit 6
    assert_eq!(class_members[2].to_usize(), 0xC2); // flip bit 7
    assert_eq!(class_members[3].to_usize(), 0x82); // flip both

    // Step 2: Find b_min (minimum resonance, tie-break by smallest value)
    let resonances: Vec<f64> = class_members.iter().map(|m| m.r(&alpha)).collect();
    println!("Resonances: {:?}", resonances);

    let min_resonance = resonances.iter().cloned().fold(f64::INFINITY, f64::min);
    let min_indices: Vec<usize> = resonances
        .iter()
        .enumerate()
        .filter(|(_, &r)| (r - min_resonance).abs() < 1e-10)
        .map(|(i, _)| i)
        .collect();

    // Among ties, choose smallest value
    let b_min_idx = min_indices
        .iter()
        .min_by_key(|&&i| class_members[i].to_usize())
        .unwrap();
    let b_min = class_members[*b_min_idx];

    // Step 3: Calculate flips (restricted to last 2 bits)
    let flips_full = input.to_usize() ^ b_min.to_usize();
    let flips = (flips_full >> 6) & 0b11; // Extract bits 6,7

    println!("Input: 0x{:02X}", input.to_usize());
    println!(
        "b_min: 0x{:02X} (resonance: {})",
        b_min.to_usize(),
        b_min.r(&alpha)
    );
    println!("Flips: 0b{:02b} (on bits 6,7)", flips);

    // Encode and verify packet structure
    let packet = encode_bjc(&input, &alpha, 1, false).unwrap();
    assert_eq!(packet.n_bits, 8);
    assert_eq!(packet.log2_k, 0); // k=1
    assert_eq!(packet.flips, flips as u8);

    // The stored r_min should match b_min's resonance
    let r_min_stored = f64::from_be_bytes(packet.r_min.try_into().unwrap());
    assert!((r_min_stored - b_min.r(&alpha)).abs() < 1e-10);
}

/// Verify that the decoder correctly implements the algorithm from spec section 2.7
#[test]
fn test_decoder_algorithm_steps() {
    let alpha = create_test_alpha();
    let input = BitWord::<8>::from(0x42u8);

    // First encode
    let packet = encode_bjc(&input, &alpha, 1, false).unwrap();

    // Now trace through decoder steps

    // Step 1: Extract flips, page, R_min
    let _flips = packet.flips & 0b11; // Only bits 0,1 are used
    let _r_min = f64::from_be_bytes(packet.r_min.clone().try_into().unwrap());

    // Step 2: Search for b_min
    // The decoder should find a value with resonance matching r_min
    // This is where the current implementation has a bug - it searches all values
    // instead of constraining to Klein group members

    // Step 3: Apply flips to recover original
    let decoded = decode_bjc::<f64, 8>(&packet, &alpha).unwrap();

    // Verify bijectivity
    assert_eq!(input, decoded, "Decoder failed to recover original input");
}

/// Test all 256 possible inputs for bijectivity
#[test]
fn test_complete_bijectivity() {
    let alpha = create_test_alpha();
    let mut failures = Vec::new();

    for i in 0..=255u8 {
        let input = BitWord::<8>::from(i);
        let packet = encode_bjc(&input, &alpha, 1, false).unwrap();
        let decoded = decode_bjc::<f64, 8>(&packet, &alpha).unwrap();

        if input != decoded {
            failures.push((i, decoded.to_usize()));

            // Debug information
            println!("\nFailed for input 0x{:02X}:", i);
            println!("  Decoded as: 0x{:02X}", decoded.to_usize());

            // Check Klein group
            let members = <BitWord<8> as Resonance<f64>>::class_members(&input);
            println!("  Klein group of input:");
            for (j, m) in members.iter().enumerate() {
                println!("    [{}] 0x{:02X}: R = {}", j, m.to_usize(), m.r(&alpha));
            }

            // Check what b_min the encoder found
            let r_min = f64::from_be_bytes(packet.r_min.try_into().unwrap());
            println!("  Stored r_min: {}", r_min);
            println!("  Stored flips: 0b{:02b}", packet.flips);
        }
    }

    assert!(
        failures.is_empty(),
        "Bijectivity failed for {} inputs: {:?}",
        failures.len(),
        failures
    );
}

/// Test Klein group properties
#[test]
fn test_klein_group_structure() {
    let _alpha = create_test_alpha();

    // Test that Klein groups have the correct structure
    // We only need to test one representative from each Klein group
    let mut tested = vec![false; 256];

    for i in 0..=255u8 {
        if tested[i as usize] {
            continue;
        }

        let base = BitWord::<8>::from(i);
        let members = <BitWord<8> as Resonance<f64>>::class_members(&base);

        // Debug first few Klein groups
        if i <= 2 {
            println!(
                "Klein group for {}: {:?}",
                i,
                members.iter().map(|m| m.to_usize()).collect::<Vec<_>>()
            );
        }

        // Mark all members as tested
        for m in &members {
            tested[m.to_usize()] = true;
        }

        // Verify we have exactly 4 members
        assert_eq!(members.len(), 4);

        // Verify they differ only in bits 6,7
        let base_masked = base.to_usize() & 0b00111111; // Mask off bits 6,7
        for member in &members {
            let member_masked = member.to_usize() & 0b00111111;
            assert_eq!(
                base_masked, member_masked,
                "Klein group members should only differ in bits 6,7"
            );
        }

        // Verify Klein four-group structure (V_4)
        // The Klein group is generated by XORing with bits 6,7
        // It should satisfy: for any a,b in the group, a XOR b is in the group
        // BUT only when the XOR is with 0, 64, 128, or 192 (the Klein masks)
        let klein_masks = vec![0u8, 64, 128, 192];

        for &member_val in &[members[0].to_usize() as u8] {
            for &mask in &klein_masks {
                let xor_result = member_val ^ mask;
                let found = members.iter().any(|m| m.to_usize() == xor_result as usize);
                assert!(
                    found,
                    "Klein group not closed: {} XOR {} = {} not in {:?}",
                    member_val,
                    mask,
                    xor_result,
                    members.iter().map(|m| m.to_usize()).collect::<Vec<_>>()
                );
            }
        }
    }
}

/// Test resonance function properties
#[test]
fn test_resonance_properties() {
    let alpha = create_test_alpha();

    // Test that no alpha equals 1.0 (except as part of unity constraint)
    for i in 0..alpha.len() {
        if i != alpha.len() - 2 && i != alpha.len() - 1 {
            assert!(
                (alpha[i] - 1.0).abs() > 0.1,
                "Alpha[{}] = {} is too close to 1.0",
                i,
                alpha[i]
            );
        }
    }

    // Test unity constraint
    let n = alpha.len();
    let unity_product = alpha[n - 2] * alpha[n - 1];
    assert!(
        (unity_product - 1.0).abs() < 1e-10,
        "Unity constraint violated: {} * {} = {}",
        alpha[n - 2],
        alpha[n - 1],
        unity_product
    );

    // Test that different bit patterns give different resonances
    // (except for Klein group members)
    let mut resonance_map = std::collections::HashMap::new();
    for i in 0..=255u8 {
        let word = BitWord::<8>::from(i);
        let resonance = word.r(&alpha);
        resonance_map
            .entry(format!("{:.10}", resonance))
            .or_insert_with(Vec::new)
            .push(i);
    }

    // Each resonance class should have at most 4 members
    for (resonance, members) in &resonance_map {
        assert!(
            members.len() <= 4,
            "Resonance {} has {} members (expected ≤ 4): {:?}",
            resonance,
            members.len(),
            members
        );
    }
}

/// Create test alpha vector using dynamic generation
fn create_test_alpha() -> AlphaVec<f64> {
    // Use the standard testing alpha which has dynamic values
    crate::tests::testing_alpha()
}

/// Test edge cases
#[test]
fn test_edge_cases() {
    let alpha = create_test_alpha();

    // Test all-zeros
    let input = BitWord::<8>::from(0x00u8);
    let packet = encode_bjc(&input, &alpha, 1, false).unwrap();
    let decoded = decode_bjc::<f64, 8>(&packet, &alpha).unwrap();
    assert_eq!(input, decoded);

    // Test all-ones
    let input = BitWord::<8>::from(0xFFu8);
    let packet = encode_bjc(&input, &alpha, 1, false).unwrap();
    let decoded = decode_bjc::<f64, 8>(&packet, &alpha).unwrap();
    assert_eq!(input, decoded);

    // Test alternating bits
    let input = BitWord::<8>::from(0xAAu8);
    let packet = encode_bjc(&input, &alpha, 1, false).unwrap();
    let decoded = decode_bjc::<f64, 8>(&packet, &alpha).unwrap();
    assert_eq!(input, decoded);
}
