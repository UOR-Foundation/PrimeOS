use crate::alpha::AlphaVec;
use crate::codec::bjc::{decode_bjc, encode_bjc};
use crate::{BitWord, Resonance};

#[test]
fn debug_bjc_round_trip_0xab() {
    // Create alpha field with unity constraint
    // Note: Unity constraint requires α[n-2] * α[n-1] = 1
    // For n=8, this means α₆ * α₇ = 1
    let alpha_values = [
        std::f64::consts::E,        // α₀ = e
        1.8392867552141612,         // α₁ (tribonacci)
        1.6180339887498950,         // α₂ (golden ratio)
        std::f64::consts::PI,       // α₃ = π
        3.0_f64.sqrt(),             // α₄ = √3
        2.0,                        // α₅ = 2
        std::f64::consts::PI / 2.0, // α₆ = π/2
        2.0 / std::f64::consts::PI, // α₇ = 2/π (unity: π/2 * 2/π = 1)
    ];
    let alpha = AlphaVec::new(alpha_values.into()).unwrap();

    // Verify unity constraint (α₆ * α₇ = 1)
    let unity_product = alpha_values[6] * alpha_values[7];
    println!(
        "Unity product α₆ × α₇ = {} × {} = {}",
        alpha_values[6], alpha_values[7], unity_product
    );
    assert!(
        (unity_product - 1.0).abs() < 1e-10,
        "Unity constraint violated"
    );

    // Test input that's failing
    let input_byte = 0xAB_u8;
    let input = BitWord::from_u8(input_byte);
    println!("\n=== ENCODING 0xAB ===");
    println!("Input byte: 0xAB = {:08b} = {}", input_byte, input_byte);
    println!("BitWord value: {}", input.to_usize());

    // Calculate resonance of input
    let r_input = input_byte.r(&alpha);
    println!("Resonance of 0xAB: {}", r_input);

    // Check class members and their resonances
    println!("\n=== CLASS MEMBERS ANALYSIS ===");
    let class_members = <u8 as Resonance<f64>>::class_members(&input_byte);
    println!("Class members of 0xAB: {:?}", class_members);
    for (i, &member) in class_members.iter().enumerate() {
        let diff = member ^ input_byte;
        println!(
            "  [{}] {} = {:08b}, R = {}, XOR diff = {:08b}",
            i,
            member,
            member,
            member.r(&alpha),
            diff
        );
    }

    // Find which member has minimum resonance
    let mut min_r = f64::INFINITY;
    let mut min_member = input_byte;
    for &member in &class_members {
        let r = member.r(&alpha);
        if r < min_r {
            min_r = r;
            min_member = member;
        }
    }
    println!(
        "\nMinimum resonance member: {} = {:08b}, R = {}",
        min_member, min_member, min_r
    );

    // Calculate expected flips
    let expected_flips_full = input_byte ^ min_member;
    let expected_flips = (expected_flips_full >> 6) & 0b11;
    println!("Expected flips (full): {:08b}", expected_flips_full);
    println!("Expected flips (bits 6,7 shifted): {:02b}", expected_flips);

    // Encode with k=1 (single channel), no hash
    let packet = encode_bjc(&input, &alpha, 1, false).unwrap();
    println!("\n=== ENCODED PACKET ===");
    println!("  n_bits: {}", packet.n_bits);
    println!("  log2_k: {}", packet.log2_k);
    println!("  r_min: {:?}", packet.r_min);
    println!("  flips: 0x{:02X} = {:02b}", packet.flips, packet.flips);
    println!("  page: {:?}", packet.page);

    // Decode
    println!("\n=== DECODING ===");
    let decoded = decode_bjc::<f64>(&packet, &alpha).unwrap();
    println!("Decoded BitWord value: {}", decoded.to_usize());
    let decoded_byte = decoded.to_usize() as u8;
    println!(
        "Decoded byte: 0x{:02X} = {:08b} = {}",
        decoded_byte, decoded_byte, decoded_byte
    );

    // Analyze the decoding process
    println!("\n=== DECODE ANALYSIS ===");
    // Convert r_min back to f64
    if packet.r_min.len() == 8 {
        let r_min_value = f64::from_be_bytes([
            packet.r_min[0],
            packet.r_min[1],
            packet.r_min[2],
            packet.r_min[3],
            packet.r_min[4],
            packet.r_min[5],
            packet.r_min[6],
            packet.r_min[7],
        ]);
        println!("r_min as f64: {}", r_min_value);

        // The decoder should find min_member from r_min
        println!("Expected b_min: {} = {:08b}", min_member, min_member);

        // Check what resonance 170 has
        println!("\nResonance of 170: {}", 170u8.r(&alpha));
        println!("Resonance of 171: {}", 171u8.r(&alpha));
        println!("Difference: {}", (170u8.r(&alpha) - 171u8.r(&alpha)).abs());

        // Check bits of 170 vs 171
        println!("\n170 = {:08b}", 170u8);
        println!("171 = {:08b}", 171u8);
        println!("XOR = {:08b} (difference is bit 0)", 170u8 ^ 171u8);

        // Apply flips to recover original
        let flips_mask = (packet.flips as u8 & 0b11) << 6;
        let recovered = min_member ^ flips_mask;
        println!("Flips mask: {:08b}", flips_mask);
        println!(
            "Recovered: {} ^ {} = {} = {:08b}",
            min_member, flips_mask, recovered, recovered
        );
    }

    // Check if decode matches input
    println!("\n=== RESULT ===");
    println!("Input:    0x{:02X} = {:08b}", input_byte, input_byte);
    println!("Decoded:  0x{:02X} = {:08b}", decoded_byte, decoded_byte);
    println!("Match:    {}", input_byte == decoded_byte);

    // Final assertion
    assert_eq!(input_byte, decoded_byte, "Round-trip failed for 0xAB");
}
