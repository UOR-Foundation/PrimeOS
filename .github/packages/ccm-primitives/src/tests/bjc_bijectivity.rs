//! Test bijectivity of BJC codec

use crate::{decode_bjc, encode_bjc, AlphaVec, BitWord};

#[test]
fn test_bjc_bijectivity_comprehensive() {
    // Create alpha vector with unique Klein group minima
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

    // Test all 256 possible byte values
    for i in 0..=255u8 {
        let input = BitWord::from_u8(i);

        // Add debug for first few cases
        if i <= 2 {
            println!("\n=== Testing input 0x{:02X} ===", i);
        }

        let packet = encode_bjc(&input, &alpha, 1, false).unwrap();

        if i <= 2 || i == 0x28 {
            // Decode r_min value
            let r_min_bytes = &packet.r_min;
            let mut arr = [0u8; 8];
            arr.copy_from_slice(&r_min_bytes[..8]);
            let r_min_value = f64::from_be_bytes(arr);

            println!(
                "Input 0x{:02X} => flips={:02b}, r_min={}, r_min bytes={:?}",
                i, packet.flips, r_min_value, packet.r_min
            );
        }

        let decoded = match decode_bjc::<f64>(&packet, &alpha) {
            Ok(d) => d,
            Err(e) => {
                use crate::Resonance;
                println!("\nDecode failed for 0x{:02X}: {:?}", i, e);
                println!("  Input resonance: {}", input.r(&alpha));

                // Check Klein group members
                let input_members = <BitWord as Resonance<f64>>::class_members(&input);
                println!(
                    "  Input Klein members: {:?}",
                    input_members
                        .iter()
                        .map(|b| (b.to_usize(), b.r(&alpha)))
                        .collect::<Vec<_>>()
                );

                // Manually decode r_min
                let r_min_bytes = &packet.r_min;
                let mut arr = [0u8; 8];
                arr.copy_from_slice(&r_min_bytes[..8]);
                let r_min_value = f64::from_be_bytes(arr);
                println!("  Encoded r_min value: {}", r_min_value);

                panic!("Decode failed for input 0x{:02X}: {:?}", i, e);
            }
        };

        if input != decoded {
            use crate::Resonance;
            println!("Failed for 0x{:02X}:", i);
            println!("  Input resonance: {}", input.r(&alpha));
            println!("  Decoded as: 0x{:02X}", decoded.to_usize());
            println!("  Decoded resonance: {}", decoded.r(&alpha));
            println!("  Packet flips: 0x{:02X}", packet.flips);

            let input_members = <BitWord as Resonance<f64>>::class_members(&input);
            println!("  Input class members:");
            for m in input_members.iter() {
                println!("    0x{:02X}: R = {}", m.to_usize(), m.r(&alpha));
            }
        }

        assert_eq!(
            input,
            decoded,
            "Bijectivity failed for input 0x{:02X}: got 0x{:02X}",
            i,
            decoded.to_usize()
        );
    }
}

#[test]
fn test_problematic_values() {
    let alpha = AlphaVec::try_from(vec![
        std::f64::consts::E,
        1.8392867552141612,
        1.6180339887498950,
        std::f64::consts::PI,
        3.0_f64.sqrt(),
        2.0,
        std::f64::consts::PI / 2.0,
        2.0 / std::f64::consts::PI,
    ])
    .unwrap();

    // Test the previously problematic values
    let test_cases = vec![0xAAu8, 0xABu8, 0x00u8, 0x01u8, 0xFFu8];

    for &value in &test_cases {
        let input = BitWord::from_u8(value);
        let packet = encode_bjc(&input, &alpha, 1, true).unwrap();
        let decoded = decode_bjc::<f64>(&packet, &alpha).unwrap();

        assert_eq!(input, decoded, "Failed for 0x{:02X}", value);
    }
}
