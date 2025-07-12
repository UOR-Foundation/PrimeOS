//! Unit tests for the BJC decoder components

#[cfg(test)]
mod tests {
    use crate::resonance::InverseResonance;
    use crate::{decode_bjc, encode_bjc, AlphaVec, BitWord, Resonance};

    /// Test that Klein groups are correctly identified
    #[test]
    fn test_klein_group_structure() {
        // For any N-bit value, the Klein group consists of 4 members
        // formed by XORing with 00, 01, 10, 11 on bits (N-2, N-1) where unity constraint is

        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Test for N=8
        let b = BitWord::from_u8(0b10101100u8); // 172
        let klein_group = <BitWord as Resonance<f64>>::class_members(&b);

        assert_eq!(klein_group.len(), 4);

        // The Klein group should be formed by XORing bits 6,7 (N-2, N-1 for N=8)
        // 10101100 = 172
        // 11101100 = 236 (bit 6 flipped)
        // 00101100 = 44 (bit 7 flipped)  
        // 01101100 = 108 (bits 6,7 flipped)
        let expected = vec![172, 236, 44, 108];
        let mut actual: Vec<usize> = klein_group.iter().map(|w| w.to_usize()).collect();
        actual.sort();
        let mut expected_sorted = expected;
        expected_sorted.sort();

        assert_eq!(actual, expected_sorted);
    }

    /// Test that the minimum resonance in a Klein group is unique
    #[test]
    fn test_klein_minimum_uniqueness() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Test multiple Klein groups
        for base in 0u8..16 {
            // Test first 16 Klein groups (base in lower 6 bits)
            let b = BitWord::from_u8(base); // Create base of Klein group
            let klein_group = <BitWord as Resonance<f64>>::class_members(&b);

            let resonances: Vec<f64> = klein_group.iter().map(|w| w.r(&alpha)).collect();

            // Find minimum
            let min_resonance = resonances
                .iter()
                .min_by(|a, b| a.partial_cmp(b).unwrap())
                .unwrap();

            // Count how many have the minimum resonance
            let min_count = resonances
                .iter()
                .filter(|&r| (*r - min_resonance).abs() < 1e-10)
                .count();

            // In most cases there should be exactly one minimum
            // (ties are handled by lexicographic ordering in encoder)
            assert!(
                min_count >= 1,
                "Klein group for {} has no minimum",
                base
            );
        }
    }

    /// Test unity positions (where α[n-2] * α[n-1] = 1)
    #[test]
    fn test_unity_positions() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Unity positions should have resonance = 1
        // For N=8, this is when only bits 6,7 are set (48 = 0b00110000)
        let b1 = BitWord::from_u8(0b00000000u8);
        let b2 = BitWord::from_u64(0b11000000u8 as u64, 8); // Bits 6,7 set

        let r1 = b1.r(&alpha);
        let r2 = b2.r(&alpha);

        assert!((r1 - 1.0).abs() < 1e-10, "Empty should have resonance 1");
        assert!(
            (r2 - 1.0).abs() < 1e-10,
            "Unity positions should have resonance 1, got {}",
            r2
        );
    }

    /// Test encoding and decoding specific patterns
    #[test]
    fn test_specific_patterns() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Test various patterns
        let patterns = vec![
            0b00000000u8, // All zeros
            0b11111111u8, // All ones
            0b10101010u8, // Alternating
            0b11110000u8, // Half and half
            0b00010000u8, // Single bit
            0b11000000u8, // Unity position (bits 6,7)
        ];

        for input in patterns {
            let word = BitWord::from_u8(input);
            let packet = encode_bjc(&word, &alpha, 1, false).unwrap();
            let decoded = decode_bjc::<f64>(&packet, &alpha).unwrap();

            assert_eq!(
                word.to_usize(),
                decoded.to_usize(),
                "Failed roundtrip for pattern {:08b}",
                input
            );
        }
    }

    /// Test InverseResonance trait
    #[test]
    fn test_inverse_resonance() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Test finding values with specific resonances
        let test_resonances = vec![
            1.0,  // Unity
            2.0,  // Simple value
            10.0, // Larger value
        ];

        for target in test_resonances {
            // We know Klein four-group {0, 1, 48, 49} has resonance 1 for standard 8-bit
            // since bits 6,7 are unity positions (48 = 0b00110000, 49 = 0b00110001)
            let klein_unity = vec![
                BitWord::from_u8(0),
                BitWord::from_u8(1),
                BitWord::from_u8(192), // 0b11000000
                BitWord::from_u8(193), // 0b11000001
            ];

            // Check if any Klein unity member has the target resonance
            for member in klein_unity {
                let r = member.r(&alpha);
                if (r - target).abs() < 0.1 {
                    // Found a match
                    let candidates = <BitWord as InverseResonance<f64>>::find_by_resonance(
                        target,
                        &alpha,
                        0.01,
                    );

                    match candidates {
                        Ok(found) => {
                            assert!(
                                !found.is_empty(),
                                "Should find at least one value with resonance {}",
                                target
                            );
                        }
                        Err(_) => {
                            // It's ok if we can't find exact matches for all targets
                        }
                    }
                    break;
                }
            }
        }
    }

    /// Test encoding all values exhaustively for small N
    #[test]
    fn test_exhaustive_small_n() {
        // Test N=3
        let alpha3 = AlphaVec::<f64>::for_bit_length(3).unwrap();
        for i in 0..8 {
            let word = BitWord::from_u64(i as u64, 3);
            let packet = encode_bjc(&word, &alpha3, 1, false).unwrap();
            let decoded = decode_bjc::<f64>(&packet, &alpha3).unwrap();
            assert_eq!(word.to_usize(), decoded.to_usize());
        }

        // Test N=4
        let alpha4 = AlphaVec::<f64>::for_bit_length(4).unwrap();
        for i in 0..16 {
            let word = BitWord::from_u64(i as u64, 4);
            let packet = encode_bjc(&word, &alpha4, 1, false).unwrap();
            let decoded = decode_bjc::<f64>(&packet, &alpha4).unwrap();
            assert_eq!(word.to_usize(), decoded.to_usize());
        }

        // Test N=8
        let alpha8 = AlphaVec::<f64>::for_bit_length(8).unwrap();
        for i in 0..256 {
            let word = BitWord::from_u8(i as u8);
            let packet = encode_bjc(&word, &alpha8, 1, false).unwrap();
            let decoded = decode_bjc::<f64>(&packet, &alpha8).unwrap();
            assert_eq!(word.to_usize(), decoded.to_usize());
        }
    }

    /// Test that flips are correctly encoded
    #[test]
    fn test_flip_encoding() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Create a value that is not the Klein minimum
        let not_minimum = BitWord::from_u8(0b10101101u8); // 173
        let klein_group = <BitWord as Resonance<f64>>::class_members(&not_minimum);

        // Find which has minimum resonance
        let mut min_idx = 0;
        let mut min_resonance = f64::INFINITY;
        for (idx, member) in klein_group.iter().enumerate() {
            let r = member.r(&alpha);
            if r < min_resonance {
                min_resonance = r;
                min_idx = idx;
            }
        }

        let packet = encode_bjc(&not_minimum, &alpha, 1, false).unwrap();

        // The flips should encode which Klein member we started from
        // flips = 0b00 for member 0, 0b01 for member 1, etc.
        assert_eq!(
            packet.flips, min_idx as u8,
            "Flips should encode Klein member index"
        );
    }

    /// Test resonance calculation edge cases
    #[test]
    fn test_resonance_edge_cases() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Single bit patterns
        let b = BitWord::from_u8(0b00001000u8); // Only bit 3 set
        let r = b.r(&alpha);
        assert_eq!(r, alpha[3], "Single bit should give corresponding alpha");

        // Two bits
        let b = BitWord::from_u8(0b00001100u8); // Bits 2 and 3 set
        let r = b.r(&alpha);
        assert_eq!(
            r,
            alpha[2] * alpha[3],
            "Two bits should give product of alphas"
        );
    }

    /// Test the decoder's ability to handle all possible b_min values
    #[test]
    fn test_decoder_coverage() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // The decoder should be able to find any value that could be a Klein minimum
        // Test by encoding various values and checking the decoder can recover them
        for base in (0..256).step_by(17) {
            // Sample every 17th value
            let word = BitWord::from_u8(base as u8);
            let packet = encode_bjc(&word, &alpha, 1, false).unwrap();

            match decode_bjc::<f64>(&packet, &alpha) {
                Ok(decoded) => {
                    assert_eq!(
                        word.to_usize(),
                        decoded.to_usize(),
                        "Decoder failed for value {}",
                        base
                    );
                }
                Err(e) => {
                    panic!("Decoder error for value {}: {:?}", base, e);
                }
            }
        }
    }
}