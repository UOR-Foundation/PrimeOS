//! Unit tests for the BJC decoder components

#[cfg(test)]
mod tests {
    use crate::resonance::InverseResonance;
    use crate::{decode_bjc, encode_bjc, AlphaVec, BitWord, Resonance};

    /// Test that Klein groups are correctly identified
    #[test]
    fn test_klein_group_structure() {
        // For any N-bit value, the Klein group consists of 4 members
        // formed by XORing with 00, 01, 10, 11 on bits 4,5 (where unity constraint is)

        let _alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Test for N=8
        let b = BitWord::from_u8(0b10101100); // 172
        let klein_group = <BitWord as Resonance<f64>>::class_members(&b);

        assert_eq!(klein_group.len(), 4);

        // The Klein group should be formed by XORing bits 4,5
        // 10101100 = 172
        // 10111100 = 188 (bit 4 flipped)
        // 10001100 = 140 (bit 5 flipped)
        // 10011100 = 156 (bits 4,5 flipped)
        let expected = vec![172, 188, 140, 156];
        let actual: Vec<usize> = klein_group.iter().map(|w| w.to_usize()).collect();

        assert_eq!(actual, expected);
    }

    /// Test that the minimum resonance in a Klein group is unique
    #[test]
    fn test_klein_minimum_uniqueness() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Test multiple Klein groups
        for base in 0u8..64 {
            // Test first 64 Klein groups
            let b = BitWord::from_u8((base << 2) as u8); // Create base of Klein group
            let klein_group = <BitWord as Resonance<f64>>::class_members(&b);

            let resonances: Vec<f64> = klein_group.iter().map(|w| w.r(&alpha)).collect();

            // Find minimum
            let min_resonance = resonances
                .iter()
                .min_by(|a, b| a.partial_cmp(b).unwrap())
                .unwrap();

            // Count how many have minimum resonance
            let min_count = resonances.iter().filter(|&&r| r == *min_resonance).count();

            // Due to our alpha values ensuring uniqueness, there should be exactly one minimum
            assert_eq!(
                min_count,
                1,
                "Klein group starting at {} has {} minima",
                base << 2,
                min_count
            );
        }
    }

    /// Test the unity constraint property
    #[test]
    fn test_unity_constraint() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // With dynamic alpha, unity constraint is at α[4] * α[5] = 1
        let product = alpha[4] * alpha[5];
        assert!(
            (product - 1.0).abs() < 1e-10,
            "Unity constraint violated: {} * {} = {}",
            alpha[4],
            alpha[5],
            product
        );

        // This means flipping both bits 4,5 shouldn't change resonance
        let b1 = BitWord::from_u8(0b00000000);
        let b2 = BitWord::from_u8(0b00110000); // Bits 4,5 flipped

        let r1 = b1.r(&alpha);
        let r2 = b2.r(&alpha);

        assert!(
            (r1 - r2).abs() < 1e-10,
            "Unity constraint test failed: {} vs {}",
            r1,
            r2
        );
    }

    /// Test that encoding and decoding are bijective for all 8-bit values
    #[test]
    fn test_full_bijectivity_8bit() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        for input in 0u8..=255 {
            let word = BitWord::from_u8(input);

            // Encode
            let packet =
                encode_bjc(&word, &alpha, 1, false).expect(&format!("Failed to encode {}", input));

            // Decode
            let decoded =
                decode_bjc::<f64>(&packet, &alpha).expect(&format!("Failed to decode {}", input));

            assert_eq!(
                decoded.to_usize(),
                input as usize,
                "Bijectivity failed for input {}",
                input
            );
        }
    }

    /// Test the decoder's ability to find Klein minima
    #[test]
    fn test_find_klein_minima() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // For each Klein group, compute its minimum and verify the decoder can find it
        for klein_base in 0u8..64 {
            let base = klein_base << 2;
            let klein_group = vec![
                BitWord::from_u8(base),
                BitWord::from_u8(base | 1),
                BitWord::from_u8(base | 2),
                BitWord::from_u8(base | 3),
            ];

            // Find the actual minimum
            let mut min_res = f64::INFINITY;
            let mut min_member = klein_group[0].clone();
            for member in &klein_group {
                let r = member.r(&alpha);
                if r < min_res || (r == min_res && member.to_usize() < min_member.to_usize()) {
                    min_res = r;
                    min_member = member.clone();
                }
            }

            // Now verify the decoder can find this minimum
            let tolerance = f64::EPSILON * min_res.abs().max(1.0);
            let candidates =
                <BitWord as InverseResonance<f64>>::find_by_resonance(min_res, &alpha, tolerance)
                    .expect("Decoder failed to find candidates");

            assert!(
                !candidates.is_empty(),
                "No candidates found for resonance {}",
                min_res
            );
            assert!(
                candidates.contains(&min_member),
                "Decoder didn't find the correct Klein minimum {} with resonance {}",
                min_member.to_usize(),
                min_res
            );
        }
    }

    /// Test decoder with specific known problematic values
    #[test]
    fn test_known_edge_cases() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Test cases that were previously problematic
        let test_cases = vec![
            0xABu8, // This was decoding as 0xAA before
            0x00u8, // Zero
            0xFFu8, // All ones
            0x01u8, // Single bit
            0x80u8, // High bit only
        ];

        for &input in &test_cases {
            let word = BitWord::from_u8(input);
            let packet = encode_bjc(&word, &alpha, 1, false).unwrap();
            let decoded = decode_bjc::<f64>(&packet, &alpha).unwrap();

            assert_eq!(
                decoded.to_usize(),
                input as usize,
                "Failed edge case: 0x{:02X} decoded as 0x{:02X}",
                input,
                decoded.to_usize()
            );
        }
    }

    /// Test decoder performance characteristics
    #[test]
    fn test_decoder_scaling() {
        let alpha3 = AlphaVec::try_from(vec![2.718281828, 1.618033989, 0.577215665]).unwrap();
        let alpha4 =
            AlphaVec::try_from(vec![2.718281828, 1.618033989, 3.141592654, 0.318309886]).unwrap();
        let alpha8 = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Test that smaller N complete quickly
        let start = std::time::Instant::now();
        for i in 0..8 {
            let word = BitWord::from_u64(i as u64, 3);
            let packet = encode_bjc(&word, &alpha3, 1, false).unwrap();
            let _decoded = decode_bjc::<f64>(&packet, &alpha3).unwrap();
        }
        let n3_time = start.elapsed();

        let start = std::time::Instant::now();
        for i in 0..16 {
            let word = BitWord::from_u64(i as u64, 3);
            let packet = encode_bjc(&word, &alpha4, 1, false).unwrap();
            let _decoded = decode_bjc::<f64>(&packet, &alpha4).unwrap();
        }
        let n4_time = start.elapsed();

        let start = std::time::Instant::now();
        for i in 0..256 {
            let word = BitWord::from_u32(i as u32);
            let packet = encode_bjc(&word, &alpha8, 1, false).unwrap();
            let _decoded = decode_bjc::<f64>(&packet, &alpha8).unwrap();
        }
        let n8_time = start.elapsed();

        println!("Decoder performance:");
        println!("  N=3: {:?} for 8 values", n3_time);
        println!("  N=4: {:?} for 16 values", n4_time);
        println!("  N=8: {:?} for 256 values", n8_time);

        // Verify reasonable performance (should complete in under 1 second)
        assert!(
            n8_time.as_secs() < 1,
            "N=8 decoding too slow: {:?}",
            n8_time
        );
    }

    /// Test the resonance decomposition logic
    #[test]
    fn test_resonance_decomposition() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Test that we can decompose known resonance values
        // For example, if bit 3 is set, resonance includes α[3]
        let b = BitWord::from_u8(0b00001000); // Only bit 3 set
        let resonance = b.r(&alpha);

        assert_eq!(resonance, alpha[3], "Single bit resonance incorrect");

        // Two bits set
        let b = BitWord::from_u8(0b00001100); // Bits 2 and 3 set
        let resonance = b.r(&alpha);
        assert_eq!(
            resonance,
            alpha[2] * alpha[3],
            "Two bit resonance incorrect"
        );
    }

    /// Test that the decoder correctly validates Klein minima
    #[test]
    fn test_klein_minimum_validation() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Create a value that is NOT a Klein minimum
        let not_minimum = BitWord::from_u8(0b10101101); // 173
        let klein_group = <BitWord as Resonance<f64>>::class_members(&not_minimum);

        // Find the actual minimum
        let resonances: Vec<(usize, f64)> = klein_group
            .iter()
            .map(|w| (w.to_usize(), w.r(&alpha)))
            .collect();

        let min_entry = resonances
            .iter()
            .min_by(|a, b| a.1.partial_cmp(&b.1).unwrap())
            .unwrap();

        // Verify that 173 is NOT the minimum
        assert_ne!(
            not_minimum.to_usize(),
            min_entry.0,
            "Test setup error: 173 should not be Klein minimum"
        );

        // The decoder should not return 173 when asked for the minimum resonance
        let tolerance = f64::EPSILON * min_entry.1.abs().max(1.0);
        let candidates =
            <BitWord as InverseResonance<f64>>::find_by_resonance(min_entry.1, &alpha, tolerance)
                .unwrap();

        assert!(
            !candidates.contains(&not_minimum),
            "Decoder incorrectly returned non-minimum value"
        );
    }
}
