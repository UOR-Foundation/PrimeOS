//! Conformance test using the official test vectors

#[cfg(test)]
mod tests {
    use crate::test_vectors::serialization::read_binary;
    use crate::{decode_bjc, encode_bjc, BitWord};
    use std::fs::File;
    use std::io::BufReader;

    #[test]
    #[cfg(feature = "std")]
    fn conformance_test() {
        println!("Running CCM-BJC v1.0 conformance test...");

        // Read test vectors
        let file = File::open("tests/data/bjc_test_vectors.bin")
            .expect("Failed to open test vector file. Run 'cargo test generate_official_test_vectors' first.");
        let mut reader = BufReader::new(file);

        let test_sets = read_binary(&mut reader).expect("Failed to read test vectors");

        println!("Loaded {} test sets", test_sets.len());

        let mut total_passed = 0;
        let mut total_failed = 0;

        // Test each set
        for set in &test_sets {
            println!(
                "\nTesting n={} with {} vectors...",
                set.n,
                set.vectors.len()
            );
            let mut passed = 0;
            let mut failed = 0;

            for (i, vector) in set.vectors.iter().enumerate() {
                // Encode the input
                let result = match vector.n {
                    3 => test_vector::<3>(vector),
                    4 => test_vector::<4>(vector),
                    8 => test_vector::<8>(vector),
                    10 => test_vector::<10>(vector),
                    16 => test_vector::<16>(vector),
                    32 => test_vector::<32>(vector),
                    64 => test_vector::<64>(vector),
                    _ => {
                        println!("  Vector {}: SKIP (unsupported n={})", i, vector.n);
                        continue;
                    }
                };

                match result {
                    Ok(_) => passed += 1,
                    Err(e) => {
                        failed += 1;
                        println!("  Vector {} FAILED: {}", i, e);
                    }
                }
            }

            println!("  n={}: {} passed, {} failed", set.n, passed, failed);
            total_passed += passed;
            total_failed += failed;
        }

        println!("\nTotal: {} passed, {} failed", total_passed, total_failed);

        assert_eq!(
            total_failed, 0,
            "Conformance test failed: {} vectors did not pass",
            total_failed
        );
    }

    fn test_vector<const N: usize>(
        vector: &crate::test_vectors::TestVector<f64>,
    ) -> Result<(), String> {
        // Convert input to BitWord
        let input_value = match N {
            3 | 4 | 8 => vector.input[0] as u64,
            10 | 16 => {
                let bytes = [vector.input[0], vector.input.get(1).copied().unwrap_or(0)];
                u16::from_le_bytes(bytes) as u64
            }
            32 => {
                let mut bytes = [0u8; 4];
                bytes[..vector.input.len().min(4)]
                    .copy_from_slice(&vector.input[..vector.input.len().min(4)]);
                u32::from_le_bytes(bytes) as u64
            }
            64 => {
                let mut bytes = [0u8; 8];
                bytes[..vector.input.len().min(8)]
                    .copy_from_slice(&vector.input[..vector.input.len().min(8)]);
                u64::from_le_bytes(bytes)
            }
            _ => return Err(format!("Unsupported N={}", N)),
        };

        let word = BitWord::<N>::from(input_value);

        // Encode
        let packet = encode_bjc(
            &word,
            &vector.alpha,
            vector.k,
            vector.expected_packet.hash.is_some(),
        )
        .map_err(|e| format!("Encode failed: {:?}", e))?;

        // Verify packet matches expected
        if !packets_equal(&packet, &vector.expected_packet) {
            return Err(format!(
                "Packet mismatch: got {:?}, expected {:?}",
                serialize_for_debug(&packet),
                serialize_for_debug(&vector.expected_packet)
            ));
        }

        // Decode
        let decoded = decode_bjc::<f64, N>(&packet, &vector.alpha)
            .map_err(|e| format!("Decode failed: {:?}", e))?;

        // Verify bijectivity
        if decoded.to_usize() as u64 != input_value {
            return Err(format!(
                "Bijectivity failed: decoded {} != input {}",
                decoded.to_usize(),
                input_value
            ));
        }

        Ok(())
    }

    fn packets_equal(a: &crate::BjcPacket, b: &crate::BjcPacket) -> bool {
        a.n_bits == b.n_bits
            && a.log2_k == b.log2_k
            && a.r_min == b.r_min
            && a.flips == b.flips
            && a.page == b.page
            && a.hash == b.hash
    }

    fn serialize_for_debug(packet: &crate::BjcPacket) -> String {
        format!(
            "n={}, k={}, r_min={:?}, flips={}, page={:?}, hash={}",
            packet.n_bits,
            1 << packet.log2_k,
            packet.r_min,
            packet.flips,
            packet.page,
            packet.hash.is_some()
        )
    }

    #[test]
    #[cfg(feature = "std")]
    fn verify_all_bijectivity() {
        println!("Verifying bijectivity for all test vectors...");

        // Read test vectors
        let file =
            File::open("tests/data/bjc_test_vectors.bin").expect("Failed to open test vector file");
        let mut reader = BufReader::new(file);

        let test_sets = read_binary(&mut reader).expect("Failed to read test vectors");

        let mut total_vectors = 0;
        let mut bijectivity_failures = 0;

        for set in &test_sets {
            for vector in &set.vectors {
                total_vectors += 1;

                let result = match vector.n {
                    3 => verify_bijectivity::<3>(vector),
                    4 => verify_bijectivity::<4>(vector),
                    8 => verify_bijectivity::<8>(vector),
                    10 => verify_bijectivity::<10>(vector),
                    16 => verify_bijectivity::<16>(vector),
                    32 => verify_bijectivity::<32>(vector),
                    64 => verify_bijectivity::<64>(vector),
                    _ => continue,
                };

                if let Err(e) = result {
                    bijectivity_failures += 1;
                    println!("Bijectivity failure: {}", e);
                }
            }
        }

        println!(
            "\nBijectivity verification: {} vectors tested, {} failures",
            total_vectors, bijectivity_failures
        );

        assert_eq!(
            bijectivity_failures, 0,
            "Bijectivity verification failed for {} vectors",
            bijectivity_failures
        );
    }

    fn verify_bijectivity<const N: usize>(
        vector: &crate::test_vectors::TestVector<f64>,
    ) -> Result<(), String> {
        // Get input value
        let input_value = match N {
            3 | 4 | 8 => vector.input[0] as u64,
            10 | 16 => {
                let bytes = [vector.input[0], vector.input.get(1).copied().unwrap_or(0)];
                u16::from_le_bytes(bytes) as u64
            }
            32 => {
                let mut bytes = [0u8; 4];
                bytes[..vector.input.len().min(4)]
                    .copy_from_slice(&vector.input[..vector.input.len().min(4)]);
                u32::from_le_bytes(bytes) as u64
            }
            64 => {
                let mut bytes = [0u8; 8];
                bytes[..vector.input.len().min(8)]
                    .copy_from_slice(&vector.input[..vector.input.len().min(8)]);
                u64::from_le_bytes(bytes)
            }
            _ => return Ok(()),
        };

        // Use the expected packet to decode
        let decoded = decode_bjc::<f64, N>(&vector.expected_packet, &vector.alpha)
            .map_err(|e| format!("Decode failed: {:?}", e))?;

        // Verify bijectivity
        if decoded.to_usize() as u64 != input_value {
            return Err(format!(
                "n={}, input={}: decoded {} != input {}",
                N,
                input_value,
                decoded.to_usize(),
                input_value
            ));
        }

        Ok(())
    }
}
