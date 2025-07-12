//! Generate the official CCM-BJC v1.0 test vectors

#[cfg(test)]
mod tests {
    use crate::test_vectors::{
        generator::{generate_random_vectors, generate_test_vectors},
        serialization::write_binary,
        standard_alphas,
    };

    #[test]
    #[cfg(feature = "std")]
    fn generate_official_test_vectors() {
        use std::fs::File;
        use std::io::BufWriter;

        println!("Generating official CCM-BJC v1.0 test vectors...");

        let mut all_test_sets = Vec::new();

        // Generate test vectors for each n value
        let n_values = vec![3, 4, 8, 10, 16, 32, 64];

        for &n in &n_values {
            println!("Generating vectors for n={}...", n);

            let alpha = standard_alphas::get_standard_alpha::<f64>(n)
                .expect(&format!("Should have standard alpha for n={}", n));

            // Generate comprehensive test vectors
            let mut test_set = generate_test_vectors(n, alpha.clone());

            // Add random test vectors (scaled by n to fit in 256KB)
            let random_count = match n {
                3 | 4 | 8 => 100, // Small n: fewer randoms needed
                10 | 16 => 500,   // Medium n
                32 => 200,        // Larger n
                64 => 100,        // Largest n
                _ => 50,
            };

            println!("  - Adding {} random vectors...", random_count);
            let random_vectors = generate_random_vectors(n, &alpha, random_count, n as u64 * 12345);
            test_set.vectors.extend(random_vectors);

            println!("  - Total vectors for n={}: {}", n, test_set.vectors.len());

            all_test_sets.push(test_set);
        }

        // Calculate total size estimate
        let total_vectors: usize = all_test_sets.iter().map(|s| s.vectors.len()).sum();
        println!("\nTotal test vectors: {}", total_vectors);

        // Write to file
        let output_path = "tests/data/bjc_test_vectors.bin";

        // Create directory if it doesn't exist
        std::fs::create_dir_all("tests/data").ok();

        let file = File::create(output_path).expect("Failed to create test vector file");
        let mut writer = BufWriter::new(file);

        write_binary(&mut writer, &all_test_sets).expect("Failed to write test vectors");

        // Get file size
        let metadata = std::fs::metadata(output_path).expect("Failed to get file metadata");
        let file_size = metadata.len();

        println!("\nTest vectors written to: {}", output_path);
        println!(
            "File size: {} bytes ({:.1} KB)",
            file_size,
            file_size as f64 / 1024.0
        );

        // Ensure we're under 256KB
        assert!(
            file_size <= 256 * 1024,
            "Test vector file too large: {} bytes (max 256KB)",
            file_size
        );
    }

    #[test]
    fn test_vector_counts() {
        // Test that we generate the expected number of vectors
        let test_cases = vec![
            (3, 8),   // n=3: 2^3 = 8 exhaustive
            (4, 16),  // n=4: 2^4 = 16 exhaustive
            (8, 256), // n=8: 2^8 = 256 exhaustive
        ];

        for (n, expected_min) in test_cases {
            let alpha = standard_alphas::get_standard_alpha::<f64>(n).unwrap();
            let test_set = generate_test_vectors(n, alpha);

            assert!(
                test_set.vectors.len() >= expected_min,
                "n={}: expected at least {} vectors, got {}",
                n,
                expected_min,
                test_set.vectors.len()
            );
        }
    }

    #[test]
    fn verify_bijectivity_sampling() {
        // Verify that our test vectors maintain bijectivity
        use crate::{decode_bjc, encode_bjc, BitWord};

        let n = 8;
        let alpha = standard_alphas::get_standard_alpha::<f64>(n).unwrap();
        let test_set = generate_test_vectors(n, alpha);

        // Test a sample of vectors
        for (i, vector) in test_set.vectors.iter().take(20).enumerate() {
            let word = BitWord::from_u8(vector.input[0]);

            // Encode
            let packet = encode_bjc(&word, &vector.alpha, 1, false)
                .expect(&format!("Failed to encode vector {}", i));

            // Decode
            let decoded = decode_bjc::<f64>(&packet, &vector.alpha)
                .expect(&format!("Failed to decode vector {}", i));

            // Verify bijectivity
            assert_eq!(
                decoded.to_usize() as u8,
                vector.input[0],
                "Bijectivity failed for vector {}: {:?} != {:?}",
                i,
                decoded.to_usize() as u8,
                vector.input[0]
            );
        }
    }
}
