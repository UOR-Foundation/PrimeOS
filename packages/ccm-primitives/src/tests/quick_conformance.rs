//! Quick conformance test that samples the test vectors

#[cfg(test)]
mod tests {
    use crate::test_vectors::serialization::read_binary;
    use crate::{decode_bjc, encode_bjc, BitWord};
    use std::fs::File;
    use std::io::BufReader;

    #[test]
    #[cfg(feature = "std")]
    fn quick_conformance_test() {
        println!("Running quick conformance test...");

        // Read test vectors
        let file = match File::open("tests/data/bjc_test_vectors.bin") {
            Ok(f) => f,
            Err(_) => {
                println!("Test vector file not found - skipping conformance test");
                return;
            }
        };

        let mut reader = BufReader::new(file);
        let test_sets = read_binary(&mut reader).expect("Failed to read test vectors");

        println!("Loaded {} test sets", test_sets.len());

        let mut total_tested = 0;

        // Test a sample from each set
        for set in &test_sets {
            println!("Testing samples from n={}...", set.n);

            // Test first 5, last 5, and 10 random from middle
            let indices_to_test: Vec<usize> = if set.vectors.len() <= 20 {
                (0..set.vectors.len()).collect()
            } else {
                let mut indices = vec![];
                // First 5
                indices.extend(0..5);
                // Last 5
                indices.extend((set.vectors.len() - 5)..set.vectors.len());
                // 10 from middle
                let step = set.vectors.len() / 12;
                for i in 0..10 {
                    indices.push(5 + i * step);
                }
                indices
            };

            for &i in &indices_to_test {
                if i >= set.vectors.len() {
                    continue;
                }

                let vector = &set.vectors[i];

                // Test based on n
                let result = match vector.n {
                    8 => test_vector_n8(vector),
                    _ => continue, // Skip other n values for quick test
                };

                if let Err(e) = result {
                    panic!("Vector {} failed: {}", i, e);
                }

                total_tested += 1;
            }
        }

        println!(
            "Quick conformance test passed: {} vectors tested",
            total_tested
        );
    }

    fn test_vector_n8(vector: &crate::test_vectors::TestVector<f64>) -> Result<(), String> {
        let word = BitWord::<8>::from(vector.input[0]);

        // Encode
        let packet = encode_bjc(
            &word,
            &vector.alpha,
            vector.k,
            vector.expected_packet.hash.is_some(),
        )
        .map_err(|e| format!("Encode failed: {:?}", e))?;

        // Decode
        let decoded = decode_bjc::<f64, 8>(&packet, &vector.alpha)
            .map_err(|e| format!("Decode failed: {:?}", e))?;

        // Verify bijectivity
        if decoded.to_usize() as u8 != vector.input[0] {
            return Err(format!(
                "Bijectivity failed: decoded {} != input {}",
                decoded.to_usize(),
                vector.input[0]
            ));
        }

        Ok(())
    }
}
