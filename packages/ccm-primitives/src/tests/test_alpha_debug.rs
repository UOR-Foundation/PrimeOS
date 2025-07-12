//! Debug alpha generation

#[cfg(test)]
mod tests {
    use crate::AlphaVec;

    #[test]
    fn debug_alpha_64() {
        // Try to generate alpha for 64 bits and see what happens
        match AlphaVec::<f64>::for_bit_length(64) {
            Ok(alpha) => {
                println!("Successfully generated alpha for 64 bits:");
                for (i, &val) in alpha.values.iter().enumerate() {
                    println!("  α[{}] = {}", i, val);
                }
            }
            Err(e) => {
                println!("Failed to generate alpha for 64 bits: {:?}", e);
            }
        }

        // Also try mathematical generation
        match AlphaVec::<f64>::mathematical(64) {
            Ok(alpha) => {
                println!("\nMathematical alpha for 64 bits:");
                for (i, &val) in alpha.values.iter().enumerate() {
                    println!("  α[{}] = {}", i, val);
                }
            }
            Err(e) => {
                println!("Failed to generate mathematical alpha for 64 bits: {:?}", e);
            }
        }
    }

    #[test]
    fn debug_alpha_8_unity() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();
        println!("Dynamic alpha for 8 bits:");
        for i in 0..8 {
            println!("  α[{}] = {}", i, alpha[i]);
        }
        println!("\nUnity products:");
        println!("  α[4] × α[5] = {}", alpha[4] * alpha[5]);
        println!("  α[6] × α[7] = {}", alpha[6] * alpha[7]);

        // Check Klein group behavior
        println!("\nKlein group test (XOR bits 6,7):");
        let values = [0u8, 0b01000000, 0b10000000, 0b11000000];
        for v in values {
            use crate::Resonance;
            let r = v.r(&alpha);
            println!("  R({:08b}) = {}", v, r);
        }
    }

    #[test]
    fn debug_unity_positions_various_lengths() {
        println!("Unity constraint positions for various bit lengths:");

        for n in [3, 4, 8, 10, 16, 32, 64] {
            match AlphaVec::<f64>::for_bit_length(n) {
                Ok(alpha) => {
                    println!("\n{} bits (has {} alpha values):", n, alpha.len());

                    // Find where unity constraint is
                    let mut unity_found = false;
                    for i in 0..alpha.len() {
                        for j in (i + 1)..alpha.len() {
                            let product = alpha[i] * alpha[j];
                            if (product - 1.0).abs() < 1e-10 {
                                println!(
                                    "  Unity at positions ({}, {}): {} × {} = {}",
                                    i, j, alpha[i], alpha[j], product
                                );
                                unity_found = true;
                            }
                        }
                    }

                    if !unity_found {
                        println!("  No unity pairs found!");
                    }

                    // Check if it's always at (4,5)
                    if alpha.len() >= 6 {
                        let product_45 = alpha[4] * alpha[5];
                        println!("  α[4] × α[5] = {}", product_45);
                    }

                    // Check if it's at last two positions
                    if alpha.len() >= 2 {
                        let last_product = alpha[alpha.len() - 2] * alpha[alpha.len() - 1];
                        println!("  α[n-2] × α[n-1] = {}", last_product);
                    }
                }
                Err(e) => println!("\n{} bits: Error - {:?}", n, e),
            }
        }
    }
}
