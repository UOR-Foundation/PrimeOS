//! Debug tests to understand resonance behavior

#[cfg(test)]
mod tests {
    use crate::{AlphaVec, HomomorphicResonance, Resonance};

    #[test]
    fn debug_resonance_values() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        println!("\n=== Alpha Values ===");
        for i in 0..8 {
            println!("α[{}] = {}", i, alpha[i]);
        }

        // Check unity constraint
        println!(
            "\nUnity constraint: α[6] * α[7] = {} * {} = {}",
            alpha[6],
            alpha[7],
            alpha[6] * alpha[7]
        );

        // Check some specific resonance values
        println!("\n=== Specific Resonance Values ===");

        // R(0) should be 1 (empty product)
        println!("R(0) = {}", 0u8.r(&alpha));

        // R(192) = R(11000000) = α[6] * α[7]
        println!("R(192) = R(11000000) = α[6] * α[7] = {}", 192u8.r(&alpha));

        // Check Klein group for 0
        println!("\n=== Klein group for 0 ===");
        let klein_0 = <u8 as Resonance<f64>>::class_members(&0u8);
        for (i, member) in klein_0.iter().enumerate() {
            println!(
                "Member {}: {} (binary: {:08b}) -> R = {}",
                i,
                member,
                member,
                member.r(&alpha)
            );
        }

        // Check which bits are homomorphic
        println!("\n=== Homomorphic Pairs ===");
        let pairs = u8::find_homomorphic_pairs(&alpha);
        for (i, j) in pairs {
            println!(
                "Bits ({}, {}) are homomorphic: α[{}] * α[{}] = {}",
                i,
                j,
                i,
                j,
                alpha[i] * alpha[j]
            );
        }

        // Compute sum of first 256 values
        println!("\n=== Sum of First 256 Values ===");
        let mut sum = 0.0;
        for i in 0u8..=255 {
            sum += i.r(&alpha);
        }
        println!("Sum R(0..256) = {}", sum);
        println!("Sum R(0..768) = {}", sum * 3.0);

        // Count unique resonance values
        println!("\n=== Unique Resonance Values ===");
        let mut resonances = std::collections::HashSet::new();
        for klein_base in 0u8..64 {
            let members = [
                klein_base,
                klein_base | 0b01000000,
                klein_base | 0b10000000,
                klein_base | 0b11000000,
            ];

            let mut min_res = f64::INFINITY;
            for &member in &members {
                let r = member.r(&alpha);
                if r < min_res {
                    min_res = r;
                }
            }

            // Round to avoid floating point precision issues
            let rounded = (min_res * 1e10).round() / 1e10;
            resonances.insert(rounded.to_bits());
        }
        println!("Number of unique resonance values: {}", resonances.len());
    }

    #[test]
    fn debug_klein_group_192() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // 192 = 11000000 (bits 6,7 set)
        println!("\n=== Klein group for 192 ===");
        let klein_192 = <u8 as Resonance<f64>>::class_members(&192u8);

        for (i, member) in klein_192.iter().enumerate() {
            println!(
                "Member {}: {} (binary: {:08b}) -> R = {}",
                i,
                member,
                member,
                member.r(&alpha)
            );
        }

        // Check if 192 forms a homomorphic subgroup with 0
        println!("\n=== Checking homomorphism for {{0, 192}} ===");
        let r_0 = 0u8.r(&alpha);
        let r_192 = 192u8.r(&alpha);
        let r_0_xor_192 = (0u8 ^ 192u8).r(&alpha);
        let r_product = r_0 * r_192;

        println!("R(0) = {}", r_0);
        println!("R(192) = {}", r_192);
        println!("R(0 ⊕ 192) = R(192) = {}", r_0_xor_192);
        println!("R(0) × R(192) = {}", r_product);
        println!("Homomorphic? {}", (r_0_xor_192 - r_product).abs() < 1e-10);
    }
}
