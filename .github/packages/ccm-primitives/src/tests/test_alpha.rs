//! Tests for dynamic alpha generation

#[cfg(test)]
mod tests {
    use crate::{AlphaVec, Resonance};

    /// Get alpha values for n-bit testing
    pub fn alpha_for_bits(n: usize) -> AlphaVec<f64> {
        AlphaVec::for_bit_length(n).expect("Valid alpha")
    }

    #[test]
    fn test_dynamic_generation_different_sizes() {
        for n in [3, 4, 8, 16, 32, 64] {
            let alpha = alpha_for_bits(n);

            println!("Alpha for {} bits:", n);
            for (i, &val) in alpha.values.iter().enumerate() {
                println!("  α[{}] = {}", i, val);
            }

            // Verify basic properties
            assert_eq!(
                alpha.len(),
                n,
                "Should have {} alpha values for {}-bit input",
                n,
                n
            );
            assert_eq!(alpha[0], 1.0, "α[0] should be identity");

            // Verify unity constraint at positions (n-2, n-1)
            if n >= 2 {
                let unity = alpha[n - 2] * alpha[n - 1];
                assert!(
                    (unity - 1.0).abs() < 1e-10,
                    "Unity constraint failed for n={}: {} * {} = {}",
                    n,
                    alpha[n - 2],
                    alpha[n - 1],
                    unity
                );
            }
        }
    }

    #[test]
    fn test_resonance_with_dynamic_alpha() {
        let alpha8 = alpha_for_bits(8);
        let alpha32 = alpha_for_bits(32);

        // Test some resonance values
        let val = 42u8;
        let r8 = val.r(&alpha8);

        println!("R(42) with 8-bit alpha: {}", r8);

        // Test that different bit lengths produce different alphas
        assert_ne!(
            alpha8[1], alpha32[1],
            "Different bit lengths should produce different alphas"
        );
    }

    #[test]
    fn test_mathematical_vs_calculated() {
        let calc = AlphaVec::<f64>::for_bit_length(8).unwrap();
        let math = AlphaVec::<f64>::mathematical(8).unwrap();

        println!("Calculated alpha for 8 bits:");
        for (i, &val) in calc.values.iter().enumerate() {
            println!("  α[{}] = {}", i, val);
        }

        println!("\nMathematical alpha for 8 bits:");
        for (i, &val) in math.values.iter().enumerate() {
            println!("  α[{}] = {}", i, val);
        }

        // Both should satisfy unity constraint at positions (6,7) for n=8
        assert!(
            (calc[6] * calc[7] - 1.0).abs() < 1e-10,
            "Calculated unity failed: {} * {} = {}",
            calc[6],
            calc[7],
            calc[6] * calc[7]
        );
        assert!(
            (math[6] * math[7] - 1.0).abs() < 1e-10,
            "Mathematical unity failed: {} * {} = {}",
            math[6],
            math[7],
            math[6] * math[7]
        );
    }

    #[test]
    fn test_scaling_property() {
        // Alpha ranges should increase with bit length
        let alpha4 = alpha_for_bits(4);
        let alpha16 = alpha_for_bits(16);
        let alpha64 = alpha_for_bits(64);

        // Calculate dynamic range (max/min)
        let range = |alpha: &AlphaVec<f64>| {
            let max = alpha.values.iter().fold(0.0f64, |a, &b| a.max(b));
            let min = alpha
                .values
                .iter()
                .filter(|&&v| v > 0.0)
                .fold(f64::MAX, |a, &b| a.min(b));
            max / min
        };

        let r4 = range(&alpha4);
        let r16 = range(&alpha16);
        let r64 = range(&alpha64);

        println!("Dynamic range for 4 bits: {}", r4);
        println!("Dynamic range for 16 bits: {}", r16);
        println!("Dynamic range for 64 bits: {}", r64);

        // Larger bit lengths should have larger ranges
        assert!(r16 > r4, "16-bit range should be larger than 4-bit");
        assert!(r64 > r16, "64-bit range should be larger than 16-bit");
    }
}
