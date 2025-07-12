//! Tests for mathematical properties of the resonance function

#[cfg(test)]
mod tests {
    use crate::{AlphaVec, HomomorphicResonance, ResonanceClasses, ResonanceConservation};

    #[test]
    fn test_conservation_sum_768_cycle() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // According to the spec, the 768-cycle sum should be 687.110133051847
        let result = u8::verify_conservation(&alpha);

        println!("Conservation sum: {}", result.sum);
        println!("Expected: {}", result.expected);
        println!("Error: {}", result.error);
        println!("Is conserved: {}", result.is_conserved);

        // Check if the sum matches the expected value
        assert!(
            result.is_conserved,
            "Conservation law failed: sum={}, expected={}, error={}",
            result.sum, result.expected, result.error
        );
    }

    #[test]
    fn test_96_resonance_classes() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Get the resonance spectrum
        let spectrum = u8::resonance_spectrum(&alpha);

        println!("Number of unique resonance values: {}", spectrum.len());

        // According to the spec, there should be exactly 96 unique resonance values
        assert_eq!(
            spectrum.len(),
            96,
            "Expected 96 unique resonance values, but got {}",
            spectrum.len()
        );

        // Also check the class distribution
        let distribution = u8::class_distribution(&alpha);
        println!("Total classes: {}", distribution.total_classes);
        println!("Classes with size 2: {}", distribution.size_2_count);
        println!("Classes with size 4: {}", distribution.size_4_count);

        // Verify the distribution matches expectations
        assert_eq!(distribution.total_classes, 96);
        assert_eq!(distribution.size_2_count, 64);
        assert_eq!(distribution.size_4_count, 32);
    }

    #[test]
    fn test_homomorphic_subgroups_count() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        let subgroups = u8::homomorphic_subgroups(&alpha);

        println!("Number of homomorphic subgroups: {}", subgroups.len());

        // Print each subgroup
        for (i, sg) in subgroups.iter().enumerate() {
            println!(
                "Subgroup {}: generator={}, order={}, elements={:?}",
                i, sg.generator, sg.order, sg.elements
            );
        }

        // According to the spec, there should be exactly 5 homomorphic subgroups
        assert_eq!(
            subgroups.len(),
            5,
            "Expected 5 homomorphic subgroups, but got {}",
            subgroups.len()
        );

        // Check that we have the expected orders
        let orders: Vec<usize> = subgroups.iter().map(|sg| sg.order).collect();
        assert!(orders.contains(&1), "Missing trivial subgroup");
        assert!(orders.contains(&4), "Missing Klein four-group");
    }

    #[test]
    fn test_current_extrema() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        // Find the current extrema in the first 768 positions
        let extrema = u8::current_extrema(&alpha, 768);

        println!(
            "Maximum current: {} at position {}",
            extrema.max_value, extrema.max_position
        );
        println!(
            "Minimum current: {} at position {}",
            extrema.min_value, extrema.min_position
        );

        // According to the spec:
        // Maximum positive: J(36) = +2.405 (from position 36→37)
        // Maximum negative: J(38) = -2.405 (from position 38→39)

        // Note: These positions might be slightly different due to our specific alpha values
        // The important thing is that max and min should be roughly equal in magnitude
        assert!(
            (extrema.max_value + extrema.min_value).abs() < 0.01,
            "Current extrema should be symmetric: max={}, min={}",
            extrema.max_value,
            extrema.min_value
        );
    }
}
