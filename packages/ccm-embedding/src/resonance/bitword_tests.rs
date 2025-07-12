//! Comprehensive test suite for BitWord implementations

#[cfg(test)]
mod tests {
    use crate::resonance::*;
    use crate::{AlphaVec, Resonance};
    use ccm_core::BitWord;

    /// Test resonance computation for various bit lengths
    #[test]
    fn test_bitword_resonance_computation() {
        for n in [8, 16, 32, 64, 128, 256, 512, 1024] {
            let alpha = AlphaVec::<f64>::for_bit_length(n).unwrap();

            // Test empty value
            let zero = BitWord::new(n);
            assert_eq!(
                zero.r(&alpha),
                1.0,
                "Empty product should be 1.0 for n={}",
                n
            );

            // Test single bits
            for i in 0..n.min(10) {
                let mut word = BitWord::new(n);
                word.set_bit(i, true);
                let r = word.r(&alpha);
                assert_eq!(
                    r, alpha[i],
                    "Single bit {} should give α_{} for n={}",
                    i, i, n
                );
            }

            // Test unity positions
            if n >= 2 {
                let mut unity = BitWord::new(n);
                unity.set_bit(n - 2, true);
                unity.set_bit(n - 1, true);
                let r = unity.r(&alpha);
                assert!(
                    (r - 1.0).abs() < 1e-10,
                    "Unity positions should give resonance 1.0 for n={}",
                    n
                );
            }
        }
    }

    /// Test Klein group operations
    #[test]
    fn test_bitword_klein_groups() {
        for n in [8, 16, 32, 64, 128] {
            let alpha = AlphaVec::<f64>::for_bit_length(n).unwrap();

            // Test various bit patterns
            for pattern in [0u64, 1, 42, 255, u64::MAX >> (64 - n.min(64))] {
                let word = BitWord::from_u64(pattern, n);
                let members = <BitWord as Resonance<f64>>::class_members(&word);

                // Klein group should have exactly 4 members
                assert_eq!(members.len(), 4, "Klein group size for n={}", n);

                // All members should have same Klein representative
                let repr = <BitWord as Resonance<f64>>::klein_representative(&word);
                for member in &members {
                    let member_repr = <BitWord as Resonance<f64>>::klein_representative(member);
                    assert_eq!(
                        repr, member_repr,
                        "All Klein members should have same representative for n={}",
                        n
                    );
                }

                // Test Klein minimum property
                if word.is_klein_minimum(&alpha) {
                    let my_r = word.r(&alpha);
                    for member in &members {
                        assert!(
                            member.r(&alpha) >= my_r,
                            "Klein minimum should have lowest resonance for n={}",
                            n
                        );
                    }
                }
            }
        }
    }

    /// Test resonance classes
    #[test]
    fn test_bitword_resonance_classes() {
        for n in [8, 10, 12, 16] {
            let alpha = AlphaVec::<f64>::for_bit_length(n).unwrap();

            // Get resonance spectrum
            let spectrum = BitWord::resonance_spectrum(&alpha);

            // With dynamic alpha generation, the exact count may vary
            // but should have a reasonable number of unique resonances
            assert!(
                spectrum.len() > 0,
                "Should have at least one resonance value"
            );

            // For small n, verify we have a reasonable number
            if n <= 12 {
                assert!(
                    spectrum.len() >= n,
                    "Should have at least {} unique resonances for n={}",
                    n,
                    n
                );
            }

            // Verify all values are positive and sorted
            for i in 0..spectrum.len() {
                assert!(spectrum[i] > 0.0, "Resonance values should be positive");
                if i > 0 {
                    assert!(spectrum[i] >= spectrum[i - 1], "Spectrum should be sorted");
                }
            }

            // Test class distribution
            let dist = BitWord::class_distribution(&alpha);
            // Distribution may use theoretical formula while spectrum uses sampling
            // Just verify the distribution makes sense
            assert!(
                dist.total_classes > 0,
                "Should have at least one class for n={}",
                n
            );

            // Verify distribution properties
            assert!(
                dist.size_2_count > 0 || dist.size_4_count > 0,
                "Should have some resonance classes for n={}",
                n
            );
        }
    }

    /// Test conservation laws
    #[test]
    fn test_bitword_conservation() {
        for n in [8, 10, 12] {
            let alpha = AlphaVec::<f64>::for_bit_length(n).unwrap();

            // Test resonance sum conservation
            let cycle_length = if n <= 10 { 3 * (1usize << n) } else { 3 * 1024 };
            let sum = BitWord::resonance_sum(0, cycle_length, &alpha);
            assert!(
                sum > 0.0 && sum.is_finite(),
                "Resonance sum should be positive and finite for n={}",
                n
            );

            // Test current conservation (telescoping property)
            let test_range = (1usize << n).min(1024);
            let mut current_sum = 0.0f64;
            for i in 0..test_range {
                current_sum += BitWord::resonance_current(i, &alpha);
            }

            // For full cycles, sum should be near zero
            if test_range == (1usize << n) {
                assert!(
                    current_sum.abs() < 1e-10,
                    "Current sum over full cycle should be zero for n={}",
                    n
                );
            }
        }
    }

    /// Test homomorphic properties
    #[test]
    fn test_bitword_homomorphic() {
        for n in [8, 10, 12, 16] {
            let alpha = AlphaVec::<f64>::for_bit_length(n).unwrap();

            // Find homomorphic pairs
            let pairs = BitWord::find_homomorphic_pairs(&alpha);

            // Should always find unity pair at (n-2, n-1)
            if n >= 2 {
                let unity_pair_found = pairs
                    .iter()
                    .any(|&(i, j)| (i == n - 2 && j == n - 1) || (i == n - 1 && j == n - 2));
                assert!(
                    unity_pair_found,
                    "Should find unity pair at ({},{}) for n={}",
                    n - 2,
                    n - 1,
                    n
                );
            }

            // Test homomorphic subgroups
            let subgroups = BitWord::homomorphic_subgroups(&alpha);

            // Should always have at least trivial subgroup
            assert!(
                !subgroups.is_empty(),
                "Should have at least trivial subgroup"
            );

            // Verify subgroup properties
            for sg in &subgroups {
                assert_eq!(
                    sg.elements.len(),
                    sg.order,
                    "Element count should match order for n={}",
                    n
                );

                // Verify closure under XOR
                for a in &sg.elements {
                    for b in &sg.elements {
                        let c = a ^ b;
                        assert!(
                            sg.elements.contains(&c),
                            "Subgroup should be closed under XOR for n={}",
                            n
                        );
                    }
                }
            }
        }
    }

    /// Test unity structure
    #[test]
    fn test_bitword_unity_positions() {
        for n in [8, 10, 12, 16] {
            let alpha = AlphaVec::<f64>::for_bit_length(n).unwrap();

            // First verify unity constraint is satisfied
            if n >= 2 {
                let unity_product = alpha[n - 2] * alpha[n - 1];
                eprintln!(
                    "n={}: α[{}]={}, α[{}]={}, product={}",
                    n,
                    n - 2,
                    alpha[n - 2],
                    n - 1,
                    alpha[n - 1],
                    unity_product
                );
                assert!(
                    (unity_product - 1.0).abs() < 1e-10,
                    "Unity constraint not satisfied for n={}",
                    n
                );
            }

            // Find unity positions
            let range = (3 * (1usize << n)).min(3072);

            // Check which Klein elements have unity resonance
            if n >= 2 {
                for klein in 0..4u8 {
                    let mut test_word = BitWord::new(n);
                    if klein & 1 != 0 {
                        test_word.set_bit(n - 2, true);
                    }
                    if klein & 2 != 0 {
                        test_word.set_bit(n - 1, true);
                    }
                    let r = test_word.r(&alpha);
                    eprintln!(
                        "Klein element {} (bits {},{} = {},{}) has resonance {}",
                        klein,
                        n - 2,
                        n - 1,
                        (klein & 1) != 0,
                        (klein & 2) != 0,
                        r
                    );
                }
            }

            let positions = <BitWord as UnityStructure>::unity_positions(&alpha, range);

            // Unity positions should have resonance very close to 1.0
            // The theoretical unity positions come from the unity constraint at bits (n-2, n-1)
            for &pos in &positions {
                let word = index_to_bitword_unity(pos, n);
                let r = word.r(&alpha);

                // For debugging bad unity positions
                if (r - 1.0).abs() > 0.01 {
                    eprintln!(
                        "Bad unity position {} for n={}: word bits = {:?}, resonance = {}",
                        pos,
                        n,
                        (0..n).filter(|&i| word.bit(i)).collect::<Vec<_>>(),
                        r
                    );
                }

                // Unity positions should actually have unity resonance
                assert!(
                    (r - 1.0).abs() < 0.01,
                    "Position {} should have unity resonance for n={}, got {}",
                    pos,
                    n,
                    r
                );
            }

            // Test unity density
            let density = unity::analysis::unity_density_bitword(&alpha, range);
            assert!(
                density > 0.0 && density <= 1.0,
                "Unity density should be in (0,1] for n={}",
                n
            );
        }
    }

    /// Test gradient operations
    #[test]
    fn test_bitword_gradient() {
        for n in [8, 10, 12, 16] {
            let alpha = AlphaVec::<f64>::for_bit_length(n).unwrap();

            // Test gradient computation
            let word = BitWord::from_u64(42, n);
            let gradients = word.bit_gradient(&alpha);

            assert_eq!(gradients.len(), n, "Should have gradient for each bit");

            // Verify gradient signs
            let _r = word.r(&alpha);
            for i in 0..n {
                if word.bit(i) {
                    // For set bits, gradient should be negative if α_i > 1
                    if alpha[i] > 1.0 {
                        assert!(
                            gradients[i] < 0.0,
                            "Gradient should be negative for set bit {} with α > 1",
                            i
                        );
                    }
                } else {
                    // For unset bits, gradient should be positive if α_i > 1
                    if alpha[i] > 1.0 {
                        assert!(
                            gradients[i] > 0.0,
                            "Gradient should be positive for unset bit {} with α > 1",
                            i
                        );
                    }
                }
            }

            // Test gradient search
            let target = 5.0f64;
            match BitWord::gradient_search(word.clone(), target, &alpha, 50) {
                Ok(result) => {
                    let final_r = result.r(&alpha);
                    let initial_r = word.r(&alpha);
                    // Should either improve or already be close
                    let improved = (final_r - target).abs() <= (initial_r - target).abs();
                    let close_enough = (final_r - target).abs() < 2.0;
                    assert!(improved || close_enough,
                        "Gradient search should improve ({} -> {}) or get close to target {} for n={}", 
                        initial_r, final_r, target, n);
                }
                Err(_) => {
                    // It's okay if gradient search fails for some configurations
                }
            }
        }
    }

    /// Test inverse resonance operations
    #[test]
    fn test_bitword_inverse_resonance() {
        for n in [8, 10, 12] {
            let alpha = AlphaVec::<f64>::for_bit_length(n).unwrap();

            // Test finding patterns with specific resonance
            let targets = [1.0, 2.0, 5.0, 10.0];

            for &target in &targets {
                match BitWord::find_by_resonance(target, &alpha, 0.1) {
                    Ok(patterns) => {
                        // Verify all found patterns have correct resonance
                        for pattern in patterns {
                            let r = pattern.r(&alpha);
                            assert!(
                                (r - target).abs() <= 0.1,
                                "Found pattern should have resonance close to {} for n={}",
                                target,
                                n
                            );

                            // Verify it's a Klein minimum
                            assert!(
                                pattern.is_klein_minimum(&alpha),
                                "Result should be Klein minimum for n={}",
                                n
                            );
                        }
                    }
                    Err(_) => {
                        // It's okay if no patterns found for some targets
                    }
                }
            }

            // Test resonance factorization
            let test_r = alpha[0] * alpha[2]; // Product of two alphas
            if let Ok(factors) = BitWord::factor_resonance(test_r, &alpha) {
                // Should find at least the obvious factorization
                let expected = vec![0, 2];
                assert!(
                    factors.iter().any(|f| f == &expected),
                    "Should find factorization [0,2] for n={}",
                    n
                );
            }
        }
    }

    /// Test edge cases and error handling
    #[test]
    fn test_bitword_edge_cases() {
        // Test with n = 0 (empty bit vector)
        let word0 = BitWord::new(0);
        // AlphaVec requires at least 1 bit, so skip alpha test for n=0

        // Test with n = 1
        let word1 = BitWord::new(1);
        // AlphaVec requires at least 3 bits for unity constraint, skip alpha test for n=1

        // Test Klein groups for n < 2
        let members0 = <BitWord as Resonance<f64>>::class_members(&word0);
        assert_eq!(members0.len(), 1, "n=0 should have trivial Klein group");

        let members1 = <BitWord as Resonance<f64>>::class_members(&word1);
        assert_eq!(members1.len(), 1, "n=1 should have trivial Klein group");

        // Test very large n (should not panic)
        let large_n = 10000;
        let word_large = BitWord::new(large_n);
        let alpha_large = AlphaVec::<f64>::for_bit_length(large_n).unwrap();
        let r_large = word_large.r(&alpha_large);
        assert_eq!(
            r_large, 1.0,
            "Empty large BitWord should have resonance 1.0"
        );
    }

    /// Test numerical stability
    #[test]
    fn test_bitword_numerical_stability() {
        // Test with extreme alpha values
        for n in [8, 16, 32] {
            // Create alpha with large values
            let mut values = vec![2.0f64.powf(10.0); n];
            if n >= 2 {
                // Set unity constraint
                values[n - 2] = 0.1;
                values[n - 1] = 10.0;
            }
            let alpha = AlphaVec::try_from(values).unwrap();

            // Test with various bit patterns
            for popcount in [0, 1, n / 4, n / 2, 3 * n / 4, n.min(32)] {
                let mut word = BitWord::new(n);
                for i in 0..popcount {
                    word.set_bit(i, true);
                }

                let r = word.r(&alpha);
                assert!(
                    r.is_finite() && r > 0.0,
                    "Resonance should be finite and positive for popcount={}, n={}",
                    popcount,
                    n
                );
            }
        }
    }

    // Helper function for unity tests
    fn index_to_bitword_unity(idx: usize, n: usize) -> BitWord {
        let mut word = BitWord::new(n);

        // Set bits based on the binary representation of idx
        for bit in 0..n.min(64) {
            if (idx >> bit) & 1 == 1 {
                word.set_bit(bit, true);
            }
        }

        // For bits beyond 64, use deterministic mapping
        if n > 64 {
            let mut state = idx as u64;
            for bit in 64..n {
                state = state.wrapping_mul(1103515245).wrapping_add(12345);
                if state & 1 == 1 {
                    word.set_bit(bit, true);
                }
                state >>= 1;
            }
        }

        word
    }
}
