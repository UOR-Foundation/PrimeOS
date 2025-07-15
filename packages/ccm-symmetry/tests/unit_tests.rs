//! Unit tests for individual components

use ccm_symmetry::*;

mod group_tests {
    use super::*;

    #[test]
    fn test_group_element_creation() {
        let elem = GroupElement::<f64>::identity(4);
        assert_eq!(elem.dimension(), 4);
        assert!(elem.is_identity());

        let group = SymmetryGroup::<f64>::generate(4).unwrap();
        let non_identity = group.element(&[1.0, 2.0, 3.0, 4.0]).unwrap();
        assert!(!non_identity.is_identity());
    }

    #[test]
    fn test_symmetry_group_operations() {
        let group = SymmetryGroup::<f64>::generate(3).unwrap();

        let g1 = group.element(&[1.0, 2.0, 3.0]).unwrap();
        let g2 = group.element(&[2.0, 3.0, 4.0]).unwrap();

        let product = group.multiply(&g1, &g2).unwrap();
        assert_eq!(product.params, vec![2.0, 6.0, 12.0]);

        let inverse = group.inverse(&g1).unwrap();
        assert!((inverse.params[0] - 1.0).abs() < 1e-10);
        assert!((inverse.params[1] - 0.5).abs() < 1e-10);
        assert!((inverse.params[2] - 1.0 / 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_group_generator_management() {
        let mut group = SymmetryGroup::<f64>::generate(2).unwrap();
        assert_eq!(group.generators().len(), 0);

        let gen = group.element(&[2.0, 3.0]).unwrap();
        group.add_generator(gen.clone()).unwrap();
        assert_eq!(group.generators().len(), 1);

        // Wrong dimension should fail
        let wrong_group = SymmetryGroup::<f64>::generate(3).unwrap();
        let bad_gen = wrong_group.element(&[1.0, 2.0, 3.0]).unwrap();
        assert!(group.add_generator(bad_gen).is_err());
    }
}

mod discrete_tests {
    use super::*;
    use ccm_core::BitWord;

    #[test]
    fn test_klein_bit_operations() {
        let klein = KleinSymmetry::new(8).unwrap();

        // Test with different bit patterns
        let patterns = [0u8, 0xFF, 0xAA, 0x55, 0x0F, 0xF0];

        for &pattern in &patterns {
            let b = BitWord::from_u8(pattern);
            let group = klein.klein_group(&b).unwrap();

            // Verify Klein group coset property
            // The 4 elements form a coset of V₄, not V₄ itself
            for i in 0..4 {
                for j in i + 1..4 {
                    let diff = &group[i] ^ &group[j];
                    // The difference should only involve the last 2 bits (unity positions)
                    let val = diff.to_usize() as u8;
                    // For 8-bit system, bits 6 and 7 are unity positions
                    assert_eq!(
                        val & 0b00111111,
                        0,
                        "Differences should only involve bits 6 and 7"
                    );
                }
            }
        }
    }

    #[test]
    fn test_resonance_automorphism_properties() {
        let identity = ResonanceAutomorphism::identity();

        // Identity should not change values
        for x in 0..1000 {
            assert_eq!(identity.apply(x), x);
        }

        // Test inverse property
        let auto = ResonanceAutomorphism {
            factor_48: 1,
            factor_256: 1,
            offset_48: 10,
            offset_256: 100,
        };

        let inverse = ResonanceAutomorphism {
            factor_48: 1,
            factor_256: 1,
            offset_48: 38,   // 48 - 10
            offset_256: 156, // 256 - 100
        };

        let _composed = auto.compose(&inverse);

        // Should give identity (approximately)
        for x in 0..100 {
            let y = auto.apply(x);
            let z = inverse.apply(y);
            assert_eq!(z % (48 * 256), x % (48 * 256));
        }
    }
}

mod lie_algebra_tests {
    use super::*;

    #[test]
    fn test_lie_algebra_operations() {
        let x = LieAlgebraElement::<f64>::from_coefficients(vec![1.0, 2.0, 3.0]);
        let y = LieAlgebraElement::from_coefficients(vec![4.0, 5.0, 6.0]);

        // Test scaling
        let scaled = x.scale(2.0);
        assert_eq!(scaled.coefficients, vec![2.0, 4.0, 6.0]);

        // Test addition
        let sum = x.add(&y).unwrap();
        assert_eq!(sum.coefficients, vec![5.0, 7.0, 9.0]);

        // Different dimensions should fail
        let z = LieAlgebraElement::from_coefficients(vec![1.0, 2.0]);
        assert!(x.add(&z).is_err());
    }

    #[test]
    fn test_jacobi_identity() {
        // Create so(3) Lie algebra
        let mut structure = vec![vec![vec![0.0; 3]; 3]; 3];

        // Standard so(3) structure constants
        structure[0][1][2] = 1.0;
        structure[1][0][2] = -1.0;
        structure[1][2][0] = 1.0;
        structure[2][1][0] = -1.0;
        structure[2][0][1] = 1.0;
        structure[0][2][1] = -1.0;

        let algebra = LieAlgebra::<f64>::from_structure_constants(structure).unwrap();

        // Jacobi identity should hold
        assert!(algebra.verify_jacobi_identity());
    }
}

mod invariant_tests {
    use super::*;
    use ccm_coherence::CliffordElement;

    #[test]
    fn test_invariant_functionals() {
        let coherence_inv = invariants::CoherenceInvariant;
        let invariants = coherence_inv.generating_invariants();

        assert_eq!(invariants.len(), 1);

        // Test on an element
        let x = CliffordElement::<f64>::scalar(3.0, 4);
        let norm = invariants[0](&x);
        assert!((norm - 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_grade_invariants() {
        for grade in 0..4 {
            let grade_inv = invariants::GradeInvariant { grade };
            let invariants = grade_inv.generating_invariants();

            assert_eq!(invariants.len(), 1);

            // Test that it extracts the correct grade
            let mut x = CliffordElement::<f64>::zero(3);
            if grade == 0 {
                x = CliffordElement::scalar(2.0, 3);
            } else if grade == 1 {
                x = CliffordElement::basis_vector(0, 3).unwrap();
            }

            let grade_norm = invariants[0](&x);
            if grade <= 1 {
                assert!(grade_norm > 0.0);
            }
        }
    }
}

mod orbit_tests {
    use super::*;

    #[test]
    fn test_orbit_properties() {
        let orbit: Orbit<f64, i32> = Orbit::new(42);

        assert_eq!(orbit.size(), 1);
        assert!(orbit.contains(&42));
        assert!(!orbit.contains(&43));
        assert_eq!(orbit.representative, 42);
    }

    #[test]
    fn test_stabilizer_construction() {
        let mut stabilizer = StabilizerSubgroup::<f64> {
            generators: Vec::new(),
        };
        assert_eq!(stabilizer.generators.len(), 0);

        let g = GroupElement::identity(3);
        stabilizer.generators.push(g);
        assert_eq!(stabilizer.generators.len(), 1);
    }
}

mod verification_tests {
    use super::*;

    #[test]
    fn test_group_axiom_verification_small() {
        // Create a trivial group
        let group = SymmetryGroup::<f64>::generate(1).unwrap();
        let verifier = GroupAxiomVerifier::new(group);

        // Empty group satisfies all axioms trivially
        assert!(verifier.verify_closure().unwrap());
        assert!(verifier.verify_associativity().unwrap());
        assert!(verifier.verify_identity().unwrap());
        assert!(verifier.verify_all().unwrap());
    }

    #[test]
    fn test_tolerance_settings() {
        let group = SymmetryGroup::<f64>::generate(2).unwrap();
        let verifier = GroupAxiomVerifier::new(group).with_tolerance(1e-6);

        // Should still verify with custom tolerance
        assert!(verifier.verify_identity().unwrap());
    }
}
