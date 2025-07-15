//! Integration tests for ccm-symmetry

use ccm_coherence::{coherence_norm, CliffordAlgebra, CliffordElement};
use ccm_core::BitWord;
use ccm_embedding::AlphaVec;
use ccm_symmetry::actions::BitWordAction;
use ccm_symmetry::*;

#[test]
fn test_klein_group_structure() {
    let klein = KleinSymmetry::new(8).unwrap();
    let b = BitWord::from_u8(42);
    let group = klein.klein_group(&b).unwrap();

    // V₄ has exactly 4 elements
    assert_eq!(group.len(), 4);

    // All elements are distinct
    for i in 0..4 {
        for j in i + 1..4 {
            assert_ne!(group[i], group[j]);
        }
    }

    // The Klein group elements form a coset of the actual Klein subgroup
    // The actual Klein subgroup V₄ = {0, flip_bit_6, flip_bit_7, flip_both}
    // Our 4 elements are: b + V₄ for some base element b

    // Check that differences between elements follow Klein group structure
    let mut differences = Vec::new();
    for i in 0..4 {
        for j in i + 1..4 {
            let diff = &group[i] ^ &group[j];
            differences.push(diff);
        }
    }

    // Should have 3 distinct differences (excluding identity)
    // These correspond to the 3 non-identity elements of V₄
    assert_eq!(differences.len(), 6); // 4 choose 2 = 6

    // The differences should only involve the last 2 bits
    for diff in &differences {
        // Convert to u8 to check which bits are set
        let val = diff.to_usize() as u8;
        // Only bits 6 and 7 should potentially be set in the differences
        assert_eq!(
            val & 0b00111111,
            0,
            "Differences should only involve bits 6 and 7"
        );
    }
}

#[test]
fn test_resonance_automorphism_composition() {
    let auto1 = ResonanceAutomorphism {
        factor_48: 1,
        factor_256: 1,
        offset_48: 5,
        offset_256: 10,
    };

    let auto2 = ResonanceAutomorphism {
        factor_48: 1,
        factor_256: 1,
        offset_48: 3,
        offset_256: 20,
    };

    let composed = auto1.compose(&auto2);

    // Test on a value
    let x = 100;
    let y1 = auto2.apply(x);
    let y2 = auto1.apply(y1);
    let y_composed = composed.apply(x);

    assert_eq!(y2, y_composed);
}

#[test]
fn test_lie_algebra_bracket() {
    // Create a simple Lie algebra (e.g., sl(2))
    let mut structure = vec![vec![vec![0.0; 3]; 3]; 3];

    // [e_0, e_1] = e_2
    structure[0][1][2] = 1.0;
    structure[1][0][2] = -1.0;

    // [e_1, e_2] = e_0
    structure[1][2][0] = 1.0;
    structure[2][1][0] = -1.0;

    // [e_2, e_0] = e_1
    structure[2][0][1] = 1.0;
    structure[0][2][1] = -1.0;

    let algebra = LieAlgebra::<f64>::from_structure_constants(structure).unwrap();

    // Test bracket computation
    let x = &algebra.basis[0];
    let y = &algebra.basis[1];
    let bracket = algebra.bracket(x, y).unwrap();

    // [e_0, e_1] should equal e_2
    assert!((bracket.coefficients[2] - 1.0).abs() < 1e-10);
    assert!(bracket.coefficients[0].abs() < 1e-10);
    assert!(bracket.coefficients[1].abs() < 1e-10);
}

#[test]
fn test_orbit_computation() {
    let group = SymmetryGroup::<f64>::generate(8).unwrap();
    let action = BitWordAction::new(8);
    let b = BitWord::from_u8(0);

    let orbit = orbits::compute_orbit(&b, &group, &action).unwrap();

    // With no generators, orbit contains only the element itself
    assert_eq!(orbit.size(), 1);
    assert!(orbit.contains(&b));
}

#[test]
fn test_clifford_action_preserves_norm() {
    let algebra = CliffordAlgebra::<f64>::generate(3).unwrap();
    let action = CliffordAction::new(algebra.clone());

    let group = SymmetryGroup::generate(3).unwrap();
    let g = group.identity();

    // Create a test element
    let x = CliffordElement::scalar(2.0, 3) + CliffordElement::basis_vector(0, 3).unwrap();
    let norm_x = coherence_norm(&x);

    // Apply identity transformation
    let gx = action.apply(&g, &x).unwrap();
    let norm_gx = coherence_norm(&gx);

    // Identity should preserve norm exactly
    assert!((norm_x - norm_gx).abs() < 1e-10);
}

#[test]
fn test_invariant_detection() {
    let group = SymmetryGroup::<f64>::generate(4).unwrap();

    // Coherence norm is always invariant
    let coherence_inv = invariants::CoherenceInvariant;
    assert!(coherence_inv.is_invariant(&group));

    // Grade structure is preserved
    let grade_inv = invariants::GradeInvariant { grade: 1 };
    assert!(grade_inv.is_invariant(&group));
}

#[test]
fn test_special_subgroups() {
    // Klein subgroup
    let klein = klein_subgroup::<f64>(8).unwrap();
    assert_eq!(klein.generators().len(), 2); // Two generators for V₄

    // Grade-preserving subgroup
    let grade_preserving = grade_preserving_subgroup::<f64>(3).unwrap();
    assert!(grade_preserving.generators().len() > 0);

    // Resonance-preserving subgroup
    let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();
    let resonance_preserving = resonance_preserving_subgroup(&alpha).unwrap();
    assert!(resonance_preserving.generators().len() > 0);
}

#[test]
fn test_group_axiom_verification() {
    let group = SymmetryGroup::<f64>::generate(3).unwrap();
    let verifier = GroupAxiomVerifier::new(group);

    // All axioms should be satisfied
    assert!(verifier.verify_identity().unwrap());
    assert!(verifier.verify_closure().unwrap());
    assert!(verifier.verify_all().unwrap());
}

#[test]
fn test_conservation_laws() {
    // Resonance current conservation
    let conserved = invariants::resonance_current_conservation::<f64>();
    assert_eq!(conserved.name, "Resonance Current");

    // The conserved quantity should be zero (sum of currents)
    let x = CliffordElement::scalar(1.0, 8);
    let value = conserved.evaluate(&x);
    assert!(value.abs() < 1e-10);
}

#[test]
fn test_noether_correspondence() {
    let symmetry = LieAlgebraElement::zero(3);
    let conserved = invariants::noether_correspondence(&symmetry);

    assert_eq!(conserved.name, "Energy");

    // Test evaluation
    let x = CliffordElement::scalar(2.0, 3);
    let energy = conserved.evaluate(&x);
    assert!(energy > 0.0); // Energy (norm squared) is positive
}

#[cfg(test)]
mod performance_tests {
    use super::*;

    #[test]
    #[ignore] // Run with --ignored flag
    fn test_large_orbit_computation() {
        let mut group = SymmetryGroup::<f64>::generate(16).unwrap();

        // Add some generators
        for i in 0..5 {
            let mut params = vec![1.0; 16];
            params[i] = 1.5;
            let elem = group.element(&params).unwrap();
            group.add_generator(elem).unwrap();
        }

        let action = BitWordAction::new(8);
        let b = BitWord::from_bytes(&[0u8, 0u8]);

        let start = std::time::Instant::now();
        let orbit = orbits::compute_orbit(&b, &group, &action).unwrap();
        let elapsed = start.elapsed();

        println!("Orbit computation took: {:?}", elapsed);
        println!("Orbit size: {}", orbit.size());

        // Should complete in reasonable time
        assert!(elapsed.as_secs() < 5);
    }
}
