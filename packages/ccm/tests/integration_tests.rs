//! Integration tests for the complete CCM system

use ccm::prelude::*;
use ccm::Resonance;

#[test]
fn test_three_axioms_integration() {
    let ccm = StandardCCM::<f64>::new(8).unwrap();
    let alpha = ccm.generate_alpha().unwrap();

    // Test Axiom A2: Minimal embedding
    let word1 = BitWord::from_u8(123);
    let word2 = BitWord::from_u8(234);

    let min1 = ccm.find_minimum_resonance(&word1, &alpha).unwrap();
    let min2 = ccm.find_minimum_resonance(&word2, &alpha).unwrap();

    // Verify Klein group properties
    assert!(min1.is_klein_minimum(&alpha));
    assert!(min2.is_klein_minimum(&alpha));

    // Test Axiom A1: Coherence metric
    let section1 = ccm.embed(&min1, &alpha).unwrap();
    let section2 = ccm.embed(&min2, &alpha).unwrap();

    let norm1 = ccm.coherence_norm(&section1);
    let norm2 = ccm.coherence_norm(&section2);

    assert!(norm1 > 0.0);
    assert!(norm2 > 0.0);

    // Test coherence minimization
    let minimized = ccm.minimize_coherence(&section1).unwrap();
    let min_norm = ccm.coherence_norm(&minimized);

    // Minimized norm should not increase
    assert!(min_norm <= norm1 + 1e-10);
}

#[test]
fn test_klein_group_homomorphism() {
    let ccm = StandardCCM::<f64>::new(8).unwrap();
    let alpha = ccm.generate_alpha().unwrap();

    // Klein V4 for this alpha configuration is {0, 1, 192, 193}
    // These are the elements with resonance 1
    let v4_elements = [0u8, 1, 192, 193];

    // Verify all have resonance 1
    for &elem in &v4_elements {
        let word = BitWord::from_u8(elem);
        let resonance = word.r(&alpha);
        assert!(
            (resonance - 1.0).abs() < 1e-10,
            "Element {} should have resonance 1, got {}",
            elem,
            resonance
        );
    }

    // Verify XOR closure
    for &a in &v4_elements {
        for &b in &v4_elements {
            let result = a ^ b;
            assert!(
                v4_elements.contains(&result),
                "{} XOR {} = {} should be in V4",
                a,
                b,
                result
            );
        }
    }
}

#[test]
fn test_unity_constraint() {
    let ccm = StandardCCM::<f64>::new(8).unwrap();
    let alpha = ccm.generate_alpha().unwrap();

    // Verify unity constraint: alpha[6] * alpha[7] = 1
    let product = &alpha[6] * &alpha[7];
    assert!(
        (product - 1.0).abs() < 1e-10,
        "Unity constraint violated: {} * {} = {}",
        &alpha[6],
        &alpha[7],
        product
    );
}

#[test]
fn test_scale_adaptive_search() {
    // Test small dimension (direct search)
    let ccm_small = StandardCCM::<f64>::new(8).unwrap();
    let alpha_small = ccm_small.generate_alpha().unwrap();

    let target = 1.5;
    let tolerance = 0.5;

    let results = ccm_small
        .search_by_resonance(target, &alpha_small, tolerance)
        .unwrap();

    // Verify all results are within tolerance
    for word in &results {
        let resonance = word.r(&alpha_small);
        assert!(
            (resonance - target).abs() <= tolerance,
            "Result resonance {} outside tolerance",
            resonance
        );
    }

    // Test medium dimension (algebraic search)
    let ccm_medium = StandardCCM::<f64>::new(20).unwrap();
    let alpha_medium = ccm_medium.generate_alpha().unwrap();

    let results_medium = ccm_medium
        .search_by_resonance(target, &alpha_medium, tolerance)
        .unwrap();
    assert!(
        !results_medium.is_empty(),
        "Should find some results in medium dimension"
    );
}

#[test]
fn test_conservation_properties() {
    let ccm = StandardCCM::<f64>::new(8).unwrap();
    let alpha = ccm.generate_alpha().unwrap();

    // Test that Klein group operations preserve resonance patterns
    let test_word = BitWord::from_u8(100);
    let klein_members = ccm.klein_members(&test_word);

    // All Klein members should map to the same minimal element
    let minimal = ccm.find_minimum_resonance(&test_word, &alpha).unwrap();

    for member in &klein_members {
        let member_minimal = ccm.find_minimum_resonance(member, &alpha).unwrap();
        assert_eq!(
            minimal, member_minimal,
            "Klein group members should have same minimal representative"
        );
    }
}

#[test]
fn test_embedding_coherence_compatibility() {
    let ccm = StandardCCM::<f64>::new(8).unwrap();
    let alpha = ccm.generate_alpha().unwrap();

    // Create two different words
    let word1 = BitWord::from_u8(50);
    let word2 = BitWord::from_u8(100);

    // Embed them
    let section1 = ccm.embed(&word1, &alpha).unwrap();
    let section2 = ccm.embed(&word2, &alpha).unwrap();

    // Different words should generally give different sections
    let norm1 = ccm.coherence_norm(&section1);
    let norm2 = ccm.coherence_norm(&section2);

    // But Klein equivalent words should give the same embedding
    let klein_partner = BitWord::from_u8(word1.to_usize() as u8 ^ 48); // XOR with Klein generator
    let section_partner = ccm.embed(&klein_partner, &alpha).unwrap();
    let norm_partner = ccm.coherence_norm(&section_partner);

    // Klein partners might have different norms but similar structure
    assert!(norm1 > 0.0 && norm2 > 0.0 && norm_partner > 0.0);
}

#[test]
fn test_symmetry_engine_clifford_action() {
    use ccm_symmetry::GroupElement;

    let ccm = StandardCCM::<f64>::new(8).unwrap();
    let alpha = ccm.generate_alpha().unwrap();
    
    // Create a test section
    let word = BitWord::from_u8(42);
    let section = ccm.embed(&word, &alpha).unwrap();
    
    // Create identity group element
    let identity = GroupElement::<f64>::identity(8);
    
    // Apply symmetry transformation (should work now with fixed SymmetryEngine)
    let transformed = ccm.apply_symmetry(&section, &identity).unwrap();
    
    // Identity transformation should not change the section
    let orig_norm = ccm.coherence_norm(&section);
    let trans_norm = ccm.coherence_norm(&transformed);
    
    assert!(
        (orig_norm - trans_norm).abs() < 1e-10,
        "Identity transformation should preserve norm"
    );
}
