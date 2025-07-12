//! Integration tests for ccm-coherence

use ccm_coherence::{
    bitword_to_clifford, coherence_norm, coherence_product, embed_with_resonance, u8_to_clifford,
    CliffordAlgebra, CliffordElement, Section,
};
use ccm_core::BitWord;
use num_complex::Complex;

#[test]
fn test_complete_embedding_workflow() {
    // Create an 8-dimensional Clifford algebra
    let algebra = CliffordAlgebra::<f64>::generate(8).unwrap();

    // Test embedding a u8 value
    let byte = 42u8;
    let element = u8_to_clifford(byte, &algebra).unwrap();

    // Verify the element is in the correct basis position
    assert_eq!(element.component(42), Some(Complex::new(1.0, 0.0)));

    // Test with resonance scaling
    let resonance = 2.5;
    let scaled = embed_with_resonance(&BitWord::from_u8(byte), resonance, &algebra).unwrap();
    assert_eq!(scaled.component(42), Some(Complex::new(2.5, 0.0)));
}

#[test]
fn test_grade_orthogonality_in_coherence_product() {
    let algebra = CliffordAlgebra::<f64>::generate(4).unwrap();

    // Create elements of different grades
    let scalar = CliffordElement::scalar(2.0, 4);
    let vector = algebra.basis_element(1).unwrap(); // e₀
    let bivector = algebra.basis_element(3).unwrap(); // e₀e₁

    // Test grade orthogonality
    let scalar_vector = coherence_product(&scalar, &vector);
    assert!(scalar_vector.norm() < 1e-10);

    let vector_bivector = coherence_product(&vector, &bivector);
    assert!(vector_bivector.norm() < 1e-10);
}

#[test]
fn test_clifford_algebra_operations() {
    let algebra = CliffordAlgebra::<f64>::generate(3).unwrap();

    // Get basis vectors
    let e0 = algebra.basis_element(1).unwrap();
    let e1 = algebra.basis_element(2).unwrap();
    let _e2 = algebra.basis_element(4).unwrap();

    // Test geometric product
    let e01 = algebra.geometric_product(&e0, &e1).unwrap();
    assert_eq!(e01.component(3), Some(Complex::new(1.0, 0.0)));

    // Test wedge product
    let e0_wedge_e1 = algebra.wedge_product(&e0, &e1).unwrap();
    assert_eq!(e0_wedge_e1.component(3), Some(Complex::new(1.0, 0.0)));

    // Test that e₀ ∧ e₀ = 0
    let e0_wedge_e0 = algebra.wedge_product(&e0, &e0).unwrap();
    for i in 0..e0_wedge_e0.num_components() {
        assert!(e0_wedge_e0.component(i).unwrap().norm() < 1e-10);
    }

    // Test inner product
    let e012 = algebra.basis_element(7).unwrap(); // e₀e₁e₂
    let e0_dot_e012 = algebra.inner_product(&e0, &e012).unwrap();
    assert_eq!(e0_dot_e012.component(6), Some(Complex::new(1.0, 0.0))); // e₁e₂
}

#[test]
fn test_section_operations() {
    // Sections are just CliffordElements
    let section1: Section<f64> = CliffordElement::scalar(3.0, 4);
    let section2: Section<f64> = CliffordElement::scalar(4.0, 4);

    // Test coherence norm
    let norm1 = coherence_norm(&section1);
    assert!((norm1 - 3.0).abs() < 1e-10);

    // Test coherence product
    let product = coherence_product(&section1, &section2);
    assert!((product.re - 12.0).abs() < 1e-10);
    assert!(product.im.abs() < 1e-10);
}

#[test]
fn test_grade_decomposition() {
    let _algebra = CliffordAlgebra::<f64>::generate(3).unwrap();

    // Create a mixed-grade element
    let mut element = CliffordElement::zero(3);
    element.set_component(0, Complex::new(1.0, 0.0)).unwrap(); // scalar
    element.set_component(1, Complex::new(2.0, 0.0)).unwrap(); // e₀
    element.set_component(3, Complex::new(3.0, 0.0)).unwrap(); // e₀e₁
    element.set_component(7, Complex::new(4.0, 0.0)).unwrap(); // e₀e₁e₂

    // Test grade extraction
    let grade0 = element.grade(0);
    let grade1 = element.grade(1);
    let grade2 = element.grade(2);
    let grade3 = element.grade(3);

    // Verify each grade
    assert!(grade0.is_k_vector(0));
    assert!(grade1.is_k_vector(1));
    assert!(grade2.is_k_vector(2));
    assert!(grade3.is_k_vector(3));

    // Verify coherence norm is sum of grade norms
    let total_norm_sq = coherence_norm(&element) * coherence_norm(&element);
    let sum_of_grade_norms = coherence_norm(&grade0) * coherence_norm(&grade0)
        + coherence_norm(&grade1) * coherence_norm(&grade1)
        + coherence_norm(&grade2) * coherence_norm(&grade2)
        + coherence_norm(&grade3) * coherence_norm(&grade3);
    let diff: f64 = total_norm_sq - sum_of_grade_norms;
    assert!(diff.abs() < 1e-10);
}

#[test]
fn test_involutions() {
    let mut element = CliffordElement::<f64>::zero(3);
    element.set_component(0, Complex::new(1.0, 0.0)).unwrap(); // grade 0
    element.set_component(1, Complex::new(2.0, 0.0)).unwrap(); // grade 1
    element.set_component(3, Complex::new(3.0, 0.0)).unwrap(); // grade 2
    element.set_component(7, Complex::new(4.0, 0.0)).unwrap(); // grade 3

    // Test grade involution
    let alpha = element.grade_involution();
    assert_eq!(alpha.component(0), Some(Complex::new(1.0, 0.0))); // even grade
    assert_eq!(alpha.component(1), Some(Complex::new(-2.0, 0.0))); // odd grade

    // Test reversion
    let rev = element.reversion();
    assert_eq!(rev.component(0), Some(Complex::new(1.0, 0.0))); // grade 0: unchanged
    assert_eq!(rev.component(1), Some(Complex::new(2.0, 0.0))); // grade 1: unchanged
    assert_eq!(rev.component(3), Some(Complex::new(-3.0, 0.0))); // grade 2: sign change
    assert_eq!(rev.component(7), Some(Complex::new(-4.0, 0.0))); // grade 3: sign change

    // Test double reversion returns original
    let double_rev = rev.reversion();
    for i in 0..element.num_components() {
        let diff = (element.component(i).unwrap() - double_rev.component(i).unwrap()).norm();
        assert!(diff < 1e-10);
    }
}

#[test]
fn test_bitword_embedding() {
    let algebra = CliffordAlgebra::<f64>::generate(8).unwrap();

    // Create a BitWord with specific pattern
    let mut word = BitWord::new(8);
    word.set_bit(0, true);
    word.set_bit(2, true);
    word.set_bit(5, true);

    // Embed into Clifford algebra
    let element = bitword_to_clifford(&word, &algebra).unwrap();

    // Should map to basis element e₀e₂e₅ (index = 1 + 4 + 32 = 37)
    assert_eq!(element.component(37), Some(Complex::new(1.0, 0.0)));

    // All other components should be zero
    for i in 0..element.num_components() {
        if i != 37 {
            assert!(element.component(i).unwrap().norm() < 1e-10);
        }
    }
}

#[test]
fn test_linear_algebra_operations() {
    let algebra = CliffordAlgebra::<f64>::generate(3).unwrap();

    let e0 = algebra.basis_element(1).unwrap();
    let e1 = algebra.basis_element(2).unwrap();

    // Test addition
    let sum = e0.clone() + e1.clone();
    assert_eq!(sum.component(1), Some(Complex::new(1.0, 0.0)));
    assert_eq!(sum.component(2), Some(Complex::new(1.0, 0.0)));

    // Test scalar multiplication
    let scaled = e0.clone() * 3.0;
    assert_eq!(scaled.component(1), Some(Complex::new(3.0, 0.0)));

    // Test negation
    let neg = -e0.clone();
    assert_eq!(neg.component(1), Some(Complex::new(-1.0, 0.0)));
}
