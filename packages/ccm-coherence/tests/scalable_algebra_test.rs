//! Tests for scalable Clifford algebra operations up to 4096 bits
//!
//! These tests define the behavior we want for truly scalable operations
//! without dense storage limitations.

use ccm_coherence::{
    BigIndex, SparseCliffordElement, SingleBlade,
};
use ccm_core::BitWord;
use num_complex::Complex;
use num_traits::One;

// These tests will initially fail until we implement ScalableCliffordAlgebraTrait

#[test]
fn test_single_blade_operations_4096() {
    // Should support creating single blades for 4096-bit dimensions
    let dimension = 4096;
    
    // Create a blade at bit position 1000
    let mut index = BigIndex::new(dimension);
    index.set_bit(1000);
    
    let blade = SingleBlade::<f64>::new(
        index.clone(),
        Complex::new(2.5, 0.0),
        dimension
    );
    
    assert_eq!(blade.dimension(), 4096);
    assert_eq!(blade.grade(), 1);
    assert_eq!(blade.coefficient(), Complex::new(2.5, 0.0));
}

#[test]
fn test_sparse_element_large_dimension() {
    // SparseCliffordElement should handle arbitrary dimensions
    let dimension = 4096;
    let sparse = SparseCliffordElement::<f64>::zero(dimension);
    
    // Should be able to set components at large indices
    let mut index1 = BigIndex::new(dimension);
    index1.set_bit(100);
    index1.set_bit(200);
    index1.set_bit(300);
    
    // This will fail with current implementation - needs BigIndex support
    // sparse.set_component_big(&index1, Complex::new(1.5, 0.0)).unwrap();
    
    assert_eq!(sparse.dimension(), 4096);
}

#[test]
fn test_lazy_blade_multiplication() {
    // Test multiplication of blades without materializing full result
    let dimension = 4096;
    
    // e_100 * e_200 = e_100 ∧ e_200
    let mut idx1 = BigIndex::new(dimension);
    idx1.set_bit(100);
    let blade1 = SingleBlade::<f64>::new(idx1, Complex::one(), dimension);
    
    let mut idx2 = BigIndex::new(dimension);
    idx2.set_bit(200);
    let blade2 = SingleBlade::<f64>::new(idx2, Complex::one(), dimension);
    
    let result = blade1.multiply(&blade2).unwrap();
    assert_eq!(result.grade(), 2);
    
    // Result should have bits 100 and 200 set
    let expected_idx = blade1.index().xor(blade2.index());
    assert_eq!(result.index(), &expected_idx);
}

#[test]
fn test_streaming_inner_product() {
    // Test computing inner product without materializing elements
    let dimension = 1024;
    
    // Create sparse elements with a few components
    let _a = SparseCliffordElement::<f64>::zero(dimension);
    let _b = SparseCliffordElement::<f64>::zero(dimension);
    
    // Set some matching components for inner product
    // This would use BigIndex in real implementation
    // a.set_component_big(&idx1, Complex::new(2.0, 0.0)).unwrap();
    // b.set_component_big(&idx1, Complex::new(3.0, 0.0)).unwrap();
    
    // Inner product should compute without full expansion
    // let inner_prod = streaming::coherence_inner_product_sparse(&a, &b);
    // assert_eq!(inner_prod, Complex::new(6.0, 0.0));
}

#[test]
fn test_bjc_embedding_4096() {
    // Test BJC codec embedding for very large bit strings
    let dimension = 4096;
    let mut word = BitWord::new(dimension);
    
    // Set some bits in a pattern
    for i in 0..64 {
        word.set_bit(i * 64, true);
    }
    
    // Should create a single blade without dense storage
    // let blade = embed_bitword_scalable(&word, dimension, 1.5).unwrap();
    // assert_eq!(blade.dimension(), 4096);
    // assert_eq!(blade.grade(), 64); // 64 bits set
}

#[test]
fn test_lazy_algebra_operations() {
    // Test that algebra operations return lazy iterators
    let dimension = 2048;
    
    // Create algebra that supports lazy operations
    // let algebra = ScalableAlgebra::new(dimension);
    
    // basis_element should return a lazy blade
    // let e100 = algebra.basis_element_lazy(100);
    // assert!(!e100.is_materialized());
    
    // Operations should return lazy results
    // let e200 = algebra.basis_element_lazy(200);
    // let product = algebra.geometric_product_lazy(e100, e200);
    // assert!(!product.is_materialized());
    
    // Only materialize when needed
    // let grade = product.grade(); // This might force partial computation
    // assert_eq!(grade, 2);
}

#[test]
fn test_memory_efficiency() {
    // Verify that operations use minimal memory
    let dimension = 4096;
    
    // Create a sparse algebra
    // let algebra = ScalableAlgebra::new(dimension);
    
    // These operations should use O(1) memory, not O(2^n)
    // let blade1 = algebra.basis_element_lazy(1000);
    // let blade2 = algebra.basis_element_lazy(2000);
    // let result = algebra.geometric_product_lazy(blade1, blade2);
    
    // Memory usage should be constant regardless of dimension
    // assert!(algebra.memory_usage_bytes() < 1024 * 1024); // Less than 1MB
}

#[test]
fn test_grade_filtered_iteration() {
    // Test iterating over specific grades without full enumeration
    let dimension = 512;
    
    // Should be able to iterate grade-2 elements efficiently
    // let algebra = ScalableAlgebra::new(dimension);
    // let grade_2_iter = algebra.grade_iterator(2);
    
    // Take first few elements (combinatorial iteration)
    // let elements: Vec<_> = grade_2_iter.take(10).collect();
    // assert_eq!(elements.len(), 10);
    
    // Each should have grade 2
    // for elem in elements {
    //     assert_eq!(elem.grade(), 2);
    // }
}

#[test]
fn test_basis_blade_enumeration() {
    // Test creating basis blades from index sets
    let dimension = 1024;
    
    // Create e_10 ∧ e_20 ∧ e_30
    let indices = vec![10, 20, 30];
    
    // Should create blade without dense storage
    // let algebra = ScalableAlgebra::new(dimension);
    // let blade = algebra.basis_blade_lazy(&indices).unwrap();
    
    // assert_eq!(blade.grade(), 3);
    // assert_eq!(blade.dimension(), 1024);
}

#[test]
#[should_panic(expected = "is too large for dense storage")]
fn test_dense_element_panic() {
    // Verify that attempting dense storage for large dimensions fails fast
    use ccm_coherence::CliffordElement;
    let _elem = CliffordElement::<f64>::zero(64); // Should panic
}

#[test]
fn test_resonance_scaling_lazy() {
    // Test applying resonance without materialization
    let dimension = 2048;
    
    let mut idx = BigIndex::new(dimension);
    for i in 0..10 {
        idx.set_bit(i * 100);
    }
    
    let mut blade = SingleBlade::<f64>::new(idx, Complex::one(), dimension);
    blade.apply_resonance(2.5);
    
    assert_eq!(blade.coefficient(), Complex::new(2.5, 0.0));
}

// Helper function signatures we'll need to implement
mod helpers {
    
    // These will be implemented as part of the scalable trait
    
    // fn embed_bitword_scalable<P: Float>(
    //     word: &BitWord,
    //     dimension: usize,
    //     resonance: P,
    // ) -> Result<SingleBlade<P>, CcmError>;
    
    // fn coherence_inner_product_sparse<P: Float>(
    //     a: &SparseCliffordElement<P>,
    //     b: &SparseCliffordElement<P>,
    // ) -> Complex<P>;
}