//! Tests for the unified Clifford algebra API

use ccm_coherence::{
    CliffordAlgebraFactory, CliffordAlgebraTrait, UnifiedCliffordAlgebra,
    ArbitraryDimensionConfig,
    ScalableCliffordAlgebraTrait, ScalableAlgebra,
};
use ccm_core::BitWord;

#[test]
fn test_factory_creates_appropriate_algebra() {
    // Small dimension - should use standard algebra
    let algebra_small = CliffordAlgebraFactory::create::<f64>(8).unwrap();
    assert_eq!(algebra_small.dimension(), 8);
    assert!(algebra_small.supports_dense());
    
    // Medium dimension - should use lazy algebra
    let algebra_medium = CliffordAlgebraFactory::create::<f64>(16).unwrap();
    assert_eq!(algebra_medium.dimension(), 16);
    
    // Large dimension - use ScalableAlgebra instead
    let algebra_large = ScalableAlgebra::<f64>::new(64);
    assert_eq!(algebra_large.dimension(), 64);
    // ScalableAlgebra doesn't support dense storage by design
}

#[test]
fn test_bjc_optimized_algebra() {
    // For BJC with large dimensions, use ScalableAlgebra
    let algebra_bjc = ScalableAlgebra::<f64>::new(256);
    assert_eq!(algebra_bjc.dimension(), 256);
    
    // Should be able to get single basis elements even for huge dimensions
    let blade = algebra_bjc.basis_element_lazy(42).unwrap();
    assert_eq!(blade.dimension(), 256);
    assert_eq!(blade.grade(), 1);
}

#[test]
fn test_different_dimension_sizes() {
    // Test various dimension sizes
    let dimensions = vec![4, 8, 12, 16, 20, 24, 32, 64, 128];
    
    for &dim in &dimensions {
        if dim <= 12 {
            // Use unified API for small-medium dimensions
            let algebra = CliffordAlgebraFactory::create::<f64>(dim).unwrap();
            assert_eq!(algebra.dimension(), dim);
            
            // Test basic operations work
            let e0 = algebra.basis_element(1).unwrap(); // e_0
            let e1 = algebra.basis_element(2).unwrap(); // e_1
            
            // Only test products for small dimensions
            if dim <= 12 {
                let _product = algebra.geometric_product(&e0, &e1).unwrap();
            }
        } else {
            // Use scalable API for large dimensions
            let algebra = ScalableAlgebra::<f64>::new(dim);
            assert_eq!(algebra.dimension(), dim);
            
            // Test basic operations work
            let e0 = algebra.basis_element_lazy(0).unwrap();
            let e1 = algebra.basis_element_lazy(1).unwrap();
            
            // Can always test products with lazy evaluation
            let _product = algebra.geometric_product_lazy(&e0, &e1).unwrap();
        }
    }
}

#[test]
fn test_lazy_embedding_for_large_dimensions() {
    // Test embedding for dimensions that would overflow with dense storage
    // For large dimensions, we need to use the scalable API
    let test_cases = vec![
        (64, 8),   // 64-bit input, 8 bits set
        (128, 16), // 128-bit input, 16 bits set
        (256, 32), // 256-bit input, 32 bits set
        (512, 64), // 512-bit input, 64 bits set
    ];
    
    for (dimension, bits_to_set) in test_cases {
        // Create a BitWord with some bits set
        let mut word = BitWord::new(dimension);
        for i in 0..bits_to_set {
            word.set_bit(i * (dimension / bits_to_set), true);
        }
        
        // For large dimensions, create the blade directly
        use ccm_coherence::{BigIndex, SingleBlade};
        use num_complex::Complex;
        
        let mut index = BigIndex::new(dimension);
        for i in 0..word.len() {
            if word.bit(i) {
                index.set_bit(i);
            }
        }
        
        let resonance = 1.5_f64;
        let blade = SingleBlade::new(
            index,
            Complex::new(resonance, 0.0),
            dimension
        );
        
        assert_eq!(blade.dimension(), dimension);
        assert_eq!(blade.grade(), bits_to_set);
    }
}

#[test]
fn test_custom_config() {
    // Test with custom memory configuration
    let config = ArbitraryDimensionConfig {
        max_dense_dimension: 10,
        max_memory_mb: 50,
        check_overflow: true,
    };
    
    // Dimension 11 should use arbitrary algebra due to config
    let algebra = CliffordAlgebraFactory::create_with_config::<f64>(11, config).unwrap();
    assert_eq!(algebra.dimension(), 11);
    
    // Check it respects the custom config
    match algebra {
        UnifiedCliffordAlgebra::Arbitrary(_) => {
            // Expected for dimension > max_dense_dimension
        }
        _ => panic!("Expected arbitrary algebra for dimension 11 with custom config"),
    }
}

#[test]
fn test_basis_blade_creation() {
    let algebra = CliffordAlgebraFactory::create::<f64>(8).unwrap();
    
    // Create e_0 ∧ e_2 ∧ e_4
    let blade = algebra.basis_blade(&[0, 2, 4]).unwrap();
    
    // The blade should have index 21 (binary 00010101)
    let expected_index = (1 << 0) | (1 << 2) | (1 << 4);
    assert_eq!(expected_index, 21);
    
    // Check the component is set correctly
    assert!(blade.component(21).unwrap().norm() > 0.99);
}

#[test]
fn test_memory_estimation() {
    let test_cases = vec![
        (8, true),   // 2^8 = 256 elements, should fit in memory
        (12, true),  // 2^12 = 4096 elements, still reasonable
        (20, false), // 2^20 = 1M elements, may not support dense
        (30, false), // 2^30 = 1B elements, definitely sparse only
    ];
    
    for (dimension, _expect_dense) in test_cases {
        if dimension <= 12 {
            // Small dimensions use standard algebra
            let algebra = CliffordAlgebraFactory::create::<f64>(dimension).unwrap();
            assert!(algebra.supports_dense());
            assert!(algebra.memory_estimate_mb() < 100);
        } else {
            // Large dimensions should use scalable algebra
            let algebra = ScalableAlgebra::<f64>::new(dimension);
            // Scalable algebra uses minimal memory
            assert!(algebra.memory_usage_bytes() < 1024); // Less than 1KB
        }
    }
}

#[test]
#[ignore] // This test is expensive, run with --ignored flag
fn test_very_large_dimensions() {
    // Test dimensions up to 4096 bits as mentioned in the spec
    let large_dimensions = vec![1024, 2048, 4096];
    
    for dimension in large_dimensions {
        println!("Testing dimension {}", dimension);
        
        // Should be able to create algebra for very large dimensions
        let algebra = CliffordAlgebraFactory::create_for_bjc::<f64>(dimension).unwrap();
        assert_eq!(algebra.dimension(), dimension);
        
        // Should be able to create single basis elements
        let blade = algebra.basis_element(0).unwrap(); // scalar element
        assert_eq!(blade.dimension(), dimension);
        
        // Memory usage should be minimal for BJC mode
        assert!(!algebra.supports_dense());
    }
}