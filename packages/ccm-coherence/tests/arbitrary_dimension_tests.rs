//! Comprehensive tests for arbitrary dimension support
//!
//! This test suite verifies that CCM Coherence works correctly across a wide range
//! of dimensions, from small (8) to very large (4096), ensuring that all operations
//! scale appropriately and maintain mathematical correctness.

use ccm_coherence::{
    arbitrary_support::{BigIndex, streaming::*},
    single_blade::SingleBlade,
    sparse_big::SparseBigElement,
    unified::{CliffordAlgebraFactory, UnifiedCliffordAlgebra, CliffordAlgebraTrait},
};
use ccm_core::{CcmError, Float};
use num_complex::Complex;
use num_traits::{One, Zero};

/// Test dimensions as specified in scaling-tasks.md
const TEST_DIMENSIONS: &[usize] = &[8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096];

/// Helper to create appropriate algebra for dimension
fn create_algebra<P: Float>(dimension: usize) -> Result<UnifiedCliffordAlgebra<P>, CcmError> {
    CliffordAlgebraFactory::create(dimension)
}

/// Helper to create BJC-optimized algebra
fn create_bjc_algebra<P: Float>(dimension: usize) -> Result<UnifiedCliffordAlgebra<P>, CcmError> {
    CliffordAlgebraFactory::create_for_bjc(dimension)
}

#[cfg(test)]
mod basic_operations {
    use super::*;

    #[test]
    fn test_algebra_creation_all_dimensions() {
        for &dim in TEST_DIMENSIONS {
            let result = create_algebra::<f64>(dim);
            assert!(result.is_ok(), "Failed to create algebra for dimension {}", dim);
            
            let algebra = result.unwrap();
            assert_eq!(algebra.dimension(), dim);
            
            // Verify appropriate implementation is selected
            let info = algebra.implementation_info();
            match dim {
                8 => assert!(info.contains("Standard")),
                16 => assert!(info.contains("Lazy")),
                32 => assert!(info.contains("Arbitrary")),
                _ => assert!(info.contains("Scalable") || info.contains("Arbitrary")),
            }
        }
    }

    #[test]
    fn test_bjc_algebra_creation() {
        // BJC requires dimension >= 3
        for &dim in &TEST_DIMENSIONS[1..] {  // Skip 8, start from 16
            let result = create_bjc_algebra::<f64>(dim);
            assert!(result.is_ok(), "Failed to create BJC algebra for dimension {}", dim);
            
            let algebra = result.unwrap();
            assert_eq!(algebra.dimension(), dim);
            assert!(!algebra.supports_dense() || dim <= 64);
        }
    }

    #[test]
    fn test_basis_element_creation() {
        for &dim in &[8, 16, 32] {  // Test smaller dimensions where dense is feasible
            let algebra = create_algebra::<f64>(dim).unwrap();
            
            // Test scalar element
            if algebra.supports_dense() {
                let scalar = algebra.basis_element(0);
                assert!(scalar.is_ok());
            }
            
            // Test first basis vector
            if dim <= 20 && algebra.supports_dense() {
                let e0 = algebra.basis_element(1);
                assert!(e0.is_ok());
            }
        }
    }

    #[test]
    fn test_single_blade_operations() {
        for &dim in TEST_DIMENSIONS {
            // Create single blades for all dimensions
            let blade1 = SingleBlade::<f64>::scalar(2.0, dim);
            assert_eq!(blade1.dimension(), dim);
            assert_eq!(blade1.grade(), 0);
            
            // Create a basis vector blade
            let mut index = BigIndex::new(dim);
            index.set_bit(0);
            let blade2 = SingleBlade::<f64>::new(index, Complex::one(), dim);
            assert_eq!(blade2.grade(), 1);
            
            // Test coherence norm
            let norm1 = blade1.coherence_norm();
            assert!(norm1 > 1.99999 && norm1 < 2.00001);
            
            let norm2 = blade2.coherence_norm();
            assert!(norm2 > 0.99999 && norm2 < 1.00001);
        }
    }

    #[test]
    fn test_grade_iteration() {
        // Test grade iteration for various dimensions
        for &dim in &[8, 16, 32, 64, 100] {
            // Count elements of grade 0 (should be 1)
            let iter = ComponentIterator::<f64>::grade_only(dim, 0);
            let count = iter.count();
            assert_eq!(count, 1, "Grade 0 should have exactly 1 element for dim {}", dim);
            
            // Count elements of grade 1 (should be dim)
            let iter = ComponentIterator::<f64>::grade_only(dim, 1);
            let count = iter.count();
            assert_eq!(count, dim, "Grade 1 should have {} elements for dim {}", dim, dim);
            
            // Count elements of grade 2 (should be dim*(dim-1)/2)
            if dim <= 20 {  // Only test for smaller dimensions
                let iter = ComponentIterator::<f64>::grade_only(dim, 2);
                let count = iter.count();
                let expected = dim * (dim - 1) / 2;
                assert_eq!(count, expected, "Grade 2 should have {} elements for dim {}", expected, dim);
            }
        }
    }
}

#[cfg(test)]
mod arithmetic_operations {
    use super::*;

    #[test]
    fn test_sparse_element_addition() {
        for &dim in &[32, 64, 128, 256] {
            let mut elem1 = SparseBigElement::<f64>::zero(dim);
            let mut elem2 = SparseBigElement::<f64>::zero(dim);
            
            // Set some components
            let mut idx1 = BigIndex::new(dim);
            idx1.set_bit(0);
            elem1.set_component(&idx1, Complex::new(1.0, 0.0)).unwrap();
            
            let mut idx2 = BigIndex::new(dim);
            idx2.set_bit(1);
            elem2.set_component(&idx2, Complex::new(2.0, 0.0)).unwrap();
            
            // Add elements (need to clone since + consumes)
            let sum = elem1.clone() + elem2.clone();
            
            // Verify result
            assert_eq!(sum.component(&idx1), Some(Complex::new(1.0, 0.0)));
            assert_eq!(sum.component(&idx2), Some(Complex::new(2.0, 0.0)));
            
            // Check coherence norm
            let norm_sq = sum.coherence_norm_squared();
            assert!((norm_sq - 5.0).abs() < 1e-10);  // 1^2 + 2^2 = 5
        }
    }

    #[test]
    fn test_geometric_product() {
        // Test geometric product for various dimensions
        for &dim in &[8, 16, 32, 64, 128] {
            let mut elem1 = SparseBigElement::<f64>::zero(dim);
            let mut elem2 = SparseBigElement::<f64>::zero(dim);
            
            // e_0 * e_1 = e_{0,1}
            let mut idx1 = BigIndex::new(dim);
            idx1.set_bit(0);
            elem1.set_component(&idx1, Complex::one()).unwrap();
            
            let mut idx2 = BigIndex::new(dim);
            idx2.set_bit(1);
            elem2.set_component(&idx2, Complex::one()).unwrap();
            
            let product = elem1.geometric_product(&elem2).unwrap();
            
            // Result should be e_{0,1}
            let mut expected_idx = BigIndex::new(dim);
            expected_idx.set_bit(0);
            expected_idx.set_bit(1);
            
            let result = product.component(&expected_idx);
            assert!(result.is_some());
            assert!((result.unwrap().re - 1.0).abs() < 1e-10);
        }
    }

    #[test]
    fn test_streaming_inner_product() {
        // Test streaming inner product for various dimensions
        for &dim in &[8, 16, 20] {  // Only dimensions where full enumeration is feasible
            let inner_product = StreamingInnerProduct::<f64>::new(dim);
            
            // Create two simple functions
            let a_fn = |idx: &BigIndex| -> Complex<f64> {
                if idx.count_ones() == 1 {
                    Complex::one()
                } else {
                    Complex::zero()
                }
            };
            
            let b_fn = |idx: &BigIndex| -> Complex<f64> {
                if idx.count_ones() == 1 {
                    Complex::one()
                } else {
                    Complex::zero()
                }
            };
            
            let result = inner_product.compute(&a_fn, &b_fn);
            
            // Result should be dim (number of grade-1 basis elements)
            assert!((result.re - dim as f64).abs() < 1e-10);
            assert!(result.im.abs() < 1e-10);
        }
    }

    #[test]
    fn test_sparse_inner_product() {
        // Test sparse inner product for large dimensions
        for &dim in &[64, 128, 256, 512] {
            let inner_product = StreamingInnerProduct::<f64>::new(dim);
            
            // Create sparse elements
            let mut components_a = Vec::new();
            let mut components_b = Vec::new();
            
            // Add a few components
            for i in 0..5 {
                let mut idx = BigIndex::new(dim);
                idx.set_bit(i);
                components_a.push((idx.clone(), Complex::new((i + 1) as f64, 0.0)));
                components_b.push((idx, Complex::new(1.0, 0.0)));
            }
            
            let result = inner_product.compute_sparse(
                components_a.into_iter(),
                components_b.into_iter()
            );
            
            // Result should be 1 + 2 + 3 + 4 + 5 = 15
            assert!((result.re - 15.0).abs() < 1e-10);
            assert!(result.im.abs() < 1e-10);
        }
    }
}

#[cfg(test)]
mod memory_verification {
    use super::*;

    #[test]
    fn test_memory_estimates() {
        for &dim in TEST_DIMENSIONS {
            let algebra = create_algebra::<f64>(dim).unwrap();
            let mem_mb = algebra.memory_estimate_mb();
            
            match dim {
                8 => assert!(mem_mb < 1),      // 2^8 * 16 bytes < 1MB
                16 => assert!(mem_mb < 10),     // Lazy, should be efficient
                32 => {
                    // Arbitrary algebra for dim 32 should show sparse memory usage
                    // If showing 0, it means it's using sparse storage which is correct
                    assert!(mem_mb < 100);
                }
                _ => assert!(mem_mb < 10),      // Scalable, minimal memory
            }
            
            println!("Dimension {}: {} MB estimated (implementation: {})", 
                     dim, mem_mb, algebra.implementation_info());
        }
    }

    #[test]
    fn test_sparse_element_memory() {
        // Verify that sparse elements use memory proportional to non-zero components
        for &dim in &[256, 512, 1024, 2048, 4096] {
            let mut elem = SparseBigElement::<f64>::zero(dim);
            
            // Add exactly 10 components
            for i in 0..10 {
                let mut idx = BigIndex::new(dim);
                idx.set_bit(i * 10);  // Spread them out
                elem.set_component(&idx, Complex::one()).unwrap();
            }
            
            // Memory should be O(10) not O(2^dim)
            assert_eq!(elem.nnz(), 10);
        }
    }
}

#[cfg(test)]
mod mathematical_properties {
    use super::*;

    #[test]
    fn test_grade_orthogonality() {
        // Verify that coherence inner product respects grade orthogonality
        for &dim in &[8, 16, 32] {
            // Create elements of different grades
            let mut grade1_elem = SparseBigElement::<f64>::zero(dim);
            let mut grade2_elem = SparseBigElement::<f64>::zero(dim);
            
            // Grade 1: single bit set
            let mut idx1 = BigIndex::new(dim);
            idx1.set_bit(0);
            grade1_elem.set_component(&idx1, Complex::one()).unwrap();
            
            // Grade 2: two bits set
            let mut idx2 = BigIndex::new(dim);
            idx2.set_bit(1);
            idx2.set_bit(2);
            grade2_elem.set_component(&idx2, Complex::one()).unwrap();
            
            // Inner product should be zero (grade orthogonality)
            let inner = StreamingInnerProduct::<f64>::new(dim);
            
            // Create component vectors directly
            let components1 = vec![(idx1.clone(), Complex::one())];
            let components2 = vec![(idx2.clone(), Complex::one())];
            
            let result = inner.compute_sparse(
                components1.into_iter(),
                components2.into_iter()
            );
            
            assert!(result.norm() < 1e-10, "Grade orthogonality violated for dim {}", dim);
        }
    }

    #[test]
    fn test_anticommutation() {
        // Test that e_i * e_j = -e_j * e_i for i ≠ j
        for &dim in &[8, 16, 32, 64] {
            let mut e0 = SparseBigElement::<f64>::zero(dim);
            let mut e1 = SparseBigElement::<f64>::zero(dim);
            
            let mut idx0 = BigIndex::new(dim);
            idx0.set_bit(0);
            e0.set_component(&idx0, Complex::one()).unwrap();
            
            let mut idx1 = BigIndex::new(dim);
            idx1.set_bit(1);
            e1.set_component(&idx1, Complex::one()).unwrap();
            
            // Compute e0 * e1 and e1 * e0
            let prod01 = e0.geometric_product(&e1).unwrap();
            let prod10 = e1.geometric_product(&e0).unwrap();
            
            // They should be negatives of each other
            let sum = prod01 + prod10;
            assert!(sum.coherence_norm() < 1e-10, 
                   "Anticommutation failed for dim {}", dim);
        }
    }

    #[test]
    fn test_basis_element_norm() {
        // All basis elements should have unit coherence norm
        for &dim in &[8, 16, 32] {
            // Test a few basis elements
            for i in 0..dim.min(10) {
                let mut idx = BigIndex::new(dim);
                idx.set_bit(i);
                
                let blade = SingleBlade::<f64>::new(idx, Complex::one(), dim);
                let norm = blade.coherence_norm();
                
                assert!(norm > 0.99999 && norm < 1.00001,
                       "Basis element {} has non-unit norm {} in dim {}",
                       i, norm, dim);
            }
        }
    }

    #[test]
    fn test_associativity() {
        // Test (a * b) * c = a * (b * c)
        for &dim in &[8, 16, 32] {
            let mut a = SparseBigElement::<f64>::zero(dim);
            let mut b = SparseBigElement::<f64>::zero(dim);
            let mut c = SparseBigElement::<f64>::zero(dim);
            
            // Set different components
            let mut idx_a = BigIndex::new(dim);
            idx_a.set_bit(0);
            a.set_component(&idx_a, Complex::new(2.0, 0.0)).unwrap();
            
            let mut idx_b = BigIndex::new(dim);
            idx_b.set_bit(1);
            b.set_component(&idx_b, Complex::new(3.0, 0.0)).unwrap();
            
            let mut idx_c = BigIndex::new(dim);
            idx_c.set_bit(2);
            c.set_component(&idx_c, Complex::new(4.0, 0.0)).unwrap();
            
            // Compute (a * b) * c
            let ab = a.geometric_product(&b).unwrap();
            let ab_c = ab.geometric_product(&c).unwrap();
            
            // Compute a * (b * c)
            let bc = b.geometric_product(&c).unwrap();
            let a_bc = a.geometric_product(&bc).unwrap();
            
            // Compare results
            let diff = ab_c - a_bc;
            assert!(diff.coherence_norm() < 1e-10,
                   "Associativity failed for dim {}", dim);
        }
    }
}

#[cfg(test)]
mod edge_cases {
    use super::*;

    #[test]
    fn test_zero_dimension() {
        let result = create_algebra::<f64>(0);
        assert!(result.is_err());
    }

    #[test]
    fn test_dimension_limits() {
        // Test dimension just at the limit
        let result = create_algebra::<f64>(4096);
        assert!(result.is_ok());
        
        // Test dimension over the limit
        let result = create_algebra::<f64>(5000);
        assert!(result.is_err());
    }

    #[test]
    fn test_empty_sparse_elements() {
        for &dim in &[64, 128, 256] {
            let elem = SparseBigElement::<f64>::zero(dim);
            assert_eq!(elem.nnz(), 0);
            assert_eq!(elem.coherence_norm(), 0.0);
        }
    }

    #[test]
    fn test_large_index_operations() {
        // Test operations with indices near the dimension limit
        let dim = 4096;
        let mut idx = BigIndex::new(dim);
        
        // Set bits near the end
        idx.set_bit(4000);
        idx.set_bit(4090);
        idx.set_bit(4095);
        
        assert_eq!(idx.count_ones(), 3);
        
        let blade = SingleBlade::<f64>::new(idx, Complex::one(), dim);
        assert_eq!(blade.grade(), 3);
    }

    #[test]
    fn test_numerical_stability() {
        // Test with very small and very large coefficients
        for &dim in &[32, 64, 128] {
            let mut elem = SparseBigElement::<f64>::zero(dim);
            
            // Very small coefficient
            let mut idx1 = BigIndex::new(dim);
            idx1.set_bit(0);
            elem.set_component(&idx1, Complex::new(1e-15, 0.0)).unwrap();
            
            // Very large coefficient
            let mut idx2 = BigIndex::new(dim);
            idx2.set_bit(1);
            elem.set_component(&idx2, Complex::new(1e15, 0.0)).unwrap();
            
            // Norm should handle both
            let norm = elem.coherence_norm();
            assert!(norm > 0.0);
            assert!(norm.is_finite());
        }
    }
}

#[cfg(all(test, not(debug_assertions)))]  // Only run in release mode
mod performance_benchmarks {
    use super::*;
    use std::time::Instant;

    #[test]
    fn benchmark_algebra_creation() {
        println!("\n=== Algebra Creation Benchmarks ===");
        
        for &dim in TEST_DIMENSIONS {
            let start = Instant::now();
            let _ = create_algebra::<f64>(dim);
            let duration = start.elapsed();
            
            println!("Dimension {}: {:?}", dim, duration);
        }
    }

    #[test]
    fn benchmark_sparse_operations() {
        println!("\n=== Sparse Operation Benchmarks ===");
        
        for &dim in &[64, 128, 256, 512, 1024] {
            let mut elem1 = SparseBigElement::<f64>::zero(dim);
            let mut elem2 = SparseBigElement::<f64>::zero(dim);
            
            // Add 100 random components
            for i in 0..100 {
                let mut idx = BigIndex::new(dim);
                idx.set_bit(i * 7 % dim);  // Spread them out
                elem1.set_component(&idx, Complex::one()).unwrap();
                elem2.set_component(&idx, Complex::new(2.0, 0.0)).unwrap();
            }
            
            // Benchmark addition
            let start = Instant::now();
            let _ = elem1.clone() + elem2.clone();
            let add_duration = start.elapsed();
            
            // Benchmark geometric product
            let start = Instant::now();
            let _ = elem1.geometric_product(&elem2);
            let mul_duration = start.elapsed();
            
            println!("Dimension {}: add={:?}, multiply={:?}", 
                     dim, add_duration, mul_duration);
        }
    }

    #[test]
    fn benchmark_grade_iteration() {
        println!("\n=== Grade Iteration Benchmarks ===");
        
        for &dim in &[16, 32, 64, 128] {
            for grade in &[1, 2, 3] {
                if *grade > dim {
                    continue;
                }
                
                let start = Instant::now();
                let iter = ComponentIterator::<f64>::grade_only(dim, *grade);
                let count = iter.count();
                let duration = start.elapsed();
                
                println!("Dimension {}, Grade {}: {} elements in {:?}", 
                         dim, grade, count, duration);
            }
        }
    }
}