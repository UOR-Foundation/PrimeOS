//! Integration tests for performance optimizations
//!
//! These tests verify that the optimizations provide correct results
//! and measurable performance improvements.

use ccm_coherence::{
    arbitrary_support::BigIndex,
    optimizations::*,
    sparse_big::SparseBigElement,
};
use num_complex::Complex;
use std::time::Instant;

#[test]
fn test_optimization_correctness() {
    // Test that optimized functions produce the same results as standard ones
    let dimensions = vec![64, 128, 256, 512, 1024];
    
    for dim in dimensions {
        let mut idx1 = BigIndex::new(dim);
        let mut idx2 = BigIndex::new(dim);
        
        // Create interesting bit patterns
        for i in 0..dim {
            if (i * i + i * 3) % 7 < 4 {
                idx1.set_bit(i);
            }
            if (i * i * i + i * 5) % 11 < 6 {
                idx2.set_bit(i);
            }
        }
        
        // Test popcount
        assert_eq!(
            idx1.count_ones(),
            optimized_popcount(idx1.as_bytes()),
            "Popcount mismatch for dimension {}", dim
        );
        
        // Test compute_sign
        let sign_std = if BigIndex::compute_sign::<f64>(&idx1, &idx2) > 0.0 { 1 } else { -1 };
        let sign_opt = optimized_compute_sign(&idx1, &idx2);
        assert_eq!(sign_std, sign_opt, "Sign computation mismatch for dimension {}", dim);
        
        // Test XOR
        let xor_std = idx1.xor(&idx2);
        let xor_parallel = parallel_xor(&idx1, &idx2);
        assert_eq!(xor_std.as_bytes(), xor_parallel.as_bytes(), "XOR mismatch for dimension {}", dim);
        
        // Test AND (on x86_64)
        #[cfg(target_arch = "x86_64")]
        {
            let and_std = idx1.and(&idx2);
            let and_simd = simd_and(&idx1, &idx2);
            assert_eq!(and_std.as_bytes(), and_simd.as_bytes(), "AND mismatch for dimension {}", dim);
        }
        
        // Test bit iterator
        let positions_std: Vec<usize> = idx1.bit_positions().collect();
        let positions_fast: Vec<usize> = FastBitIterator::new(&idx1).collect();
        assert_eq!(positions_std, positions_fast, "Bit iterator mismatch for dimension {}", dim);
    }
}

#[test]
fn test_performance_improvements() {
    // Test that optimizations actually provide performance benefits
    let dimension = 1024;
    let iterations = 100;
    
    // Create test data
    let mut indices = Vec::new();
    for i in 0..20 {
        let mut idx = BigIndex::new(dimension);
        for j in (i..dimension).step_by(20) {
            idx.set_bit(j);
        }
        indices.push(idx);
    }
    
    // Measure standard popcount
    let start = Instant::now();
    for _ in 0..iterations {
        for idx in &indices {
            let _ = idx.count_ones();
        }
    }
    let standard_time = start.elapsed();
    
    // Measure optimized popcount
    let start = Instant::now();
    for _ in 0..iterations {
        for idx in &indices {
            let _ = optimized_popcount(idx.as_bytes());
        }
    }
    let optimized_time = start.elapsed();
    
    println!("Popcount performance:");
    println!("  Standard: {:?}", standard_time);
    println!("  Optimized: {:?}", optimized_time);
    println!("  Speedup: {:.2}x", standard_time.as_secs_f64() / optimized_time.as_secs_f64());
    
    // We expect at least some improvement
    assert!(
        optimized_time <= standard_time,
        "Optimized popcount should not be slower than standard"
    );
}

#[test]
#[cfg(feature = "std")]
fn test_cache_behavior() {
    use std::sync::Arc;
    use std::thread;
    
    let cache = Arc::new(BigIndexCache::new(100));
    let mut idx = BigIndex::new(256);
    
    // Set some bits
    for i in (0..256).step_by(7) {
        idx.set_bit(i);
    }
    
    // Test single-threaded cache
    let count1 = cache.count_ones(&idx);
    let count2 = cache.count_ones(&idx);
    assert_eq!(count1, count2);
    assert_eq!(count1, idx.count_ones());
    
    // Test multi-threaded cache access
    let cache_clone = Arc::clone(&cache);
    let idx_clone = idx.clone();
    
    let handle = thread::spawn(move || {
        cache_clone.count_ones(&idx_clone)
    });
    
    let result_main = cache.count_ones(&idx);
    let result_thread = handle.join().unwrap();
    
    assert_eq!(result_main, result_thread);
}

#[test]
fn test_large_scale_operations() {
    // Test with very large dimensions
    let dimension = 4096;
    
    let mut elem1 = SparseBigElement::<f64>::zero(dimension);
    let mut elem2 = SparseBigElement::<f64>::zero(dimension);
    
    // Add sparse components
    for i in 0..50 {
        let mut idx = BigIndex::new(dimension);
        idx.set_bit(i * 80);
        if i % 3 == 0 {
            idx.set_bit(i * 80 + 40);
        }
        elem1.set_component(&idx, Complex::new(1.0, 0.0)).unwrap();
        elem2.set_component(&idx, Complex::new(0.5, 0.0)).unwrap();
    }
    
    // Test that operations complete in reasonable time
    let start = Instant::now();
    let _product = elem1.geometric_product(&elem2).unwrap();
    let product_time = start.elapsed();
    
    println!("Geometric product for dimension {} completed in {:?}", dimension, product_time);
    
    // Should complete in under 1 second even for large dimensions
    assert!(
        product_time.as_secs() < 1,
        "Large-scale operation took too long: {:?}", product_time
    );
}

#[test]
fn test_bit_manipulation_edge_cases() {
    // Test empty indices
    let empty = BigIndex::new(1024);
    assert_eq!(optimized_popcount(empty.as_bytes()), 0);
    assert_eq!(optimized_compute_sign(&empty, &empty), 1);
    
    // Test full index
    let mut full = BigIndex::new(64);
    for i in 0..64 {
        full.set_bit(i);
    }
    assert_eq!(optimized_popcount(full.as_bytes()), 64);
    
    // Test single bit
    let mut single = BigIndex::new(1024);
    single.set_bit(777);
    assert_eq!(optimized_popcount(single.as_bytes()), 1);
    let positions: Vec<usize> = FastBitIterator::new(&single).collect();
    assert_eq!(positions, vec![777]);
}