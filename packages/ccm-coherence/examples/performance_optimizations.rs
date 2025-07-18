//! Example demonstrating performance optimizations in CCM Coherence
//!
//! This example shows how to use the optimized operations for better performance
//! with large-dimensional Clifford algebras.

use ccm_coherence::{
    arbitrary_support::BigIndex,
    optimizations::*,
    sparse_big::SparseBigElement,
};
use num_complex::Complex;
use std::time::Instant;

fn main() {
    println!("=== CCM Coherence Performance Optimizations Example ===\n");
    
    // Example 1: Using optimized popcount
    println!("1. Optimized Popcount Example");
    let mut large_index = BigIndex::new(4096);
    
    // Set many bits
    for i in (0..4096).step_by(7) {
        large_index.set_bit(i);
    }
    
    let start = Instant::now();
    let count_standard = large_index.count_ones();
    let time_standard = start.elapsed();
    
    let start = Instant::now();
    let count_optimized = optimized_popcount(large_index.as_bytes());
    let time_optimized = start.elapsed();
    
    println!("  Standard popcount: {} bits in {:?}", count_standard, time_standard);
    println!("  Optimized popcount: {} bits in {:?}", count_optimized, time_optimized);
    println!("  Speedup: {:.2}x\n", time_standard.as_secs_f64() / time_optimized.as_secs_f64());
    
    // Example 2: Using fast bit iterator
    println!("2. Fast Bit Iterator Example");
    let mut sparse_index = BigIndex::new(1024);
    for i in vec![10, 50, 100, 200, 500, 750, 900] {
        sparse_index.set_bit(i);
    }
    
    let start = Instant::now();
    let positions_standard: Vec<usize> = sparse_index.bit_positions().collect();
    let time_standard = start.elapsed();
    
    let start = Instant::now();
    let positions_fast: Vec<usize> = FastBitIterator::new(&sparse_index).collect();
    let time_fast = start.elapsed();
    
    println!("  Standard iterator found: {:?}", positions_standard);
    println!("  Time: {:?}", time_standard);
    println!("  Fast iterator found: {:?}", positions_fast);
    println!("  Time: {:?}", time_fast);
    println!("  Speedup: {:.2}x\n", time_standard.as_secs_f64() / time_fast.as_secs_f64());
    
    // Example 3: Using cache for repeated operations
    #[cfg(feature = "std")]
    {
        println!("3. Cache Effectiveness Example");
        let cache = BigIndexCache::new(100);
        
        let mut indices = Vec::new();
        for i in 0..10 {
            let mut idx = BigIndex::new(256);
            for j in (i..256).step_by(10) {
                idx.set_bit(j);
            }
            indices.push(idx);
        }
        
        // First pass - cache miss
        let start = Instant::now();
        for idx in &indices {
            let _ = cache.count_ones(idx);
        }
        let first_pass = start.elapsed();
        
        // Second pass - cache hit
        let start = Instant::now();
        for _ in 0..100 {
            for idx in &indices {
                let _ = cache.count_ones(idx);
            }
        }
        let cached_passes = start.elapsed();
        
        println!("  First pass (cache miss): {:?}", first_pass);
        println!("  100 cached passes: {:?}", cached_passes);
        println!("  Average cached operation: {:?}\n", cached_passes / 1000);
    }
    
    // Example 4: SIMD operations (if available)
    #[cfg(target_arch = "x86_64")]
    {
        println!("4. SIMD Operations Example");
        let mut a = BigIndex::new(2048);
        let mut b = BigIndex::new(2048);
        
        // Create some pattern
        for i in (0..2048).step_by(3) {
            a.set_bit(i);
        }
        for i in (0..2048).step_by(5) {
            b.set_bit(i);
        }
        
        let start = Instant::now();
        let result_standard = a.and(&b);
        let time_standard = start.elapsed();
        
        let start = Instant::now();
        let result_simd = simd_and(&a, &b);
        let time_simd = start.elapsed();
        
        println!("  Standard AND: {:?} ({} bits set)", time_standard, result_standard.count_ones());
        println!("  SIMD AND: {:?} ({} bits set)", time_simd, result_simd.count_ones());
        println!("  Speedup: {:.2}x\n", time_standard.as_secs_f64() / time_simd.as_secs_f64());
    }
    
    // Example 5: Optimized sign computation
    println!("5. Optimized Sign Computation Example");
    let mut idx1 = BigIndex::new(512);
    let mut idx2 = BigIndex::new(512);
    
    // Create overlapping patterns
    for i in (0..512).step_by(7) {
        idx1.set_bit(i);
    }
    for i in (3..512).step_by(11) {
        idx2.set_bit(i);
    }
    
    let start = Instant::now();
    let sign_standard = BigIndex::compute_sign::<f64>(&idx1, &idx2);
    let time_standard = start.elapsed();
    
    let start = Instant::now();
    let sign_optimized = optimized_compute_sign(&idx1, &idx2);
    let time_optimized = start.elapsed();
    
    println!("  Standard sign: {} in {:?}", sign_standard, time_standard);
    println!("  Optimized sign: {} in {:?}", sign_optimized, time_optimized);
    println!("  Speedup: {:.2}x\n", time_standard.as_secs_f64() / time_optimized.as_secs_f64());
    
    // Example 6: Working with sparse elements efficiently
    println!("6. Sparse Element Operations");
    let mut elem1 = SparseBigElement::<f64>::zero(1024);
    let mut elem2 = SparseBigElement::<f64>::zero(1024);
    
    // Add some components
    println!("  Creating sparse elements with 50 components each...");
    for i in 0..50 {
        let mut idx = BigIndex::new(1024);
        idx.set_bit(i * 20);
        if i % 3 == 0 {
            idx.set_bit(i * 20 + 5);
        }
        elem1.set_component(&idx, Complex::new(1.0 / (i + 1) as f64, 0.0)).unwrap();
        elem2.set_component(&idx, Complex::new((i + 1) as f64, 0.0)).unwrap();
    }
    
    let start = Instant::now();
    let product = elem1.geometric_product(&elem2).unwrap();
    let product_time = start.elapsed();
    
    println!("  Geometric product computed in: {:?}", product_time);
    println!("  Result has {} non-zero components", product.nnz());
    println!("  Memory usage: ~{} KB", (product.nnz() * 32) / 1024);
    
    println!("\n=== Performance Tips ===");
    println!("1. Use optimized_popcount() for large indices");
    println!("2. Use FastBitIterator for sparse indices");
    println!("3. Enable caching for repeated operations");
    println!("4. Use SIMD operations on x86_64 when available");
    println!("5. Prefer sparse representations for dimension > 64");
}