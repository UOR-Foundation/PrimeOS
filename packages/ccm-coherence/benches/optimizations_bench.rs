//! Benchmarks for performance optimizations
//!
//! Run with: cargo bench --features std

use ccm_coherence::{
    arbitrary_support::BigIndex,
    optimizations::*,
    sparse_big::SparseBigElement,
};
use num_complex::Complex;
use std::time::{Duration, Instant};

const ITERATIONS: u32 = 1000;

fn benchmark_popcount_comparison(dimension: usize) {
    println!("\n=== Popcount Benchmark (dimension {}) ===", dimension);
    
    // Create test indices with various bit patterns
    let mut sparse_idx = BigIndex::new(dimension);
    let mut medium_idx = BigIndex::new(dimension);
    let mut dense_idx = BigIndex::new(dimension);
    
    // Sparse: ~10% bits set
    for i in (0..dimension).step_by(10) {
        sparse_idx.set_bit(i);
    }
    
    // Medium: ~50% bits set
    for i in (0..dimension).step_by(2) {
        medium_idx.set_bit(i);
    }
    
    // Dense: ~90% bits set
    for i in 0..dimension {
        if i % 10 != 0 {
            dense_idx.set_bit(i);
        }
    }
    
    // Benchmark standard count_ones
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let _ = sparse_idx.count_ones();
        let _ = medium_idx.count_ones();
        let _ = dense_idx.count_ones();
    }
    let standard_time = start.elapsed();
    
    // Benchmark optimized popcount
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let _ = optimized_popcount(&sparse_idx.bits);
        let _ = optimized_popcount(&medium_idx.bits);
        let _ = optimized_popcount(&dense_idx.bits);
    }
    let optimized_time = start.elapsed();
    
    println!("Standard popcount: {:?}", standard_time);
    println!("Optimized popcount: {:?}", optimized_time);
    println!("Speedup: {:.2}x", standard_time.as_secs_f64() / optimized_time.as_secs_f64());
}

fn benchmark_sign_computation(dimension: usize) {
    println!("\n=== Sign Computation Benchmark (dimension {}) ===", dimension);
    
    // Create test indices
    let mut idx1 = BigIndex::new(dimension);
    let mut idx2 = BigIndex::new(dimension);
    
    // Set alternating bits
    for i in (0..dimension).step_by(3) {
        idx1.set_bit(i);
    }
    for i in (1..dimension).step_by(3) {
        idx2.set_bit(i);
    }
    
    // Benchmark standard compute_sign
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let _ = BigIndex::compute_sign::<f64>(&idx1, &idx2);
    }
    let standard_time = start.elapsed();
    
    // Benchmark optimized compute_sign
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let _ = optimized_compute_sign(&idx1, &idx2);
    }
    let optimized_time = start.elapsed();
    
    println!("Standard compute_sign: {:?}", standard_time);
    println!("Optimized compute_sign: {:?}", optimized_time);
    println!("Speedup: {:.2}x", standard_time.as_secs_f64() / optimized_time.as_secs_f64());
}

fn benchmark_bit_operations(dimension: usize) {
    println!("\n=== Bit Operations Benchmark (dimension {}) ===", dimension);
    
    let mut a = BigIndex::new(dimension);
    let mut b = BigIndex::new(dimension);
    
    // Create random-like pattern
    for i in 0..dimension {
        if (i * 7 + i * i) % 5 < 3 {
            a.set_bit(i);
        }
        if (i * 11 + i * i * i) % 7 < 4 {
            b.set_bit(i);
        }
    }
    
    // Benchmark XOR
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let _ = a.xor(&b);
    }
    let standard_xor_time = start.elapsed();
    
    // Benchmark parallel XOR (if available)
    #[cfg(feature = "std")]
    {
        let start = Instant::now();
        for _ in 0..ITERATIONS {
            let _ = parallel_xor(&a, &b);
        }
        let parallel_xor_time = start.elapsed();
        
        println!("Standard XOR: {:?}", standard_xor_time);
        println!("Parallel XOR: {:?}", parallel_xor_time);
        println!("Speedup: {:.2}x", standard_xor_time.as_secs_f64() / parallel_xor_time.as_secs_f64());
    }
    
    // Benchmark AND
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let _ = a.and(&b);
    }
    let standard_and_time = start.elapsed();
    
    // Benchmark SIMD AND (if available)
    #[cfg(target_arch = "x86_64")]
    {
        let start = Instant::now();
        for _ in 0..ITERATIONS {
            let _ = simd_and(&a, &b);
        }
        let simd_and_time = start.elapsed();
        
        println!("\nStandard AND: {:?}", standard_and_time);
        println!("SIMD AND: {:?}", simd_and_time);
        println!("Speedup: {:.2}x", standard_and_time.as_secs_f64() / simd_and_time.as_secs_f64());
    }
}

fn benchmark_bit_iteration(dimension: usize) {
    println!("\n=== Bit Iteration Benchmark (dimension {}) ===", dimension);
    
    let mut idx = BigIndex::new(dimension);
    
    // Set ~20% of bits
    for i in (0..dimension).step_by(5) {
        idx.set_bit(i);
    }
    
    // Benchmark standard iteration
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let positions: Vec<usize> = idx.bit_positions().collect();
        let _ = positions.len(); // Prevent optimization
    }
    let standard_time = start.elapsed();
    
    // Benchmark fast iteration
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let positions: Vec<usize> = FastBitIterator::new(&idx).collect();
        let _ = positions.len(); // Prevent optimization
    }
    let fast_time = start.elapsed();
    
    println!("Standard iteration: {:?}", standard_time);
    println!("Fast iteration: {:?}", fast_time);
    println!("Speedup: {:.2}x", standard_time.as_secs_f64() / fast_time.as_secs_f64());
}

fn benchmark_cache_effectiveness(dimension: usize) {
    #[cfg(feature = "std")]
    {
        println!("\n=== Cache Effectiveness Benchmark (dimension {}) ===", dimension);
        
        let cache = BigIndexCache::new(1000);
        let mut indices = Vec::new();
        
        // Create a set of indices that will be reused
        for i in 0..20 {
            let mut idx = BigIndex::new(dimension);
            for j in (i..dimension).step_by(20) {
                idx.set_bit(j);
            }
            indices.push(idx);
        }
        
        // Benchmark without cache (using standard methods)
        let start = Instant::now();
        for _ in 0..ITERATIONS {
            for idx in &indices {
                let _ = idx.count_ones();
                for idx2 in &indices {
                    let _ = BigIndex::compute_sign::<f64>(idx, idx2);
                }
            }
        }
        let no_cache_time = start.elapsed();
        
        // Benchmark with cache
        let start = Instant::now();
        for _ in 0..ITERATIONS {
            for idx in &indices {
                let _ = cache.count_ones(idx);
                for idx2 in &indices {
                    let _ = cache.compute_sign(idx, idx2);
                }
            }
        }
        let with_cache_time = start.elapsed();
        
        println!("Without cache: {:?}", no_cache_time);
        println!("With cache: {:?}", with_cache_time);
        println!("Speedup: {:.2}x", no_cache_time.as_secs_f64() / with_cache_time.as_secs_f64());
    }
}

fn benchmark_sparse_operations(dimension: usize) {
    println!("\n=== Sparse Element Operations Benchmark (dimension {}) ===", dimension);
    
    // Create sparse elements
    let mut elem1 = SparseBigElement::<f64>::zero(dimension);
    let mut elem2 = SparseBigElement::<f64>::zero(dimension);
    
    // Add components (~100 components each)
    for i in 0..100 {
        let mut idx = BigIndex::new(dimension);
        idx.set_bit(i * 7 % dimension);
        if i % 3 == 0 {
            idx.set_bit((i * 11) % dimension);
        }
        elem1.set_component(&idx, Complex::new((i + 1) as f64, 0.0)).unwrap();
        elem2.set_component(&idx, Complex::new(-(i as f64), 0.0)).unwrap();
    }
    
    // Benchmark geometric product
    let start = Instant::now();
    for _ in 0..100 {  // Fewer iterations as this is expensive
        let _ = elem1.geometric_product(&elem2);
    }
    let product_time = start.elapsed();
    
    println!("Geometric product (100 iterations): {:?}", product_time);
    println!("Average per product: {:?}", product_time / 100);
}

fn main() {
    println!("=== CCM Coherence Performance Optimization Benchmarks ===\n");
    
    // Test various dimensions
    let dimensions = vec![64, 256, 1024, 4096];
    
    for &dim in &dimensions {
        println!("\n{'='*60}");
        println!("Testing dimension: {}", dim);
        println!("{'='*60}");
        
        benchmark_popcount_comparison(dim);
        benchmark_sign_computation(dim);
        benchmark_bit_operations(dim);
        benchmark_bit_iteration(dim);
        benchmark_cache_effectiveness(dim);
        
        if dim <= 1024 {  // Skip very expensive operations for 4096
            benchmark_sparse_operations(dim);
        }
    }
    
    println!("\n=== Benchmark Complete ===");
}