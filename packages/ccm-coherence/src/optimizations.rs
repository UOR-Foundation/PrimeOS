//! Performance optimizations for BigIndex and other scalable operations
//!
//! This module provides optimized implementations using:
//! - Caching for frequently used operations
//! - SIMD instructions where available
//! - Parallel algorithms for large-scale operations

use crate::arbitrary_support::BigIndex;

#[cfg(feature = "std")]
use std::{
    collections::HashMap,
    sync::{Arc, RwLock},
};

/// Cache for frequently computed BigIndex operations
#[cfg(feature = "std")]
pub struct BigIndexCache {
    /// Cache for count_ones results
    popcount_cache: Arc<RwLock<HashMap<Vec<u8>, usize>>>,
    /// Cache for sign computation results
    sign_cache: Arc<RwLock<HashMap<(Vec<u8>, Vec<u8>), i32>>>,
    /// Maximum cache size
    max_cache_size: usize,
}

#[cfg(feature = "std")]
impl BigIndexCache {
    pub fn new(max_cache_size: usize) -> Self {
        Self {
            popcount_cache: Arc::new(RwLock::new(HashMap::new())),
            sign_cache: Arc::new(RwLock::new(HashMap::new())),
            max_cache_size,
        }
    }
    
    /// Get or compute popcount for a BigIndex
    pub fn count_ones(&self, index: &BigIndex) -> usize {
        // Check cache first
        {
            let cache = self.popcount_cache.read().unwrap();
            if let Some(&count) = cache.get(index.as_bytes()) {
                return count;
            }
        }
        
        // Compute if not in cache
        let count = optimized_popcount(index.as_bytes());
        
        // Store in cache if not full
        {
            let mut cache = self.popcount_cache.write().unwrap();
            if cache.len() < self.max_cache_size {
                cache.insert(index.as_bytes().to_vec(), count);
            }
        }
        
        count
    }
    
    /// Get or compute sign for BigIndex multiplication
    pub fn compute_sign(&self, idx1: &BigIndex, idx2: &BigIndex) -> i32 {
        let key = (idx1.as_bytes().to_vec(), idx2.as_bytes().to_vec());
        
        // Check cache first
        {
            let cache = self.sign_cache.read().unwrap();
            if let Some(&sign) = cache.get(&key) {
                return sign;
            }
        }
        
        // Compute if not in cache
        let sign = optimized_compute_sign(idx1, idx2);
        
        // Store in cache if not full
        {
            let mut cache = self.sign_cache.write().unwrap();
            if cache.len() < self.max_cache_size {
                cache.insert(key, sign);
            }
        }
        
        sign
    }
}

/// Optimized popcount using lookup table and/or SIMD
pub fn optimized_popcount(bits: &[u8]) -> usize {
    // For small bit vectors, use built-in popcount
    #[cfg(target_arch = "x86_64")]
    {
        if is_x86_feature_detected!("popcnt") {
            return popcount_simd(bits);
        }
    }
    
    // Fallback to byte-wise popcount
    bits.iter().map(|b| b.count_ones() as usize).sum()
}

/// SIMD popcount for x86_64 with POPCNT instruction
#[cfg(target_arch = "x86_64")]
fn popcount_simd(bits: &[u8]) -> usize {
    use core::arch::x86_64::*;
    
    unsafe {
        let mut count = 0;
        let chunks = bits.chunks_exact(8);
        let remainder = chunks.remainder();
        
        // Process 8 bytes at a time using 64-bit popcount
        for chunk in chunks {
            let val = u64::from_le_bytes(chunk.try_into().unwrap());
            count += _popcnt64(val as i64) as usize;
        }
        
        // Handle remaining bytes
        for &byte in remainder {
            count += byte.count_ones() as usize;
        }
        
        count
    }
}

/// Optimized sign computation with early exit
pub fn optimized_compute_sign(idx1: &BigIndex, idx2: &BigIndex) -> i32 {
    let mut swaps = 0;
    
    // Early exit if either index is zero
    if idx1.is_zero() || idx2.is_zero() {
        return 1;
    }
    
    // Use byte-level operations when possible
    let bits1 = idx1.as_bytes();
    let bits2 = idx2.as_bytes();
    let byte_count = bits1.len().min(bits2.len());
    
    for byte_idx in 0..byte_count {
        let byte1 = bits1.get(byte_idx).copied().unwrap_or(0);
        if byte1 == 0 {
            continue;
        }
        
        // Count swaps for this byte
        for bit_pos in 0..8 {
            let global_pos = byte_idx * 8 + bit_pos;
            if global_pos >= idx1.bit_count() {
                break;
            }
            
            if (byte1 & (1 << bit_pos)) != 0 {
                // Count bits in idx2 before this position
                swaps += count_bits_before(idx2, global_pos);
            }
        }
    }
    
    if swaps % 2 == 0 { 1 } else { -1 }
}

/// Count bits set in idx before position
fn count_bits_before(idx: &BigIndex, position: usize) -> usize {
    let mut count = 0;
    let full_bytes = position / 8;
    let bits = idx.as_bytes();
    
    // Count all bits in full bytes
    for i in 0..full_bytes.min(bits.len()) {
        count += bits[i].count_ones() as usize;
    }
    
    // Count bits in partial byte
    if full_bytes < bits.len() && position % 8 > 0 {
        let mask = (1u8 << (position % 8)) - 1;
        count += (bits[full_bytes] & mask).count_ones() as usize;
    }
    
    count
}

/// Parallel XOR operation for large BigIndex (requires rayon feature)
#[cfg(all(feature = "std", feature = "rayon"))]
pub fn parallel_xor(a: &BigIndex, b: &BigIndex) -> BigIndex {
    use rayon::prelude::*;
    
    let bit_count = a.bit_count().max(b.bit_count());
    let byte_count = (bit_count + 7) / 8;
    
    // Use parallel processing for large indices
    if byte_count > 1024 {
        let mut result_bits = vec![0u8; byte_count];
        
        result_bits
            .par_chunks_mut(256)
            .enumerate()
            .for_each(|(chunk_idx, chunk)| {
                let start = chunk_idx * 256;
                for (i, byte) in chunk.iter_mut().enumerate() {
                    let idx = start + i;
                    let a_byte = a.as_bytes().get(idx).copied().unwrap_or(0);
                    let b_byte = b.as_bytes().get(idx).copied().unwrap_or(0);
                    *byte = a_byte ^ b_byte;
                }
            });
        
        // Create new BigIndex from result
        let mut result = BigIndex::new(bit_count);
        for (i, &byte) in result_bits.iter().enumerate() {
            for bit in 0..8 {
                if i * 8 + bit < bit_count && (byte & (1 << bit)) != 0 {
                    result.set_bit(i * 8 + bit);
                }
            }
        }
        result
    } else {
        // Use sequential for small indices
        a.xor(b)
    }
}

/// Parallel XOR operation fallback when rayon is not available
#[cfg(all(feature = "std", not(feature = "rayon")))]
pub fn parallel_xor(a: &BigIndex, b: &BigIndex) -> BigIndex {
    // Just use regular XOR when rayon is not available
    a.xor(b)
}

/// Optimized bit iteration using bit manipulation tricks
pub struct FastBitIterator<'a> {
    bits: &'a [u8],
    bit_count: usize,
    current_byte_idx: usize,
    current_byte: u8,
    current_pos: usize,
}

impl<'a> FastBitIterator<'a> {
    pub fn new(index: &'a BigIndex) -> Self {
        let current_byte = index.bits.get(0).copied().unwrap_or(0);
        Self {
            bits: &index.bits,
            bit_count: index.bit_count,
            current_byte_idx: 0,
            current_byte,
            current_pos: 0,
        }
    }
}

impl<'a> Iterator for FastBitIterator<'a> {
    type Item = usize;
    
    fn next(&mut self) -> Option<Self::Item> {
        while self.current_pos < self.bit_count {
            // Skip if current byte is zero
            while self.current_byte == 0 {
                self.current_byte_idx += 1;
                if self.current_byte_idx >= self.bits.len() {
                    return None;
                }
                self.current_byte = self.bits[self.current_byte_idx];
                self.current_pos = self.current_byte_idx * 8;
                if self.current_pos >= self.bit_count {
                    return None;
                }
            }
            
            // Find next set bit using bit manipulation
            let trailing_zeros = self.current_byte.trailing_zeros() as usize;
            let bit_pos = self.current_pos + trailing_zeros;
            
            // Clear the found bit
            self.current_byte &= self.current_byte - 1;
            
            if bit_pos < self.bit_count {
                return Some(bit_pos);
            }
        }
        
        None
    }
}

/// SIMD-optimized AND operation
#[cfg(target_arch = "x86_64")]
pub fn simd_and(a: &BigIndex, b: &BigIndex) -> BigIndex {
    use core::arch::x86_64::*;
    
    let bit_count = a.bit_count().min(b.bit_count());
    let byte_count = (bit_count + 7) / 8;
    let mut result = BigIndex::new(bit_count);
    let a_bytes = a.as_bytes();
    let b_bytes = b.as_bytes();
    
    unsafe {
        // Process 16 bytes at a time using SSE2
        if is_x86_feature_detected!("sse2") {
            let chunks = byte_count / 16;
            
            // We need to collect result bytes first, then set bits
            let mut result_bytes = vec![0u8; byte_count];
            
            for i in 0..chunks {
                let offset = i * 16;
                let a_ptr = a_bytes.as_ptr().add(offset) as *const __m128i;
                let b_ptr = b_bytes.as_ptr().add(offset) as *const __m128i;
                let result_ptr = result_bytes.as_mut_ptr().add(offset) as *mut __m128i;
                
                let a_vec = _mm_loadu_si128(a_ptr);
                let b_vec = _mm_loadu_si128(b_ptr);
                let and_vec = _mm_and_si128(a_vec, b_vec);
                _mm_storeu_si128(result_ptr, and_vec);
            }
            
            // Handle remaining bytes
            for i in (chunks * 16)..byte_count {
                result_bytes[i] = a_bytes[i] & b_bytes[i];
            }
            
            // Convert bytes back to BigIndex
            for (i, &byte) in result_bytes.iter().enumerate() {
                for bit in 0..8 {
                    if i * 8 + bit < bit_count && (byte & (1 << bit)) != 0 {
                        result.set_bit(i * 8 + bit);
                    }
                }
            }
        } else {
            // Fallback to regular AND
            for i in 0..byte_count {
                let byte_result = a_bytes[i] & b_bytes[i];
                for bit in 0..8 {
                    if i * 8 + bit < bit_count && (byte_result & (1 << bit)) != 0 {
                        result.set_bit(i * 8 + bit);
                    }
                }
            }
        }
    }
    
    result
}

#[cfg(not(target_arch = "x86_64"))]
pub fn simd_and(a: &BigIndex, b: &BigIndex) -> BigIndex {
    a.and(b)
}

/// Precomputed lookup table for small bit patterns
pub struct BitPatternLookup {
    /// Popcount for each byte value
    popcount_table: [u8; 256],
    /// Bit positions for each byte value
    bit_positions_table: [[u8; 8]; 256],
}

impl BitPatternLookup {
    pub const fn new() -> Self {
        let mut popcount_table = [0u8; 256];
        let mut bit_positions_table = [[0u8; 8]; 256];
        
        let mut i = 0;
        while i < 256 {
            let mut count = 0;
            let mut positions = [0u8; 8];
            let mut pos_idx = 0;
            
            let mut j = 0;
            while j < 8 {
                if (i & (1 << j)) != 0 {
                    count += 1;
                    positions[pos_idx] = j;
                    pos_idx += 1;
                }
                j += 1;
            }
            
            popcount_table[i] = count;
            bit_positions_table[i] = positions;
            i += 1;
        }
        
        Self {
            popcount_table,
            bit_positions_table,
        }
    }
}

/// Global lookup table instance
pub static BIT_LOOKUP: BitPatternLookup = BitPatternLookup::new();

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_optimized_popcount() {
        // Test empty index
        let idx = BigIndex::new(128);
        assert_eq!(optimized_popcount(idx.as_bytes()), 0);
        assert_eq!(idx.count_ones(), 0);
        
        // Test sparse index
        let mut idx = BigIndex::new(128);
        idx.set_bit(0);
        idx.set_bit(63);
        idx.set_bit(127);
        assert_eq!(optimized_popcount(idx.as_bytes()), 3);
        assert_eq!(idx.count_ones(), 3);
        
        // Test dense index
        let mut idx = BigIndex::new(64);
        for i in 0..64 {
            idx.set_bit(i);
        }
        assert_eq!(optimized_popcount(idx.as_bytes()), 64);
        assert_eq!(idx.count_ones(), 64);
        
        // Test large index
        let mut idx = BigIndex::new(4096);
        for i in (0..4096).step_by(7) {
            idx.set_bit(i);
        }
        let expected = (0..4096).step_by(7).count();
        assert_eq!(optimized_popcount(idx.as_bytes()), expected);
        assert_eq!(idx.count_ones(), expected);
    }
    
    #[test]
    fn test_optimized_compute_sign() {
        // Test with zero indices
        let idx1 = BigIndex::new(64);
        let idx2 = BigIndex::new(64);
        assert_eq!(optimized_compute_sign(&idx1, &idx2), 1);
        
        // Test simple case: e_0 * e_1 (no swaps needed)
        let mut idx1 = BigIndex::new(64);
        idx1.set_bit(0);
        let mut idx2 = BigIndex::new(64);
        idx2.set_bit(1);
        assert_eq!(optimized_compute_sign(&idx1, &idx2), 1);
        assert_eq!(BigIndex::compute_sign::<f64>(&idx1, &idx2), 1.0);
        
        // Test swap case: e_1 * e_0 (one swap)
        assert_eq!(optimized_compute_sign(&idx2, &idx1), -1);
        assert_eq!(BigIndex::compute_sign::<f64>(&idx2, &idx1), -1.0);
        
        // Test complex case
        let mut idx1 = BigIndex::new(128);
        idx1.set_bit(10);
        idx1.set_bit(20);
        idx1.set_bit(30);
        
        let mut idx2 = BigIndex::new(128);
        idx2.set_bit(5);
        idx2.set_bit(15);
        idx2.set_bit(25);
        
        let sign_opt = optimized_compute_sign(&idx1, &idx2);
        let sign_std = if BigIndex::compute_sign::<f64>(&idx1, &idx2) > 0.0 { 1 } else { -1 };
        assert_eq!(sign_opt, sign_std);
    }
    
    #[test]
    fn test_fast_bit_iterator() {
        // Test empty index
        let idx = BigIndex::new(64);
        let positions: Vec<usize> = FastBitIterator::new(&idx).collect();
        assert_eq!(positions, vec![]);
        
        // Test simple case
        let mut idx = BigIndex::new(64);
        idx.set_bit(5);
        idx.set_bit(10);
        idx.set_bit(63);
        
        let positions: Vec<usize> = FastBitIterator::new(&idx).collect();
        assert_eq!(positions, vec![5, 10, 63]);
        
        // Compare with standard iterator
        let positions_std: Vec<usize> = idx.bit_positions().collect();
        assert_eq!(positions, positions_std);
        
        // Test large sparse index
        let mut idx = BigIndex::new(4096);
        let test_positions = vec![100, 500, 1000, 2000, 3000, 4095];
        for &pos in &test_positions {
            idx.set_bit(pos);
        }
        
        let positions: Vec<usize> = FastBitIterator::new(&idx).collect();
        assert_eq!(positions, test_positions);
    }
    
    #[test]
    fn test_count_bits_before() {
        let mut idx = BigIndex::new(64);
        idx.set_bit(10);
        idx.set_bit(20);
        idx.set_bit(30);
        
        assert_eq!(count_bits_before(&idx, 0), 0);
        assert_eq!(count_bits_before(&idx, 10), 0);
        assert_eq!(count_bits_before(&idx, 11), 1);
        assert_eq!(count_bits_before(&idx, 15), 1);
        assert_eq!(count_bits_before(&idx, 20), 1);
        assert_eq!(count_bits_before(&idx, 21), 2);
        assert_eq!(count_bits_before(&idx, 25), 2);
        assert_eq!(count_bits_before(&idx, 30), 2);
        assert_eq!(count_bits_before(&idx, 31), 3);
        assert_eq!(count_bits_before(&idx, 35), 3);
        assert_eq!(count_bits_before(&idx, 64), 3);
        
        // Test large index
        let mut idx = BigIndex::new(1024);
        for i in (0..1024).step_by(10) {
            idx.set_bit(i);
        }
        assert_eq!(count_bits_before(&idx, 50), 5);
        assert_eq!(count_bits_before(&idx, 100), 10);
        assert_eq!(count_bits_before(&idx, 555), 56); // 0, 10, 20, ..., 550 = 56 values
    }
    
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_simd_and() {
        let mut a = BigIndex::new(256);
        let mut b = BigIndex::new(256);
        
        // Set some overlapping bits
        for i in (0..256).step_by(3) {
            a.set_bit(i);
        }
        for i in (0..256).step_by(5) {
            b.set_bit(i);
        }
        
        let result_std = a.and(&b);
        let result_simd = simd_and(&a, &b);
        
        // Results should be identical
        assert_eq!(result_std.as_bytes(), result_simd.as_bytes());
        assert_eq!(result_std.bit_count(), result_simd.bit_count());
        
        // Check specific bits that should be set (multiples of 15)
        for i in (0..256).step_by(15) {
            assert!(result_simd.get_bit(i), "Bit {} should be set", i);
        }
    }
    
    #[cfg(feature = "std")]
    #[test]
    fn test_cache_functionality() {
        let cache = BigIndexCache::new(10);
        
        let mut idx1 = BigIndex::new(128);
        idx1.set_bit(10);
        idx1.set_bit(20);
        idx1.set_bit(30);
        
        let mut idx2 = BigIndex::new(128);
        idx2.set_bit(5);
        idx2.set_bit(15);
        
        // First call should compute
        let count1 = cache.count_ones(&idx1);
        assert_eq!(count1, 3);
        
        // Second call should use cache
        let count1_cached = cache.count_ones(&idx1);
        assert_eq!(count1_cached, 3);
        
        // Test sign computation cache
        let sign1 = cache.compute_sign(&idx1, &idx2);
        let sign1_cached = cache.compute_sign(&idx1, &idx2);
        assert_eq!(sign1, sign1_cached);
        
        // Verify against standard implementation
        let sign_std = if BigIndex::compute_sign::<f64>(&idx1, &idx2) > 0.0 { 1 } else { -1 };
        assert_eq!(sign1, sign_std);
    }
    
    #[test]
    fn test_parallel_xor() {
        let mut a = BigIndex::new(2048);
        let mut b = BigIndex::new(2048);
        
        // Create some pattern
        for i in 0..2048 {
            if i % 3 == 0 {
                a.set_bit(i);
            }
            if i % 5 == 0 {
                b.set_bit(i);
            }
        }
        
        let result_std = a.xor(&b);
        let result_parallel = parallel_xor(&a, &b);
        
        // Results should be identical
        assert_eq!(result_std.as_bytes(), result_parallel.as_bytes());
        assert_eq!(result_std.bit_count(), result_parallel.bit_count());
        assert_eq!(result_std.count_ones(), result_parallel.count_ones());
    }
    
    #[test]
    fn test_bit_pattern_lookup() {
        // Test lookup table correctness
        for i in 0..=255u8 {
            let expected = i.count_ones() as u8;
            assert_eq!(BIT_LOOKUP.popcount_table[i as usize], expected);
        }
        
        // Test bit positions
        assert_eq!(BIT_LOOKUP.popcount_table[0b10101010], 4);
        assert_eq!(BIT_LOOKUP.popcount_table[0b11111111], 8);
        assert_eq!(BIT_LOOKUP.popcount_table[0b00000001], 1);
    }
}