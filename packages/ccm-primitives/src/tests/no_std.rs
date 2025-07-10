//! Tests for no_std compatibility

// This file ensures the crate builds without std
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

use crate::{AlphaVec, BitWord, Resonance};

#[test]
fn test_no_std_basic_operations() {
    // Create alpha vector (requires alloc)
    let values = [1.0, 2.0, 0.5].into();
    let alpha = AlphaVec::new(values).unwrap();

    // Basic BitWord operations
    let word = BitWord::<3>::from(0b101u8);
    assert_eq!(word.popcount(), 2);

    // Resonance calculation
    let resonance = word.r(&alpha).unwrap();
    assert!(resonance > 0.0);
}

#[test]
fn test_no_heap_operations() {
    // These operations should work without any heap allocation
    let word1 = BitWord::<8>::from(0x42u8);
    let word2 = BitWord::<8>::from(0x18u8);

    // XOR operation
    let result = word1 ^ word2;
    assert_eq!(result.to_usize(), 0x5A);

    // Bit manipulation
    let mut word = BitWord::<8>::zero();
    word.set_bit(3, true);
    word.set_bit(7, true);
    assert_eq!(word.to_usize(), 0x88);
}

#[cfg(all(not(feature = "std"), feature = "alloc"))]
#[test]
fn test_alloc_features() {
    use alloc::vec;

    // Test that Vec-based operations work
    let values = vec![1.0, 1.5, 2.0 / 3.0]; // Last two multiply to 1
    let alpha = AlphaVec::try_from(values).unwrap();
    assert_eq!(alpha.len(), 3);
}
