//! Fixed and variable-length bit vectors

use core::ops::{BitXor, BitXorAssign};

/// Fixed-size bit word with compile-time known length
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BitWord<const N: usize> {
    bits: u64, // For N <= 64
}

impl<const N: usize> BitWord<N> {
    /// Create a new BitWord from a u64 value
    pub fn new(value: u64) -> Self {
        assert!(N <= 64, "BitWord only supports N <= 64");
        let mask = if N == 64 { !0u64 } else { (1u64 << N) - 1 };
        Self { bits: value & mask }
    }

    /// Create a zero BitWord
    pub fn zero() -> Self {
        Self { bits: 0 }
    }

    /// Get the value as usize (panics if N > 64 on 32-bit systems)
    pub fn to_usize(&self) -> usize {
        self.bits as usize
    }

    /// Count the number of set bits
    pub fn popcount(&self) -> u32 {
        self.bits.count_ones()
    }

    /// Get bit at position i (0-indexed)
    pub fn bit(&self, i: usize) -> bool {
        if i >= N {
            false
        } else {
            (self.bits >> i) & 1 == 1
        }
    }

    /// Set bit at position i
    pub fn set_bit(&mut self, i: usize, value: bool) {
        if i < N {
            if value {
                self.bits |= 1u64 << i;
            } else {
                self.bits &= !(1u64 << i);
            }
        }
    }
}

impl<const N: usize> From<u64> for BitWord<N> {
    fn from(value: u64) -> Self {
        Self::new(value)
    }
}

impl<const N: usize> From<u32> for BitWord<N> {
    fn from(value: u32) -> Self {
        Self::new(value as u64)
    }
}

impl<const N: usize> From<u8> for BitWord<N> {
    fn from(value: u8) -> Self {
        Self::new(value as u64)
    }
}

impl<const N: usize> BitXor for BitWord<N> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Self {
            bits: self.bits ^ rhs.bits,
        }
    }
}

impl<const N: usize> BitXorAssign for BitWord<N> {
    fn bitxor_assign(&mut self, rhs: Self) {
        self.bits ^= rhs.bits;
    }
}

/// Dynamic bit word for runtime-determined lengths
#[cfg(feature = "alloc")]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitWordDyn {
    bits: alloc::vec::Vec<u64>,
    len: usize, // Number of bits
}

#[cfg(feature = "alloc")]
impl BitWordDyn {
    /// Create a new dynamic BitWord with the given number of bits
    pub fn new(len: usize) -> Self {
        let num_words = len.div_ceil(64);
        Self {
            bits: alloc::vec![0; num_words],
            len,
        }
    }

    /// Create from a slice of bytes
    pub fn from_bytes(bytes: &[u8]) -> Self {
        let len = bytes.len() * 8;
        let num_words = len.div_ceil(64);
        let mut bits = alloc::vec![0u64; num_words];

        for (i, &byte) in bytes.iter().enumerate() {
            let word_idx = i / 8;
            let byte_idx = i % 8;
            bits[word_idx] |= (byte as u64) << (byte_idx * 8);
        }

        Self { bits, len }
    }

    /// Get the number of bits
    pub fn len(&self) -> usize {
        self.len
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// XOR with another BitWordDyn
    pub fn xor(&self, rhs: &Self) -> Self {
        assert_eq!(self.len, rhs.len, "BitWordDyn lengths must match for XOR");

        let mut result = self.clone();
        for (a, b) in result.bits.iter_mut().zip(rhs.bits.iter()) {
            *a ^= b;
        }

        result
    }

    /// Count the number of set bits
    pub fn popcount(&self) -> u32 {
        self.bits.iter().map(|&word| word.count_ones()).sum()
    }

    /// Convert to usize (only valid for len <= 64)
    pub fn to_usize(&self) -> usize {
        assert!(self.len <= 64, "BitWordDyn too large to convert to usize");
        if self.bits.is_empty() {
            0
        } else {
            self.bits[0] as usize
        }
    }

    /// Get bit at position i
    pub fn bit(&self, i: usize) -> bool {
        if i >= self.len {
            false
        } else {
            let word_idx = i / 64;
            let bit_idx = i % 64;
            (self.bits[word_idx] >> bit_idx) & 1 == 1
        }
    }

    /// Set bit at position i
    pub fn set_bit(&mut self, i: usize, value: bool) {
        if i < self.len {
            let word_idx = i / 64;
            let bit_idx = i % 64;
            if value {
                self.bits[word_idx] |= 1u64 << bit_idx;
            } else {
                self.bits[word_idx] &= !(1u64 << bit_idx);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitword_basic() {
        let a = BitWord::<8>::from(0b10110010u8);
        assert_eq!(a.popcount(), 4);
        assert_eq!(a.to_usize(), 0b10110010);

        let b = BitWord::<8>::from(0b11001100u8);
        let c = a ^ b;
        assert_eq!(c.to_usize(), 0b01111110);
    }

    #[test]
    fn test_bit_access() {
        let mut word = BitWord::<8>::zero();
        word.set_bit(0, true);
        word.set_bit(3, true);
        word.set_bit(7, true);

        assert_eq!(word.to_usize(), 0b10001001);
        assert!(word.bit(0));
        assert!(!word.bit(1));
        assert!(word.bit(3));
        assert!(word.bit(7));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_bitword_dyn() {
        let bytes = vec![0xFF, 0x00, 0xAA, 0x55];
        let word = BitWordDyn::from_bytes(&bytes);

        assert_eq!(word.len(), 32);
        assert_eq!(word.popcount(), 16);

        // Test first byte
        for i in 0..8 {
            assert!(word.bit(i));
        }

        // Test second byte
        for i in 8..16 {
            assert!(!word.bit(i));
        }
    }
}
