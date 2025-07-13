//! Variable-length bit vectors for arbitrary input support

#[cfg(feature = "alloc")]
use alloc::{vec, vec::Vec};

#[cfg(feature = "alloc")]
use core::ops::{BitXor, BitXorAssign};

/// Bit word for arbitrary lengths
#[cfg(feature = "alloc")]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitWord {
    bits: Vec<u64>,
    len: usize, // Number of bits
}

#[cfg(feature = "alloc")]
impl BitWord {
    /// Create a new BitWord with the given number of bits
    pub fn new(len: usize) -> Self {
        let num_words = len.div_ceil(64);
        Self {
            bits: vec![0; num_words],
            len,
        }
    }

    /// Create from a slice of bytes
    pub fn from_bytes(bytes: &[u8]) -> Self {
        let len = bytes.len() * 8;
        let num_words = len.div_ceil(64);
        let mut bits = vec![0u64; num_words];

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

    /// XOR with another BitWord
    pub fn xor(&self, rhs: &Self) -> Self {
        assert_eq!(self.len, rhs.len, "BitWord lengths must match for XOR");

        let mut result = self.clone();
        for (a, b) in result.bits.iter_mut().zip(rhs.bits.iter()) {
            *a ^= b;
        }

        result
    }

    /// Count the number of set bits
    pub fn popcount(&self) -> u32 {
        if self.bits.is_empty() {
            return 0;
        }

        let mut count = 0u32;
        let full_words = self.len / 64;
        let remaining_bits = self.len % 64;

        // Count full words
        for i in 0..full_words {
            count += self.bits[i].count_ones();
        }

        // Count remaining bits in the last word
        if remaining_bits > 0 && full_words < self.bits.len() {
            let mask = (1u64 << remaining_bits) - 1;
            count += (self.bits[full_words] & mask).count_ones();
        }

        count
    }

    /// Convert to usize (only valid for len <= 64)
    pub fn to_usize(&self) -> usize {
        assert!(self.len <= 64, "BitWord too large to convert to usize");
        if self.bits.is_empty() {
            0
        } else {
            let value = self.bits[0] as usize;
            // Mask to ensure we only return bits up to len
            if self.len < 64 {
                value & ((1usize << self.len) - 1)
            } else {
                value
            }
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

    /// Create from a single u64 value with specified length
    pub fn from_u64(value: u64, len: usize) -> Self {
        let mut word = Self::new(len);
        if len > 0 && !word.bits.is_empty() {
            word.bits[0] = value;
            // Clear any bits beyond len
            if len < 64 {
                word.bits[0] &= (1u64 << len) - 1;
            }
        }
        word
    }

    /// Create from a u8 value
    pub fn from_u8(value: u8) -> Self {
        Self::from_u64(value as u64, 8)
    }

    /// Create from a u32 value  
    pub fn from_u32(value: u32) -> Self {
        Self::from_u64(value as u64, 32)
    }

    /// Create from a usize value with appropriate bit length
    pub fn from_usize(value: usize) -> Self {
        Self::from_u64(value as u64, 64)
    }

    /// Flip bit at position i
    pub fn flip_bit(&mut self, i: usize) {
        if i < self.len {
            let word_idx = i / 64;
            let bit_idx = i % 64;
            self.bits[word_idx] ^= 1u64 << bit_idx;
        }
    }
}

// Implement BitXor trait
#[cfg(feature = "alloc")]
impl BitXor for BitWord {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.xor(&rhs)
    }
}

#[cfg(feature = "alloc")]
impl BitXor for &BitWord {
    type Output = BitWord;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.xor(rhs)
    }
}

#[cfg(feature = "alloc")]
impl BitXorAssign for BitWord {
    fn bitxor_assign(&mut self, rhs: Self) {
        assert_eq!(self.len, rhs.len, "BitWord lengths must match for XOR");
        for (a, b) in self.bits.iter_mut().zip(rhs.bits.iter()) {
            *a ^= b;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitword_basic() {
        let a = BitWord::from_u64(0b10110010, 8);
        assert_eq!(a.popcount(), 4);
        assert_eq!(a.to_usize(), 0b10110010);

        let b = BitWord::from_u64(0b11001100, 8);
        let c = a.xor(&b);
        assert_eq!(c.to_usize(), 0b01111110);
    }

    #[test]
    fn test_bit_access() {
        let mut word = BitWord::new(8);
        word.set_bit(0, true);
        word.set_bit(3, true);
        word.set_bit(7, true);

        assert_eq!(word.to_usize(), 0b10001001);
        assert!(word.bit(0));
        assert!(!word.bit(1));
        assert!(word.bit(3));
        assert!(word.bit(7));
    }

    #[test]
    fn test_bitword_from_bytes() {
        let bytes = vec![0xFF, 0x00, 0xAA, 0x55];
        let word = BitWord::from_bytes(&bytes);

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

    #[test]
    fn test_large_bitword() {
        // Test 128-bit word
        let word128 = BitWord::new(128);
        assert_eq!(word128.len(), 128);
        assert_eq!(word128.popcount(), 0);

        // Test 256-bit word
        let mut word256 = BitWord::new(256);
        assert_eq!(word256.len(), 256);

        // Set some bits
        word256.set_bit(0, true);
        word256.set_bit(127, true);
        word256.set_bit(255, true);

        assert!(word256.bit(0));
        assert!(word256.bit(127));
        assert!(word256.bit(255));
        assert_eq!(word256.popcount(), 3);
    }

    #[test]
    fn test_bitword_xor_large() {
        // Test XOR with large BitWords
        let mut a = BitWord::new(256);
        let mut b = BitWord::new(256);

        // Set alternating bits in a
        for i in (0..256).step_by(2) {
            a.set_bit(i, true);
        }

        // Set alternating bits in b (offset by 1)
        for i in (1..256).step_by(2) {
            b.set_bit(i, true);
        }

        let c = a.xor(&b);

        // Result should have all bits set
        assert_eq!(c.popcount(), 256);

        // Test using operators
        let d = &a ^ &b;
        assert_eq!(d.popcount(), 256);
    }

    #[test]
    fn test_flip_bit() {
        let mut word = BitWord::from_u8(0b10110010);

        word.flip_bit(0); // Was 0, now 1
        word.flip_bit(1); // Was 1, now 0

        assert_eq!(word.to_usize(), 0b10110001);
    }

    #[test]
    fn test_from_convenience_methods() {
        let w8 = BitWord::from_u8(0xFF);
        assert_eq!(w8.len(), 8);
        assert_eq!(w8.popcount(), 8);

        let w32 = BitWord::from_u32(0xDEADBEEF);
        assert_eq!(w32.len(), 32);
        assert_eq!(w32.to_usize(), 0xDEADBEEF);
    }

    #[test]
    fn test_edge_cases() {
        // Empty BitWord
        let empty = BitWord::new(0);
        assert_eq!(empty.len(), 0);
        assert_eq!(empty.popcount(), 0);
        assert_eq!(empty.to_usize(), 0);

        // Single bit
        let mut single = BitWord::new(1);
        single.set_bit(0, true);
        assert_eq!(single.popcount(), 1);
        assert_eq!(single.to_usize(), 1);
    }

    #[test]
    fn test_very_large_bitword() {
        // Test with 4096 bits as mentioned in the spec
        let mut large = BitWord::new(4096);
        assert_eq!(large.len(), 4096);

        // Set bits at various positions
        large.set_bit(0, true);
        large.set_bit(1000, true);
        large.set_bit(2000, true);
        large.set_bit(3000, true);
        large.set_bit(4095, true);

        assert_eq!(large.popcount(), 5);
        assert!(large.bit(0));
        assert!(large.bit(1000));
        assert!(large.bit(4095));
        assert!(!large.bit(500));
    }
}
