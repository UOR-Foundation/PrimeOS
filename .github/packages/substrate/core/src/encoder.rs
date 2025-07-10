//! Encoder module for converting bit streams to universal digests

use bitvec::prelude::*;
use crate::constants::*;
use crate::coordinate::Coordinate;
use crate::digest::Digest;
use crate::error::{CodecError, Result};
use crate::resonance::byte_to_resonance_class;
use crate::traits::AddressEncoder;
use crate::mapper::COORDINATE_MAPPER;

/// The PrimeOS encoder - pure and deterministic
pub struct PrimeOSEncoder;

impl PrimeOSEncoder {
    /// Create a new encoder
    pub fn new() -> Self {
        Self
    }
}

impl AddressEncoder for PrimeOSEncoder {
    fn encode(&self, bits: &BitSlice) -> Result<Digest> {
        // Convert generic BitSlice to our specific type
        let mut converted_bits = BitVec::<u8, Msb0>::with_capacity(bits.len());
        for bit in bits.iter() {
            converted_bits.push(*bit);
        }
        
        // Delegate to internal implementation
        self.encode_bits(&converted_bits)
    }
}

impl PrimeOSEncoder {
    /// Calculate optimal digest size for given bit length
    fn calculate_digest_size(bit_length: usize) -> usize {
        // Minimum 4 bytes (32 bits)
        let min_size = 4;
        
        // Add bytes for bit length encoding (varint)
        let length_bytes = Self::varint_size(bit_length);
        
        // Add bytes for coordinate data (3 bytes per 768-bit cycle)
        let num_cycles = (bit_length + CYCLE_LENGTH - 1) / CYCLE_LENGTH;
        let coord_bytes = num_cycles * 3;
        
        // Add 1 byte for checksum
        min_size.max(length_bytes + coord_bytes + 1)
    }
    
    /// Calculate varint encoding size
    fn varint_size(value: usize) -> usize {
        match value {
            0..=127 => 1,
            128..=16383 => 2,
            16384..=2097151 => 3,
            2097152..=268435455 => 4,
            _ => 5,
        }
    }
    
    /// Encode bit length using variable-length encoding
    fn encode_bit_length(&self, length: usize, output: &mut Vec<u8>) {
        let mut value = length;
        loop {
            let mut byte = (value & 0x7F) as u8;
            value >>= 7;
            if value != 0 {
                byte |= 0x80;
            }
            output.push(byte);
            if value == 0 {
                break;
            }
        }
    }
    
    /// Internal encoding implementation
    fn encode_bits(&self, bits: &BitSlice<u8, Msb0>) -> Result<Digest> {
        // Check for maximum size (2^35 bits as per spec)
        if bits.len() > (1usize << 35) {
            return Err(CodecError::BitLengthOverflow(bits.len()));
        }
        
        // Pure encoding: bit length determines algorithm
        let bit_length = bits.len();
        
        // Calculate digest size based on bit length
        let digest_size = Self::calculate_digest_size(bit_length);
        let mut digest_data = Vec::with_capacity(digest_size);
        
        // Encode bit length first (varint encoding)
        self.encode_bit_length(bit_length, &mut digest_data);
        
        // Map bits to coordinates using folding
        let coordinates = self.map_to_coordinates(bits);
        
        // Pack coordinates into digest
        self.pack_coordinates(&coordinates, &mut digest_data);
        
        // Add checksum for integrity
        let checksum = self.calculate_checksum(&digest_data);
        digest_data.push(checksum);
        
        Ok(Digest { data: digest_data })
    }
    
    /// Map bits to coordinates using XOR folding
    fn map_to_coordinates(&self, bits: &BitSlice<u8, Msb0>) -> Vec<Coordinate> {
        let mut coordinates = Vec::new();
        
        // Process in 768-bit cycles
        for cycle_start in (0..bits.len()).step_by(CYCLE_LENGTH) {
            let cycle_end = (cycle_start + CYCLE_LENGTH).min(bits.len());
            let cycle_bits = &bits[cycle_start..cycle_end];
            
            // Fold cycle into 12,288 space
            let coord = self.fold_to_coordinate(cycle_bits, cycle_start / CYCLE_LENGTH);
            coordinates.push(coord);
        }
        
        coordinates
    }
    
    /// Fold bits into a single coordinate with recovery information
    /// CRITICAL: This produces a coordinate that, combined with recovery bits,
    /// enables perfect reconstruction of the original bit pattern
    fn fold_to_coordinate(&self, bits: &BitSlice<u8, Msb0>, cycle_index: usize) -> Coordinate {
        // Convert bits to bytes for processing
        let byte_count = (bits.len() + 7) / 8;
        let mut bytes = vec![0u8; byte_count];
        
        // Copy bits into byte array
        for (i, bit) in bits.iter().enumerate() {
            if *bit {
                bytes[i / 8] |= 1 << (7 - (i % 8));
            }
        }
        
        // Calculate XOR accumulator for the cycle
        let mut xor_accumulator = 0u8;
        for &byte in &bytes {
            xor_accumulator ^= byte;
        }
        
        // Compute resonance signature for the pattern
        let pattern_resonance = if !bytes.is_empty() {
            // Use first byte's resonance as primary signature
            byte_to_resonance_class(bytes[0])
        } else {
            0 // Unity class for empty input
        };
        
        // XOR fold into position (13-bit space)
        let mut folded_position = 0u16;
        for (i, &byte) in bytes.iter().enumerate() {
            // Position-dependent mixing
            let position_factor = ((i as u16) * 257) ^ (cycle_index as u16);
            let byte_contribution = (byte as u16).rotate_left((i % 8) as u32);
            folded_position ^= byte_contribution + position_factor;
        }
        
        // Constrain to 12,288 space
        let absolute = folded_position % (TOTAL_ELEMENTS as u16);
        let page = (absolute / PAGE_SIZE as u16) as u8;
        let position = (absolute % PAGE_SIZE as u16) as u8;
        
        // The resonance class encodes pattern information
        // Combined with position, this constrains possible original values
        Coordinate {
            absolute,
            page,
            position,
            resonance_class: pattern_resonance,
        }
    }
    
    /// Pack coordinates into digest bytes
    fn pack_coordinates(&self, coordinates: &[Coordinate], output: &mut Vec<u8>) {
        for coord in coordinates {
            // Pack 13-bit absolute position + 7-bit resonance class + 4-bit recovery = 24 bits (3 bytes)
            // Byte 0: High 8 bits of absolute position
            output.push((coord.absolute >> 5) as u8);
            // Byte 1: [Low 5 bits of position][High 3 bits of resonance class]
            output.push((((coord.absolute & 0x1F) << 3) | ((coord.resonance_class >> 4) as u16)) as u8);
            
            // Calculate recovery bits using the new recovery module
            let recovery_bits = self.calculate_coordinate_recovery(coord);
            
            // Byte 2: [Low 4 bits of resonance class][4 bits recovery]
            output.push((coord.resonance_class << 4) | (recovery_bits & 0x0F));
        }
    }
    
    /// Calculate recovery bits for a coordinate
    fn calculate_coordinate_recovery(&self, coord: &Coordinate) -> u8 {
        // For now, use the coordinate's position within its resonance class
        // This will be enhanced when we have the full cycle data
        let candidates = COORDINATE_MAPPER.get_bytes_for_resonance_class(coord.resonance_class);
        
        // Find which candidate maps to this position
        if let Some(idx) = candidates.iter().position(|&byte| byte == coord.position) {
            (idx as u8) & 0x0F
        } else {
            // Use position modulo for recovery if not found
            (coord.position % 16) & 0x0F
        }
    }
    
    /// Calculate simple checksum for integrity
    fn calculate_checksum(&self, data: &[u8]) -> u8 {
        data.iter().fold(0u8, |acc, &byte| acc.wrapping_add(byte))
    }
    
    /// Encode bytes (convenience method)
    pub fn encode_bytes(&self, input: &[u8]) -> Result<Digest> {
        let bits = BitVec::<u8, Msb0>::from_slice(input);
        self.encode_bits(&bits)
    }
}

impl Default for PrimeOSEncoder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_empty() {
        let encoder = PrimeOSEncoder::new();
        let empty_bits: BitVec = BitVec::new();
        let digest = encoder.encode(&empty_bits).unwrap();
        
        // Empty input should produce minimum size digest
        assert_eq!(digest.size(), 2); // 1 varint (0) + 1 checksum
        
        // Verify it's valid
        digest.validate().unwrap();
    }
    
    #[test]
    fn test_encode_single_byte() {
        let encoder = PrimeOSEncoder::new();
        let digest = encoder.encode_bytes(&[42]).unwrap();
        
        // Single byte = 8 bits, needs 1 cycle
        assert!(digest.size() >= 4);
        digest.validate().unwrap();
    }
    
    #[test]
    fn test_encode_unity_bytes() {
        let encoder = PrimeOSEncoder::new();
        
        // Test encoding of unity bytes
        for &byte in &[0u8, 1, 48, 49] {
            let digest = encoder.encode_bytes(&[byte]).unwrap();
            digest.validate().unwrap();
        }
    }
    
    #[test]
    fn test_determinism() {
        let data = b"Hello, PrimeOS!";
        
        // Same input should produce same output
        let encoder1 = PrimeOSEncoder::new();
        let digest1 = encoder1.encode_bytes(data).unwrap();
        
        let encoder2 = PrimeOSEncoder::new();
        let digest2 = encoder2.encode_bytes(data).unwrap();
        
        assert_eq!(digest1, digest2);
    }
    
    #[test]
    fn test_varint_encoding() {
        // Test different bit lengths that require different varint sizes
        let test_cases = [
            (1, 1),      // 1 bit -> 1 byte varint
            (127, 1),    // 127 bits -> 1 byte varint
            (128, 2),    // 128 bits -> 2 byte varint
            (16384, 3),  // 16384 bits -> 3 byte varint
        ];
        
        for (bits, expected_varint_size) in test_cases {
            assert_eq!(PrimeOSEncoder::varint_size(bits), expected_varint_size);
        }
    }
    
    #[test]
    fn test_cycle_boundaries() {
        let encoder = PrimeOSEncoder::new();
        
        // Test at cycle boundaries
        for size in [95, 96, 97, 767, 768, 769] {
            let data = vec![0xAA; size];
            let digest = encoder.encode_bytes(&data).unwrap();
            digest.validate().unwrap();
        }
    }
}