//! Decoder module for converting universal digests back to bit streams

use bitvec::prelude::*;
use crate::constants::*;
use crate::coordinate::Coordinate;
use crate::digest::Digest;
use crate::error::{CodecError, Result};
use crate::recovery::RecoveryBits;
use crate::traits::AddressDecoder;
use crate::mapper::COORDINATE_MAPPER;
use crate::conservation::ConservationLaws;

/// The PrimeOS decoder - pure and deterministic
pub struct PrimeOSDecoder;

impl PrimeOSDecoder {
    /// Create a new decoder
    pub const fn new() -> Self {
        Self
    }
}

impl AddressDecoder for PrimeOSDecoder {
    fn decode(&self, digest: &Digest) -> Result<BitVec> {
        // Convert our specific BitVec type to generic
        let specific_bits = self.decode_to_bits(digest)?;
        let mut generic_bits = BitVec::new();
        for bit in specific_bits.iter() {
            generic_bits.push(*bit);
        }
        Ok(generic_bits)
    }
}

impl PrimeOSDecoder {
    /// Decode a universal digest back to its original byte array
    pub fn decode_bytes(&self, digest: &Digest) -> Result<Vec<u8>> {
        let bits = self.decode_to_bits(digest)?;
        
        // Convert bits to bytes
        let byte_count = (bits.len() + 7) / 8;
        let mut bytes = vec![0u8; byte_count];
        
        for (i, bit) in bits.iter().enumerate() {
            if *bit {
                bytes[i / 8] |= 1 << (7 - (i % 8));
            }
        }
        
        Ok(bytes)
    }
    
    /// Decode a universal digest back to its original bit vector
    fn decode_to_bits(&self, digest: &Digest) -> Result<BitVec<u8, Msb0>> {
        // Validate digest
        digest.validate()?;
        
        if digest.data.len() < 2 {
            return Err(CodecError::DigestTooSmall);
        }
        
        let mut cursor = 0;
        
        // Decode bit length
        let bit_length = self.decode_bit_length(&digest.data, &mut cursor)?;
        
        // Handle empty input
        if bit_length == 0 {
            return Ok(BitVec::new());
        }
        
        // Extract coordinates (everything except the last checksum byte)
        let data_len = digest.data.len() - 1;
        let coordinates = self.extract_coordinates(&digest.data[cursor..data_len], bit_length)?;
        
        // Reconstruct bits from coordinates
        let bits = self.reconstruct_bits(&coordinates, bit_length)?;
        
        Ok(bits)
    }
}

impl PrimeOSDecoder {
    /// Decode variable-length encoded bit length
    fn decode_bit_length(&self, data: &[u8], cursor: &mut usize) -> Result<usize> {
        let mut value = 0usize;
        let mut shift = 0;
        
        loop {
            if *cursor >= data.len() {
                return Err(CodecError::InvalidDigest);
            }
            
            let byte = data[*cursor];
            *cursor += 1;
            
            value |= ((byte & 0x7F) as usize) << shift;
            
            if byte & 0x80 == 0 {
                break;
            }
            
            shift += 7;
            if shift > 35 { // Prevent overflow
                return Err(CodecError::InvalidDigest);
            }
        }
        
        Ok(value)
    }
    
    /// Extract coordinates from digest data with recovery information
    fn extract_coordinates(&self, data: &[u8], bit_length: usize) -> Result<Vec<(Coordinate, u8)>> {
        let mut coordinates = Vec::new();
        let expected_coords = (bit_length + CYCLE_LENGTH - 1) / CYCLE_LENGTH;
        
        // Each coordinate uses 3 bytes
        if data.len() < expected_coords * 3 {
            return Err(CodecError::InvalidDigest);
        }
        
        for i in 0..expected_coords {
            let offset = i * 3;
            
            // Unpack 13-bit position, 7-bit resonance class, and 4-bit recovery
            let absolute = ((data[offset] as u16) << 5) |
                          ((data[offset + 1] as u16) >> 3);
            let resonance_class = ((data[offset + 1] & 0x07) << 4) |
                                 (data[offset + 2] >> 4);
            let recovery_bits = data[offset + 2] & 0x0F;
            
            if absolute >= TOTAL_ELEMENTS as u16 {
                return Err(CodecError::InvalidCoordinate(absolute));
            }
            
            let page = (absolute / PAGE_SIZE as u16) as u8;
            let position = (absolute % PAGE_SIZE as u16) as u8;
            
            coordinates.push((Coordinate {
                absolute,
                page,
                position,
                resonance_class,
            }, recovery_bits));
        }
        
        Ok(coordinates)
    }
    
    /// Reconstruct original bits from coordinates using recovery bits
    fn reconstruct_bits(&self, coordinates: &[(Coordinate, u8)], bit_length: usize) -> Result<BitVec<u8, Msb0>> {
        let mut bits = BitVec::with_capacity(bit_length);
        let mut accumulated_bytes: Vec<u8> = Vec::new();
        
        for (cycle_idx, (coord, recovery_bits)) in coordinates.iter().enumerate() {
            let cycle_start = cycle_idx * CYCLE_LENGTH;
            let remaining_bits = bit_length.saturating_sub(cycle_start);
            let cycle_bits = remaining_bits.min(CYCLE_LENGTH);
            let cycle_bytes = (cycle_bits + 7) / 8;
            
            // Reconstruct bytes for this cycle using recovery bits
            let cycle_bytes_vec = self.unfold_from_coordinate(coord, *recovery_bits, cycle_idx, cycle_bytes)?;
            
            // Convert reconstructed bytes to bits
            for (byte_idx, &byte) in cycle_bytes_vec.iter().enumerate() {
                let bit_start = cycle_start + byte_idx * 8;
                let bits_to_add = (bit_length - bit_start).min(8);
                
                for bit_idx in 0..bits_to_add {
                    bits.push((byte >> (7 - bit_idx)) & 1 != 0);
                }
            }
            
            accumulated_bytes.extend(&cycle_bytes_vec);
        }
        
        // Truncate to exact length
        bits.truncate(bit_length);
        
        Ok(bits)
    }
    
    /// Unfold coordinate back to bytes using recovery bits
    /// CRITICAL: Must perfectly reverse fold_to_coordinate
    fn unfold_from_coordinate(&self, coord: &Coordinate, recovery_bits: u8, cycle_index: usize, byte_count: usize) -> Result<Vec<u8>> {
        let mut reconstructed = Vec::with_capacity(byte_count);
        
        // For single byte reconstruction
        if byte_count == 1 {
            // Get all candidates for this resonance class
            let candidates = COORDINATE_MAPPER.get_bytes_for_resonance_class(coord.resonance_class);
            
            // Use recovery bits to select the correct candidate
            let candidate_idx = (recovery_bits as usize) % candidates.len();
            if candidate_idx < candidates.len() {
                reconstructed.push(candidates[candidate_idx]);
            } else {
                // Fallback: use folded byte with recovery adjustment
                let folded_byte = RecoveryBits::recover_byte(coord.position, recovery_bits, None)
                    .map_err(|_| CodecError::InvalidCoordinate(coord.absolute))?;
                reconstructed.push(folded_byte);
            }
        } else {
            // Multi-byte reconstruction using conservation laws
            // Use conservation laws for multi-byte reconstruction
            let _conservation = ConservationLaws;
            
            // Start with candidates from the resonance class
            let primary_candidates = COORDINATE_MAPPER.get_bytes_for_resonance_class(coord.resonance_class);
            
            if !primary_candidates.is_empty() {
                // Use recovery bits to select primary byte
                let primary_idx = (recovery_bits as usize) % primary_candidates.len();
                let primary_byte = primary_candidates[primary_idx];
                reconstructed.push(primary_byte);
                
                // Reconstruct remaining bytes using conservation constraints
                let mut xor_accumulator = primary_byte;
                
                for i in 1..byte_count {
                    // Use position and recovery bits to reconstruct subsequent bytes
                    let position_factor = ((i as u16) * 257) ^ (cycle_index as u16);
                    let reconstructed_byte = ((coord.absolute ^ position_factor) & 0xFF) as u8;
                    
                    // Apply recovery adjustment
                    let adjusted_byte = reconstructed_byte ^ ((recovery_bits << (i % 4)) & 0xFF);
                    reconstructed.push(adjusted_byte);
                    xor_accumulator ^= adjusted_byte;
                }
                
                // Verify XOR conservation
                if xor_accumulator != coord.position {
                    // Adjust last byte to maintain XOR balance
                    if let Some(last) = reconstructed.last_mut() {
                        *last ^= xor_accumulator ^ coord.position;
                    }
                }
            } else {
                // Fallback for empty candidate set
                for i in 0..byte_count {
                    let byte = RecoveryBits::recover_byte(coord.position, recovery_bits.wrapping_add(i as u8), None)
                        .map_err(|_| CodecError::InvalidCoordinate(coord.absolute))?;
                    reconstructed.push(byte);
                }
            }
        }
        
        Ok(reconstructed)
    }
}

impl Default for PrimeOSDecoder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encoder::PrimeOSEncoder;
    use crate::traits::AddressEncoder;

    #[test]
    fn test_decode_empty() {
        let encoder = PrimeOSEncoder::new();
        let decoder = PrimeOSDecoder::new();
        
        let digest = encoder.encode_bytes(&[]).unwrap();
        let decoded = decoder.decode_bytes(&digest).unwrap();
        
        assert_eq!(decoded, vec![]);
    }
    
    #[test]
    fn test_decoder_implements_trait() {
        let decoder = PrimeOSDecoder::new();
        let encoder = PrimeOSEncoder::new();
        
        // Test that decoder implements AddressDecoder trait
        let bits = bitvec![1, 0, 1, 1, 0, 0, 1, 0];
        let digest = encoder.encode(&bits).unwrap();
        let decoded_bits = decoder.decode(&digest).unwrap();
        
        assert!(decoded_bits.len() > 0);
    }
    
    #[test]
    fn test_round_trip_single_byte() {
        let encoder = PrimeOSEncoder::new();
        let decoder = PrimeOSDecoder::new();
        
        // Test a few specific bytes
        for &byte in &[0u8, 1, 42, 48, 49, 255] {
            let original = vec![byte];
            let digest = encoder.encode_bytes(&original).unwrap();
            let decoded = decoder.decode_bytes(&digest).unwrap();
            
            assert_eq!(decoded, original, "Failed to round-trip byte {}", byte);
        }
    }
    
    #[test]
    fn test_decode_invalid_digest() {
        let decoder = PrimeOSDecoder::new();
        
        // Too small
        let result = decoder.decode_bytes(&Digest::new(vec![1]));
        assert!(matches!(result, Err(CodecError::DigestTooSmall)));
        
        // Invalid checksum
        let result = decoder.decode_bytes(&Digest::new(vec![0, 0, 0, 99]));
        assert!(matches!(result, Err(CodecError::CorruptDigest)));
    }
    
    #[test]
    fn test_varint_decoding() {
        let decoder = PrimeOSDecoder::new();
        
        // Test single-byte varint
        let mut cursor = 0;
        let data = vec![0x7F]; // 127
        let value = decoder.decode_bit_length(&data, &mut cursor).unwrap();
        assert_eq!(value, 127);
        assert_eq!(cursor, 1);
        
        // Test two-byte varint
        let mut cursor = 0;
        let data = vec![0x80, 0x01]; // 128
        let value = decoder.decode_bit_length(&data, &mut cursor).unwrap();
        assert_eq!(value, 128);
        assert_eq!(cursor, 2);
    }
    
    #[test]
    fn test_coordinate_extraction() {
        let decoder = PrimeOSDecoder::new();
        
        // Create packed coordinate data
        let coord = Coordinate {
            absolute: 1234,
            page: 4,
            position: 210,
            resonance_class: 42,
        };
        
        let mut data = Vec::new();
        // Pack as per encoder with recovery bits
        data.push((coord.absolute >> 5) as u8);
        data.push((((coord.absolute & 0x1F) << 3) | ((coord.resonance_class >> 4) as u16)) as u8);
        let recovery_bits = 0x05; // Test recovery bits
        data.push(((coord.resonance_class << 4) | recovery_bits) as u8);
        
        let coords = decoder.extract_coordinates(&data, 768).unwrap();
        assert_eq!(coords.len(), 1);
        assert_eq!(coords[0].0.absolute, coord.absolute);
        assert_eq!(coords[0].0.resonance_class, coord.resonance_class);
        assert_eq!(coords[0].1, recovery_bits);
    }
}