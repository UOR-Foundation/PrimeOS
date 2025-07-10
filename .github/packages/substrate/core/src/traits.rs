//! Core traits for the PrimeOS codec
//! 
//! These traits define the interface for encoding and decoding operations.

use crate::{Digest, Result};
use bitvec::prelude::*;

/// Core trait for encoding bit patterns to digests
pub trait AddressEncoder {
    /// Encode an arbitrary bit pattern to a digest
    fn encode(&self, bits: &BitSlice) -> Result<Digest>;
}

/// Core trait for decoding digests back to bit patterns
pub trait AddressDecoder {
    /// Decode a digest back to its original bit pattern
    fn decode(&self, digest: &Digest) -> Result<BitVec>;
}

/// Combined encoder/decoder trait
pub trait Codec: AddressEncoder + AddressDecoder {
    /// Verify bijection property - encoding then decoding returns original
    fn verify_bijection(&self, bits: &BitSlice) -> Result<bool> {
        let digest = self.encode(bits)?;
        let decoded = self.decode(&digest)?;
        Ok(bits == decoded.as_bitslice())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::CodecError;

    // Mock encoder for testing
    struct MockEncoder;
    
    impl AddressEncoder for MockEncoder {
        fn encode(&self, bits: &BitSlice) -> Result<Digest> {
            // Simple mock: store bit length and first few bits
            let mut data = Vec::new();
            
            // Store length as first byte (for small tests)
            data.push(bits.len() as u8);
            
            // Store first byte of data if any
            if !bits.is_empty() {
                let mut byte = 0u8;
                for (i, bit) in bits.iter().take(8).enumerate() {
                    if *bit {
                        byte |= 1 << (7 - i);
                    }
                }
                data.push(byte);
            }
            
            // Add checksum
            let checksum = data.iter().fold(0u8, |acc, &b| acc.wrapping_add(b));
            data.push(checksum);
            
            Ok(Digest::from(data))
        }
    }

    // Mock decoder for testing
    struct MockDecoder;
    
    impl AddressDecoder for MockDecoder {
        fn decode(&self, digest: &Digest) -> Result<BitVec> {
            let data = digest.as_bytes();
            if data.len() < 2 {
                return Err(CodecError::DigestTooSmall);
            }
            
            // Verify checksum
            let checksum = data[data.len() - 1];
            let calculated = data[..data.len() - 1].iter()
                .fold(0u8, |acc, &b| acc.wrapping_add(b));
            if checksum != calculated {
                return Err(CodecError::CorruptDigest);
            }
            
            // Extract length
            let bit_len = data[0] as usize;
            let mut bits = BitVec::with_capacity(bit_len);
            
            // Extract bits from second byte if present
            if data.len() > 2 {
                let byte = data[1];
                for i in 0..bit_len.min(8) {
                    bits.push((byte >> (7 - i)) & 1 != 0);
                }
            }
            
            // Fill remaining with zeros (mock behavior)
            while bits.len() < bit_len {
                bits.push(false);
            }
            
            Ok(bits)
        }
    }

    // Combined mock codec
    struct MockCodec;
    
    impl AddressEncoder for MockCodec {
        fn encode(&self, bits: &BitSlice) -> Result<Digest> {
            MockEncoder.encode(bits)
        }
    }
    
    impl AddressDecoder for MockCodec {
        fn decode(&self, digest: &Digest) -> Result<BitVec> {
            MockDecoder.decode(digest)
        }
    }
    
    impl Codec for MockCodec {}

    #[test]
    fn test_encoder_trait() {
        let encoder = MockEncoder;
        let bits = bitvec![1, 0, 1, 1, 0, 0, 1, 0];
        
        let digest = encoder.encode(&bits).unwrap();
        assert!(digest.size() >= 3); // length + data + checksum
        
        // Verify length is encoded
        assert_eq!(digest.as_bytes()[0], 8);
    }

    #[test]
    fn test_decoder_trait() {
        let decoder = MockDecoder;
        
        // Create a valid digest
        let data = vec![8, 0b10110010, 186]; // length=8, data, checksum
        let digest = Digest::from(data);
        
        let bits = decoder.decode(&digest).unwrap();
        assert_eq!(bits.len(), 8);
        assert_eq!(bits.as_raw_slice()[0] & 0b11110000, 0b10110000);
    }

    #[test]
    fn test_codec_bijection() {
        let codec = MockCodec;
        
        // Test with simple pattern
        let original = bitvec![1, 0, 1, 1, 0, 0, 1, 0];
        let is_bijective = codec.verify_bijection(&original).unwrap();
        
        // Our mock only preserves first 8 bits perfectly
        assert!(is_bijective);
    }

    #[test]
    fn test_codec_empty_input() {
        let codec = MockCodec;
        
        let empty = bitvec![];
        let digest = codec.encode(&empty).unwrap();
        let decoded = codec.decode(&digest).unwrap();
        
        assert_eq!(decoded.len(), 0);
        assert!(codec.verify_bijection(&empty).unwrap());
    }

    #[test]
    fn test_decoder_checksum_validation() {
        let decoder = MockDecoder;
        
        // Create digest with invalid checksum
        let data = vec![8, 0b10110010, 99]; // wrong checksum
        let digest = Digest::from(data);
        
        let result = decoder.decode(&digest);
        assert!(matches!(result, Err(CodecError::CorruptDigest)));
    }

    #[test]
    fn test_decoder_too_small() {
        let decoder = MockDecoder;
        
        let digest = Digest::from(vec![1]); // Too small
        let result = decoder.decode(&digest);
        assert!(matches!(result, Err(CodecError::DigestTooSmall)));
    }
}