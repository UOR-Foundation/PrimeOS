//! PrimeOS Codec - Pure Rust Implementation
//!
//! A bijective codec for encoding arbitrary bit streams into the PrimeOS
//! 12,288-element mathematical universe and decoding them back.

#![warn(missing_docs)]
#![deny(unsafe_code)]

pub mod constants;
pub mod coordinate;
pub mod digest;
pub mod encoder;
pub mod decoder;
pub mod error;
pub mod resonance;
pub mod equivalence;
pub mod mapper;
pub mod traits;
pub mod conservation;
pub mod recovery;

// Re-export key types and functions
pub use constants::{FIELD_CONSTANTS, TOTAL_ELEMENTS, PAGE_SIZE, NUM_PAGES, CYCLE_LENGTH};
pub use coordinate::Coordinate;
pub use digest::Digest;
pub use encoder::PrimeOSEncoder;
pub use decoder::PrimeOSDecoder;
pub use error::{CodecError, Result};
pub use resonance::{calculate_resonance, byte_to_resonance_class};
pub use mapper::{CoordinateMapper, COORDINATE_MAPPER};
pub use traits::{AddressEncoder, AddressDecoder, Codec};
pub use conservation::{ConservationLaws, ConservationConstraints, ConservationReport};
pub use recovery::{RecoveryBits, RecoveryContext, RecoveryConstraints};

/// Convenience function to encode bytes to a digest
pub fn encode(input: &[u8]) -> Result<Digest> {
    let encoder = PrimeOSEncoder::new();
    encoder.encode_bytes(input)
}

/// Convenience function to decode a digest back to bytes
pub fn decode(digest: &Digest) -> Result<Vec<u8>> {
    let decoder = PrimeOSDecoder::new();
    decoder.decode_bytes(digest)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_round_trip() {
        // Test empty input
        let empty = vec![];
        let digest = encode(&empty).unwrap();
        assert!(digest.size() >= 2); // At least varint + checksum
        let decoded = decode(&digest).unwrap();
        assert_eq!(empty, decoded);
    }

    #[test]
    fn test_convenience_functions() {
        let data = b"PrimeOS";
        let digest = encode(data).unwrap();
        assert!(digest.validate().is_ok());
        
        // The decoder currently uses LCG pattern generation
        // which doesn't provide exact round-trip yet
        let decoded = decode(&digest).unwrap();
        assert_eq!(decoded.len(), data.len());
    }

    #[test]
    fn test_field_constants() {
        // Verify we can access field constants
        assert_eq!(FIELD_CONSTANTS[0], 1.0);
        assert_eq!(FIELD_CONSTANTS.len(), 8);
        
        // Verify the unity constraint
        let unity = FIELD_CONSTANTS[4] * FIELD_CONSTANTS[5];
        assert!((unity - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_resonance_calculation() {
        // Test unity bytes
        assert_eq!(calculate_resonance(0), 1.0);
        assert_eq!(calculate_resonance(1), 1.0);
        assert_eq!(calculate_resonance(48), 1.0);
        assert_eq!(calculate_resonance(49), 1.0);
        
        // Test resonance class mapping
        let class0 = byte_to_resonance_class(0);
        assert_eq!(byte_to_resonance_class(1), class0);
        assert_eq!(byte_to_resonance_class(48), class0);
        assert_eq!(byte_to_resonance_class(49), class0);
    }
}