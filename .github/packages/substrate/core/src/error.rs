//! Error types for the PrimeOS codec

use thiserror::Error;

/// Result type for codec operations
pub type Result<T> = std::result::Result<T, CodecError>;

/// Errors that can occur during encoding/decoding
#[derive(Error, Debug, Clone, PartialEq)]
pub enum CodecError {
    /// Invalid digest format
    #[error("Invalid digest format")]
    InvalidDigest,
    
    /// Invalid coordinate
    #[error("Invalid coordinate: {0}")]
    InvalidCoordinate(u16),
    
    /// Digest too small
    #[error("Digest too small: minimum 2 bytes required")]
    DigestTooSmall,
    
    /// Bit length overflow
    #[error("Bit length overflow: {0} bits exceeds maximum")]
    BitLengthOverflow(usize),
    
    /// Corrupt digest
    #[error("Corrupt digest: checksum mismatch")]
    CorruptDigest,
    
    /// Empty input provided
    #[error("Empty input provided")]
    EmptyInput,
}

impl CodecError {
    /// Check if error is fatal (unrecoverable)
    pub fn is_fatal(&self) -> bool {
        matches!(self, 
            CodecError::InvalidDigest | 
            CodecError::InvalidCoordinate(_) |
            CodecError::DigestTooSmall |
            CodecError::BitLengthOverflow(_) |
            CodecError::CorruptDigest
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_messages() {
        assert_eq!(CodecError::InvalidDigest.to_string(), "Invalid digest format");
        assert_eq!(CodecError::InvalidCoordinate(12345).to_string(), "Invalid coordinate: 12345");
        assert_eq!(CodecError::DigestTooSmall.to_string(), "Digest too small: minimum 2 bytes required");
        assert_eq!(CodecError::BitLengthOverflow(1000000).to_string(), "Bit length overflow: 1000000 bits exceeds maximum");
        assert_eq!(CodecError::CorruptDigest.to_string(), "Corrupt digest: checksum mismatch");
        assert_eq!(CodecError::EmptyInput.to_string(), "Empty input provided");
    }

    #[test]
    fn test_is_fatal() {
        assert!(CodecError::InvalidDigest.is_fatal());
        assert!(CodecError::InvalidCoordinate(0).is_fatal());
        assert!(CodecError::DigestTooSmall.is_fatal());
        assert!(CodecError::BitLengthOverflow(0).is_fatal());
        assert!(CodecError::CorruptDigest.is_fatal());
        assert!(!CodecError::EmptyInput.is_fatal());
    }
}