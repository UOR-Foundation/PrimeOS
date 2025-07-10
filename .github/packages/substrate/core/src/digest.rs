//! Digest structure for PrimeOS codec

use crate::error::{CodecError, Result};
use std::fmt;

/// A digest that uniquely identifies encoded data
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Digest {
    /// The actual digest data (variable length, min 4 bytes)
    pub data: Vec<u8>,
}

impl Digest {
    /// Create a new digest from raw bytes
    pub fn new(data: Vec<u8>) -> Self {
        Self { data }
    }

    /// Get the size in bytes
    pub fn size(&self) -> usize {
        self.data.len()
    }

    /// Create from raw bytes (with validation)
    pub fn from_bytes(bytes: Vec<u8>) -> Result<Self> {
        if bytes.len() < 2 {  // Minimum is varint + checksum
            return Err(CodecError::DigestTooSmall);
        }
        Ok(Self { data: bytes })
    }

    /// Get as byte slice
    pub fn as_bytes(&self) -> &[u8] {
        &self.data
    }

    /// Convert to hex string for display
    pub fn to_hex(&self) -> String {
        hex::encode(&self.data)
    }

    /// Validate the digest's integrity using checksum
    pub fn validate(&self) -> Result<()> {
        if self.data.len() < 2 {  // Minimum is varint + checksum
            return Err(CodecError::DigestTooSmall);
        }

        // The last byte is the checksum
        let data_len = self.data.len() - 1;
        let expected_checksum = self.data[data_len];
        let actual_checksum = Self::calculate_checksum(&self.data[..data_len]);

        if expected_checksum != actual_checksum {
            return Err(CodecError::CorruptDigest);
        }

        Ok(())
    }

    /// Calculate simple checksum for integrity
    fn calculate_checksum(data: &[u8]) -> u8 {
        data.iter().fold(0u8, |acc, &byte| acc.wrapping_add(byte))
    }
}

impl fmt::Display for Digest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let hex = self.to_hex();
        if hex.len() > 32 {
            write!(f, "Digest({}...)", &hex[..32])
        } else {
            write!(f, "Digest({})", hex)
        }
    }
}

impl From<Vec<u8>> for Digest {
    fn from(data: Vec<u8>) -> Self {
        Self::new(data)
    }
}

impl AsRef<[u8]> for Digest {
    fn as_ref(&self) -> &[u8] {
        &self.data
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_digest_creation() {
        let data = vec![1, 2, 3, 4, 5];
        let digest = Digest::new(data.clone());
        assert_eq!(digest.size(), 5);
        assert_eq!(digest.as_bytes(), &data);
    }

    #[test]
    fn test_digest_validation() {
        // Create a valid digest with checksum
        let mut data = vec![1, 2, 3, 4];
        let checksum = data.iter().fold(0u8, |acc, &b| acc.wrapping_add(b));
        data.push(checksum);

        let digest = Digest::new(data);
        assert!(digest.validate().is_ok());

        // Create an invalid digest
        let invalid_digest = Digest::new(vec![1, 2, 3, 99]);
        assert!(invalid_digest.validate().is_err());
    }

    #[test]
    fn test_digest_too_small() {
        let result = Digest::from_bytes(vec![1]);
        assert!(matches!(result, Err(CodecError::DigestTooSmall)));
    }

    #[test]
    fn test_hex_conversion() {
        let digest = Digest::new(vec![0xDE, 0xAD, 0xBE, 0xEF]);
        assert_eq!(digest.to_hex(), "deadbeef");
    }

    #[test]
    fn test_display() {
        let short_digest = Digest::new(vec![0xAB; 8]);
        assert_eq!(format!("{}", short_digest), "Digest(abababababababab)");

        let long_digest = Digest::new(vec![0xCD; 20]);
        let display = format!("{}", long_digest);
        assert!(display.starts_with("Digest(cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd..."));
    }
}