//! SHA-256 wrapper utilities

use ccm_core::CcmError;

#[cfg(feature = "sha2")]
use sha2::{Digest, Sha256};

/// Compute SHA-256 hash of data
#[cfg(feature = "sha2")]
pub fn sha256(data: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(data);
    let result = hasher.finalize();

    let mut output = [0u8; 32];
    output.copy_from_slice(&result);
    output
}

/// Verify SHA-256 hash
#[cfg(feature = "sha2")]
pub fn verify_sha256(data: &[u8], expected: &[u8; 32]) -> Result<(), CcmError> {
    let computed = sha256(data);

    // Constant-time comparison if ct feature is enabled
    #[cfg(feature = "ct")]
    {
        use subtle::ConstantTimeEq;
        if computed.ct_eq(expected).into() {
            Ok(())
        } else {
            Err(CcmError::HashMismatch)
        }
    }

    #[cfg(not(feature = "ct"))]
    {
        if computed == *expected {
            Ok(())
        } else {
            Err(CcmError::HashMismatch)
        }
    }
}

/// Stub implementation when sha2 feature is disabled
#[cfg(not(feature = "sha2"))]
pub fn sha256(_data: &[u8]) -> [u8; 32] {
    [0u8; 32]
}

#[cfg(not(feature = "sha2"))]
pub fn verify_sha256(_data: &[u8], _expected: &[u8; 32]) -> Result<(), CcmError> {
    Err(CcmError::Custom("SHA-256 feature not enabled"))
}

#[cfg(all(test, feature = "sha2"))]
mod tests {
    use super::*;

    #[test]
    fn test_sha256() {
        let data = b"hello world";
        let hash = sha256(data);

        // Known hash for "hello world"
        let expected = [
            0xb9, 0x4d, 0x27, 0xb9, 0x93, 0x4d, 0x3e, 0x08, 0xa5, 0x2e, 0x52, 0xd7, 0xda, 0x7d,
            0xab, 0xfa, 0xc4, 0x84, 0xef, 0xe3, 0x7a, 0x53, 0x80, 0xee, 0x90, 0x88, 0xf7, 0xac,
            0xe2, 0xef, 0xcd, 0xe9,
        ];

        assert_eq!(hash, expected);
    }

    #[test]
    fn test_verify_sha256() {
        let data = b"test data";
        let hash = sha256(data);

        assert!(verify_sha256(data, &hash).is_ok());

        let wrong_hash = [0xFF; 32];
        assert!(verify_sha256(data, &wrong_hash).is_err());
    }
}
