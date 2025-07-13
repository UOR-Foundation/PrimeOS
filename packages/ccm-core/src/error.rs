//! Error types for CCM operations

use core::fmt;

/// Unified error enum for all CCM operations
#[derive(Debug, Clone)]
pub enum CcmError {
    /// Invalid length parameter (e.g., n < 2)
    InvalidLength,

    /// Alpha vector constraint violation (e.g., αₙ₋₂ · αₙ₋₁ ≠ 1)
    AlphaConstraint,

    /// Precision not supported without binary128 feature
    UnsupportedPrecision,

    /// Floating point overflow/underflow in resonance calculation
    FpRange,

    /// SHA-256 hash verification failed
    HashMismatch,

    /// Unknown magic bytes in packet header
    UnknownMagic,

    /// Search exhausted without finding valid encoding
    SearchExhausted,

    /// I/O error
    #[cfg(feature = "std")]
    IoError(String),

    #[cfg(not(feature = "std"))]
    IoError(core::fmt::Error),

    /// Custom error with static string message
    Custom(&'static str),

    /// Invalid input parameters
    InvalidInput,

    /// Feature not implemented
    NotImplemented,
}

impl fmt::Display for CcmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidLength => write!(f, "Invalid length: must be >= 2"),
            Self::AlphaConstraint => {
                write!(f, "Alpha constraint violated: α[n-2] * α[n-1] must equal 1")
            }
            Self::UnsupportedPrecision => {
                write!(f, "Precision not supported without binary128 feature")
            }
            Self::FpRange => write!(f, "Floating point overflow or underflow"),
            Self::HashMismatch => write!(f, "SHA-256 hash verification failed"),
            Self::UnknownMagic => write!(f, "Unknown magic bytes in packet header"),
            Self::SearchExhausted => write!(f, "Search exhausted without finding valid encoding"),
            #[cfg(feature = "std")]
            Self::IoError(msg) => write!(f, "I/O error: {msg}"),
            #[cfg(not(feature = "std"))]
            Self::IoError(_) => write!(f, "I/O error"),
            Self::Custom(msg) => write!(f, "{msg}"),
            Self::InvalidInput => write!(f, "Invalid input parameters"),
            Self::NotImplemented => write!(f, "Feature not implemented"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for CcmError {}

#[cfg(feature = "std")]
impl From<std::io::Error> for CcmError {
    fn from(error: std::io::Error) -> Self {
        Self::IoError(error.to_string())
    }
}

// Implement PartialEq manually
impl PartialEq for CcmError {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::InvalidLength, Self::InvalidLength) => true,
            (Self::AlphaConstraint, Self::AlphaConstraint) => true,
            (Self::UnsupportedPrecision, Self::UnsupportedPrecision) => true,
            (Self::FpRange, Self::FpRange) => true,
            (Self::HashMismatch, Self::HashMismatch) => true,
            (Self::UnknownMagic, Self::UnknownMagic) => true,
            (Self::SearchExhausted, Self::SearchExhausted) => true,
            #[cfg(feature = "std")]
            (Self::IoError(a), Self::IoError(b)) => a == b,
            #[cfg(not(feature = "std"))]
            (Self::IoError(_), Self::IoError(_)) => true, // core::fmt::Error has no PartialEq
            (Self::Custom(a), Self::Custom(b)) => a == b,
            (Self::InvalidInput, Self::InvalidInput) => true,
            (Self::NotImplemented, Self::NotImplemented) => true,
            _ => false,
        }
    }
}
