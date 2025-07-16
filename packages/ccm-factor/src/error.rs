//! Error types for CCM-Factor

use core::fmt;

#[cfg(feature = "std")]
use std::error::Error;

/// Result type for CCM-Factor operations
pub type Result<T> = core::result::Result<T, FactorError>;

/// Errors that can occur during factorization
#[derive(Debug, Clone, PartialEq)]
pub enum FactorError {
    /// CCM core error
    CCMError(ccm_core::CcmError),

    /// Invalid input (e.g., zero, one)
    InvalidInput(String),

    /// Factorization failed after maximum attempts
    FactorizationFailed,

    /// Verification of factors failed
    VerificationFailed,

    /// Numerical overflow occurred
    Overflow,

    /// Insufficient precision for operation
    InsufficientPrecision,

    /// No alignment windows found
    NoAlignmentFound,

    /// Conservation law violation
    ConservationViolation(String),

    /// Channel size mismatch
    ChannelSizeMismatch,
    
    /// Internal error (cache, locks, etc)
    InternalError(String),
}

impl fmt::Display for FactorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CCMError(e) => write!(f, "CCM error: {:?}", e),
            Self::InvalidInput(msg) => write!(f, "Invalid input: {}", msg),
            Self::FactorizationFailed => write!(f, "Factorization failed after maximum attempts"),
            Self::VerificationFailed => write!(f, "Factor verification failed"),
            Self::Overflow => write!(f, "Numerical overflow occurred"),
            Self::InsufficientPrecision => write!(f, "Insufficient precision for operation"),
            Self::NoAlignmentFound => write!(f, "No alignment windows found"),
            Self::ConservationViolation(msg) => write!(f, "Conservation law violation: {}", msg),
            Self::ChannelSizeMismatch => write!(f, "Channel size mismatch"),
            Self::InternalError(msg) => write!(f, "Internal error: {}", msg),
        }
    }
}

#[cfg(feature = "std")]
impl Error for FactorError {}

impl From<ccm_core::CcmError> for FactorError {
    fn from(err: ccm_core::CcmError) -> Self {
        Self::CCMError(err)
    }
}
