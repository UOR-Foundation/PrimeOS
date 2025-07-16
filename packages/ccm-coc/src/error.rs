//! Error types for the COC framework

use ccm_core::CcmError;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::string::String;
#[cfg(feature = "std")]
use std::string::String;

/// Result type alias for COC operations
pub type Result<T> = core::result::Result<T, CocError>;

/// Error types that can occur in COC operations
#[derive(Debug, Clone, PartialEq)]
pub enum CocError {
    /// Object cannot be decomposed further
    Atomic,
    
    /// No valid decomposition found
    NoDecomposition,
    
    /// Conservation law violated
    ConservationViolation {
        /// ID of the violated law
        law_id: String,
        /// Expected value
        expected: f64,
        /// Actual value
        actual: f64,
        /// Relative error
        relative_error: f64,
    },
    
    /// Decomposition timed out
    Timeout,
    
    /// Invalid configuration
    InvalidConfig(String),
    
    /// CCM operation failed
    CCMError(CcmError),
    
    /// Domain-specific error
    DomainError(String),
    
    /// Invalid input provided
    InvalidInput(String),
    
    /// Feature not implemented
    NotImplemented(String),
    
    /// Numerical precision error
    NumericalError(String),
}

impl From<CcmError> for CocError {
    fn from(err: CcmError) -> Self {
        CocError::CCMError(err)
    }
}

impl core::fmt::Display for CocError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            CocError::Atomic => write!(f, "Object is atomic and cannot be decomposed"),
            CocError::NoDecomposition => write!(f, "No valid decomposition found"),
            CocError::ConservationViolation { law_id, expected, actual, relative_error } => {
                write!(
                    f,
                    "Conservation law '{}' violated: expected {}, got {} (error: {})",
                    law_id, expected, actual, relative_error
                )
            }
            CocError::Timeout => write!(f, "Decomposition timed out"),
            CocError::InvalidConfig(msg) => write!(f, "Invalid configuration: {}", msg),
            CocError::CCMError(err) => write!(f, "CCM error: {:?}", err),
            CocError::DomainError(msg) => write!(f, "Domain error: {}", msg),
            CocError::InvalidInput(msg) => write!(f, "Invalid input: {}", msg),
            CocError::NotImplemented(msg) => write!(f, "Not implemented: {}", msg),
            CocError::NumericalError(msg) => write!(f, "Numerical error: {}", msg),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for CocError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}