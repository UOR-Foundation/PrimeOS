//! Core CCM types and unified API
//!
//! This crate provides the foundational types and unified interface for
//! Coherence-Centric Mathematics (CCM).

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

// Core modules
pub mod bitword;
pub mod error;
pub mod math;

// Re-export commonly used types
pub use bitword::BitWord;
pub use error::CcmError;

// Float trait for numeric operations
pub use num_traits::Float;

// Core API trait
pub trait CCMCore<P: Float> {
    /// The section type representing embedded mathematical objects
    type Section: Clone;

    /// Embed a mathematical object into a CCM section
    fn embed(&self, object: &BitWord, alpha: &[P]) -> Result<Self::Section, CcmError>;

    /// Compute the coherence norm of a section
    fn coherence_norm(&self, section: &Self::Section) -> P;

    /// Minimize coherence norm of a section
    fn minimize_coherence(&self, initial: &Self::Section) -> Result<Self::Section, CcmError>;

    /// Find minimum resonance element in an equivalence class
    fn find_minimum_resonance(&self, input: &BitWord, alpha: &[P]) -> Result<BitWord, CcmError>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitword_creation() {
        let word = BitWord::from_u8(42);
        assert_eq!(word.len(), 8);
    }
}
