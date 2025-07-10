//! Core primitives for Coherence-Centric Mathematics (CCM).
//!
//! This crate provides all low-level building blocks required by any CCM implementation,
//! including the BJC-1.0 codec. The implementation follows the normative specification v1.0.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod alpha;
pub mod bitword;
pub mod codec;
pub mod coherence;
pub mod error;
pub mod hash;
pub mod math;
pub mod page;
pub mod resonance;

#[cfg(test)]
mod tests;

// Re-export core types and functions
pub use alpha::{AlphaError, AlphaVec};
pub use bitword::{BitWord, BitWordDyn};
pub use codec::bjc::{decode_bjc, encode_bjc, BjcPacket, FloatEncoding};
pub use codec::search::search_b_min;
pub use coherence::Coherence;
pub use error::CcmError;
pub use page::{inject_page, page_of};
pub use resonance::Resonance;

#[cfg(feature = "sha2")]
pub use hash::{sha256, verify_sha256};

// Common trait bounds used throughout the crate
pub trait Float:
    num_traits::Float + num_traits::FromPrimitive + core::fmt::Debug + core::fmt::Display + Copy
{
}
