//! BJC Codec - Efficient data encoding using CCM
//!
//! This crate implements the BJC-1.0 codec specification using
//! Coherence-Centric Mathematics principles for optimal data encoding.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

// Import dependencies
use ccm_core::{BitWord, CCMCore, CcmError, Float};
use ccm_embedding::{AlphaVec, Resonance};

// Modules
pub mod bjc;
pub mod hash;
pub mod search;

// Re-export main codec functions
pub use bjc::{decode_bjc, encode_bjc, BjcPacket, FloatEncoding};
pub use search::search_b_min;

#[cfg(feature = "dynamic")]
pub use bjc::dynamic::{decode_bjc_dynamic, encode_bjc_dynamic};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_encode_decode() {
        let input = BitWord::from_u8(42);
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        let packet = encode_bjc(&input, &alpha, 1, false).unwrap();
        let decoded = decode_bjc(&packet, &alpha).unwrap();

        assert_eq!(input.to_usize(), decoded.to_usize());
    }
}
