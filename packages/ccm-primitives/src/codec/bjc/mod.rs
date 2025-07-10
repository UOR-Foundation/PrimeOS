//! BJC-1.0 encoder/decoder implementation

use crate::hash::{sha256, verify_sha256};
use crate::page::page_of;
use crate::{AlphaVec, BitWord, CcmError, Float, Resonance};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// BJC packet structure
#[derive(Debug, Clone, PartialEq)]
pub struct BjcPacket {
    /// Header n (bit-7 ⇒ binary128)
    pub n_bits: u8,

    /// log₂(k) where k is the number of channels
    pub log2_k: u8,

    /// Minimum resonance value (8 or 16 bytes)
    pub r_min: Vec<u8>,

    /// Bit flips from Klein group (last 2 bits only)
    pub flips: u8,

    /// Page data (empty when k = 1)
    pub page: Vec<u8>,

    /// Optional SHA-256 hash
    pub hash: Option<[u8; 32]>,
}

/// Magic bytes for different BJC versions
pub const MAGIC_BJC0: &[u8; 4] = b"BJC0"; // No hash
pub const MAGIC_BJC1: &[u8; 4] = b"BJC1"; // With hash

/// Encode a BitWord into BJC format
pub fn encode_bjc<P: FloatEncoding, const N: usize>(
    raw: &BitWord<N>,
    alpha: &AlphaVec<P>,
    k: usize,
    include_hash: bool,
) -> Result<BjcPacket, CcmError> {
    // Step 1: Validate inputs
    if N < 2 {
        return Err(CcmError::InvalidLength);
    }

    if alpha.len() < N {
        return Err(CcmError::InvalidLength);
    }

    // Check precision requirements
    if N > 53 && core::mem::size_of::<P>() <= 8 {
        #[cfg(not(feature = "binary128"))]
        return Err(CcmError::UnsupportedPrecision);
    }

    // Step 2: Find b_min with minimum resonance
    let b_min = find_minimum_resonance(raw, alpha)?;

    // Step 3: Compute flips (XOR restricted to last 2 bits)
    let flips = (raw.to_usize() ^ b_min.to_usize()) as u8 & 0b11;

    // Step 4: Compute page (if k > 1)
    let page_data = if k > 1 {
        let page_idx = page_of(b_min);
        encode_page(page_idx, k)?
    } else {
        Vec::new()
    };

    // Step 5: Encode r_min
    let r_min_value = b_min.r(alpha)?;
    let r_min_bytes = encode_float(r_min_value)?;

    // Step 6: Compute hash if requested
    let hash = if include_hash {
        let mut data = Vec::new();
        data.push(N as u8);
        data.push((k as u32).trailing_zeros() as u8);
        data.extend_from_slice(&r_min_bytes);
        data.push(flips);
        data.extend_from_slice(&page_data);

        Some(sha256(&data))
    } else {
        None
    };

    // Create packet
    let n_bits = if cfg!(feature = "binary128") && N > 53 {
        N as u8 | 0x80
    } else {
        N as u8
    };

    Ok(BjcPacket {
        n_bits,
        log2_k: (k as u32).trailing_zeros() as u8,
        r_min: r_min_bytes,
        flips,
        page: page_data,
        hash,
    })
}

/// Decode a BJC packet back to BitWord
pub fn decode_bjc<P: FloatEncoding, const N: usize>(
    packet: &BjcPacket,
    alpha: &AlphaVec<P>,
) -> Result<BitWord<N>, CcmError> {
    // Validate packet
    let packet_n = packet.n_bits & 0x7F;
    if packet_n as usize != N {
        return Err(CcmError::InvalidLength);
    }

    // Decode r_min
    let r_min_value: P = decode_float(&packet.r_min)?;

    // Find b_min by searching for the resonance value
    let b_min = find_by_resonance(r_min_value, alpha, N)?;

    // Verify resonance matches within tolerance
    let computed_r = b_min.r(alpha)?;
    if !resonance_matches(computed_r, r_min_value) {
        return Err(CcmError::Custom("Resonance mismatch"));
    }

    // Apply flips to recover original
    let mut raw = b_min;
    let flips_mask = packet.flips as u64;
    raw = BitWord::from(raw.to_usize() as u64 ^ flips_mask);

    // Verify hash if present
    if let Some(expected_hash) = &packet.hash {
        let mut data = Vec::new();
        data.push(packet.n_bits);
        data.push(packet.log2_k);
        data.extend_from_slice(&packet.r_min);
        data.push(packet.flips);
        data.extend_from_slice(&packet.page);

        verify_sha256(&data, expected_hash)?;
    }

    Ok(raw)
}

/// Find the Klein group element with minimum resonance
fn find_minimum_resonance<P: FloatEncoding, const N: usize>(
    raw: &BitWord<N>,
    alpha: &AlphaVec<P>,
) -> Result<BitWord<N>, CcmError> {
    let klein_group = [0u64, 1, 48, 49]; // V₄ = {0, 1, 48, 49}
    let raw_value = raw.to_usize() as u64;

    let mut min_resonance = P::infinity();
    let mut b_min = *raw;

    for &mask in &klein_group {
        let candidate_value = raw_value ^ (mask & 0b11); // Restrict to last 2 bits
        let candidate = BitWord::<N>::from(candidate_value);

        let resonance = candidate.r(alpha)?;

        if resonance < min_resonance {
            min_resonance = resonance;
            b_min = candidate;
        } else if resonance == min_resonance {
            // Tie-breaking: choose numerically smallest
            if candidate_value < b_min.to_usize() as u64 {
                b_min = candidate;
            }
        }
    }

    Ok(b_min)
}

/// Find a BitWord with the given resonance value
fn find_by_resonance<P: FloatEncoding, const N: usize>(
    target: P,
    alpha: &AlphaVec<P>,
    n: usize,
) -> Result<BitWord<N>, CcmError> {
    // In a real implementation, this would use the search module
    // For now, brute force search
    let max = if n == 64 { !0u64 } else { (1u64 << n) - 1 };

    for i in 0..=max {
        let candidate = BitWord::<N>::from(i);
        let resonance = candidate.r(alpha)?;

        if resonance_matches(resonance, target) {
            return Ok(candidate);
        }
    }

    Err(CcmError::SearchExhausted)
}

/// Check if two resonance values match within tolerance
fn resonance_matches<P: FloatEncoding>(a: P, b: P) -> bool {
    use crate::math::approx_eq;

    // 2 ulp for f64, 1 ulp for binary128
    let tolerance = if cfg!(feature = "binary128") {
        <P as num_traits::Float>::epsilon()
    } else {
        <P as num_traits::Float>::epsilon()
            * <P as num_traits::FromPrimitive>::from_f64(2.0).unwrap()
    };

    approx_eq(a, b, tolerance)
}

/// Trait for types that can be encoded/decoded as bytes
pub trait FloatEncoding: Float {
    fn encode_bytes(&self) -> Vec<u8>;
    fn decode_bytes(bytes: &[u8]) -> Result<Self, CcmError>;
}

impl FloatEncoding for f32 {
    fn encode_bytes(&self) -> Vec<u8> {
        self.to_le_bytes().to_vec()
    }

    fn decode_bytes(bytes: &[u8]) -> Result<Self, CcmError> {
        if bytes.len() != 4 {
            return Err(CcmError::Custom("Invalid f32 encoding"));
        }
        let mut arr = [0u8; 4];
        arr.copy_from_slice(bytes);
        Ok(f32::from_le_bytes(arr))
    }
}

impl FloatEncoding for f64 {
    fn encode_bytes(&self) -> Vec<u8> {
        self.to_le_bytes().to_vec()
    }

    fn decode_bytes(bytes: &[u8]) -> Result<Self, CcmError> {
        if bytes.len() != 8 {
            return Err(CcmError::Custom("Invalid f64 encoding"));
        }
        let mut arr = [0u8; 8];
        arr.copy_from_slice(bytes);
        Ok(f64::from_le_bytes(arr))
    }
}

/// Encode a float to bytes
fn encode_float<P: FloatEncoding>(value: P) -> Result<Vec<u8>, CcmError> {
    Ok(value.encode_bytes())
}

/// Decode a float from bytes
fn decode_float<P: FloatEncoding>(bytes: &[u8]) -> Result<P, CcmError> {
    P::decode_bytes(bytes)
}

/// Encode page index for multi-channel
fn encode_page(page: usize, _k: usize) -> Result<Vec<u8>, CcmError> {
    // Simple encoding: store page as variable-length integer
    let mut bytes = Vec::new();
    let mut value = page;

    while value > 0 {
        bytes.push((value & 0xFF) as u8);
        value >>= 8;
    }

    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_decode_roundtrip() {
        let alpha =
            AlphaVec::try_from(vec![1.0, 1.618, 0.618, 1.414, 0.707, 1.0, 0.5, 2.0]).unwrap();

        let raw = BitWord::<8>::from(0b10110010u8);
        let packet = encode_bjc(&raw, &alpha, 1, false).unwrap();
        let decoded = decode_bjc::<f64, 8>(&packet, &alpha).unwrap();

        assert_eq!(raw, decoded);
    }
}
