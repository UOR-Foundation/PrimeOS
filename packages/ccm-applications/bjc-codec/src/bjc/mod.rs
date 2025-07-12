//! BJC-1.0 encoder/decoder implementation

use crate::hash::{sha256, verify_sha256};
use ccm_core::{BitWord, CcmError, Float};
use ccm_embedding::{page_of, AlphaVec, Resonance};

#[cfg(feature = "alloc")]
use alloc::vec;
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
pub fn encode_bjc<P: FloatEncoding>(
    raw: &BitWord,
    alpha: &AlphaVec<P>,
    k: usize,
    include_hash: bool,
) -> Result<BjcPacket, CcmError> {
    // Step 1: Validate inputs
    let n = raw.len();

    // For Klein groups, we need N >= 2
    if n < 2 {
        return Err(CcmError::InvalidLength);
    }

    // Alpha must have at least 2 values for Klein group operations
    if alpha.len() < 2 {
        return Err(CcmError::InvalidLength);
    }

    // Check precision requirements
    if n > 53 && core::mem::size_of::<P>() <= 8 {
        #[cfg(not(feature = "binary128"))]
        return Err(CcmError::UnsupportedPrecision);
    }

    // Step 2: Find b_min with minimum resonance
    let b_min = find_minimum_resonance(raw, alpha)?;

    // Debug output
    if n == 8 && n <= 64 && raw.to_usize() == 0x28 {
        eprintln!(
            "DEBUG encode 0x28: b_min={}, resonance={}",
            b_min.to_usize(),
            b_min.r(alpha)
        );
    }

    // Step 3: Compute flips (XOR restricted to last 2 bits for Klein groups)
    let flips = if n >= 2 && n <= 64 {
        // For small bit lengths, use efficient bit operations
        let bit_mask = 0b11 << (n - 2); // Mask for bits (N-2, N-1)
        let flips_full = (raw.to_usize() ^ b_min.to_usize()) & bit_mask;
        // Store flips in bits 0,1 of the flip byte
        ((flips_full >> (n - 2)) & 0b11) as u8
    } else if n >= 2 {
        // For large bit lengths, use bit-level operations
        let mut flips = 0u8;
        if raw.bit(n - 2) != b_min.bit(n - 2) {
            flips |= 0b01;
        }
        if raw.bit(n - 1) != b_min.bit(n - 1) {
            flips |= 0b10;
        }
        flips
    } else {
        0 // No Klein groups for n < 2
    };

    // Step 4: Compute page (if k > 1)
    let page_data = if k > 1 {
        let page_idx = page_of(&b_min);
        encode_page(page_idx, k)?
    } else {
        Vec::new()
    };

    // Step 5: Encode r_min
    let r_min_value = b_min.r(alpha);
    let r_min_bytes = encode_float(r_min_value)?;

    // Step 6: Compute hash if requested
    let hash = if include_hash {
        let mut data = Vec::new();
        data.push(n as u8);
        data.push((k as u32).trailing_zeros() as u8);
        data.extend_from_slice(&r_min_bytes);
        data.push(flips);
        data.extend_from_slice(&page_data);

        Some(sha256(&data))
    } else {
        None
    };

    // Create packet
    let n_bits = if cfg!(feature = "binary128") && n > 53 {
        n as u8 | 0x80
    } else {
        n as u8
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
pub fn decode_bjc<P: FloatEncoding>(
    packet: &BjcPacket,
    alpha: &AlphaVec<P>,
) -> Result<BitWord, CcmError> {
    // Validate packet
    let n = (packet.n_bits & 0x7F) as usize;

    if n < 2 {
        return Err(CcmError::InvalidLength);
    }

    // Decode r_min
    let r_min_value: P = decode_float(&packet.r_min)?;

    // The BJC spec requires deterministic encoding/decoding
    // When multiple Klein groups have the same minimum resonance,
    // the encoder uses the first valid b_min (in lexicographic order)
    // that can produce the input through valid flips.
    // The decoder must use the same logic.

    // Find all possible b_min values with the target resonance
    let b_min_candidates: Vec<BitWord> = find_all_by_resonance(r_min_value, alpha, n)?;

    // Apply flips to recover original
    // Flips are stored in bits 0,1 of the flip byte, but apply to bits (n-2, n-1)

    // Try all candidates and collect valid decodings
    let mut valid_decodings: Vec<BitWord> = Vec::new();

    for b_min in b_min_candidates {
        // Apply flips to get the candidate original value
        let mut candidate_raw = b_min.clone();

        // Apply flips at positions (n-2, n-1)
        if n >= 2 {
            if packet.flips & 0b01 != 0 {
                candidate_raw.flip_bit(n - 2);
            }
            if packet.flips & 0b10 != 0 {
                candidate_raw.flip_bit(n - 1);
            }
        }

        // Check if this b_min is valid for the candidate
        // by verifying it's the minimum in candidate's Klein group
        let class_members = <BitWord as Resonance<P>>::class_members(&candidate_raw);

        let mut min_resonance = P::infinity();
        let mut min_member = class_members[0].clone();

        for member in &class_members {
            let r = member.r(alpha);
            if r < min_resonance {
                min_resonance = r;
                min_member = member.clone();
            } else if r == min_resonance && n <= 64 && member.to_usize() < min_member.to_usize() {
                min_resonance = r;
                min_member = member.clone();
            }
        }

        // Check if b_min is the minimum member
        if min_member == b_min {
            // Valid decoding found!
            valid_decodings.push(candidate_raw);
        }
    }

    // If we found valid decodings, return the lexicographically smallest one
    // (This ensures deterministic decoding when there are ties)
    if !valid_decodings.is_empty() {
        // For BitWords that fit in usize, sort by numeric value
        // For larger BitWords, this would need a different comparison
        if n <= 64 {
            valid_decodings.sort_by_key(|b| b.to_usize());
        }
        let raw = valid_decodings[0].clone();

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

        return Ok(raw);
    }

    // If no valid candidate found, return error
    Err(CcmError::Custom("No valid decoding found"))
}

/// Find the Klein group element with minimum resonance
fn find_minimum_resonance<P: FloatEncoding>(
    raw: &BitWord,
    alpha: &AlphaVec<P>,
) -> Result<BitWord, CcmError> {
    // For bijectivity, we need a deterministic way to choose b_min
    // when multiple Klein groups have the same minimum resonance.

    // The input is in exactly one Klein group
    let class_members = <BitWord as Resonance<P>>::class_members(raw);

    // Find the member with minimum resonance in this Klein group
    let mut min_resonance = P::infinity();
    let mut b_min = class_members[0].clone();

    for candidate in &class_members {
        let resonance = candidate.r(alpha);

        if resonance < min_resonance {
            min_resonance = resonance;
            b_min = candidate.clone();
        } else if resonance == min_resonance {
            // Tie-breaking: choose numerically smallest
            let n = raw.len();
            if n <= 64 && candidate.to_usize() < b_min.to_usize() {
                b_min = candidate.clone();
            }
        }
    }

    // Return the b_min from this Klein group
    // The flips will encode which member of the Klein group we started from
    Ok(b_min)
}

/// Find all BitWords that are minimum in their Klein group with the given resonance
fn find_all_by_resonance<P: FloatEncoding>(
    target: P,
    alpha: &AlphaVec<P>,
    n: usize,
) -> Result<Vec<BitWord>, CcmError> {
    // Step 1: For small N, use exhaustive search
    if n <= 12 {
        return find_by_exhaustive_search(target, alpha, n);
    }

    let mut candidates = Vec::new();

    // Step 2: Check unity positions first (most common case)
    candidates.extend(check_unity_positions(target, alpha, n));

    // Step 3: Try direct calculation approach for known patterns
    if candidates.is_empty() {
        candidates.extend(try_direct_calculation(target, alpha, n)?);
    }

    // Step 4: If not found, use gradient search from unity positions
    if candidates.is_empty() {
        candidates.extend(gradient_search_from_unity(target, alpha, n)?);
    }

    // Step 5: Search using homomorphic properties
    if candidates.is_empty() && n <= 32 {
        candidates.extend(search_homomorphic_patterns(target, alpha, n));
    }

    // Step 6: For larger N, use resonance decomposition
    if candidates.is_empty() && n > 12 {
        candidates.extend(search_by_decomposition(target, alpha, n)?);
    }

    if candidates.is_empty() {
        Err(CcmError::SearchExhausted)
    } else {
        Ok(candidates)
    }
}

/// Trait for types that can be encoded/decoded as bytes
pub trait FloatEncoding: Float {
    fn encode_bytes(&self) -> Vec<u8>;
    fn decode_bytes(bytes: &[u8]) -> Result<Self, CcmError>;
}

// f32 is not implemented as it lacks sufficient precision for CCM

impl FloatEncoding for f64 {
    fn encode_bytes(&self) -> Vec<u8> {
        // Network order (big-endian) as per spec section 4.1
        self.to_be_bytes().to_vec()
    }

    fn decode_bytes(bytes: &[u8]) -> Result<Self, CcmError> {
        if bytes.len() != 8 {
            return Err(CcmError::Custom("Invalid f64 encoding"));
        }
        let mut arr = [0u8; 8];
        arr.copy_from_slice(bytes);
        // Network order (big-endian) as per spec section 4.1
        Ok(f64::from_be_bytes(arr))
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
fn encode_page(page: usize, k: usize) -> Result<Vec<u8>, CcmError> {
    // Spec section 4.3: encode page ∈ ℤ/k as big-endian integer (⌈log₂k/8⌉ bytes)
    if k <= 1 {
        return Ok(Vec::new());
    }

    let log2_k = <f64 as num_traits::Float>::log2(k as f64).ceil() as u32;
    let num_bytes = log2_k.div_ceil(8) as usize;

    let mut bytes = vec![0u8; num_bytes];
    let mut value = page;

    // Write as big-endian
    for i in (0..num_bytes).rev() {
        bytes[i] = (value & 0xFF) as u8;
        value >>= 8;
    }

    Ok(bytes)
}

// ===== Decoder Implementation Functions =====

/// Exhaustive search for small N
fn find_by_exhaustive_search<P: FloatEncoding>(
    target: P,
    alpha: &AlphaVec<P>,
    n: usize,
) -> Result<Vec<BitWord>, CcmError> {
    let mut results = Vec::new();
    let tolerance = P::epsilon() * target.abs().max(P::one());

    let max_val = if n >= 64 { u64::MAX } else { (1u64 << n) - 1 };

    // Check all possible values
    for val in 0..=max_val {
        let word = BitWord::from_u64(val, n);

        // Check if this is a Klein minimum with the target resonance
        if word.is_klein_minimum(alpha) {
            let resonance = word.r(alpha);
            if (resonance - target).abs() <= tolerance {
                results.push(word);
            }
        }
    }

    Ok(results)
}

/// Check unity positions where resonance = 1
fn check_unity_positions<P: FloatEncoding>(
    target: P,
    alpha: &AlphaVec<P>,
    n: usize,
) -> Vec<BitWord> {
    let mut results = Vec::new();
    let tolerance = P::epsilon() * target.abs().max(P::one());

    // If target is near 1, check Klein four-group elements
    if (target - P::one()).abs() <= tolerance {
        // Klein group is at bits (n-2, n-1) where unity constraint is
        if n >= 2 {
            let unity_elements = [
                0u64,
                1u64 << (n - 2),
                1u64 << (n - 1),
                (1u64 << (n - 2)) | (1u64 << (n - 1)),
            ];

            for &val in &unity_elements {
                let word = BitWord::from_u64(val, n);
                let resonance = word.r(alpha);

                if (resonance - target).abs() <= tolerance {
                    results.push(word);
                }
            }
        } else {
            // For n < 2, only check 0 (empty product = 1)
            let word = BitWord::from_u64(0u64, n);
            let resonance = word.r(alpha);

            if (resonance - target).abs() <= tolerance {
                results.push(word);
            }
        }
    }

    results
}

/// Gradient-guided search from unity positions
fn gradient_search_from_unity<P: FloatEncoding>(
    target: P,
    alpha: &AlphaVec<P>,
    n: usize,
) -> Result<Vec<BitWord>, CcmError> {
    let mut results = Vec::new();
    let tolerance = P::epsilon() * target.abs().max(P::one());

    // Start from Klein four-group elements
    let start_positions = if n >= 2 {
        vec![
            0u64,
            1u64 << (n - 2),
            1u64 << (n - 1),
            (1u64 << (n - 2)) | (1u64 << (n - 1)),
        ]
    } else {
        vec![0u64]
    };

    for start_val in start_positions {
        let mut current = BitWord::from_u64(start_val, n);
        let mut current_resonance = current.r(alpha);

        // Simple gradient descent: flip bits that move us closer to target
        for bit_idx in 0..n {
            if n >= 2 && (bit_idx == n - 2 || bit_idx == n - 1) {
                continue; // Skip Klein group bits for now
            }

            // Try flipping this bit
            let mut test = current.clone();
            test.flip_bit(bit_idx);
            let test_resonance = test.r(alpha);

            // If this moves us closer to target, keep it
            if (test_resonance - target).abs() < (current_resonance - target).abs() {
                current = test;
                current_resonance = test_resonance;
            }
        }

        // Check if we found a Klein minimum with target resonance
        if current.is_klein_minimum(alpha) && (current_resonance - target).abs() <= tolerance {
            results.push(current);
        }
    }

    Ok(results)
}

/// Search using homomorphic patterns
fn search_homomorphic_patterns<P: FloatEncoding>(
    target: P,
    alpha: &AlphaVec<P>,
    n: usize,
) -> Vec<BitWord> {
    let mut results = Vec::new();
    let tolerance = P::epsilon() * target.abs().max(P::one());

    // Homomorphic bits are 0 (where α[0] = 1) and (n-2, n-1) where unity constraint is
    if n >= 2 {
        // Generate all patterns using only bits 0, n-2, n-1
        for use_bit_0 in [false, true] {
            for use_bit_n_minus_2 in [false, true] {
                for use_bit_n_minus_1 in [false, true] {
                    let mut val = 0u64;
                    if use_bit_0 {
                        val |= 1;
                    }
                    if use_bit_n_minus_2 {
                        val |= 1 << (n - 2);
                    }
                    if use_bit_n_minus_1 {
                        val |= 1 << (n - 1);
                    }

                    let word = BitWord::from_u64(val, n);

                    // Check all Klein group members derived from this pattern
                    let members = <BitWord as Resonance<P>>::class_members(&word);
                    for member in members {
                        if member.is_klein_minimum(alpha) {
                            let resonance = member.r(alpha);
                            if (resonance - target).abs() <= tolerance {
                                results.push(member);
                            }
                        }
                    }
                }
            }
        }
    }

    results
}

/// Search by decomposing target resonance using InverseResonance
fn search_by_decomposition<P: FloatEncoding>(
    target: P,
    alpha: &AlphaVec<P>,
    n: usize,
) -> Result<Vec<BitWord>, CcmError> {
    use crate::resonance::InverseResonance;

    let mut results = Vec::new();
    let tolerance = P::epsilon() * target.abs().max(P::one());

    // First try the optimized inverse resonance search
    match <BitWord as InverseResonance<P>>::find_by_resonance(target, alpha, tolerance) {
        Ok(candidates) => return Ok(candidates),
        Err(CcmError::SearchExhausted) => {
            // Continue with factorization approach
        }
        Err(e) => return Err(e),
    }

    // Try to factor the target resonance into alpha components
    let factorizations = <BitWord as InverseResonance<P>>::factor_resonance(target, alpha)?;

    for factor_indices in factorizations {
        // Convert indices to BitWord
        let mut value = 0u64;
        for idx in &factor_indices {
            if *idx < 64 {
                value |= 1u64 << idx;
            }
        }

        let word = BitWord::from_u64(value, n);

        // Verify this is a Klein minimum with correct resonance
        if word.is_klein_minimum(alpha) {
            let resonance = word.r(alpha);
            if (resonance - target).abs() <= tolerance {
                results.push(word);
            }
        }
    }

    Ok(results)
}

pub mod dynamic;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_decode_roundtrip() {
        // Use dynamic alpha which guarantees unity constraint
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();

        let raw = BitWord::from_u8(0b10110010u8);
        let packet = encode_bjc(&raw, &alpha, 1, false).unwrap();
        let decoded = decode_bjc::<f64>(&packet, &alpha).unwrap();

        assert_eq!(raw, decoded);
    }
}
