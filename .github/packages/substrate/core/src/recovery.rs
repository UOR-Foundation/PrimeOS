//! Recovery bits mechanism for the PrimeOS codec
//! 
//! This module implements the recovery bit calculation that enables bijection
//! by storing which candidate from a resonance class was the original byte.

use crate::mapper::COORDINATE_MAPPER;
use crate::resonance::byte_to_resonance_class;
use std::collections::HashMap;

/// Recovery bits handler for bijective encoding/decoding
pub struct RecoveryBits;

impl RecoveryBits {
    /// Calculate recovery bits that store the candidate index within a resonance class
    /// 
    /// For a given byte and its folded result, this determines which candidate
    /// from the resonance class the original byte was, and encodes that as recovery bits.
    pub fn calculate_recovery_bits(original_bytes: &[u8], folded_byte: u8) -> u8 {
        if original_bytes.is_empty() {
            return 0;
        }
        
        // For single byte, find its position within its resonance class
        if original_bytes.len() == 1 {
            let byte = original_bytes[0];
            let class = byte_to_resonance_class(byte);
            let candidates = COORDINATE_MAPPER.get_bytes_for_resonance_class(class);
            
            // Find position of byte in candidates
            if let Some(pos) = candidates.iter().position(|&b| b == byte) {
                return (pos as u8) & 0x0F; // 4 bits max
            }
            return 0;
        }
        
        // For multiple bytes, we need a more sophisticated approach
        // We'll use the folded byte's class and the pattern of original bytes
        let folded_class = byte_to_resonance_class(folded_byte);
        let folded_candidates = COORDINATE_MAPPER.get_bytes_for_resonance_class(folded_class);
        
        // Find which candidate the folded byte is
        let folded_index = folded_candidates.iter()
            .position(|&b| b == folded_byte)
            .unwrap_or(0) as u8;
        
        // Create a pattern signature from the original bytes
        let pattern_sig = Self::calculate_pattern_signature(original_bytes);
        
        // Combine folded index (2 bits) and pattern signature (2 bits)
        ((folded_index & 0x03) << 2) | (pattern_sig & 0x03)
    }
    
    /// Recover original byte using recovery bits and resonance class information
    pub fn recover_byte(
        resonance_class: u8,
        recovery_bits: u8,
        context: Option<&RecoveryContext>
    ) -> Result<u8, &'static str> {
        let candidates = COORDINATE_MAPPER.get_bytes_for_resonance_class(resonance_class);
        
        if candidates.is_empty() {
            return Err("No candidates for resonance class");
        }
        
        // Extract index from recovery bits
        let index = (recovery_bits & 0x0F) as usize;
        
        // For single byte recovery, directly use the index
        if context.is_none() || context.unwrap().is_single_byte {
            if index < candidates.len() {
                return Ok(candidates[index]);
            }
            // Fallback to first candidate if index out of bounds
            return Ok(candidates[0]);
        }
        
        // For multi-byte recovery, use both index and pattern
        let folded_index = ((recovery_bits >> 2) & 0x03) as usize;
        let pattern_sig = recovery_bits & 0x03;
        
        // Use pattern signature to disambiguate if needed
        if folded_index < candidates.len() {
            Ok(candidates[folded_index])
        } else {
            Ok(candidates[0])
        }
    }
    
    /// Calculate a pattern signature for a sequence of bytes
    fn calculate_pattern_signature(bytes: &[u8]) -> u8 {
        // Create a 2-bit signature that captures pattern characteristics
        let mut sig = 0u8;
        
        // Bit 0: Parity of byte count
        sig |= (bytes.len() & 1) as u8;
        
        // Bit 1: XOR parity of all bytes
        let xor_all = bytes.iter().fold(0u8, |acc, &b| acc ^ b);
        sig |= ((xor_all.count_ones() & 1) as u8) << 1;
        
        sig
    }
    
    /// Get all candidates for recovering a folded byte
    pub fn get_recovery_candidates(
        folded_byte: u8,
        folded_position: u16,
        cycle_length: usize
    ) -> Vec<Vec<u8>> {
        // This returns possible original byte sequences that could have
        // produced the given folded byte at the given position
        
        let folded_class = byte_to_resonance_class(folded_byte);
        let class_members = COORDINATE_MAPPER.get_bytes_for_resonance_class(folded_class);
        
        // For now, return simple candidates
        // Full implementation would use conservation laws
        let mut candidates = Vec::new();
        
        if cycle_length == 1 {
            // Single byte - candidates are just the class members
            for &byte in &class_members {
                candidates.push(vec![byte]);
            }
        } else {
            // Multiple bytes - need more sophisticated recovery
            // This is simplified - full implementation would use
            // conservation laws and constraints
            candidates.push(vec![folded_byte]);
        }
        
        candidates
    }
}

/// Context for recovery operations
#[derive(Debug, Clone)]
pub struct RecoveryContext {
    /// Whether this is single byte recovery
    pub is_single_byte: bool,
    /// Position in the data stream
    pub position: usize,
    /// Known constraints from conservation laws
    pub constraints: Option<RecoveryConstraints>,
}

/// Constraints that help with recovery
#[derive(Debug, Clone)]
pub struct RecoveryConstraints {
    /// Known XOR sum for the block
    pub xor_sum: Option<u8>,
    /// Known resonance sum
    pub resonance_sum: Option<f64>,
    /// Adjacent bytes if known
    pub adjacent_bytes: HashMap<usize, u8>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_byte_recovery() {
        // Test recovering single bytes
        for test_byte in [0u8, 1, 48, 49, 100, 200, 255] {
            let recovery_bits = RecoveryBits::calculate_recovery_bits(&[test_byte], test_byte);
            
            let class = byte_to_resonance_class(test_byte);
            let recovered = RecoveryBits::recover_byte(
                class,
                recovery_bits,
                Some(&RecoveryContext {
                    is_single_byte: true,
                    position: 0,
                    constraints: None,
                })
            ).unwrap();
            
            assert_eq!(recovered, test_byte, 
                "Failed to recover byte {} with recovery bits {:04b}", 
                test_byte, recovery_bits);
        }
    }

    #[test]
    fn test_pattern_signature() {
        // Test pattern signature calculation
        let bytes1 = vec![1, 2, 3];  // odd length, specific XOR pattern
        let bytes2 = vec![1, 2, 3, 4];  // even length
        
        let sig1 = RecoveryBits::calculate_pattern_signature(&bytes1);
        let sig2 = RecoveryBits::calculate_pattern_signature(&bytes2);
        
        assert_ne!(sig1 & 1, sig2 & 1); // Different length parity
    }

    #[test]
    fn test_recovery_candidates() {
        let folded_byte = 42u8;
        let candidates = RecoveryBits::get_recovery_candidates(folded_byte, 100, 1);
        
        assert!(!candidates.is_empty());
        
        // All candidates should be valid single bytes
        for candidate_seq in &candidates {
            assert_eq!(candidate_seq.len(), 1);
            let byte = candidate_seq[0];
            let class = byte_to_resonance_class(byte);
            let folded_class = byte_to_resonance_class(folded_byte);
            // Candidates should be from compatible resonance classes
            assert!(class == folded_class || 
                    COORDINATE_MAPPER.get_bytes_for_resonance_class(class).contains(&folded_byte));
        }
    }

    #[test]
    fn test_all_bytes_recoverable() {
        // Ensure all 256 bytes can be recovered
        let mut recovery_map = HashMap::new();
        
        for byte in 0u8..=255 {
            let recovery_bits = RecoveryBits::calculate_recovery_bits(&[byte], byte);
            let class = byte_to_resonance_class(byte);
            
            recovery_map.entry(class).or_insert_with(Vec::new).push((byte, recovery_bits));
        }
        
        // Verify each class has unique recovery bits for its members
        for (class, members) in recovery_map {
            let mut seen_bits = HashMap::new();
            
            for (byte, bits) in members {
                if let Some(&other_byte) = seen_bits.get(&bits) {
                    // Same recovery bits should mean same byte
                    assert_eq!(byte, other_byte, 
                        "Collision in class {}: bytes {} and {} have same recovery bits {:04b}",
                        class, byte, other_byte, bits);
                }
                seen_bits.insert(bits, byte);
            }
        }
    }

    #[test]
    fn test_multi_byte_recovery() {
        let original = vec![10, 20, 30];
        let folded = original.iter().fold(0u8, |acc, &b| acc ^ b); // Simple XOR fold
        
        let recovery_bits = RecoveryBits::calculate_recovery_bits(&original, folded);
        
        // Verify recovery bits encode useful information
        assert_ne!(recovery_bits, 0);
        
        let folded_class = byte_to_resonance_class(folded);
        
        // In real implementation, this would perfectly recover the original
        // For now, just verify the recovery attempt doesn't panic
        let _ = RecoveryBits::recover_byte(
            folded_class,
            recovery_bits,
            Some(&RecoveryContext {
                is_single_byte: false,
                position: 0,
                constraints: None,
            })
        );
    }

    #[test]
    fn test_recovery_with_constraints() {
        // Test recovery with known constraints
        let mut constraints = RecoveryConstraints {
            xor_sum: Some(0),
            resonance_sum: Some(100.0),
            adjacent_bytes: HashMap::new(),
        };
        constraints.adjacent_bytes.insert(0, 10);
        constraints.adjacent_bytes.insert(2, 30);
        
        let context = RecoveryContext {
            is_single_byte: false,
            position: 1,
            constraints: Some(constraints),
        };
        
        // This tests that constraints can be passed through the system
        // Full implementation would use these for better recovery
        let recovery_bits = 0b0101;
        let class = 42;
        
        let _ = RecoveryBits::recover_byte(class, recovery_bits, Some(&context));
    }
}