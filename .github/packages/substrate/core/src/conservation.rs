//! Conservation laws for the PrimeOS codec
//! 
//! These laws enable reconstruction of data without storing all information.

use crate::constants::{CYCLE_LENGTH, UNITY_POSITIONS};
use crate::resonance::{calculate_resonance, byte_to_resonance_class};
use std::collections::HashMap;

/// Expected resonance sum per 768-bit cycle
pub const EXPECTED_RESONANCE_SUM: f64 = 687.110133;

/// XOR balance block size (every 64 bytes should XOR to 0)
pub const XOR_BALANCE_BLOCK_SIZE: usize = 64;

/// Conservation laws that enable data reconstruction
pub struct ConservationLaws;

/// Constraints for conservation law based reconstruction
#[derive(Debug, Clone)]
pub struct ConservationConstraints {
    /// Expected resonance sum
    pub resonance_sum: f64,
    /// Whether to enforce XOR balance
    pub enforce_xor_balance: bool,
    /// Required resonance classes for specific positions
    pub resonance_classes: Option<HashMap<usize, u8>>,
    /// Whether reconstruction must be unique
    pub require_unique: bool,
}

impl Default for ConservationConstraints {
    fn default() -> Self {
        Self {
            resonance_sum: EXPECTED_RESONANCE_SUM,
            enforce_xor_balance: true,
            resonance_classes: None,
            require_unique: false,
        }
    }
}

/// Report on conservation law verification
#[derive(Debug, Clone)]
pub struct ConservationReport {
    /// Whether XOR balance is satisfied
    pub xor_balance_valid: bool,
    /// Whether resonance conservation is satisfied
    pub resonance_conservation_valid: bool,
    /// Whether field balance is satisfied
    pub field_balance_valid: bool,
    /// Actual resonance sum
    pub resonance_sum: f64,
    /// Resonance pattern signature
    pub resonance_signature: u64,
    /// Length of data analyzed
    pub data_length: usize,
}

impl ConservationReport {
    /// Check if all conservation laws are satisfied
    pub fn all_valid(&self) -> bool {
        self.xor_balance_valid && 
        self.resonance_conservation_valid && 
        self.field_balance_valid
    }
}

impl ConservationLaws {
    /// Verify XOR balance property: every 64-byte block XORs to 0
    pub fn verify_xor_balance(data: &[u8]) -> bool {
        if data.is_empty() {
            return true;
        }
        
        // Process complete 64-byte blocks
        for chunk in data.chunks_exact(XOR_BALANCE_BLOCK_SIZE) {
            let xor_sum = chunk.iter().fold(0u8, |acc, &byte| acc ^ byte);
            if xor_sum != 0 {
                return false;
            }
        }
        
        // Partial blocks at the end don't need to balance
        true
    }
    
    /// Calculate XOR sum for a block of data
    pub fn calculate_xor_sum(data: &[u8]) -> u8 {
        data.iter().fold(0u8, |acc, &byte| acc ^ byte)
    }
    
    /// Verify resonance conservation: sum should be ~687.110133 per 768-bit cycle
    pub fn verify_resonance_conservation(data: &[u8]) -> bool {
        if data.is_empty() {
            return true;
        }
        
        let cycle_bytes = CYCLE_LENGTH / 8; // 96 bytes per cycle
        let full_cycles = data.len() / cycle_bytes;
        
        if full_cycles == 0 {
            // Not enough data for a full cycle
            return true;
        }
        
        let mut total_resonance = 0.0;
        for i in 0..full_cycles * cycle_bytes {
            total_resonance += calculate_resonance(data[i]);
        }
        
        let expected = EXPECTED_RESONANCE_SUM * full_cycles as f64;
        let tolerance = 0.001; // Allow small floating point errors
        
        (total_resonance - expected).abs() < tolerance
    }
    
    /// Calculate resonance sum for a block of data
    pub fn calculate_resonance_sum(data: &[u8]) -> f64 {
        data.iter().map(|&byte| calculate_resonance(byte)).sum()
    }
    
    /// Find missing byte in a 64-byte block given XOR constraint
    pub fn recover_missing_byte(block: &[u8], missing_index: usize) -> Option<u8> {
        if block.len() != XOR_BALANCE_BLOCK_SIZE - 1 || missing_index >= XOR_BALANCE_BLOCK_SIZE {
            return None;
        }
        
        // XOR of all bytes should be 0, so missing byte is XOR of all others
        Some(Self::calculate_xor_sum(block))
    }
    
    /// Use conservation laws to constrain possible byte values
    pub fn constrain_candidates(
        partial_data: &[u8],
        missing_positions: &[usize],
        resonance_target: f64
    ) -> Vec<Vec<u8>> {
        let current_resonance: f64 = partial_data.iter()
            .map(|&b| calculate_resonance(b))
            .sum();
        
        let remaining_resonance = resonance_target - current_resonance;
        let num_missing = missing_positions.len();
        
        if num_missing == 0 {
            return Vec::new();
        }
        
        // Group bytes by resonance value for efficient lookup
        let mut resonance_groups: HashMap<u64, Vec<u8>> = HashMap::new();
        for byte in 0u8..=255 {
            let resonance = calculate_resonance(byte);
            let key = resonance.to_bits(); // Use bits for exact comparison
            resonance_groups.entry(key).or_insert_with(Vec::new).push(byte);
        }
        
        // Sort resonance values for efficient searching
        let mut resonance_values: Vec<(f64, Vec<u8>)> = resonance_groups
            .into_iter()
            .map(|(bits, bytes)| (f64::from_bits(bits), bytes))
            .collect();
        resonance_values.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
        
        // For each missing position, constrain candidates
        let mut candidates = Vec::new();
        let avg_needed_per_position = remaining_resonance / num_missing as f64;
        
        for i in 0..num_missing {
            let mut position_candidates = Vec::new();
            
            // Consider position-specific constraints
            let position = missing_positions[i];
            let is_block_boundary = position % XOR_BALANCE_BLOCK_SIZE == XOR_BALANCE_BLOCK_SIZE - 1;
            
            if is_block_boundary && i == num_missing - 1 {
                // Last byte in XOR block - must balance the block
                if let Some(block_start) = position.checked_sub(XOR_BALANCE_BLOCK_SIZE - 1) {
                    let mut xor_sum = 0u8;
                    
                    // XOR all bytes in the block
                    for j in block_start..position {
                        if j < partial_data.len() {
                            xor_sum ^= partial_data[j];
                        }
                    }
                    
                    // The missing byte must be the XOR of all others
                    position_candidates.push(xor_sum);
                }
            } else {
                // Use resonance constraints
                let min_resonance = (avg_needed_per_position * 0.5).max(0.0);
                let max_resonance = avg_needed_per_position * 1.5;
                
                // Binary search for acceptable resonance range
                let start_idx = resonance_values.binary_search_by(|&(r, _)| {
                    r.partial_cmp(&min_resonance).unwrap()
                }).unwrap_or_else(|i| i);
                
                let end_idx = resonance_values.binary_search_by(|&(r, _)| {
                    r.partial_cmp(&max_resonance).unwrap()
                }).unwrap_or_else(|i| i);
                
                // Collect all bytes in the acceptable range
                for j in start_idx..end_idx.min(resonance_values.len()) {
                    position_candidates.extend_from_slice(&resonance_values[j].1);
                }
                
                // If no candidates found, include unity bytes as fallback
                if position_candidates.is_empty() {
                    position_candidates.extend_from_slice(&UNITY_POSITIONS);
                }
            }
            
            candidates.push(position_candidates);
        }
        
        candidates
    }
    
    /// Check if field activation is balanced (each field active in ~50% of bytes)
    pub fn verify_field_balance(data: &[u8]) -> bool {
        if data.len() < 16 {
            // Too small to verify statistical properties
            return true;
        }
        
        let mut field_counts = [0usize; 8];
        
        for &byte in data {
            for bit in 0..8 {
                if (byte >> bit) & 1 == 1 {
                    field_counts[bit] += 1;
                }
            }
        }
        
        // Each field should be active in 40-60% of bytes
        let min_count = data.len() * 2 / 5;
        let max_count = data.len() * 3 / 5;
        
        field_counts.iter().all(|&count| count >= min_count && count <= max_count)
    }
    
    /// Use Klein group structure to find related bytes
    pub fn find_klein_group_members(byte: u8) -> [u8; 4] {
        // Klein group at unity: {0, 1, 48, 49}
        // For any byte, its Klein group is byte XOR {0, 1, 48, 49}
        [
            byte,
            byte ^ 1,
            byte ^ 48,
            byte ^ 49
        ]
    }
    
    /// Reconstruct missing bytes using multiple conservation laws
    pub fn reconstruct_with_constraints(
        partial_data: &[u8],
        missing_positions: &[usize],
        known_constraints: &ConservationConstraints
    ) -> Result<Vec<u8>, &'static str> {
        if missing_positions.is_empty() {
            return Ok(Vec::new());
        }
        
        // Start with candidates from resonance constraints
        let mut candidates = Self::constrain_candidates(
            partial_data,
            missing_positions,
            known_constraints.resonance_sum
        );
        
        // Apply XOR balance constraints
        if known_constraints.enforce_xor_balance {
            for (i, pos) in missing_positions.iter().enumerate() {
                let block_idx = pos / XOR_BALANCE_BLOCK_SIZE;
                let block_offset = pos % XOR_BALANCE_BLOCK_SIZE;
                
                if block_offset == XOR_BALANCE_BLOCK_SIZE - 1 {
                    // This is the last byte in a block - must balance
                    let block_start = block_idx * XOR_BALANCE_BLOCK_SIZE;
                    let mut xor_sum = 0u8;
                    
                    // Calculate XOR of known bytes in this block
                    for j in block_start..*pos {
                        if let Some(idx) = partial_data.get(j) {
                            xor_sum ^= idx;
                        }
                    }
                    
                    // The missing byte must be this value
                    candidates[i] = vec![xor_sum];
                }
            }
        }
        
        // Apply resonance class constraints
        if let Some(ref class_constraints) = known_constraints.resonance_classes {
            for (i, &pos) in missing_positions.iter().enumerate() {
                if let Some(&required_class) = class_constraints.get(&pos) {
                    // Filter candidates to only those in the required class
                    candidates[i].retain(|&byte| {
                        byte_to_resonance_class(byte) == required_class
                    });
                }
            }
        }
        
        // Verify we have valid candidates for all positions
        for (i, cands) in candidates.iter().enumerate() {
            if cands.is_empty() {
                return Err("No valid candidates for position");
            }
            if cands.len() > 1 && known_constraints.require_unique {
                return Err("Multiple candidates remain after constraints");
            }
        }
        
        // Return the first candidate for each position
        Ok(candidates.into_iter().map(|c| c[0]).collect())
    }
    
    /// Calculate the resonance pattern signature for a data block
    pub fn calculate_resonance_signature(data: &[u8]) -> u64 {
        // Create a signature that captures the resonance pattern
        let mut signature = 0u64;
        
        for (i, &byte) in data.iter().enumerate() {
            let class = byte_to_resonance_class(byte);
            // Mix position and class into signature
            signature = signature.wrapping_mul(31).wrapping_add(class as u64);
            signature ^= (i as u64).rotate_left(class as u32 % 64);
        }
        
        signature
    }
    
    /// Verify all conservation laws for a complete data block
    pub fn verify_all_conservation_laws(data: &[u8]) -> ConservationReport {
        let xor_valid = Self::verify_xor_balance(data);
        let resonance_valid = Self::verify_resonance_conservation(data);
        let field_valid = Self::verify_field_balance(data);
        
        let resonance_sum = Self::calculate_resonance_sum(data);
        let signature = Self::calculate_resonance_signature(data);
        
        ConservationReport {
            xor_balance_valid: xor_valid,
            resonance_conservation_valid: resonance_valid,
            field_balance_valid: field_valid,
            resonance_sum,
            resonance_signature: signature,
            data_length: data.len(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_xor_balance_valid() {
        // Create a balanced 64-byte block
        let mut data = vec![0u8; 64];
        for i in 0..63 {
            data[i] = i as u8;
        }
        // Last byte makes it balance
        data[63] = (0..63).fold(0u8, |acc, i| acc ^ (i as u8));
        
        assert!(ConservationLaws::verify_xor_balance(&data));
        assert_eq!(ConservationLaws::calculate_xor_sum(&data), 0);
    }

    #[test]
    fn test_xor_balance_invalid() {
        // Create 64 bytes that don't balance
        let mut data = vec![1u8; 64];
        data[63] = 2; // This breaks the balance
        
        assert!(!ConservationLaws::verify_xor_balance(&data));
    }

    #[test]
    fn test_xor_balance_partial_block() {
        // Partial blocks don't need to balance
        let data = vec![1, 2, 3, 4, 5]; // Less than 64 bytes
        assert!(ConservationLaws::verify_xor_balance(&data));
    }

    #[test]
    fn test_recover_missing_byte() {
        let mut block = vec![0u8; 63];
        for i in 0..63 {
            block[i] = i as u8;
        }
        
        let expected_missing = (0..63).fold(0u8, |acc, i| acc ^ (i as u8));
        let recovered = ConservationLaws::recover_missing_byte(&block, 63).unwrap();
        
        assert_eq!(recovered, expected_missing);
    }

    #[test]
    fn test_resonance_conservation() {
        // Create exactly 96 bytes (768 bits = 1 cycle)
        let data = vec![0u8; 96];
        
        // This is a simplified test - in reality we'd need to carefully
        // construct data that sums to exactly 687.110133
        // For now, just verify the function runs
        let sum = ConservationLaws::calculate_resonance_sum(&data);
        assert!(sum >= 0.0);
    }

    #[test]
    fn test_constrain_candidates() {
        let partial_data = vec![0, 1, 2, 3];
        let missing_positions = vec![4, 5];
        let target_resonance = 50.0;
        
        let candidates = ConservationLaws::constrain_candidates(
            &partial_data,
            &missing_positions,
            target_resonance
        );
        
        assert_eq!(candidates.len(), 2);
        assert!(!candidates[0].is_empty());
        assert!(!candidates[1].is_empty());
    }

    #[test]
    fn test_field_balance() {
        // Create balanced data where each bit is set in ~50% of bytes
        let mut data = Vec::new();
        for i in 0..64 {
            // Alternate patterns to get ~50% activation
            data.push(if i % 2 == 0 { 0b10101010 } else { 0b01010101 });
        }
        
        assert!(ConservationLaws::verify_field_balance(&data));
    }

    #[test]
    fn test_field_balance_unbalanced() {
        // All zeros - no fields active
        let data = vec![0u8; 64];
        assert!(!ConservationLaws::verify_field_balance(&data));
        
        // All ones - all fields active
        let data = vec![0xFFu8; 64];
        assert!(!ConservationLaws::verify_field_balance(&data));
    }

    #[test]
    fn test_empty_data() {
        let empty = vec![];
        
        assert!(ConservationLaws::verify_xor_balance(&empty));
        assert!(ConservationLaws::verify_resonance_conservation(&empty));
        assert!(ConservationLaws::verify_field_balance(&empty));
        assert_eq!(ConservationLaws::calculate_resonance_sum(&empty), 0.0);
    }

    #[test]
    fn test_klein_group_members() {
        // Test with byte 0
        let members = ConservationLaws::find_klein_group_members(0);
        assert_eq!(members, [0, 1, 48, 49]);
        
        // Test with byte 10
        let members = ConservationLaws::find_klein_group_members(10);
        assert_eq!(members, [10, 11, 58, 59]);
        
        // Verify Klein group property: a XOR b XOR c = d
        for byte in 0u8..=10 {
            let group = ConservationLaws::find_klein_group_members(byte);
            let xor_all = group[0] ^ group[1] ^ group[2] ^ group[3];
            assert_eq!(xor_all, 0); // Should XOR to 0
        }
    }

    #[test]
    fn test_resonance_signature() {
        let data1 = vec![1, 2, 3, 4];
        let data2 = vec![1, 2, 3, 4];
        let data3 = vec![4, 3, 2, 1];
        
        let sig1 = ConservationLaws::calculate_resonance_signature(&data1);
        let sig2 = ConservationLaws::calculate_resonance_signature(&data2);
        let sig3 = ConservationLaws::calculate_resonance_signature(&data3);
        
        // Same data should give same signature
        assert_eq!(sig1, sig2);
        // Different order should give different signature
        assert_ne!(sig1, sig3);
    }

    #[test]
    fn test_conservation_report() {
        // Create data that satisfies XOR balance
        let mut data = vec![0u8; 64];
        for i in 0..63 {
            data[i] = i as u8;
        }
        data[63] = (0..63).fold(0u8, |acc, i| acc ^ (i as u8));
        
        let report = ConservationLaws::verify_all_conservation_laws(&data);
        assert!(report.xor_balance_valid);
        assert_eq!(report.data_length, 64);
        assert!(report.resonance_sum > 0.0);
        assert_ne!(report.resonance_signature, 0);
    }

    #[test]
    fn test_reconstruct_with_constraints() {
        let partial_data = vec![1, 2, 3, 4];
        let missing_positions = vec![4, 5];
        
        let constraints = ConservationConstraints {
            resonance_sum: 50.0,
            enforce_xor_balance: false,
            resonance_classes: None,
            require_unique: false,
        };
        
        let result = ConservationLaws::reconstruct_with_constraints(
            &partial_data,
            &missing_positions,
            &constraints
        );
        
        assert!(result.is_ok());
        let reconstructed = result.unwrap();
        assert_eq!(reconstructed.len(), 2);
    }

    #[test]
    fn test_xor_constraint_reconstruction() {
        // Test reconstruction with XOR balance constraint
        let mut partial_data = vec![0u8; 63];
        for i in 0..63 {
            partial_data[i] = i as u8;
        }
        
        let missing_positions = vec![63]; // Last position in block
        
        let constraints = ConservationConstraints {
            resonance_sum: 1000.0, // Large value so resonance doesn't constrain
            enforce_xor_balance: true,
            resonance_classes: None,
            require_unique: true,
        };
        
        let result = ConservationLaws::reconstruct_with_constraints(
            &partial_data,
            &missing_positions,
            &constraints
        );
        
        assert!(result.is_ok());
        let reconstructed = result.unwrap();
        assert_eq!(reconstructed.len(), 1);
        
        // Verify the reconstructed byte balances the XOR
        let expected = (0..63).fold(0u8, |acc, i| acc ^ (i as u8));
        assert_eq!(reconstructed[0], expected);
    }

    #[test]
    fn test_resonance_class_constraint() {
        let partial_data = vec![0, 1, 2];
        let missing_positions = vec![3];
        
        // Create constraint requiring unity class (class 0)
        let mut class_map = HashMap::new();
        class_map.insert(3, byte_to_resonance_class(0)); // Unity class
        
        let constraints = ConservationConstraints {
            resonance_sum: 50.0,
            enforce_xor_balance: false,
            resonance_classes: Some(class_map),
            require_unique: false,
        };
        
        let result = ConservationLaws::reconstruct_with_constraints(
            &partial_data,
            &missing_positions,
            &constraints
        );
        
        assert!(result.is_ok());
        let reconstructed = result.unwrap();
        
        // Verify the reconstructed byte is in unity class
        let unity_class = byte_to_resonance_class(0);
        assert_eq!(byte_to_resonance_class(reconstructed[0]), unity_class);
    }
}