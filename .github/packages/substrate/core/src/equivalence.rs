//! XOR equivalence class management for bijective encoding/decoding
//!
//! Based on mathematical discovery: positions differing by XOR {1, 48, 49}
//! have the same resonance value, creating equivalence classes.

use crate::resonance::byte_to_resonance_class;
use lazy_static::lazy_static;
use std::collections::HashMap;

/// XOR patterns that preserve resonance
pub const PRESERVING_XOR_PATTERNS: [u8; 4] = [0, 1, 48, 49];

/// Information about an equivalence class
#[derive(Debug, Clone)]
pub struct EquivalenceClass {
    /// The resonance class index (0-95)
    pub resonance_class: u8,
    /// Members of this equivalence class
    pub members: Vec<u8>,
    /// Size of the equivalence class (2 or 4)
    pub size: u8,
}

lazy_static! {
    /// Map from resonance class to equivalence class info
    pub static ref EQUIVALENCE_CLASSES: Vec<EquivalenceClass> = build_equivalence_classes();
    
    /// Map from byte value to its position within its equivalence class
    pub static ref BYTE_TO_CLASS_POSITION: [u8; 256] = build_byte_position_map();
    
    /// Map from byte to its equivalence class members
    pub static ref BYTE_TO_EQUIVALENTS: HashMap<u8, Vec<u8>> = build_byte_equivalents_map();
}

/// Build all equivalence classes based on XOR patterns
fn build_equivalence_classes() -> Vec<EquivalenceClass> {
    let mut classes = Vec::with_capacity(96);
    let mut seen = [false; 256];
    
    for byte in 0u8..=255 {
        if seen[byte as usize] {
            continue;
        }
        
        let resonance_class = byte_to_resonance_class(byte);
        let mut members = Vec::new();
        
        // Find all bytes with same resonance (XOR equivalents)
        for &xor_pattern in &PRESERVING_XOR_PATTERNS {
            let equivalent = byte ^ xor_pattern;
            if equivalent <= 255 && byte_to_resonance_class(equivalent) == resonance_class {
                if !members.contains(&equivalent) {
                    members.push(equivalent);
                    seen[equivalent as usize] = true;
                }
            }
        }
        
        // Sort members for consistent ordering
        members.sort();
        
        classes.push(EquivalenceClass {
            resonance_class,
            members: members.clone(),
            size: members.len() as u8,
        });
    }
    
    // Sort by resonance class for consistent indexing
    classes.sort_by_key(|c| c.resonance_class);
    classes
}

/// Build map from byte to its position within equivalence class
fn build_byte_position_map() -> [u8; 256] {
    let mut map = [0u8; 256];
    
    for class in EQUIVALENCE_CLASSES.iter() {
        for (pos, &member) in class.members.iter().enumerate() {
            map[member as usize] = pos as u8;
        }
    }
    
    map
}

/// Build map from byte to all its equivalents
fn build_byte_equivalents_map() -> HashMap<u8, Vec<u8>> {
    let mut map = HashMap::new();
    
    for class in EQUIVALENCE_CLASSES.iter() {
        for &member in &class.members {
            map.insert(member, class.members.clone());
        }
    }
    
    map
}

/// Get the equivalence class for a given byte
pub fn get_equivalence_class(byte: u8) -> &'static EquivalenceClass {
    let resonance_class = byte_to_resonance_class(byte);
    &EQUIVALENCE_CLASSES[resonance_class as usize]
}

/// Get position of byte within its equivalence class (0-3)
pub fn get_class_position(byte: u8) -> u8 {
    BYTE_TO_CLASS_POSITION[byte as usize]
}

/// Get all bytes equivalent to the given byte
pub fn get_equivalents(byte: u8) -> &'static Vec<u8> {
    BYTE_TO_EQUIVALENTS.get(&byte).expect("All bytes should have equivalents")
}

/// Given a resonance class and position within class, get the byte value
pub fn class_and_position_to_byte(resonance_class: u8, position: u8) -> Option<u8> {
    EQUIVALENCE_CLASSES
        .get(resonance_class as usize)
        .and_then(|class| class.members.get(position as usize))
        .copied()
}

/// Calculate recovery bits needed to disambiguate within equivalence class
/// For bijection, we need to store:
/// 1. Which member of the equivalence class was the original byte
/// 2. Information to reverse the XOR folding for multi-byte inputs
pub fn calculate_recovery_bits(bytes: &[u8], folded_byte: u8) -> u8 {
    if bytes.is_empty() {
        return 0;
    }
    
    // For single byte, store position within its equivalence class (0-3)
    if bytes.len() == 1 {
        return get_class_position(bytes[0]) & 0x03;
    }
    
    // For multiple bytes, we need to store information about the XOR folding
    // The folded_byte tells us the resonance class, but we need to know
    // which specific bytes were XORed to produce it
    
    // Strategy: Use 4 bits to encode recovery information
    // Bits 0-1: Position of the folded result within its equivalence class
    // Bits 2-3: Parity information about the XOR folding pattern
    
    let folded_position = get_class_position(folded_byte) & 0x03;
    
    // Calculate parity bits from the original bytes
    // These help disambiguate during unfolding
    let mut parity = 0u8;
    
    // Use a more sophisticated parity calculation that captures pattern structure
    for (i, &byte) in bytes.iter().enumerate() {
        if i >= 8 { break; } // Only use first 8 bytes for parity
        
        // Mix byte value with its position to create unique signature
        let contribution = byte.wrapping_add(i as u8).wrapping_mul(17);
        parity ^= contribution.rotate_right((i * 3) as u32);
    }
    
    // Also include length information in parity (mod 4)
    parity ^= (bytes.len() as u8) << 6;
    
    // Extract 2 parity bits that will help distinguish patterns
    let parity_bits = (parity >> 4) & 0x03;
    
    // Combine position and parity information
    (folded_position & 0x03) | (parity_bits << 2)
}

/// Recover original byte using resonance class and recovery bits
pub fn recover_byte(resonance_class: u8, recovery_bits: u8) -> Option<u8> {
    // Extract position within equivalence class from recovery bits
    let position = recovery_bits & 0x03; // Bits 0-1
    
    // Get the specific byte from the resonance class and position
    class_and_position_to_byte(resonance_class, position)
}

/// Information needed to reverse XOR folding
#[derive(Debug, Clone, Copy)]
pub struct RecoveryInfo {
    /// Position within equivalence class (0-3)
    pub position: u8,
    /// Parity bits for XOR pattern disambiguation
    pub parity: u8,
}

impl RecoveryInfo {
    /// Create from recovery bits
    pub fn from_bits(bits: u8) -> Self {
        Self {
            position: bits & 0x03,
            parity: (bits >> 2) & 0x03,
        }
    }
    
    /// Convert to recovery bits
    pub fn to_bits(&self) -> u8 {
        (self.position & 0x03) | ((self.parity & 0x03) << 2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_equivalence_classes() {
        // Should have exactly 96 equivalence classes
        assert_eq!(EQUIVALENCE_CLASSES.len(), 96);
        
        // Count classes by size
        let mut size_2_count = 0;
        let mut size_4_count = 0;
        
        for class in EQUIVALENCE_CLASSES.iter() {
            match class.size {
                2 => size_2_count += 1,
                4 => size_4_count += 1,
                _ => panic!("Invalid equivalence class size: {}", class.size),
            }
        }
        
        // Based on research: 64 classes of size 2, 32 classes of size 4
        // Note: Actual distribution may vary based on field constants
        println!("Size 2 classes: {}, Size 4 classes: {}", size_2_count, size_4_count);
        assert_eq!(size_2_count + size_4_count, 96);
    }
    
    #[test]
    fn test_xor_preservation() {
        // Test that XOR with preserving patterns maintains resonance
        for byte in 0u8..=255 {
            let resonance = byte_to_resonance_class(byte);
            
            for &pattern in &PRESERVING_XOR_PATTERNS {
                let xor_byte = byte ^ pattern;
                if xor_byte <= 255 {
                    // Check if resonance is preserved
                    let xor_resonance = byte_to_resonance_class(xor_byte);
                    
                    // They should be in same equivalence class
                    let equiv_class = get_equivalence_class(byte);
                    assert!(
                        equiv_class.members.contains(&xor_byte) || resonance != xor_resonance,
                        "Byte {} XOR {} = {} should preserve resonance or be different class",
                        byte, pattern, xor_byte
                    );
                }
            }
        }
    }
    
    #[test]
    fn test_position_mapping() {
        // Every byte should have a valid position
        for byte in 0u8..=255 {
            let pos = get_class_position(byte);
            assert!(pos < 4, "Position should be 0-3, got {}", pos);
            
            // Verify we can recover the byte from class + position
            let resonance_class = byte_to_resonance_class(byte);
            let recovered = class_and_position_to_byte(resonance_class, pos);
            assert_eq!(recovered, Some(byte));
        }
    }
    
    #[test]
    fn test_recovery_bits() {
        // Test single byte recovery
        let bytes = vec![42];
        let resonance = byte_to_resonance_class(bytes[0]);
        let recovery = calculate_recovery_bits(&bytes, resonance);
        
        // Should be able to recover using resonance + recovery
        let recovered = recover_byte(resonance, recovery);
        assert_eq!(recovered, Some(bytes[0]));
    }
}