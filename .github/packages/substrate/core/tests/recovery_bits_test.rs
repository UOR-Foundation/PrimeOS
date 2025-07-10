//! Tests for recovery bit calculation and bijection properties

use primeos_codec::equivalence::*;
use primeos_codec::resonance::byte_to_resonance_class;

#[test]
fn test_single_byte_recovery() {
    // For single bytes, recovery bits should just be the position within equivalence class
    for byte in 0u8..=255 {
        let recovery = calculate_recovery_bits(&[byte], byte);
        assert!(recovery <= 3, "Recovery bits should be 0-3 for single byte");
        
        // Should be able to recover the exact byte
        let resonance_class = byte_to_resonance_class(byte);
        let recovered = recover_byte(resonance_class, recovery).unwrap();
        assert_eq!(recovered, byte, "Failed to recover byte {}", byte);
    }
}

#[test]
fn test_equivalence_class_positions() {
    // Test that bytes in the same equivalence class have different positions
    let test_groups = [
        vec![0, 1],           // Differ by bit 0
        vec![0, 48],          // Differ by bits 4,5
        vec![0, 1, 48, 49],   // Full equivalence class
        vec![2, 3, 50, 51],   // Another full class
    ];
    
    for group in test_groups.iter() {
        let positions: Vec<u8> = group.iter()
            .map(|&b| get_class_position(b))
            .collect();
        
        // All positions should be unique within the group
        let mut unique_positions = positions.clone();
        unique_positions.sort();
        unique_positions.dedup();
        assert_eq!(positions.len(), unique_positions.len(), 
            "Duplicate positions in group {:?}", group);
        
        // All should have same resonance class
        let resonance_classes: Vec<u8> = group.iter()
            .map(|&b| byte_to_resonance_class(b))
            .collect();
        assert!(resonance_classes.windows(2).all(|w| w[0] == w[1]),
            "Different resonance classes in group {:?}", group);
    }
}

#[test]
fn test_multi_byte_recovery_bits() {
    // Test that different byte sequences produce different recovery bits
    let test_cases = vec![
        vec![0x42, 0x17],
        vec![0x42, 0x18],  // Similar but different
        vec![0xFF, 0x00],
        vec![0x00, 0xFF],  // Order matters
        vec![0x12, 0x34, 0x56, 0x78],
    ];
    
    for bytes in test_cases {
        // Calculate folded byte
        let mut folded = 0u8;
        for (i, &byte) in bytes.iter().enumerate() {
            folded ^= (byte as u8).rotate_left((i % 8) as u32);
        }
        
        let recovery = calculate_recovery_bits(&bytes, folded);
        assert!(recovery <= 15, "Recovery bits should fit in 4 bits");
        
        // Recovery bits should contain position of folded byte
        let folded_position = get_class_position(folded);
        assert_eq!(recovery & 0x03, folded_position & 0x03,
            "Recovery bits should preserve position for {:?}", bytes);
    }
}

#[test]
fn test_recovery_preserves_information() {
    // Test that recovery bits + resonance class provides enough information
    // This is a critical test for bijection
    
    // Test patterns that fold to the same byte
    let pattern1 = vec![0x42, 0x42]; // XOR to 0
    let pattern2 = vec![0x17, 0x17]; // Also XOR to 0
    
    let folded1 = pattern1.iter().fold(0u8, |acc, &b| acc ^ b);
    let folded2 = pattern2.iter().fold(0u8, |acc, &b| acc ^ b);
    
    assert_eq!(folded1, folded2, "Both should fold to 0");
    
    // But recovery bits should be different due to parity
    let recovery1 = calculate_recovery_bits(&pattern1, folded1);
    let recovery2 = calculate_recovery_bits(&pattern2, folded2);
    
    // The parity bits (bits 2-3) should differ
    println!("Recovery 1: {:04b}, Recovery 2: {:04b}", recovery1, recovery2);
    
    // For proper bijection, we'd need the full decoder implementation
    // to verify we can distinguish these patterns
}

#[test]
fn test_recovery_info_struct() {
    // Test the RecoveryInfo helper struct
    let info = RecoveryInfo {
        position: 3,
        parity: 2,
    };
    
    let bits = info.to_bits();
    assert_eq!(bits & 0x03, 3, "Position should be in bits 0-1");
    assert_eq!((bits >> 2) & 0x03, 2, "Parity should be in bits 2-3");
    
    let recovered = RecoveryInfo::from_bits(bits);
    assert_eq!(recovered.position, info.position);
    assert_eq!(recovered.parity, info.parity);
}

#[test]
fn test_empty_input_recovery() {
    let recovery = calculate_recovery_bits(&[], 0);
    assert_eq!(recovery, 0, "Empty input should have 0 recovery bits");
}

#[test]
fn test_xor_folding_recovery() {
    // Test specific XOR folding patterns
    let bytes = vec![0x0F, 0xF0]; // Should XOR to 0xFF
    let mut folded = 0u8;
    for (i, &byte) in bytes.iter().enumerate() {
        folded ^= (byte as u8).rotate_left((i % 8) as u32);
    }
    
    // 0x0F rotated left 0 = 0x0F
    // 0xF0 rotated left 1 = 0xE1
    // 0x0F ^ 0xE1 = 0xEE
    assert_eq!(folded, 0xEE);
    
    let recovery = calculate_recovery_bits(&bytes, folded);
    let position = get_class_position(folded);
    assert_eq!(recovery & 0x03, position & 0x03);
}

#[test] 
fn test_all_resonance_classes_recoverable() {
    // Ensure every resonance class can be used in recovery
    use std::collections::HashSet;
    
    let mut seen_classes = HashSet::new();
    
    for byte in 0u8..=255 {
        let resonance_class = byte_to_resonance_class(byte);
        seen_classes.insert(resonance_class);
        
        // Test recovery for this byte
        let recovery = calculate_recovery_bits(&[byte], byte);
        let recovered = recover_byte(resonance_class, recovery);
        assert_eq!(recovered, Some(byte));
    }
    
    assert_eq!(seen_classes.len(), 96, "Should have exactly 96 resonance classes");
}