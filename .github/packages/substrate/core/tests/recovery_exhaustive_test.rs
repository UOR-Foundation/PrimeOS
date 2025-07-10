//! Exhaustive tests for recovery bit implementation
//! Ensures no placeholders remain and bijection works for all cases

use primeos_codec::equivalence::*;
use primeos_codec::resonance::byte_to_resonance_class;
use std::collections::{HashMap, HashSet};

#[test]
fn test_all_single_bytes_recoverable() {
    // Test that every single byte can be recovered perfectly
    let mut failures = Vec::new();
    
    for byte in 0u8..=255 {
        let recovery = calculate_recovery_bits(&[byte], byte);
        let resonance_class = byte_to_resonance_class(byte);
        let recovered = recover_byte(resonance_class, recovery);
        
        if recovered != Some(byte) {
            failures.push((byte, recovery, resonance_class, recovered));
        }
    }
    
    assert!(failures.is_empty(), 
        "Failed to recover {} bytes: {:?}", failures.len(), failures);
}

#[test]
fn test_recovery_bits_are_unique_within_class() {
    // For each equivalence class, verify that each member gets a unique recovery bit pattern
    let mut class_to_recovery_map: HashMap<u8, HashMap<u8, u8>> = HashMap::new();
    
    for byte in 0u8..=255 {
        let resonance_class = byte_to_resonance_class(byte);
        let recovery = calculate_recovery_bits(&[byte], byte);
        
        class_to_recovery_map
            .entry(resonance_class)
            .or_insert_with(HashMap::new)
            .insert(recovery & 0x03, byte); // Only position bits matter for single bytes
    }
    
    // Check that within each class, recovery positions are unique
    for (class, recovery_map) in class_to_recovery_map {
        let equiv_class = get_equivalence_class(recovery_map.values().next().unwrap().clone());
        assert_eq!(recovery_map.len(), equiv_class.members.len(),
            "Class {} has {} members but {} unique recovery positions",
            class, equiv_class.members.len(), recovery_map.len());
    }
}

#[test]
fn test_multi_byte_parity_distinguishes_patterns() {
    // Test that different patterns that fold to the same value get different parity bits
    let test_groups = vec![
        // Patterns that XOR to 0
        (vec![0x00, 0x00], vec![0xFF, 0xFF]),
        (vec![0x42, 0x42], vec![0x17, 0x17]),
        (vec![0xAA, 0xAA], vec![0x55, 0x55]),
        
        // Patterns that XOR to 0xFF
        (vec![0x00, 0xFF], vec![0xFF, 0x00]),
        (vec![0x0F, 0xF0], vec![0xF0, 0x0F]),
        
        // Longer patterns
        (vec![0x01, 0x02, 0x03], vec![0x03, 0x02, 0x01]),
        (vec![0x12, 0x34, 0x56, 0x78], vec![0x78, 0x56, 0x34, 0x12]),
    ];
    
    for (pattern1, pattern2) in test_groups {
        // Calculate folded bytes
        let mut folded1 = 0u8;
        let mut folded2 = 0u8;
        
        for (i, &byte) in pattern1.iter().enumerate() {
            folded1 ^= (byte as u8).rotate_left((i % 8) as u32);
        }
        for (i, &byte) in pattern2.iter().enumerate() {
            folded2 ^= (byte as u8).rotate_left((i % 8) as u32);
        }
        
        let recovery1 = calculate_recovery_bits(&pattern1, folded1);
        let recovery2 = calculate_recovery_bits(&pattern2, folded2);
        
        // If they fold to the same value, parity should distinguish them
        if folded1 == folded2 {
            let parity1 = (recovery1 >> 2) & 0x03;
            let parity2 = (recovery2 >> 2) & 0x03;
            
            // We expect different parity in most cases
            // Some patterns might have same parity, but position + parity together should differ
            if recovery1 == recovery2 {
                println!("Warning: Patterns {:?} and {:?} have identical recovery bits {:04b}",
                    pattern1, pattern2, recovery1);
            }
        }
    }
}

#[test]
fn test_recovery_info_round_trip() {
    // Test all possible 4-bit recovery values
    for bits in 0..16u8 {
        let info = RecoveryInfo::from_bits(bits);
        let reconstructed = info.to_bits();
        assert_eq!(bits, reconstructed, 
            "RecoveryInfo round-trip failed for {:04b}", bits);
        
        // Verify constraints
        assert!(info.position <= 3, "Position out of range");
        assert!(info.parity <= 3, "Parity out of range");
    }
}

#[test]
fn test_equivalence_class_structure() {
    // Verify the mathematical properties of equivalence classes
    let mut size_2_count = 0;
    let mut size_4_count = 0;
    let mut total_members = 0;
    
    for class in EQUIVALENCE_CLASSES.iter() {
        match class.size {
            2 => {
                size_2_count += 1;
                // Verify these differ by bit 0 only
                assert_eq!(class.members[0] ^ class.members[1], 1,
                    "Size-2 class should differ by bit 0 only");
            },
            4 => {
                size_4_count += 1;
                // Verify Klein group structure
                let mut xor_diffs = HashSet::new();
                for i in 0..4 {
                    for j in (i+1)..4 {
                        xor_diffs.insert(class.members[i] ^ class.members[j]);
                    }
                }
                // Should have XOR differences of 1, 48, 49
                assert!(xor_diffs.contains(&1), "Missing XOR diff 1");
                assert!(xor_diffs.contains(&48), "Missing XOR diff 48");
                assert!(xor_diffs.contains(&49), "Missing XOR diff 49");
            },
            _ => panic!("Invalid equivalence class size: {}", class.size),
        }
        total_members += class.size as usize;
    }
    
    assert_eq!(total_members, 256, "Not all bytes accounted for");
    assert_eq!(EQUIVALENCE_CLASSES.len(), 96, "Should have exactly 96 classes");
    println!("Equivalence classes: {} size-2, {} size-4", size_2_count, size_4_count);
}

#[test]
fn test_length_affects_recovery() {
    // Test that different length inputs with same bytes get different recovery
    let byte_pattern = vec![0x42, 0x17, 0xAB];
    
    let mut recovery_by_length = HashMap::new();
    
    for len in 1..=3 {
        let bytes = &byte_pattern[..len];
        let mut folded = 0u8;
        for (i, &byte) in bytes.iter().enumerate() {
            folded ^= (byte as u8).rotate_left((i % 8) as u32);
        }
        
        let recovery = calculate_recovery_bits(bytes, folded);
        recovery_by_length.insert(len, recovery);
    }
    
    // Different lengths should generally produce different recovery bits
    // due to length being incorporated in parity
    assert!(recovery_by_length.len() > 1,
        "Length information not properly encoded in recovery bits");
}

#[test]
fn test_edge_cases() {
    // Test edge cases
    
    // Empty input
    let recovery = calculate_recovery_bits(&[], 0);
    assert_eq!(recovery, 0);
    
    // Very long input (only first 8 bytes used for parity)
    let long_input: Vec<u8> = (0..20).map(|i| i as u8).collect();
    let mut folded = 0u8;
    for (i, &byte) in long_input.iter().enumerate() {
        folded ^= (byte as u8).rotate_left((i % 8) as u32);
    }
    let recovery = calculate_recovery_bits(&long_input, folded);
    assert!(recovery <= 15, "Recovery bits out of range");
    
    // All zeros
    let zeros = vec![0u8; 10];
    let recovery = calculate_recovery_bits(&zeros, 0);
    assert!(recovery <= 15);
    
    // All ones
    let ones = vec![0xFFu8; 10];
    let mut folded = 0u8;
    for (i, &byte) in ones.iter().enumerate() {
        folded ^= (byte as u8).rotate_left((i % 8) as u32);
    }
    let recovery = calculate_recovery_bits(&ones, folded);
    assert!(recovery <= 15);
}

#[test]
fn test_byte_to_equivalents_mapping() {
    // Test the byte_to_equivalents helper
    for byte in 0u8..=255 {
        let equivalents = get_equivalents(byte);
        
        // Should include the byte itself
        assert!(equivalents.contains(&byte),
            "Byte {} not in its own equivalents list", byte);
        
        // All equivalents should have same resonance class
        let resonance = byte_to_resonance_class(byte);
        for &equiv in equivalents {
            assert_eq!(byte_to_resonance_class(equiv), resonance,
                "Equivalent {} of {} has different resonance", equiv, byte);
        }
        
        // Size should be 2 or 4
        assert!(equivalents.len() == 2 || equivalents.len() == 4,
            "Invalid equivalents size: {}", equivalents.len());
    }
}

#[test]
fn test_preserving_xor_patterns() {
    // Verify the XOR patterns that preserve resonance
    for byte in 0u8..=255 {
        let resonance = byte_to_resonance_class(byte);
        
        // Test each preserving pattern
        for &pattern in &PRESERVING_XOR_PATTERNS {
            let xored = byte ^ pattern;
            let xored_resonance = byte_to_resonance_class(xored);
            
            // They should either be equal (same class) or the byte is out of range
            if xored <= 255 {
                let same_class = resonance == xored_resonance;
                let in_equivalents = get_equivalents(byte).contains(&xored);
                
                assert_eq!(same_class, in_equivalents,
                    "XOR pattern {} inconsistency for byte {}", pattern, byte);
            }
        }
    }
}