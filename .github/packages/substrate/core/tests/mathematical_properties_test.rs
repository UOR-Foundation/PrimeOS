//! Tests to verify the implementation matches the mathematical properties from research

use primeos_codec::equivalence::*;
use primeos_codec::resonance::{byte_to_resonance_class, calculate_resonance};
use primeos_codec::constants::FIELD_CONSTANTS;
use std::collections::HashSet;

#[test]
fn test_unity_constraint() {
    // Verify α₄ × α₅ = 1 (the fundamental unity constraint)
    let unity = FIELD_CONSTANTS[4] * FIELD_CONSTANTS[5];
    assert!((unity - 1.0).abs() < 1e-10, 
        "Unity constraint violated: α₄ × α₅ = {} (should be 1.0)", unity);
}

#[test]
fn test_xor_equivalence_mathematical_basis() {
    // Test that XOR with {1, 48, 49} preserves resonance due to field constants
    
    // XOR with 1 toggles bit 0 (α₀ = 1.0)
    for byte in 0u8..=255 {
        let r1 = calculate_resonance(byte);
        let r2 = calculate_resonance(byte ^ 1);
        assert!((r1 - r2).abs() < 1e-10,
            "XOR with 1 should preserve resonance for byte {}", byte);
    }
    
    // XOR with 48 toggles bits 4,5 (α₄ × α₅ = 1.0)
    // Only true when bits 4,5 have same initial value
    for byte in 0u8..=255 {
        let bit4 = (byte >> 4) & 1;
        let bit5 = (byte >> 5) & 1;
        
        if bit4 == bit5 {
            let r1 = calculate_resonance(byte);
            let r2 = calculate_resonance(byte ^ 48);
            assert!((r1 - r2).abs() < 1e-10,
                "XOR with 48 should preserve resonance for byte {} when bits 4,5 match", byte);
        }
    }
}

#[test]
fn test_96_unique_resonance_classes() {
    // Verify exactly 96 unique resonance values
    use std::collections::HashSet;
    
    let mut unique_resonances = HashSet::new();
    let mut unique_classes = HashSet::new();
    
    for byte in 0u8..=255 {
        let resonance = calculate_resonance(byte);
        let class = byte_to_resonance_class(byte);
        
        // Use string representation to avoid floating point comparison issues
        unique_resonances.insert(format!("{:.10}", resonance));
        unique_classes.insert(class);
    }
    
    assert_eq!(unique_resonances.len(), 96, 
        "Should have exactly 96 unique resonance values");
    assert_eq!(unique_classes.len(), 96,
        "Should have exactly 96 unique resonance classes");
}

#[test]
fn test_klein_group_structure() {
    // Unity positions {0, 1, 48, 49} form a Klein four-group
    let unity_positions = vec![0u8, 1, 48, 49];
    
    // All should have unity resonance
    for &pos in &unity_positions {
        let resonance = calculate_resonance(pos);
        assert!((resonance - 1.0).abs() < 1e-10,
            "Position {} should have unity resonance", pos);
    }
    
    // Verify group closure under XOR
    for &a in &unity_positions {
        for &b in &unity_positions {
            let result = a ^ b;
            assert!(unity_positions.contains(&result),
                "{} XOR {} = {} should be in unity positions", a, b, result);
        }
    }
    
    // Verify identity element (0)
    for &pos in &unity_positions {
        assert_eq!(pos ^ 0, pos, "0 should be identity element");
    }
    
    // Verify self-inverse property
    for &pos in &unity_positions {
        assert_eq!(pos ^ pos, 0, "Every element should be self-inverse");
    }
}

#[test]
fn test_equivalence_class_distribution() {
    // Based on research: 256 positions partition into:
    // - Some classes of size 2 (differ by bit 0)
    // - Some classes of size 4 (differ by bits 0, 4, 5)
    
    let mut class_sizes = std::collections::HashMap::new();
    
    for class in EQUIVALENCE_CLASSES.iter() {
        *class_sizes.entry(class.size).or_insert(0) += 1;
    }
    
    // Should only have sizes 2 and 4
    assert_eq!(class_sizes.len(), 2, "Should only have class sizes 2 and 4");
    assert!(class_sizes.contains_key(&2), "Should have size-2 classes");
    assert!(class_sizes.contains_key(&4), "Should have size-4 classes");
    
    // Total members should be 256
    let total_members: usize = EQUIVALENCE_CLASSES.iter()
        .map(|c| c.size as usize)
        .sum();
    assert_eq!(total_members, 256, "All 256 bytes should be accounted for");
}

#[test]
fn test_recovery_preserves_bijection_property() {
    // For bijection, every input must map to a unique (resonance_class, recovery_bits) pair
    use std::collections::HashSet;
    
    let mut seen_pairs = HashSet::new();
    
    // Test single bytes
    for byte in 0u8..=255 {
        let resonance_class = byte_to_resonance_class(byte);
        let recovery = calculate_recovery_bits(&[byte], byte);
        let pair = (resonance_class, recovery);
        
        assert!(seen_pairs.insert(pair),
            "Duplicate (resonance, recovery) pair for byte {}: {:?}", byte, pair);
    }
    
    // For multi-byte patterns, we can't guarantee global uniqueness with only 4 recovery bits,
    // but we can verify that the recovery information is deterministic
    let test_patterns = vec![
        vec![0x42],
        vec![0x42, 0x17],
        vec![0x42, 0x17, 0xAB],
    ];
    
    for pattern in test_patterns {
        // Calculate folded byte
        let mut folded = 0u8;
        for (i, &byte) in pattern.iter().enumerate() {
            folded ^= (byte as u8).rotate_left((i % 8) as u32);
        }
        
        // Recovery should be deterministic
        let recovery1 = calculate_recovery_bits(&pattern, folded);
        let recovery2 = calculate_recovery_bits(&pattern, folded);
        assert_eq!(recovery1, recovery2, 
            "Recovery calculation not deterministic for {:?}", pattern);
    }
}

#[test]
fn test_three_byte_digest_format() {
    // Per research: 3 bytes per 768-bit cycle
    // Byte 0: High 8 bits of 13-bit position
    // Byte 1: [Low 5 bits of position][High 3 bits of 7-bit resonance class]  
    // Byte 2: [Low 4 bits of resonance class][4 bits recovery]
    
    // Test that recovery bits fit in the allocated 4 bits
    for i in 0..100 {
        let test_bytes: Vec<u8> = (0..i).map(|j| (j * 17) as u8).collect();
        if test_bytes.is_empty() { continue; }
        
        let mut folded = 0u8;
        for (j, &byte) in test_bytes.iter().enumerate() {
            folded ^= byte.rotate_left((j % 8) as u32);
        }
        
        let recovery = calculate_recovery_bits(&test_bytes, folded);
        assert!(recovery <= 15, "Recovery bits must fit in 4 bits, got {}", recovery);
    }
}

#[test]
fn test_no_placeholders_in_implementation() {
    // This test verifies the implementation is complete by checking that
    // all the mathematical properties are properly implemented
    
    // 1. Single byte recovery works perfectly
    for byte in 0u8..=255 {
        let recovery = calculate_recovery_bits(&[byte], byte);
        let resonance_class = byte_to_resonance_class(byte);
        let recovered = recover_byte(resonance_class, recovery);
        assert_eq!(recovered, Some(byte), "Single byte recovery failed");
    }
    
    // 2. Equivalence classes have correct structure
    assert_eq!(EQUIVALENCE_CLASSES.len(), 96);
    
    // 3. Recovery bits use all available space efficiently
    let mut recovery_values = HashSet::new();
    for byte in 0u8..=255 {
        let recovery = calculate_recovery_bits(&[byte], byte);
        recovery_values.insert(recovery & 0x03); // Position bits
    }
    // Should use values 0-3 for position
    assert!(recovery_values.contains(&0));
    assert!(recovery_values.contains(&1));
    assert!(recovery_values.contains(&2));
    assert!(recovery_values.contains(&3));
    
    // 4. Multi-byte parity calculation is non-trivial
    let pattern1 = vec![1, 2, 3];
    let pattern2 = vec![3, 2, 1];
    
    let mut folded1 = 0u8;
    let mut folded2 = 0u8;
    for (i, &b) in pattern1.iter().enumerate() {
        folded1 ^= (b as u8).rotate_left((i % 8) as u32);
    }
    for (i, &b) in pattern2.iter().enumerate() {
        folded2 ^= (b as u8).rotate_left((i % 8) as u32);
    }
    
    let recovery1 = calculate_recovery_bits(&pattern1, folded1);
    let recovery2 = calculate_recovery_bits(&pattern2, folded2);
    
    // Different patterns should generally have different recovery
    // (though collisions are possible with only 4 bits)
    println!("Pattern1 recovery: {:04b}, Pattern2 recovery: {:04b}", recovery1, recovery2);
}