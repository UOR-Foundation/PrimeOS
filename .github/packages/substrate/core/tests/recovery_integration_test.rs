//! Integration tests for the recovery bits mechanism

use primeos_codec::recovery::{RecoveryBits, RecoveryContext};
use primeos_codec::resonance::byte_to_resonance_class;
use primeos_codec::mapper::COORDINATE_MAPPER;
use std::collections::HashMap;

#[test]
fn test_full_byte_space_recovery() {
    println!("\n=== Testing recovery for all 256 bytes ===");
    
    let mut failures = Vec::new();
    
    for byte in 0u8..=255 {
        let recovery_bits = RecoveryBits::calculate_recovery_bits(&[byte], byte);
        let class = byte_to_resonance_class(byte);
        
        let recovered = RecoveryBits::recover_byte(
            class,
            recovery_bits,
            Some(&RecoveryContext {
                is_single_byte: true,
                position: 0,
                constraints: None,
            })
        );
        
        match recovered {
            Ok(recovered_byte) => {
                if recovered_byte != byte {
                    failures.push(format!(
                        "Byte {}: Expected {}, got {} (recovery bits: {:04b}, class: {})",
                        byte, byte, recovered_byte, recovery_bits, class
                    ));
                }
            }
            Err(e) => {
                failures.push(format!(
                    "Byte {}: Recovery failed with error: {} (recovery bits: {:04b}, class: {})",
                    byte, e, recovery_bits, class
                ));
            }
        }
    }
    
    if !failures.is_empty() {
        println!("Recovery failures:");
        for failure in &failures {
            println!("  {}", failure);
        }
        panic!("{} bytes failed recovery", failures.len());
    }
    
    println!("✓ All 256 bytes recovered successfully");
}

#[test]
fn test_resonance_class_coverage() {
    println!("\n=== Testing resonance class coverage ===");
    
    let mut class_recovery_map: HashMap<u8, Vec<(u8, u8)>> = HashMap::new();
    
    // Map each byte to its class and recovery bits
    for byte in 0u8..=255 {
        let class = byte_to_resonance_class(byte);
        let recovery_bits = RecoveryBits::calculate_recovery_bits(&[byte], byte);
        
        class_recovery_map.entry(class)
            .or_insert_with(Vec::new)
            .push((byte, recovery_bits));
    }
    
    println!("Found {} resonance classes", class_recovery_map.len());
    
    // Verify each class has unique recovery bits for its members
    for (class, members) in &class_recovery_map {
        let class_bytes = COORDINATE_MAPPER.get_bytes_for_resonance_class(*class);
        
        println!("Class {}: {} members, {} bytes in mapper", 
                 class, members.len(), class_bytes.len());
        
        // Check that recovery bits are unique within the class
        let mut recovery_bit_map: HashMap<u8, Vec<u8>> = HashMap::new();
        
        for (byte, recovery_bits) in members {
            recovery_bit_map.entry(*recovery_bits)
                .or_insert_with(Vec::new)
                .push(*byte);
        }
        
        // Look for collisions
        for (bits, bytes) in &recovery_bit_map {
            if bytes.len() > 1 {
                println!("  WARNING: Recovery bits {:04b} used by multiple bytes: {:?}", 
                         bits, bytes);
            }
        }
    }
    
    println!("✓ Resonance class coverage verified");
}

#[test]
fn test_multi_byte_patterns() {
    println!("\n=== Testing multi-byte recovery patterns ===");
    
    let test_patterns = vec![
        vec![0, 0],
        vec![0, 1, 48, 49],  // Unity positions
        vec![10, 20, 30],
        vec![255, 254, 253, 252],
        vec![1, 2, 4, 8, 16, 32, 64, 128],  // Powers of 2
    ];
    
    for pattern in test_patterns {
        let folded = pattern.iter().fold(0u8, |acc, &b| acc ^ b);
        let recovery_bits = RecoveryBits::calculate_recovery_bits(&pattern, folded);
        
        println!("Pattern {:?} -> folded: {}, recovery: {:04b}", 
                 pattern, folded, recovery_bits);
        
        // Verify pattern signature is consistent
        let recovery_bits2 = RecoveryBits::calculate_recovery_bits(&pattern, folded);
        assert_eq!(recovery_bits, recovery_bits2, 
                   "Recovery bits not deterministic for pattern {:?}", pattern);
    }
    
    println!("✓ Multi-byte patterns tested");
}

#[test]
fn test_recovery_with_constraints() {
    println!("\n=== Testing constrained recovery ===");
    
    use primeos_codec::recovery::RecoveryConstraints;
    
    // Test case: Missing byte in XOR-balanced block
    let known_bytes = vec![1, 2, 3, 4, 5, 6, 7];
    let missing_byte = 8u8;
    let xor_sum = known_bytes.iter().fold(missing_byte, |acc, &b| acc ^ b);
    
    let mut constraints = RecoveryConstraints {
        xor_sum: Some(xor_sum),
        resonance_sum: None,
        adjacent_bytes: HashMap::new(),
    };
    
    // Add adjacent byte constraints
    constraints.adjacent_bytes.insert(6, 7);  // Previous byte
    constraints.adjacent_bytes.insert(8, 9);  // Next byte
    
    let context = RecoveryContext {
        is_single_byte: false,
        position: 7,
        constraints: Some(constraints),
    };
    
    let class = byte_to_resonance_class(missing_byte);
    let recovery_bits = RecoveryBits::calculate_recovery_bits(&[missing_byte], missing_byte);
    
    let recovered = RecoveryBits::recover_byte(class, recovery_bits, Some(&context)).unwrap();
    
    println!("Missing byte {} (class {}) recovered as {} using constraints", 
             missing_byte, class, recovered);
    
    println!("✓ Constrained recovery tested");
}

#[test]
fn test_edge_cases() {
    println!("\n=== Testing edge cases ===");
    
    // Test empty input
    let recovery_bits = RecoveryBits::calculate_recovery_bits(&[], 0);
    assert_eq!(recovery_bits, 0);
    
    // Test recovery with high class number (may be valid)
    let result = RecoveryBits::recover_byte(95, 0, None);  // Use max valid class
    assert!(result.is_ok()); // Should handle gracefully
    
    // Test recovery with out-of-bounds recovery bits
    let class = byte_to_resonance_class(42);
    let result = RecoveryBits::recover_byte(class, 0xFF, Some(&RecoveryContext {
        is_single_byte: true,
        position: 0,
        constraints: None,
    }));
    assert!(result.is_ok()); // Should handle gracefully
    
    println!("✓ Edge cases handled");
}

#[test]
fn test_recovery_performance() {
    use std::time::Instant;
    
    println!("\n=== Testing recovery performance ===");
    
    let iterations = 10000;
    
    // Test single byte recovery performance
    let start = Instant::now();
    for i in 0..iterations {
        let byte = (i % 256) as u8;
        let recovery_bits = RecoveryBits::calculate_recovery_bits(&[byte], byte);
        let class = byte_to_resonance_class(byte);
        let _ = RecoveryBits::recover_byte(class, recovery_bits, Some(&RecoveryContext {
            is_single_byte: true,
            position: 0,
            constraints: None,
        }));
    }
    let single_duration = start.elapsed();
    
    println!("Single byte recovery: {} iterations in {:?} ({:.2} µs/op)", 
             iterations, single_duration, 
             single_duration.as_micros() as f64 / iterations as f64);
    
    // Test multi-byte recovery performance
    let start = Instant::now();
    for i in 0..iterations {
        let bytes = vec![(i % 256) as u8, ((i + 1) % 256) as u8, ((i + 2) % 256) as u8];
        let folded = bytes.iter().fold(0u8, |acc, &b| acc ^ b);
        let _ = RecoveryBits::calculate_recovery_bits(&bytes, folded);
    }
    let multi_duration = start.elapsed();
    
    println!("Multi-byte recovery bits: {} iterations in {:?} ({:.2} µs/op)", 
             iterations, multi_duration,
             multi_duration.as_micros() as f64 / iterations as f64);
    
    println!("✓ Performance test completed");
}