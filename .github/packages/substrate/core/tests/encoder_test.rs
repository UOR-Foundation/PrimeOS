//! Comprehensive tests for the PrimeOS encoder

use primeos_codec::{PrimeOSEncoder, AddressEncoder};
use primeos_codec::recovery::RecoveryBits;
use primeos_codec::resonance::byte_to_resonance_class;
use bitvec::prelude::*;

#[test]
fn test_encoder_implements_trait() {
    let encoder = PrimeOSEncoder::new();
    let bits = bitvec![1, 0, 1, 1, 0, 0, 1, 0];
    
    // Test that encoder implements AddressEncoder trait
    let digest = encoder.encode(&bits).unwrap();
    assert!(digest.size() >= 4);
}

#[test]
fn test_encoder_empty_input() {
    println!("\n=== Testing encoder with empty input ===");
    
    let encoder = PrimeOSEncoder::new();
    let empty_bits: BitVec = BitVec::new();
    
    let digest = encoder.encode(&empty_bits).unwrap();
    println!("Empty input -> {} byte digest", digest.size());
    
    // Should be minimal: 1 byte varint (0) + 1 byte checksum
    assert_eq!(digest.size(), 2);
    assert!(digest.validate().is_ok());
}

#[test]
fn test_encoder_single_byte_patterns() {
    println!("\n=== Testing encoder with single byte patterns ===");
    
    let test_bytes = vec![
        0u8,    // All zeros
        255u8,  // All ones
        1u8,    // Single bit
        48u8,   // Unity position
        49u8,   // Unity position
        170u8,  // 10101010 pattern
        85u8,   // 01010101 pattern
    ];
    
    for byte in test_bytes {
        let encoder = PrimeOSEncoder::new();
        let digest = encoder.encode_bytes(&[byte]).unwrap();
        
        println!("Byte {} (class {}) -> {} byte digest", 
                 byte, byte_to_resonance_class(byte), digest.size());
        
        // Single byte = 8 bits = 1 cycle
        // Should be: varint + 3 bytes coordinate + checksum
        assert!(digest.size() >= 5);
        assert!(digest.validate().is_ok());
    }
}

#[test]
fn test_encoder_multi_byte_patterns() {
    println!("\n=== Testing encoder with multi-byte patterns ===");
    
    let test_patterns = vec![
        vec![0, 0],
        vec![0, 1, 48, 49],  // Unity positions
        vec![1, 2, 3, 4, 5, 6, 7, 8],
        vec![255; 16],       // All ones
        vec![170, 85, 170, 85, 170, 85, 170, 85],  // Alternating pattern
    ];
    
    for pattern in test_patterns {
        let encoder = PrimeOSEncoder::new();
        let digest = encoder.encode_bytes(&pattern).unwrap();
        
        println!("Pattern len {} -> {} byte digest", pattern.len(), digest.size());
        assert!(digest.validate().is_ok());
    }
}

#[test]
fn test_encoder_cycle_boundaries() {
    println!("\n=== Testing encoder at cycle boundaries ===");
    
    // CYCLE_LENGTH = 768 bits = 96 bytes
    let test_sizes = vec![
        95,   // Just under 1 cycle
        96,   // Exactly 1 cycle
        97,   // Just over 1 cycle
        191,  // Just under 2 cycles
        192,  // Exactly 2 cycles
        193,  // Just over 2 cycles
    ];
    
    for size in test_sizes {
        let encoder = PrimeOSEncoder::new();
        let data = vec![0xAA; size];
        let digest = encoder.encode_bytes(&data).unwrap();
        
        let expected_cycles = (size * 8 + 767) / 768;
        println!("Size {} bytes -> {} cycles -> {} byte digest", 
                 size, expected_cycles, digest.size());
        
        assert!(digest.validate().is_ok());
    }
}

#[test]
fn test_encoder_deterministic() {
    println!("\n=== Testing encoder determinism ===");
    
    let test_data = vec![
        vec![42],
        b"Hello, PrimeOS!".to_vec(),
        vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
        vec![255; 100],
    ];
    
    for data in test_data {
        let mut encoder1 = PrimeOSEncoder::new();
        let digest1 = encoder1.encode_bytes(&data).unwrap();
        
        let mut encoder2 = PrimeOSEncoder::new();
        let digest2 = encoder2.encode_bytes(&data).unwrap();
        
        assert_eq!(digest1, digest2, 
                   "Encoding not deterministic for data len {}", data.len());
    }
    
    println!("✓ All encodings are deterministic");
}

#[test]
fn test_encoder_recovery_bits() {
    println!("\n=== Testing encoder recovery bits ===");
    
    // Test that recovery bits are properly calculated
    let mut encoder = PrimeOSEncoder::new();
    
    // Encode a pattern where we know the recovery bits matter
    let data = vec![0, 1, 48, 49]; // Unity positions - same resonance class
    let digest = encoder.encode_bytes(&data).unwrap();
    
    // Extract the packed coordinates
    let digest_bytes = digest.as_bytes();
    
    // Skip varint length
    let mut pos = 1;
    while pos < digest_bytes.len() && (digest_bytes[pos - 1] & 0x80) != 0 {
        pos += 1;
    }
    
    // Each coordinate is 3 bytes
    if pos + 3 <= digest_bytes.len() - 1 { // -1 for checksum
        let recovery_bits = digest_bytes[pos + 2] & 0x0F;
        println!("Recovery bits: {:04b}", recovery_bits);
        
        // Recovery bits should encode pattern information
        assert!(recovery_bits != 0 || data.len() == 1);
    }
}

#[test]
fn test_encoder_varint_sizes() {
    println!("\n=== Testing encoder varint encoding ===");
    
    // Test patterns that result in different bit lengths
    let test_cases = vec![
        (15, 120),    // 120 bits -> 1 byte varint
        (16, 128),    // 128 bits -> 2 byte varint
        (2048, 16384), // 16384 bits -> 3 byte varint
    ];
    
    for (byte_size, bit_size) in test_cases {
        let encoder = PrimeOSEncoder::new();
        let data = vec![0xFF; byte_size];
        let digest = encoder.encode_bytes(&data).unwrap();
        
        // Check first byte(s) encode the bit length
        let first_byte = digest.as_bytes()[0];
        
        if bit_size < 128 {
            assert_eq!(first_byte & 0x7F, bit_size as u8);
            assert_eq!(first_byte & 0x80, 0);
        } else {
            assert_ne!(first_byte & 0x80, 0);
        }
        
        println!("Bit length {} encoded correctly", bit_size);
    }
}

#[test]
fn test_encoder_resonance_preservation() {
    println!("\n=== Testing encoder resonance preservation ===");
    
    // Test that bytes with same resonance class are distinguished by recovery bits
    let mut same_class_groups = std::collections::HashMap::new();
    
    for byte in 0u8..=255 {
        let class = byte_to_resonance_class(byte);
        same_class_groups.entry(class).or_insert_with(Vec::new).push(byte);
    }
    
    // Test a few resonance classes
    for (class, bytes) in same_class_groups.iter().take(5) {
        if bytes.len() > 1 {
            println!("Testing class {} with {} members", class, bytes.len());
            
            let mut digests = Vec::new();
            for &byte in bytes {
                let encoder = PrimeOSEncoder::new();
                let digest = encoder.encode_bytes(&[byte]).unwrap();
                digests.push(digest);
            }
            
            // All digests should be different despite same resonance class
            for i in 0..digests.len() {
                for j in i+1..digests.len() {
                    assert_ne!(digests[i], digests[j],
                              "Bytes {} and {} (same class {}) produced identical digests",
                              bytes[i], bytes[j], class);
                }
            }
        }
    }
}

#[test]
fn test_encoder_performance() {
    use std::time::Instant;
    
    println!("\n=== Testing encoder performance ===");
    
    let sizes = vec![
        ("1 byte", 1),
        ("1 KB", 1024),
        ("10 KB", 10 * 1024),
        ("100 KB", 100 * 1024),
    ];
    
    for (name, size) in sizes {
        let data = vec![0xAA; size];
        let start = Instant::now();
        
        let encoder = PrimeOSEncoder::new();
        let digest = encoder.encode_bytes(&data).unwrap();
        
        let duration = start.elapsed();
        let throughput = size as f64 / duration.as_secs_f64() / 1_048_576.0;
        
        println!("{}: {} bytes -> {} byte digest in {:?} ({:.2} MB/s)",
                 name, size, digest.size(), duration, throughput);
    }
}