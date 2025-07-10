//! Comprehensive tests for the PrimeOS decoder

use primeos_codec::{PrimeOSDecoder, PrimeOSEncoder, AddressDecoder, AddressEncoder};
use primeos_codec::resonance::byte_to_resonance_class;
use bitvec::prelude::*;

#[test]
fn test_decoder_implements_trait() {
    let decoder = PrimeOSDecoder::new();
    let encoder = PrimeOSEncoder::new();
    
    // Test that decoder implements AddressDecoder trait
    let bits = bitvec![1, 0, 1, 1, 0, 0, 1, 0];
    let digest = encoder.encode(&bits).unwrap();
    let decoded_bits = decoder.decode(&digest).unwrap();
    
    assert_eq!(decoded_bits.len(), bits.len());
}

#[test]
fn test_decoder_empty_input() {
    println!("\n=== Testing decoder with empty input ===");
    
    let encoder = PrimeOSEncoder::new();
    let decoder = PrimeOSDecoder::new();
    
    let empty_bits: BitVec = BitVec::new();
    let digest = encoder.encode(&empty_bits).unwrap();
    let decoded = decoder.decode(&digest).unwrap();
    
    assert_eq!(decoded.len(), 0);
    assert_eq!(decoded, empty_bits);
    println!("✓ Empty input decoded correctly");
}

#[test]
fn test_decoder_single_byte_round_trip() {
    println!("\n=== Testing decoder single byte round-trip ===");
    
    let encoder = PrimeOSEncoder::new();
    let decoder = PrimeOSDecoder::new();
    
    // Test specific bytes including unity positions
    let test_bytes = vec![
        0u8,    // Unity position
        1u8,    // Unity position
        42u8,   // Random byte
        48u8,   // Unity position
        49u8,   // Unity position
        170u8,  // 10101010 pattern
        255u8,  // All ones
    ];
    
    for byte in test_bytes {
        let original = vec![byte];
        let digest = encoder.encode_bytes(&original).unwrap();
        let decoded = decoder.decode_bytes(&digest).unwrap();
        
        assert_eq!(decoded, original, 
                   "Failed to round-trip byte {} (class {})", 
                   byte, byte_to_resonance_class(byte));
        
        println!("✓ Byte {} (class {}) round-tripped correctly", 
                 byte, byte_to_resonance_class(byte));
    }
}

#[test]
fn test_decoder_multi_byte_patterns() {
    println!("\n=== Testing decoder with multi-byte patterns ===");
    
    let encoder = PrimeOSEncoder::new();
    let decoder = PrimeOSDecoder::new();
    
    let test_patterns = vec![
        vec![0, 0],
        vec![0, 1, 48, 49],  // Unity positions
        vec![1, 2, 3, 4, 5, 6, 7, 8],
        vec![255; 16],       // All ones
        vec![170, 85, 170, 85, 170, 85, 170, 85],  // Alternating pattern
        b"Hello, PrimeOS!".to_vec(),
    ];
    
    for pattern in test_patterns {
        let digest = encoder.encode_bytes(&pattern).unwrap();
        let decoded = decoder.decode_bytes(&digest).unwrap();
        
        assert_eq!(decoded, pattern,
                   "Failed to round-trip pattern of length {}", pattern.len());
        
        println!("✓ Pattern of length {} round-tripped correctly", pattern.len());
    }
}

#[test]
fn test_decoder_bit_level_round_trip() {
    println!("\n=== Testing decoder bit-level round-trip ===");
    
    let encoder = PrimeOSEncoder::new();
    let decoder = PrimeOSDecoder::new();
    
    // Test non-byte-aligned bit patterns
    let test_bits = vec![
        bitvec![1],                    // Single bit
        bitvec![1, 0, 1],             // 3 bits
        bitvec![1; 7],                // 7 bits
        bitvec![1, 0, 1, 1, 0, 0, 1], // 7 bits pattern
        bitvec![1; 9],                // 9 bits (crosses byte boundary)
        bitvec![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0],  // 15 bit alternating
    ];
    
    for original_bits in test_bits {
        let digest = encoder.encode(&original_bits).unwrap();
        let decoded_bits = decoder.decode(&digest).unwrap();
        
        assert_eq!(decoded_bits, original_bits,
                   "Failed to round-trip {} bits", original_bits.len());
        
        println!("✓ {} bits round-tripped correctly", original_bits.len());
    }
}

#[test]
fn test_decoder_cycle_boundaries() {
    println!("\n=== Testing decoder at cycle boundaries ===");
    
    let encoder = PrimeOSEncoder::new();
    let decoder = PrimeOSDecoder::new();
    
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
        let original = vec![0xAA; size];
        let digest = encoder.encode_bytes(&original).unwrap();
        let decoded = decoder.decode_bytes(&digest).unwrap();
        
        assert_eq!(decoded, original,
                   "Failed at cycle boundary size {}", size);
        
        let expected_cycles = (size * 8 + 767) / 768;
        println!("✓ Size {} bytes ({} cycles) decoded correctly", 
                 size, expected_cycles);
    }
}

#[test]
fn test_decoder_recovery_bits_usage() {
    println!("\n=== Testing decoder recovery bits usage ===");
    
    let encoder = PrimeOSEncoder::new();
    let decoder = PrimeOSDecoder::new();
    
    // Test bytes that are in the same resonance class
    // The recovery bits should distinguish them
    let mut same_class_groups = std::collections::HashMap::new();
    
    for byte in 0u8..=255 {
        let class = byte_to_resonance_class(byte);
        same_class_groups.entry(class).or_insert_with(Vec::new).push(byte);
    }
    
    // Test a resonance class with multiple members
    for (class, bytes) in same_class_groups.iter() {
        if bytes.len() > 1 && *class < 5 {  // Test first few classes
            println!("Testing class {} with {} members", class, bytes.len());
            
            for &byte in bytes.iter().take(4) {  // Test up to 4 members
                let original = vec![byte];
                let digest = encoder.encode_bytes(&original).unwrap();
                let decoded = decoder.decode_bytes(&digest).unwrap();
                
                assert_eq!(decoded, original,
                          "Failed to decode byte {} in class {}", byte, class);
            }
            
            println!("✓ All tested members of class {} decoded correctly", class);
        }
    }
}

#[test]
fn test_decoder_invalid_inputs() {
    println!("\n=== Testing decoder with invalid inputs ===");
    
    let decoder = PrimeOSDecoder::new();
    
    use primeos_codec::{Digest, CodecError};
    
    // Test too small digest
    let result = decoder.decode_bytes(&Digest::new(vec![1]));
    assert!(matches!(result, Err(CodecError::DigestTooSmall)));
    println!("✓ Correctly rejected too-small digest");
    
    // Test invalid checksum
    let result = decoder.decode_bytes(&Digest::new(vec![0, 0, 0, 99]));
    assert!(matches!(result, Err(CodecError::CorruptDigest)));
    println!("✓ Correctly rejected invalid checksum");
    
    // Test coordinate out of range
    let mut bad_data = vec![8]; // bit length = 8
    bad_data.push(0xFF); // High byte of coordinate (way out of range)
    bad_data.push(0xFF); 
    bad_data.push(0x00);
    let checksum = bad_data.iter().fold(0u8, |acc, &b| acc.wrapping_add(b));
    bad_data.push(checksum);
    
    let result = decoder.decode_bytes(&Digest::new(bad_data));
    assert!(result.is_err());
    println!("✓ Correctly rejected out-of-range coordinate");
}

#[test]
fn test_decoder_determinism() {
    println!("\n=== Testing decoder determinism ===");
    
    let encoder = PrimeOSEncoder::new();
    
    let test_data = vec![
        vec![42],
        b"Hello, PrimeOS!".to_vec(),
        vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
        vec![255; 100],
    ];
    
    for data in test_data {
        let digest = encoder.encode_bytes(&data).unwrap();
        
        // Decode multiple times
        let decoder1 = PrimeOSDecoder::new();
        let decoded1 = decoder1.decode_bytes(&digest).unwrap();
        
        let decoder2 = PrimeOSDecoder::new();
        let decoded2 = decoder2.decode_bytes(&digest).unwrap();
        
        assert_eq!(decoded1, decoded2,
                   "Decoding not deterministic for data len {}", data.len());
        assert_eq!(decoded1, data,
                   "Decoded data doesn't match original");
    }
    
    println!("✓ All decodings are deterministic");
}

#[test]
fn test_decoder_large_inputs() {
    println!("\n=== Testing decoder with large inputs ===");
    
    let encoder = PrimeOSEncoder::new();
    let decoder = PrimeOSDecoder::new();
    
    let sizes = vec![
        1024,       // 1 KB
        10 * 1024,  // 10 KB
    ];
    
    for size in sizes {
        // Create pattern that's not just repeated bytes
        let mut data = Vec::with_capacity(size);
        for i in 0..size {
            data.push((i * 7 + 13) as u8);  // Simple pattern
        }
        
        let digest = encoder.encode_bytes(&data).unwrap();
        let decoded = decoder.decode_bytes(&digest).unwrap();
        
        assert_eq!(decoded.len(), data.len());
        assert_eq!(decoded, data,
                   "Failed to decode {} bytes", size);
        
        println!("✓ Successfully decoded {} bytes", size);
    }
}

#[test]
fn test_decoder_performance() {
    use std::time::Instant;
    
    println!("\n=== Testing decoder performance ===");
    
    let encoder = PrimeOSEncoder::new();
    let decoder = PrimeOSDecoder::new();
    
    let sizes = vec![
        ("1 byte", 1),
        ("1 KB", 1024),
        ("10 KB", 10 * 1024),
        ("100 KB", 100 * 1024),
    ];
    
    for (name, size) in sizes {
        let data = vec![0xAA; size];
        let digest = encoder.encode_bytes(&data).unwrap();
        
        let start = Instant::now();
        let decoded = decoder.decode_bytes(&digest).unwrap();
        let duration = start.elapsed();
        
        assert_eq!(decoded.len(), size);
        
        let throughput = size as f64 / duration.as_secs_f64() / 1_048_576.0;
        
        println!("{}: {} bytes decoded in {:?} ({:.2} MB/s)",
                 name, size, duration, throughput);
    }
}