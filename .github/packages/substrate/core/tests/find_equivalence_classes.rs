//! Find which bytes actually form XOR equivalence classes

use primeos_codec::*;
use std::collections::HashMap;

#[test]
fn find_xor_equivalence_classes() {
    // Group bytes by resonance value
    let mut resonance_groups: HashMap<u64, Vec<u8>> = HashMap::new();
    
    for byte in 0u8..=255 {
        let resonance = calculate_resonance(byte);
        resonance_groups.entry(resonance.to_bits()).or_insert_with(Vec::new).push(byte);
    }
    
    println!("Found {} unique resonance values", resonance_groups.len());
    
    // For each group, check if it forms an XOR equivalence class
    let mut valid_xor_groups = 0;
    let mut invalid_xor_groups = 0;
    
    for (resonance_bits, bytes) in &resonance_groups {
        let resonance = f64::from_bits(*resonance_bits);
        
        // Check if this group forms a valid XOR equivalence class
        let mut is_valid_xor_group = true;
        
        if bytes.len() == 4 {
            // Should be closed under XOR with {0, 1, 48, 49}
            let base = bytes[0];
            let expected_set: Vec<u8> = vec![base, base ^ 1, base ^ 48, base ^ 49];
            let mut expected_sorted = expected_set.clone();
            expected_sorted.sort();
            let mut actual_sorted = bytes.clone();
            actual_sorted.sort();
            
            if expected_sorted == actual_sorted {
                println!("Valid 4-element XOR group: {:?} (resonance = {:.6})", bytes, resonance);
                valid_xor_groups += 1;
            } else {
                is_valid_xor_group = false;
            }
        } else if bytes.len() == 2 {
            // Should differ by XOR 1
            if bytes[0] ^ bytes[1] == 1 {
                println!("Valid 2-element XOR group: {:?} (resonance = {:.6})", bytes, resonance);
                valid_xor_groups += 1;
            } else {
                is_valid_xor_group = false;
            }
        } else {
            is_valid_xor_group = false;
        }
        
        if !is_valid_xor_group {
            invalid_xor_groups += 1;
            if bytes.len() <= 6 {
                println!("Non-XOR group (size {}): {:?} (resonance = {:.6})", bytes.len(), bytes, resonance);
            }
        }
    }
    
    println!("\nSummary:");
    println!("Valid XOR equivalence groups: {}", valid_xor_groups);
    println!("Non-XOR groups: {}", invalid_xor_groups);
    println!("Total groups: {}", resonance_groups.len());
    
    // The key insight: only certain bytes form XOR equivalence classes
    // Specifically, those where bits 4 and 5 are either both 0 or both 1
}

#[test] 
fn analyze_xor_pattern() {
    println!("Analyzing which bytes preserve resonance under XOR {{1, 48, 49}}:");
    
    let mut preserving_count = 0;
    let mut non_preserving_count = 0;
    
    for byte in 0u8..=255 {
        let res = calculate_resonance(byte);
        let res_xor1 = calculate_resonance(byte ^ 1);
        let res_xor48 = calculate_resonance(byte ^ 48);
        let res_xor49 = calculate_resonance(byte ^ 49);
        
        let preserves_1 = (res - res_xor1).abs() < 1e-10;
        let preserves_48 = (res - res_xor48).abs() < 1e-10;
        let preserves_49 = (res - res_xor49).abs() < 1e-10;
        
        if preserves_1 && preserves_48 && preserves_49 {
            preserving_count += 1;
            if preserving_count <= 20 {
                println!("  Byte {:3} = {:08b} preserves resonance", byte, byte);
            }
        } else {
            non_preserving_count += 1;
        }
    }
    
    println!("\nBytes that preserve resonance under XOR {{1, 48, 49}}: {}", preserving_count);
    println!("Bytes that don't preserve resonance: {}", non_preserving_count);
    
    // Key insight: only bytes where bits 4 and 5 have the same value (both 0 or both 1)
    // will preserve resonance under XOR 48
}