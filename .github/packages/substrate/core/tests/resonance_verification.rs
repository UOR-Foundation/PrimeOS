//! Verify resonance calculations and class mappings

use primeos_codec::*;

#[test]
fn verify_xor_equivalence_property() {
    // The XOR equivalence property states that bytes differing by XOR with {1, 48, 49}
    // have the same resonance value because:
    // - XOR with 1 flips bit 0, multiplying by α₀ = 1 (no change)
    // - XOR with 48 (0b00110000) flips bits 4 and 5, multiplying by α₄ × α₅ = 1 (no change)
    // - XOR with 49 (0b00110001) combines both effects
    
    println!("Testing XOR equivalence for specific bytes:");
    
    // Test a few specific cases
    let test_bytes = [0, 2, 16, 100, 200];
    
    for &base in &test_bytes {
        let base_resonance = calculate_resonance(base);
        let base_class = byte_to_resonance_class(base);
        
        // XOR with 1
        let xor1 = base ^ 1;
        let xor1_resonance = calculate_resonance(xor1);
        let xor1_class = byte_to_resonance_class(xor1);
        
        println!("Byte {} (class {}): resonance = {:.6}", base, base_class, base_resonance);
        println!("  XOR 1 -> {} (class {}): resonance = {:.6}", xor1, xor1_class, xor1_resonance);
        
        // Resonances should be equal
        assert!((base_resonance - xor1_resonance).abs() < 1e-10,
                "Byte {} and {} should have same resonance", base, xor1);
        
        // XOR with 48
        let xor48 = base ^ 48;
        let xor48_resonance = calculate_resonance(xor48);
        let xor48_class = byte_to_resonance_class(xor48);
        
        println!("  XOR 48 -> {} (class {}): resonance = {:.6}", xor48, xor48_class, xor48_resonance);
        
        assert!((base_resonance - xor48_resonance).abs() < 1e-10,
                "Byte {} and {} should have same resonance", base, xor48);
        
        // XOR with 49
        let xor49 = base ^ 49;
        let xor49_resonance = calculate_resonance(xor49);
        let xor49_class = byte_to_resonance_class(xor49);
        
        println!("  XOR 49 -> {} (class {}): resonance = {:.6}", xor49, xor49_class, xor49_resonance);
        
        assert!((base_resonance - xor49_resonance).abs() < 1e-10,
                "Byte {} and {} should have same resonance", base, xor49);
        
        println!();
    }
}

#[test]
fn verify_field_constant_relationships() {
    // α₄ × α₅ should equal exactly 1.0
    let product = FIELD_CONSTANTS[4] * FIELD_CONSTANTS[5];
    println!("α₄ × α₅ = {:.15}", product);
    assert!((product - 1.0).abs() < 1e-15, "α₄ × α₅ must equal 1.0");
    
    // α₃ × α₅ should equal π
    let pi_product = FIELD_CONSTANTS[3] * FIELD_CONSTANTS[5];
    println!("α₃ × α₅ = {:.15}", pi_product);
    println!("π       = {:.15}", std::f64::consts::PI);
    assert!((pi_product - std::f64::consts::PI).abs() < 1e-10, "α₃ × α₅ must equal π");
}

#[test]
fn verify_resonance_class_count() {
    use std::collections::HashSet;
    
    // Count unique resonance values
    let mut unique_resonances = HashSet::new();
    for byte in 0u8..=255 {
        let resonance = calculate_resonance(byte);
        unique_resonances.insert(resonance.to_bits());
    }
    
    println!("Total unique resonance values: {}", unique_resonances.len());
    assert_eq!(unique_resonances.len(), 96, "Must have exactly 96 unique resonances");
}

#[test]
fn debug_failing_xor_case() {
    // Debug why byte 16 XOR 48 = 32 might not have same class
    let byte16 = 16u8;
    let byte32 = 32u8;
    let byte48 = 48u8;
    
    println!("Debugging XOR case:");
    println!("16 = {:08b}", byte16);
    println!("48 = {:08b}", byte48);
    println!("16 XOR 48 = {} = {:08b}", byte16 ^ byte48, byte16 ^ byte48);
    
    let res16 = calculate_resonance(byte16);
    let res32 = calculate_resonance(byte32);
    
    println!("\nResonance values:");
    println!("Resonance(16) = {:.15}", res16);
    println!("Resonance(32) = {:.15}", res32);
    println!("Difference = {:.2e}", (res16 - res32).abs());
    
    // Check what bits are involved
    println!("\nBit analysis:");
    println!("16 has bit 4 set");
    println!("32 has bit 5 set");
    println!("XOR flips bit 4 (turn off) and bit 5 (turn on)");
    
    // Calculate the change in resonance
    let change_factor = FIELD_CONSTANTS[5] / FIELD_CONSTANTS[4];
    println!("\nChange factor: α₅/α₄ = {:.15}", change_factor);
    println!("Expected resonance(32) = resonance(16) × α₅/α₄ = {:.15}", res16 * change_factor);
    println!("Actual resonance(32) = {:.15}", res32);
}