//! Generate the resonance class mapping for PrimeOS codec
//! This helps us understand and verify the 96 unique resonance classes

use std::collections::{HashMap, HashSet};

const FIELD_CONSTANTS: [f64; 8] = [
    1.0,                    // α₀: Identity
    1.8392867552141612,     // α₁: Tribonacci constant
    1.6180339887498950,     // α₂: Golden ratio (φ)
    0.5,                    // α₃: Half
    0.15915494309189535,    // α₄: 1/(2π)
    6.283185307179586,      // α₅: 2π
    0.199612,               // α₆: Phase constant
    0.014134725,            // α₇: Quantum constant
];

fn calculate_resonance(byte: u8) -> f64 {
    let mut resonance = 1.0;
    for bit in 0..8 {
        if (byte >> bit) & 1 == 1 {
            resonance *= FIELD_CONSTANTS[bit];
        }
    }
    resonance
}

fn main() {
    // Calculate all resonances
    let mut resonances: Vec<(u8, f64)> = Vec::new();
    for byte in 0u8..=255 {
        let resonance = calculate_resonance(byte);
        resonances.push((byte, resonance));
    }

    // Sort by resonance value
    resonances.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());

    // Find unique resonances and assign class IDs
    let mut unique_resonances = HashMap::new();
    let mut class_map = [0u8; 256];
    let mut class_id = 0u8;
    
    for (byte, resonance) in &resonances {
        // Use resonance bits as key for exact comparison
        let resonance_bits = resonance.to_bits();
        
        if !unique_resonances.contains_key(&resonance_bits) {
            unique_resonances.insert(resonance_bits, class_id);
            class_id += 1;
        }
        
        class_map[*byte as usize] = unique_resonances[&resonance_bits];
    }

    println!("Total unique resonance classes: {}", unique_resonances.len());
    
    // Verify unity constraint
    let unity = FIELD_CONSTANTS[4] * FIELD_CONSTANTS[5];
    println!("\nα₄ × α₅ = {:.15} (should be 1.0)", unity);
    
    // Check unity bytes
    println!("\nUnity bytes (resonance = 1.0):");
    for byte in [0, 1, 48, 49] {
        let resonance = calculate_resonance(byte);
        let class = class_map[byte as usize];
        println!("  Byte {}: resonance = {:.6}, class = {}", byte, resonance, class);
    }
    
    // Show equivalence classes
    println!("\nExample equivalence classes:");
    let mut class_members: HashMap<u8, Vec<u8>> = HashMap::new();
    for byte in 0u8..=255 {
        class_members.entry(class_map[byte as usize])
            .or_insert_with(Vec::new)
            .push(byte);
    }
    
    // Show first few classes
    for class in 0..5 {
        if let Some(members) = class_members.get(&class) {
            let resonance = calculate_resonance(members[0]);
            println!("  Class {}: {:?} (resonance = {:.6})", class, members, resonance);
        }
    }
    
    // Generate the const array for Rust
    println!("\n// Generated resonance class map:");
    println!("pub const RESONANCE_CLASS_MAP: [u8; 256] = [");
    for chunk in class_map.chunks(16) {
        print!("    ");
        for (i, &value) in chunk.iter().enumerate() {
            if i > 0 { print!(", "); }
            print!("{:2}", value);
        }
        println!(",");
    }
    println!("];");
    
    // Verify XOR relationships
    println!("\nVerifying XOR relationships:");
    for base in [0, 2, 4, 6, 8] {
        let base_class = class_map[base];
        let xor1_class = class_map[base ^ 1];
        let xor48_class = class_map[base ^ 48];
        let xor49_class = class_map[base ^ 49];
        
        println!("  Base {}: class {} (XOR 1: {}, XOR 48: {}, XOR 49: {})",
                 base, base_class, xor1_class, xor48_class, xor49_class);
        
        // They should all be the same class
        assert_eq!(base_class, xor1_class);
        assert_eq!(base_class, xor48_class);
        assert_eq!(base_class, xor49_class);
    }
}