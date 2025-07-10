//! Resonance calculation and mapping for PrimeOS codec

use crate::constants::FIELD_CONSTANTS;

/// Calculate the resonance value for a given byte
pub const fn calculate_resonance(byte: u8) -> f64 {
    let mut resonance = 1.0;
    let mut bit = 0;
    
    while bit < 8 {
        if (byte >> bit) & 1 == 1 {
            resonance *= FIELD_CONSTANTS[bit];
        }
        bit += 1;
    }
    
    resonance
}

/// Precomputed resonance table (generated at compile time)
pub const RESONANCE_TABLE: [f64; 256] = generate_resonance_table();

/// Compile-time generation of resonance table
const fn generate_resonance_table() -> [f64; 256] {
    let mut table = [0.0; 256];
    let mut i = 0;
    while i < 256 {
        table[i] = calculate_resonance(i as u8);
        i += 1;
    }
    table
}

/// Resonance class mapping - maps each byte to its resonance class (0-95)
/// This mapping ensures exactly 96 unique resonance classes based on the
/// mathematical properties of the field constants (α₀ = 1, α₄ × α₅ = 1)
pub const RESONANCE_CLASS_MAP: [u8; 256] = [
    76, 76, 82, 82, 81, 81, 86, 86, 71, 71, 75, 75, 74, 74, 80, 80,
    58, 58, 66, 66, 64, 64, 70, 70, 49, 49, 57, 57, 54, 54, 63, 63,
    91, 91, 94, 94, 93, 93, 95, 95, 87, 87, 90, 90, 89, 89, 92, 92,
    76, 76, 82, 82, 81, 81, 86, 86, 71, 71, 75, 75, 74, 74, 80, 80,
    62, 62, 69, 69, 68, 68, 72, 72, 53, 53, 61, 61, 59, 59, 67, 67,
    40, 40, 47, 47, 45, 45, 52, 52, 30, 30, 39, 39, 35, 35, 44, 44,
    79, 79, 85, 85, 84, 84, 88, 88, 73, 73, 78, 78, 77, 77, 83, 83,
    62, 62, 69, 69, 68, 68, 72, 72, 53, 53, 61, 61, 59, 59, 67, 67,
    28, 28, 36, 36, 34, 34, 42, 42, 23, 23, 27, 27, 26, 26, 33, 33,
    12, 12, 18, 18, 17, 17, 22, 22,  7,  7, 11, 11, 10, 10, 16, 16,
    51, 51, 60, 60, 56, 56, 65, 65, 43, 43, 50, 50, 48, 48, 55, 55,
    28, 28, 36, 36, 34, 34, 42, 42, 23, 23, 27, 27, 26, 26, 33, 33,
    15, 15, 21, 21, 20, 20, 24, 24,  9,  9, 14, 14, 13, 13, 19, 19,
     3,  3,  6,  6,  5,  5,  8,  8,  0,  0,  2,  2,  1,  1,  4,  4,
    32, 32, 41, 41, 38, 38, 46, 46, 25, 25, 31, 31, 29, 29, 37, 37,
    15, 15, 21, 21, 20, 20, 24, 24,  9,  9, 14, 14, 13, 13, 19, 19,
];

/// Class representatives - the first byte in each equivalence class
/// This is used for decoding to find a representative byte for each class
pub const CLASS_REPRESENTATIVES: [u8; 96] = generate_class_representatives();

/// Generate class representatives at compile time
const fn generate_class_representatives() -> [u8; 96] {
    let mut representatives = [255u8; 96];
    let mut i = 0;
    
    // Find the first byte for each class
    while i < 256 {
        let class = RESONANCE_CLASS_MAP[i];
        if representatives[class as usize] == 255 {
            representatives[class as usize] = i as u8;
        }
        i += 1;
    }
    
    representatives
}

/// Get the resonance class for a byte
#[inline]
pub const fn byte_to_resonance_class(byte: u8) -> u8 {
    RESONANCE_CLASS_MAP[byte as usize]
}

/// Get the resonance value for a byte
#[inline]
pub const fn get_resonance(byte: u8) -> f64 {
    RESONANCE_TABLE[byte as usize]
}

/// Get a representative byte for a resonance class
#[inline]
pub const fn class_to_representative(class: u8) -> u8 {
    CLASS_REPRESENTATIVES[class as usize]
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    
    #[test]
    fn test_unity_resonance() {
        // Unity bytes should have resonance = 1.0
        for &byte in &[0, 1, 48, 49] {
            let resonance = get_resonance(byte);
            assert!((resonance - 1.0).abs() < 1e-10, 
                    "Byte {} should have unity resonance, got {}", byte, resonance);
        }
    }
    
    #[test]
    fn test_resonance_calculation() {
        // Test specific known values
        assert_eq!(get_resonance(0), 1.0); // No bits set
        
        // Byte 1 = 0b00000001, only bit 0 set
        assert_eq!(get_resonance(1), FIELD_CONSTANTS[0]);
        
        // Byte 2 = 0b00000010, only bit 1 set
        assert_eq!(get_resonance(2), FIELD_CONSTANTS[1]);
        
        // Byte 3 = 0b00000011, bits 0 and 1 set
        assert_eq!(get_resonance(3), FIELD_CONSTANTS[0] * FIELD_CONSTANTS[1]);
    }
    
    #[test]
    fn test_resonance_class_count() {
        // Count unique resonance classes
        let mut unique_classes = HashSet::new();
        for i in 0..256 {
            unique_classes.insert(byte_to_resonance_class(i as u8));
        }
        
        assert_eq!(unique_classes.len(), 96, 
                "Should have exactly 96 resonance classes, got {}", unique_classes.len());
    }
    
    #[test]
    fn test_unity_bytes_same_class() {
        // All unity bytes should map to the same resonance class
        let unity_class = byte_to_resonance_class(0);
        assert_eq!(byte_to_resonance_class(1), unity_class);
        assert_eq!(byte_to_resonance_class(48), unity_class);
        assert_eq!(byte_to_resonance_class(49), unity_class);
    }
    
    #[test]
    fn test_xor_equivalence() {
        // Test that bytes where bits 4 and 5 have the same value (both 0 or both 1)
        // form equivalence classes under XOR {1, 48, 49}
        for base in 0u8..=255 {
            let bit4 = (base >> 4) & 1;
            let bit5 = (base >> 5) & 1;
            
            // Only test bytes where bits 4 and 5 have same value
            if bit4 == bit5 {
                let base_class = byte_to_resonance_class(base);
                
                // These should all have the same class
                let xor1_class = byte_to_resonance_class(base ^ 1);
                let xor48_class = byte_to_resonance_class(base ^ 48);
                let xor49_class = byte_to_resonance_class(base ^ 49);
                
                assert_eq!(base_class, xor1_class, 
                        "Byte {} and {} should have same class", base, base ^ 1);
                assert_eq!(base_class, xor48_class, 
                        "Byte {} and {} should have same class", base, base ^ 48);
                assert_eq!(base_class, xor49_class, 
                        "Byte {} and {} should have same class", base, base ^ 49);
            }
        }
    }
    
    #[test]
    fn test_class_representatives() {
        // Verify all representatives are valid
        for class in 0..96 {
            let rep = class_to_representative(class);
            assert_eq!(byte_to_resonance_class(rep), class,
                    "Representative {} for class {} maps to wrong class", rep, class);
        }
    }
    
    #[test]
    fn test_field_constant_relationships() {
        // Verify α₄ × α₅ = 1
        let unity = FIELD_CONSTANTS[4] * FIELD_CONSTANTS[5];
        assert!((unity - 1.0).abs() < 1e-10, 
                "α₄ × α₅ should equal 1.0, got {}", unity);
        
        // Verify α₃ × α₅ = π
        let pi = FIELD_CONSTANTS[3] * FIELD_CONSTANTS[5];
        assert!((pi - std::f64::consts::PI).abs() < 1e-10,
                "α₃ × α₅ should equal π, got {}", pi);
    }
}