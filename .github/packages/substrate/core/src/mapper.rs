//! Coordinate mapper for the PrimeOS codec
//! Maps bit patterns to coordinates in 12,288-element mathematical space

use crate::constants::*;
use crate::coordinate::Coordinate;
use lazy_static::lazy_static;

/// Maps bit patterns to coordinates in 12,288 space
#[derive(Debug, Clone)]
pub struct CoordinateMapper {
    /// Precomputed resonance values
    pub resonance_table: [f64; 256],
    
    /// Resonance to class index mapping
    pub resonance_classes: [u8; 256],
    
    /// Reverse mapping: class index to representative bytes
    pub class_representatives: Vec<Vec<u8>>,
}

impl CoordinateMapper {
    /// Create a new coordinate mapper with precomputed tables
    pub fn new() -> Self {
        // Initialize resonance table
        let mut resonance_table = [0.0; 256];
        let mut resonance_classes = [0u8; 256];
        
        // Compute resonances for all bytes
        for i in 0..256 {
            resonance_table[i] = Self::compute_resonance(i as u8);
        }
        
        // Create array of indices for sorting
        let mut indices: [u8; 256] = [0; 256];
        for i in 0..256 {
            indices[i] = i as u8;
        }
        
        // Sort indices by resonance value (bubble sort for const context compatibility)
        for i in 0..256 {
            for j in 0..255 - i {
                if resonance_table[indices[j] as usize] > resonance_table[indices[j + 1] as usize] {
                    indices.swap(j, j + 1);
                }
            }
        }
        
        // Assign resonance classes based on unique values
        let mut current_class = 0u8;
        let mut last_resonance = -1.0;
        
        for &idx in &indices {
            let resonance = resonance_table[idx as usize];
            
            // Check if this is a new unique resonance value
            if (resonance - last_resonance).abs() > 1e-10 {
                if last_resonance >= 0.0 {
                    current_class += 1;
                }
                last_resonance = resonance;
            }
            
            resonance_classes[idx as usize] = current_class;
        }
        
        // Build class representatives at runtime
        let num_classes = (current_class + 1) as usize;
        let mut class_representatives = vec![Vec::new(); num_classes];
        
        for byte in 0u8..=255 {
            let class = resonance_classes[byte as usize];
            class_representatives[class as usize].push(byte);
        }
        
        Self {
            resonance_table,
            resonance_classes,
            class_representatives,
        }
    }
    
    /// Compute resonance value for a byte
    const fn compute_resonance(byte: u8) -> f64 {
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
    
    /// Get all bytes that map to a given resonance class
    pub fn get_bytes_for_resonance_class(&self, class: u8) -> Vec<u8> {
        if (class as usize) < self.class_representatives.len() {
            self.class_representatives[class as usize].clone()
        } else {
            Vec::new()
        }
    }
    
    /// Get resonance class for a byte
    pub fn get_resonance_class(&self, byte: u8) -> u8 {
        self.resonance_classes[byte as usize]
    }
    
    /// Get resonance value for a byte
    pub fn get_resonance(&self, byte: u8) -> f64 {
        self.resonance_table[byte as usize]
    }
    
    /// Convert byte directly to coordinate
    pub fn byte_to_coordinate(&self, byte: u8) -> Coordinate {
        let resonance_class = self.resonance_classes[byte as usize];
        
        Coordinate {
            absolute: byte as u16,
            page: 0,
            position: byte,
            resonance_class,
        }
    }
    
    /// Get the number of unique resonance classes
    pub fn num_resonance_classes(&self) -> usize {
        self.class_representatives.len()
    }
    
    /// Check if the mapper has exactly 96 resonance classes as expected
    pub fn verify_resonance_count(&self) -> bool {
        self.num_resonance_classes() == RESONANCE_CLASSES
    }
}

/// Global instance of the coordinate mapper
lazy_static! {
    pub static ref COORDINATE_MAPPER: CoordinateMapper = CoordinateMapper::new();
}

impl Default for CoordinateMapper {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{HashMap, HashSet};

    #[test]
    fn test_resonance_table_initialization() {
        let mapper = CoordinateMapper::new();
        
        // Test some known values
        assert_eq!(mapper.get_resonance(0), 1.0); // No bits set
        
        // Test that all resonances are positive
        for byte in 0u8..=255 {
            assert!(mapper.get_resonance(byte) > 0.0);
        }
    }
    
    #[test]
    fn test_exactly_96_resonance_classes() {
        let mapper = CoordinateMapper::new();
        
        // Verify we have exactly 96 unique resonance classes
        assert_eq!(mapper.num_resonance_classes(), 96);
        assert!(mapper.verify_resonance_count());
        
        // Verify all bytes are assigned to valid classes
        for byte in 0u8..=255 {
            let class = mapper.get_resonance_class(byte);
            assert!(class < 96);
        }
    }
    
    #[test]
    fn test_xor_equivalence_preservation() {
        let mapper = CoordinateMapper::new();
        
        // From research: The unity positions {0, 1, 48, 49} have the same resonance
        // and form the Klein four-group under XOR
        let unity_positions = [0u8, 1, 48, 49];
        
        // Verify all unity positions have the same resonance
        let unity_resonances: Vec<f64> = unity_positions.iter()
            .map(|&b| mapper.get_resonance(b))
            .collect();
        
        for i in 1..unity_positions.len() {
            assert!((unity_resonances[0] - unity_resonances[i]).abs() < 1e-10,
                "Unity positions should have same resonance");
        }
        
        // Verify they're in the same resonance class
        let unity_classes: Vec<u8> = unity_positions.iter()
            .map(|&b| mapper.get_resonance_class(b))
            .collect();
        
        for i in 1..unity_positions.len() {
            assert_eq!(unity_classes[0], unity_classes[i],
                "Unity positions should be in same resonance class");
        }
        
        // Verify Klein group property: XOR of any two gives another in the group
        for &a in &unity_positions {
            for &b in &unity_positions {
                let result = a ^ b;
                assert!(unity_positions.contains(&result),
                    "{} XOR {} = {} should be in unity positions", a, b, result);
            }
        }
    }
    
    #[test]
    fn test_class_representatives_completeness() {
        let mapper = CoordinateMapper::new();
        
        // Collect all bytes from class representatives
        let mut all_bytes = HashSet::new();
        for class in 0..mapper.num_resonance_classes() {
            let bytes = mapper.get_bytes_for_resonance_class(class as u8);
            for byte in bytes {
                all_bytes.insert(byte);
            }
        }
        
        // Should have all 256 bytes
        assert_eq!(all_bytes.len(), 256);
        
        // Verify each byte is in exactly one class
        for byte in 0u8..=255 {
            let class = mapper.get_resonance_class(byte);
            let class_bytes = mapper.get_bytes_for_resonance_class(class);
            assert!(class_bytes.contains(&byte));
        }
    }
    
    #[test]
    fn test_resonance_class_sizes() {
        let mapper = CoordinateMapper::new();
        
        // Count the size distribution of resonance classes
        let mut size_counts = HashMap::new();
        
        for class in 0..mapper.num_resonance_classes() {
            let size = mapper.get_bytes_for_resonance_class(class as u8).len();
            *size_counts.entry(size).or_insert(0) += 1;
        }
        
        // From research: 64 classes of size 2, 32 classes of size 4
        println!("Resonance class size distribution: {:?}", size_counts);
        
        // Verify expected distribution
        assert_eq!(size_counts.get(&2).copied().unwrap_or(0), 64);
        assert_eq!(size_counts.get(&4).copied().unwrap_or(0), 32);
    }
    
    #[test]
    fn test_byte_to_coordinate() {
        let mapper = CoordinateMapper::new();
        
        // Test direct byte mapping
        for byte in [0u8, 1, 48, 49, 100, 255] {
            let coord = mapper.byte_to_coordinate(byte);
            
            assert_eq!(coord.absolute, byte as u16);
            assert_eq!(coord.page, 0);
            assert_eq!(coord.position, byte);
            assert_eq!(coord.resonance_class, mapper.get_resonance_class(byte));
            
            // Manual validation should match is_valid()
            // Note: position is u8, so it's always < 256
            let manual_valid = coord.absolute < TOTAL_ELEMENTS as u16 &&
                              coord.page < 48 &&
                              coord.resonance_class < 96;
            
            assert!(manual_valid, "Manual validation failed for byte {}: absolute={}, page={}, position={}, resonance_class={}",
                    byte, coord.absolute, coord.page, coord.position, coord.resonance_class);
            
            // Now test the actual is_valid() method
            assert!(coord.is_valid(), "coord.is_valid() failed for byte {}: absolute={}, page={}, position={}, resonance_class={}",
                    byte, coord.absolute, coord.page, coord.position, coord.resonance_class);
        }
    }
    
    #[test]
    fn test_unity_positions() {
        let mapper = CoordinateMapper::new();
        
        // Unity positions should all have the same resonance class
        let unity_bytes = [0u8, 1, 48, 49];
        let unity_classes: Vec<u8> = unity_bytes.iter()
            .map(|&b| mapper.get_resonance_class(b))
            .collect();
        
        // All should be the same class
        assert!(unity_classes.windows(2).all(|w| w[0] == w[1]),
            "Unity positions should have same resonance class");
    }
    
    #[test]
    fn test_field_constant_relationships() {
        // Verify critical field constant relationships
        let product_4_5 = FIELD_CONSTANTS[4] * FIELD_CONSTANTS[5];
        assert!((product_4_5 - 1.0).abs() < 1e-10, "α₄ × α₅ should equal 1.0");
        
        let product_3_5 = FIELD_CONSTANTS[3] * FIELD_CONSTANTS[5];
        assert!((product_3_5 - std::f64::consts::PI).abs() < 1e-10, "α₃ × α₅ should equal π");
    }
    
    #[test]
    fn test_determinism() {
        // Create multiple instances and verify they produce identical mappings
        let mapper1 = CoordinateMapper::new();
        let mapper2 = CoordinateMapper::new();
        
        // Check resonance tables match
        for byte in 0u8..=255 {
            assert_eq!(mapper1.get_resonance(byte), mapper2.get_resonance(byte));
            assert_eq!(mapper1.get_resonance_class(byte), mapper2.get_resonance_class(byte));
        }
        
        // Check class representatives match
        for class in 0..96u8 {
            let bytes1 = mapper1.get_bytes_for_resonance_class(class);
            let bytes2 = mapper2.get_bytes_for_resonance_class(class);
            assert_eq!(bytes1, bytes2);
        }
    }
}