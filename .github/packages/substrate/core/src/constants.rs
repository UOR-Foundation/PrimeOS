//! Field constants and system configuration for PrimeOS codec

/// Field constants that define the resonance calculations
/// CRITICAL: These exact values must be used for bijection to work
pub const FIELD_CONSTANTS: [f64; 8] = [
    1.0,                    // α₀: Identity
    1.8392867552141612,     // α₁: Tribonacci constant
    1.6180339887498950,     // α₂: Golden ratio (φ)
    0.5,                    // α₃: Half
    0.15915494309189535,    // α₄: 1/(2π)
    6.283185307179586,      // α₅: 2π
    0.199612,               // α₆: Phase constant (exact value)
    0.014134725,            // α₇: Quantum constant (exact value)
];

/// Mathematical space constants
pub const TOTAL_ELEMENTS: usize = 12_288;  // 3 × 4^6
pub const PAGE_SIZE: usize = 256;          // Elements per page
pub const NUM_PAGES: usize = 48;           // Total pages
pub const CYCLE_LENGTH: usize = 768;       // Resonance cycle
pub const RESONANCE_CLASSES: usize = 96;   // Unique resonance values

/// Unity positions form Klein four-group
/// Note: The spec shows both 4 and 12 positions - using the Klein group of 4
pub const UNITY_POSITIONS: [u8; 4] = [0, 1, 48, 49];

/// LCG constants for deterministic pattern generation
pub const LCG_MULTIPLIER: u64 = 1664525;
pub const LCG_INCREMENT: u64 = 1013904223;

/// Checksum modulus for digest validation (not in spec, using simple checksum)
pub const CHECKSUM_MODULUS: u64 = 65537;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mathematical_relationships() {
        // Verify α₄ × α₅ = 1.0 (exact unity)
        let unity_product = FIELD_CONSTANTS[4] * FIELD_CONSTANTS[5];
        assert!((unity_product - 1.0).abs() < 1e-10, 
                "α₄ × α₅ should equal 1.0, got {}", unity_product);

        // Verify α₃ × α₅ = π
        let pi_product = FIELD_CONSTANTS[3] * FIELD_CONSTANTS[5];
        assert!((pi_product - std::f64::consts::PI).abs() < 1e-10,
                "α₃ × α₅ should equal π, got {}", pi_product);

        // Verify α₃ / α₄ = π
        let pi_ratio = FIELD_CONSTANTS[3] / FIELD_CONSTANTS[4];
        assert!((pi_ratio - std::f64::consts::PI).abs() < 1e-10,
                "α₃ / α₄ should equal π, got {}", pi_ratio);
    }

    #[test]
    fn test_space_constants() {
        // Verify critical relationships
        assert_eq!(TOTAL_ELEMENTS, PAGE_SIZE * NUM_PAGES);
        assert_eq!(TOTAL_ELEMENTS, 3 * 4096);  // 3 × 4^6
        assert_eq!(CYCLE_LENGTH, 768);
        assert_eq!(NUM_PAGES, 48);
        assert_eq!(PAGE_SIZE, 256);
    }

    #[test]
    fn test_klein_group() {
        // Verify Klein four-group structure
        for &a in &UNITY_POSITIONS {
            for &b in &UNITY_POSITIONS {
                let result = a ^ b;
                assert!(UNITY_POSITIONS.contains(&result),
                        "{} XOR {} = {} should be in unity positions", a, b, result);
            }
        }
    }
}