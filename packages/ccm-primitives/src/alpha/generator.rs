//! Dynamic alpha value generation based on input characteristics
//!
//! Instead of hard-coded constants, alpha values are calculated as a pure
//! function of the input parameters (primarily bit length).

use crate::{AlphaVec, Float, AlphaError};
use num_traits::FromPrimitive;

/// Configuration for alpha generation
#[derive(Debug, Clone, Copy)]
pub struct AlphaConfig {
    /// Number of bits in the input
    pub bit_length: usize,
    /// Number of alpha values to generate (default: 8)
    pub alpha_count: usize,
    /// Which positions should satisfy unity constraint (default: (4,5))
    pub unity_pair: (usize, usize),
}

impl Default for AlphaConfig {
    fn default() -> Self {
        Self {
            bit_length: 8,
            alpha_count: 8,
            unity_pair: (4, 5),
        }
    }
}

impl AlphaConfig {
    /// Create config for N-bit input
    pub fn for_bits(n: usize) -> Self {
        Self {
            bit_length: n,
            ..Default::default()
        }
    }
}

/// Generate alpha values dynamically based on configuration
pub fn generate_alpha<P: Float + FromPrimitive>(config: AlphaConfig) -> Result<AlphaVec<P>, AlphaError> {
    let n = config.bit_length;
    let count = config.alpha_count;
    
    // Ensure we have enough alphas
    if count < 3 {
        return Err(AlphaError::InvalidLength(count));
    }
    
    let mut alphas = Vec::with_capacity(count);
    
    for i in 0..count {
        let alpha = calculate_alpha_at_position::<P>(i, n, count)?;
        alphas.push(alpha);
    }
    
    // Apply unity constraint
    let (u1, u2) = config.unity_pair;
    if u1 < count && u2 < count && u1 != u2 {
        apply_unity_constraint(&mut alphas, u1, u2);
    }
    
    AlphaVec::new(alphas.into_boxed_slice())
}

/// Calculate a single alpha value based on position and parameters
fn calculate_alpha_at_position<P: Float + FromPrimitive>(
    index: usize,
    bit_length: usize,
    total_count: usize,
) -> Result<P, AlphaError> {
    // Special cases
    if index == 0 {
        return Ok(P::one()); // α₀ = 1 (multiplicative identity)
    }
    
    // According to CCM, the number of unique resonances = 3 × 2^(n-2)
    // This means we need alpha values that create sufficient discrimination
    // while maintaining numerical stability across all bit lengths
    
    // For orders of magnitude scaling (8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096):
    // We use a logarithmic scaling approach that respects power-of-2 boundaries
    
    // Determine the "order" of the bit length (which power of 2 range it falls into)
    let order = (bit_length as f64).log2();
    
    // For each order of magnitude, we need different scaling behavior
    // The key insight is that alpha values should scale with the information content
    // not with the raw bit count
    
    // Position in [0, 1] range
    let position = index as f64 / (total_count - 1) as f64;
    
    // Use a stable mathematical formula based on order
    // This creates a logarithmic distribution of alpha values
    let alpha_f64 = if index <= total_count / 2 {
        // Lower half: values between 0 and 1
        // Use exponential decay based on position and order
        let decay_rate = 1.0 + order / 4.0;
        (1.0 - position).powf(decay_rate)
    } else {
        // Upper half: values greater than 1
        // Use exponential growth based on position and order
        let growth_rate = 1.0 + order / 4.0;
        let adjusted_position = (position - 0.5) * 2.0;
        1.0 + adjusted_position.powf(1.0 / growth_rate) * (1.0 + order)
    };
    
    // Apply mathematical shaping based on index patterns
    let shaped_value = match index {
        1 => {
            // Second position often uses mathematical constants
            if bit_length <= 8 {
                1.839286755  // Tribonacci constant
            } else {
                std::f64::consts::E.powf(position)
            }
        },
        2 => {
            // Third position often uses golden ratio or related
            if bit_length <= 8 {
                1.618033989  // Golden ratio
            } else {
                std::f64::consts::PI.powf(position * 0.5)
            }
        },
        i if i == total_count / 2 => {
            // Middle position uses balanced value
            (1.0 + order).sqrt()
        },
        _ => alpha_f64
    };
    
    // Ensure strictly positive
    if shaped_value <= 0.0 {
        return Err(AlphaError::NonPositiveValue(index));
    }
    
    P::from_f64(shaped_value).ok_or(AlphaError::NonPositiveValue(index))
}


/// Apply unity constraint to ensure α[u1] × α[u2] = 1
fn apply_unity_constraint<P: Float>(alphas: &mut [P], u1: usize, u2: usize) {
    if u1 >= alphas.len() || u2 >= alphas.len() {
        return;
    }
    
    let product = alphas[u1] * alphas[u2];
    if product > P::zero() {
        // Adjust the second value to satisfy constraint
        alphas[u2] = P::one() / alphas[u1];
    }
}

/// Generate alpha values using mathematical constants for specific bit lengths
/// This provides an alternative to pure calculation when specific properties are desired
pub fn generate_mathematical_alpha<P: Float + FromPrimitive>(bit_length: usize) -> Result<AlphaVec<P>, AlphaError> {
    // Use well-known mathematical constants scaled by bit length
    let scale = (bit_length as f64).ln();
    
    let constants = [
        1.0,                    // Identity
        1.839286755,            // Tribonacci
        1.618033989,            // Golden ratio
        0.5_f64.powf(scale),    // Scaled binary
        1.0 / std::f64::consts::PI, // Will be adjusted for unity
        std::f64::consts::PI,   // Unity pair with above
        scale.exp() / 10.0,     // Exponential scaling
        10.0 / scale.exp(),     // Inverse exponential
    ];
    
    let mut alphas = Vec::with_capacity(8);
    for (i, &c) in constants.iter().enumerate() {
        alphas.push(P::from_f64(c).ok_or(AlphaError::NonPositiveValue(i))?);
    }
    
    // Apply unity constraint to positions 4,5
    apply_unity_constraint(&mut alphas, 4, 5);
    
    AlphaVec::new(alphas.into_boxed_slice())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_dynamic_generation() {
        // Test for different bit lengths
        for n in [3, 8, 16, 32, 64] {
            let config = AlphaConfig::for_bits(n);
            let alpha = generate_alpha::<f64>(config).unwrap();
            
            println!("Bit length {}: {:?}", n, alpha.values);
            
            // Verify constraints
            assert_eq!(alpha.len(), 8);
            assert_eq!(alpha[0], 1.0); // Identity
            
            // Check unity constraint
            let product = alpha[4] * alpha[5];
            assert!((product - 1.0).abs() < 1e-10);
        }
    }
    
    #[test]
    fn test_mathematical_generation() {
        for n in [4, 8, 16] {
            let alpha = generate_mathematical_alpha::<f64>(n).unwrap();
            println!("Mathematical alphas for {} bits: {:?}", n, alpha.values);
            
            // Verify unity constraint
            let product = alpha[4] * alpha[5];
            assert!((product - 1.0).abs() < 1e-10);
        }
    }
    
    #[test]
    fn test_alpha_scaling() {
        // Verify that alpha ranges scale with bit length
        let alpha_8 = generate_alpha::<f64>(AlphaConfig::for_bits(8)).unwrap();
        let alpha_32 = generate_alpha::<f64>(AlphaConfig::for_bits(32)).unwrap();
        
        // Calculate ranges
        let range_8 = alpha_8.values.iter().fold(0.0f64, |acc, &v| acc.max(v)) 
                    / alpha_8.values.iter().fold(f64::MAX, |acc, &v| acc.min(v));
        let range_32 = alpha_32.values.iter().fold(0.0f64, |acc, &v| acc.max(v)) 
                     / alpha_32.values.iter().fold(f64::MAX, |acc, &v| acc.min(v));
        
        println!("Range for 8 bits: {}", range_8);
        println!("Range for 32 bits: {}", range_32);
        
        // Larger bit lengths should have wider ranges
        assert!(range_32 > range_8);
    }
}