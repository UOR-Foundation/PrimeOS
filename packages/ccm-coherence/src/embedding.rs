//! Embedding operations for mapping between bit patterns and Clifford elements

use crate::{CliffordAlgebra, CliffordElement};
use crate::unified::{CliffordAlgebraTrait, CliffordAlgebraFactory};
use ccm_core::{BitWord, CcmError, Float};
use num_complex::Complex;
use num_traits::One;

/// Map a BitWord to a CliffordElement
///
/// The mapping is based on the bit pattern:
/// - Each bit position i corresponds to basis vector e_i
/// - A BitWord with bits set at positions {i, j, k} maps to basis blade e_i ∧ e_j ∧ e_k
pub fn bitword_to_clifford<P: Float>(
    word: &BitWord,
    algebra: &CliffordAlgebra<P>,
) -> Result<CliffordElement<P>, CcmError> {
    if word.len() > algebra.dimension() {
        return Err(CcmError::InvalidInput);
    }

    // Convert BitWord to basis element index
    let mut pattern = 0usize;
    for i in 0..word.len() {
        if word.bit(i) {
            pattern |= 1 << i;
        }
    }

    // Create Clifford element with this basis blade
    let mut element = CliffordElement::zero(algebra.dimension());
    element.components[pattern] = Complex::one();

    Ok(element)
}

/// Map a BitWord to a CliffordElement using the trait interface
///
/// This version works with any CliffordAlgebraTrait implementation
pub fn bitword_to_clifford_trait<P: Float>(
    word: &BitWord,
    algebra: &dyn CliffordAlgebraTrait<P>,
) -> Result<CliffordElement<P>, CcmError> {
    if word.len() > algebra.dimension() {
        return Err(CcmError::InvalidInput);
    }

    // Convert BitWord to basis element index
    let mut pattern = 0usize;
    for i in 0..word.len() {
        if word.bit(i) {
            pattern |= 1 << i;
        }
    }

    // Use the trait method to get basis element
    algebra.basis_element(pattern)
}

/// Map a u8 byte to a CliffordElement  
pub fn u8_to_clifford<P: Float>(
    byte: u8,
    algebra: &CliffordAlgebra<P>,
) -> Result<CliffordElement<P>, CcmError> {
    if algebra.dimension() < 8 {
        return Err(CcmError::InvalidInput);
    }

    let mut element = CliffordElement::zero(algebra.dimension());
    element.components[byte as usize] = Complex::one();

    Ok(element)
}

/// Map a u8 byte to a CliffordElement using the trait interface
pub fn u8_to_clifford_trait<P: Float>(
    byte: u8,
    algebra: &dyn CliffordAlgebraTrait<P>,
) -> Result<CliffordElement<P>, CcmError> {
    if algebra.dimension() < 8 {
        return Err(CcmError::InvalidInput);
    }

    algebra.basis_element(byte as usize)
}

/// Map resonance value to coefficient magnitude
/// This scales the Clifford element by the resonance value
pub fn apply_resonance<P: Float>(element: &mut CliffordElement<P>, resonance: P) {
    for i in 0..element.components.len() {
        element.components[i] = element.components[i].scale(resonance);
    }
}

/// Create a Clifford element from bit pattern with given resonance
pub fn embed_with_resonance<P: Float>(
    word: &BitWord,
    resonance: P,
    algebra: &CliffordAlgebra<P>,
) -> Result<CliffordElement<P>, CcmError> {
    let mut element = bitword_to_clifford(word, algebra)?;
    apply_resonance(&mut element, resonance);
    Ok(element)
}

/// Extract the dominant bit pattern from a Clifford element
/// Returns the basis blade with largest coefficient magnitude
pub fn extract_dominant_pattern<P: Float>(element: &CliffordElement<P>) -> (usize, Complex<P>) {
    let mut max_idx = 0;
    let mut max_val = element.components[0];
    let mut max_norm = max_val.norm_sqr();

    for i in 1..element.components.len() {
        let norm = element.components[i].norm_sqr();
        if norm > max_norm {
            max_idx = i;
            max_val = element.components[i];
            max_norm = norm;
        }
    }

    (max_idx, max_val)
}

/// Convert a basis index back to a BitWord
pub fn index_to_bitword(index: usize, dimension: usize) -> BitWord {
    let mut word = BitWord::new(dimension);

    for i in 0..dimension {
        if (index >> i) & 1 == 1 {
            word.set_bit(i, true);
        }
    }

    word
}

/// Optimized embedding for BJC codec usage
///
/// For large dimensions, this creates a sparse single-blade element
/// without allocating the full 2^n components
pub fn embed_bitword_lazy<P: Float>(
    word: &BitWord,
    dimension: usize,
    resonance: P,
) -> Result<CliffordElement<P>, CcmError> {
    if word.len() > dimension {
        return Err(CcmError::InvalidInput);
    }
    
    // Use factory to get appropriate algebra for dimension
    let algebra = CliffordAlgebraFactory::create_for_bjc::<P>(dimension)?;
    
    // Convert BitWord to basis element index
    let mut pattern = 0usize;
    for i in 0..word.len() {
        if word.bit(i) {
            pattern |= 1 << i;
        }
    }
    
    // Get basis element (will be sparse for large dimensions)
    let mut element = algebra.basis_element(pattern)?;
    
    // Scale by resonance
    apply_resonance(&mut element, resonance);
    
    Ok(element)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_u8_to_clifford() {
        let algebra = CliffordAlgebra::<f64>::generate(8).unwrap();

        // Test mapping of specific bytes
        let elem0 = u8_to_clifford(0, &algebra).unwrap();
        assert_eq!(elem0.component(0), Some(Complex::one())); // scalar

        let elem1 = u8_to_clifford(1, &algebra).unwrap();
        assert_eq!(elem1.component(1), Some(Complex::one())); // e₀

        let elem255 = u8_to_clifford(255, &algebra).unwrap();
        assert_eq!(elem255.component(255), Some(Complex::one())); // e₀e₁...e₇
    }

    #[test]
    fn test_bitword_mapping() {
        let algebra = CliffordAlgebra::<f64>::generate(8).unwrap();

        // Create a BitWord with bits 0 and 2 set
        let mut word = BitWord::new(8);
        word.set_bit(0, true);
        word.set_bit(2, true);

        let elem = bitword_to_clifford(&word, &algebra).unwrap();

        // Should map to index 5 (binary 00000101)
        assert_eq!(elem.component(5), Some(Complex::one()));
    }

    #[test]
    fn test_resonance_application() {
        let algebra = CliffordAlgebra::<f64>::generate(8).unwrap();
        let mut elem = u8_to_clifford(42, &algebra).unwrap();

        apply_resonance(&mut elem, 2.5);

        assert_eq!(elem.component(42), Some(Complex::new(2.5, 0.0)));
    }

    #[test]
    fn test_extract_pattern() {
        let _algebra = CliffordAlgebra::<f64>::generate(8).unwrap();
        let mut elem = CliffordElement::zero(8);

        elem.set_component(10, Complex::new(1.0, 0.0)).unwrap();
        elem.set_component(20, Complex::new(2.0, 0.0)).unwrap();
        elem.set_component(30, Complex::new(0.5, 0.0)).unwrap();

        let (idx, val) = extract_dominant_pattern(&elem);
        assert_eq!(idx, 20);
        assert_eq!(val, Complex::new(2.0, 0.0));
    }

    #[test]
    fn test_roundtrip_conversion() {
        let dimension = 8;
        let test_index = 42usize;

        let word = index_to_bitword(test_index, dimension);

        // Verify the conversion
        let mut reconstructed = 0usize;
        for i in 0..dimension {
            if word.bit(i) {
                reconstructed |= 1 << i;
            }
        }

        assert_eq!(reconstructed, test_index);
    }
}
