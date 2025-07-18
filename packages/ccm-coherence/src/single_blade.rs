//! Single blade storage for BJC optimization
//!
//! BJC (Bijective Junction Codec) only needs to store one basis blade at a time,
//! making the full Clifford algebra storage wasteful. This module provides
//! an optimized storage type for single blade operations.

use crate::arbitrary_support::BigIndex;
use ccm_core::{CcmError, Float};
use num_complex::Complex;
use num_traits::{One, Zero};

/// A single blade element in a Clifford algebra
///
/// This represents a single basis element with a coefficient,
/// optimized for BJC operations where only one blade is active at a time.
#[derive(Debug, Clone, PartialEq)]
pub struct SingleBlade<P: Float> {
    /// The index of the basis blade (bit pattern)
    pub(crate) index: BigIndex,
    /// The coefficient of this blade
    coefficient: Complex<P>,
    /// The dimension of the underlying space
    dimension: usize,
}

impl<P: Float> SingleBlade<P> {
    /// Create a new single blade
    pub fn new(index: BigIndex, coefficient: Complex<P>, dimension: usize) -> Self {
        Self {
            index,
            coefficient,
            dimension,
        }
    }

    /// Create a zero blade
    pub fn zero(dimension: usize) -> Self {
        Self {
            index: BigIndex::new(dimension),
            coefficient: Complex::zero(),
            dimension,
        }
    }

    /// Create a scalar blade
    pub fn scalar(value: P, dimension: usize) -> Self {
        Self {
            index: BigIndex::new(dimension), // All bits zero = scalar
            coefficient: Complex::new(value, P::zero()),
            dimension,
        }
    }

    /// Create from a bit pattern (for dimensions <= 64)
    pub fn from_bitword(bitword: usize, dimension: usize) -> Result<Self, CcmError> {
        if dimension > 64 {
            return Err(CcmError::Custom("Dimension too large for bitword conversion"));
        }

        let index = BigIndex::from_usize(bitword, dimension);
        Ok(Self {
            index,
            coefficient: Complex::one(),
            dimension,
        })
    }

    /// Get the grade of this blade
    pub fn grade(&self) -> usize {
        self.index.count_ones()
    }

    /// Get the dimension
    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// Get the coefficient
    pub fn coefficient(&self) -> Complex<P> {
        self.coefficient
    }
    
    /// Get the index
    pub fn index(&self) -> &BigIndex {
        &self.index
    }

    /// Set the coefficient
    pub fn set_coefficient(&mut self, coefficient: Complex<P>) {
        self.coefficient = coefficient;
    }

    /// Scale by a real scalar
    pub fn scale(&mut self, scalar: P) {
        self.coefficient = self.coefficient.scale(scalar);
    }

    /// Scale by a complex scalar
    pub fn scale_complex(&mut self, scalar: Complex<P>) {
        self.coefficient = self.coefficient * scalar;
    }

    /// Check if this blade is zero
    pub fn is_zero(&self) -> bool {
        self.coefficient.norm_sqr() < P::epsilon()
    }

    /// Compute the coherence norm of this single blade
    pub fn coherence_norm(&self) -> P {
        // For a single blade, the coherence norm is just the magnitude
        self.coefficient.norm()
    }

    /// Convert to a sparse representation index/value pair
    pub fn to_sparse_pair(&self) -> Result<(usize, Complex<P>), CcmError> {
        match self.index.to_usize() {
            Some(idx) => Ok((idx, self.coefficient)),
            None => Err(CcmError::Custom("Dimension too large for usize conversion")),
        }
    }

    /// Multiply two single blades
    pub fn multiply(&self, other: &Self) -> Result<Self, CcmError> {
        if self.dimension != other.dimension {
            return Err(CcmError::InvalidInput);
        }

        // XOR indices to get result blade
        let result_index = self.index.xor(&other.index);

        // Compute sign from reordering
        let sign = self.compute_multiplication_sign(&other.index)?;

        // Multiply coefficients with sign
        let result_coefficient = self.coefficient * other.coefficient * Complex::new(sign, P::zero());

        Ok(Self::new(result_index, result_coefficient, self.dimension))
    }

    /// Compute the sign from reordering basis elements in multiplication
    fn compute_multiplication_sign(&self, other_index: &BigIndex) -> Result<P, CcmError> {
        // For small dimensions, use exact computation
        if let (Some(idx1), Some(idx2)) = (self.index.to_usize(), other_index.to_usize()) {
            let sign = crate::arbitrary_support::ArbitraryCliffordAlgebra::<P>::compute_sign(idx1, idx2);
            Ok(sign)
        } else {
            // For large dimensions, we would need a BigInt-based sign computation
            // For now, return 1.0 as a default
            Ok(P::one())
        }
    }

    /// Apply resonance scaling for BJC
    pub fn apply_resonance(&mut self, resonance_value: P) {
        self.scale(resonance_value);
    }
}

/// Lazy evaluation wrapper for single blade operations
pub struct LazySingleBlade<P: Float> {
    /// Function to compute the blade when needed
    compute_fn: Box<dyn Fn() -> SingleBlade<P>>,
    /// Cached result
    cached: Option<SingleBlade<P>>,
}

impl<P: Float> LazySingleBlade<P> {
    /// Create a new lazy single blade
    pub fn new<F>(compute_fn: F) -> Self
    where
        F: Fn() -> SingleBlade<P> + 'static,
    {
        Self {
            compute_fn: Box::new(compute_fn),
            cached: None,
        }
    }

    /// Get the blade, computing if necessary
    pub fn get(&mut self) -> &SingleBlade<P> {
        if self.cached.is_none() {
            self.cached = Some((self.compute_fn)());
        }
        self.cached.as_ref().unwrap()
    }

    /// Force computation and return owned blade
    pub fn compute(self) -> SingleBlade<P> {
        if let Some(blade) = self.cached {
            blade
        } else {
            (self.compute_fn)()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_blade_creation() {
        let blade = SingleBlade::<f64>::scalar(2.5, 8);
        assert_eq!(blade.dimension(), 8);
        assert_eq!(blade.grade(), 0);
        assert_eq!(blade.coefficient(), Complex::new(2.5, 0.0));
    }

    #[test]
    fn test_from_bitword() {
        // Create e1 (bit pattern 0b01)
        let e1 = SingleBlade::<f64>::from_bitword(0b01, 8).unwrap();
        assert_eq!(e1.grade(), 1);

        // Create e1 ^ e2 (bit pattern 0b11)
        let e12 = SingleBlade::<f64>::from_bitword(0b11, 8).unwrap();
        assert_eq!(e12.grade(), 2);

        // Create e1 ^ e2 ^ e3 (bit pattern 0b111)
        let e123 = SingleBlade::<f64>::from_bitword(0b111, 8).unwrap();
        assert_eq!(e123.grade(), 3);
    }

    #[test]
    fn test_multiplication() {
        // e1 * e2 = e12
        let e1 = SingleBlade::<f64>::from_bitword(0b01, 8).unwrap();
        let e2 = SingleBlade::<f64>::from_bitword(0b10, 8).unwrap();
        let e12 = e1.multiply(&e2).unwrap();

        assert_eq!(e12.grade(), 2);
        // Verify the index is correct (0b01 XOR 0b10 = 0b11)
        let (idx, _) = e12.to_sparse_pair().unwrap();
        assert_eq!(idx, 0b11);
    }

    #[test]
    fn test_lazy_evaluation() {
        let mut lazy = LazySingleBlade::new(|| {
            SingleBlade::<f64>::from_bitword(0b101, 8).unwrap()
        });

        let blade = lazy.get();
        assert_eq!(blade.grade(), 2); // Two bits set
    }
    
    #[test]
    fn test_coherence_norm() {
        // Test scalar blade
        let scalar = SingleBlade::<f64>::scalar(3.0, 8);
        assert_eq!(scalar.coherence_norm(), 3.0);
        
        // Test basis blade with coefficient
        let mut blade = SingleBlade::<f64>::from_bitword(0b1010, 8).unwrap();
        blade.set_coefficient(Complex::new(4.0, 3.0));
        assert_eq!(blade.coherence_norm(), 5.0); // sqrt(4^2 + 3^2) = 5
        
        // Test zero blade
        let zero = SingleBlade::<f64>::zero(8);
        assert_eq!(zero.coherence_norm(), 0.0);
    }
    
    #[test]
    fn test_coherence_norm_large_dimension() {
        // Test with 4096-bit dimension
        let dimension = 4096;
        let mut index = BigIndex::new(dimension);
        index.set_bit(1000);
        index.set_bit(2000);
        index.set_bit(3000);
        
        let blade = SingleBlade::<f64>::new(
            index,
            Complex::new(6.0, 8.0),
            dimension
        );
        
        assert_eq!(blade.coherence_norm(), 10.0); // sqrt(6^2 + 8^2) = 10
        assert_eq!(blade.dimension(), 4096);
        assert_eq!(blade.grade(), 3);
    }
}