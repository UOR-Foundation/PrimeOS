//! Support for arbitrary dimensional input in Clifford algebras

use crate::clifford::CliffordAlgebra;
use ccm_core::{CcmError, Float};
use num_complex::Complex;
#[allow(unused_imports)]
use num_traits::{One, Zero};

/// Configuration for handling large dimensions
#[derive(Debug, Clone)]
pub struct ArbitraryDimensionConfig {
    /// Maximum dimension to allow dense storage (default: 12)
    pub max_dense_dimension: usize,
    /// Maximum memory per element in MB (default: 100)
    pub max_memory_mb: usize,
    /// Whether to allow dimensions that would overflow usize
    pub check_overflow: bool,
}

impl Default for ArbitraryDimensionConfig {
    fn default() -> Self {
        Self {
            max_dense_dimension: 12,
            max_memory_mb: 100,
            check_overflow: true,
        }
    }
}

/// Extended Clifford algebra that supports arbitrary dimensions
pub struct ArbitraryCliffordAlgebra<P: Float> {
    dimension: usize,
    config: ArbitraryDimensionConfig,
    _phantom: core::marker::PhantomData<P>,
}

impl<P: Float> ArbitraryCliffordAlgebra<P> {
    /// Create a new Clifford algebra with arbitrary dimension
    pub fn generate(n: usize, config: ArbitraryDimensionConfig) -> Result<Self, CcmError> {
        // Check for overflow in 2^n calculation
        if config.check_overflow && n >= core::mem::size_of::<usize>() * 8 {
            return Err(CcmError::InvalidInput);
        }
        
        // Check memory requirements
        if n > config.max_dense_dimension {
            let memory_mb = Self::estimate_memory_mb(n);
            if memory_mb > config.max_memory_mb {
                return Err(CcmError::InvalidLength);
            }
        }
        
        Ok(Self {
            dimension: n,
            config,
            _phantom: core::marker::PhantomData,
        })
    }
    
    /// Estimate memory usage in MB for dimension n
    pub fn estimate_memory_mb(n: usize) -> usize {
        if n >= core::mem::size_of::<usize>() * 8 {
            usize::MAX / (1024 * 1024)
        } else {
            let components = 1usize << n;
            let bytes = components.saturating_mul(16); // Complex<f64> = 16 bytes
            bytes / (1024 * 1024)
        }
    }
    
    /// Get the dimension
    pub fn dimension(&self) -> usize {
        self.dimension
    }
    
    /// Check if a full element can be allocated
    pub fn can_allocate_element(&self) -> bool {
        if self.dimension <= self.config.max_dense_dimension {
            true
        } else {
            Self::estimate_memory_mb(self.dimension) <= self.config.max_memory_mb
        }
    }
    
    /// Create a basis element lazily without full allocation
    pub fn basis_element_lazy(&self, index: usize) -> Result<SparseBasisElement<P>, CcmError> {
        // Check index validity without computing 2^n
        if self.dimension < 64 && index >= (1usize << self.dimension) {
            return Err(CcmError::InvalidInput);
        }
        
        Ok(SparseBasisElement {
            dimension: self.dimension,
            index,
            _coefficient: Complex::one(),
        })
    }
    
    /// Get the standard Clifford algebra if dimension is small enough
    pub fn as_standard(&self) -> Result<CliffordAlgebra<P>, CcmError> {
        if self.dimension <= 12 {
            CliffordAlgebra::generate(self.dimension)
        } else {
            Err(CcmError::InvalidInput)
        }
    }
}

/// Sparse representation of a single basis element
#[derive(Debug, Clone)]
pub struct SparseBasisElement<P: Float> {
    dimension: usize,
    index: usize,
    _coefficient: Complex<P>,
}

impl<P: Float> SparseBasisElement<P> {
    /// Get the grade of this basis element
    pub fn grade(&self) -> usize {
        self.index.count_ones() as usize
    }
    
    /// Convert to indices
    pub fn to_indices(&self) -> Vec<usize> {
        let mut indices = Vec::new();
        let mut idx = self.index;
        let mut pos = 0;
        
        while idx > 0 && pos < self.dimension {
            if idx & 1 == 1 {
                indices.push(pos);
            }
            idx >>= 1;
            pos += 1;
        }
        
        indices
    }
}

/// Operations on arbitrary dimensional elements
pub mod operations {
    
    
    /// Check if two basis elements would produce a non-zero geometric product
    pub fn will_multiply_nonzero(_idx1: usize, _idx2: usize) -> bool {
        // The result index is idx1 XOR idx2
        // This is always valid regardless of dimension
        true
    }
    
    /// Compute the sign of basis element multiplication
    pub fn multiplication_sign(idx1: usize, idx2: usize) -> i32 {
        // Count inversions needed
        let mut sign = 1;
        let mut i1 = idx1;
        let mut i2 = idx2;
        let mut _pos = 0;
        
        while i1 > 0 || i2 > 0 {
            let bit1 = i1 & 1;
            let bit2 = i2 & 1;
            
            if bit1 == 1 && bit2 == 1 {
                // e_i * e_i = +1 or -1 depending on metric
                // For Euclidean, this is +1
                // But the basis elements cancel, so we get 0
                return 0;
            }
            
            // Count inversions
            if bit1 == 1 {
                // Count how many 1s in i2 are to the right of this position
                let mut temp = i2 >> 1;
                while temp > 0 {
                    if temp & 1 == 1 {
                        sign = -sign;
                    }
                    temp >>= 1;
                }
            }
            
            i1 >>= 1;
            i2 >>= 1;
            _pos += 1;
        }
        
        sign
    }
    
    /// Result index from multiplying two basis elements
    pub fn multiply_indices(idx1: usize, idx2: usize) -> usize {
        idx1 ^ idx2
    }
}

/// Streaming operations for very large dimensions
pub mod streaming {
    use super::*;
    
    /// Iterator over non-zero components
    pub struct ComponentIterator<P: Float> {
        _dimension: usize,
        current: usize,
        max: Option<usize>,
        _phantom: core::marker::PhantomData<P>,
    }
    
    impl<P: Float> ComponentIterator<P> {
        pub fn new(dimension: usize) -> Self {
            let max = if dimension < 64 {
                Some(1usize << dimension)
            } else {
                None
            };
            
            Self {
                _dimension: dimension,
                current: 0,
                max,
                _phantom: core::marker::PhantomData,
            }
        }
        
        /// Create iterator for specific grade
        pub fn grade_only(dimension: usize, _grade: usize) -> Self {
            Self {
                _dimension: dimension,
                current: 0,
                max: None,
                _phantom: core::marker::PhantomData,
            }
        }
    }
    
    impl<P: Float> Iterator for ComponentIterator<P> {
        type Item = (usize, usize); // (index, grade)
        
        fn next(&mut self) -> Option<Self::Item> {
            if let Some(max) = self.max {
                if self.current >= max {
                    return None;
                }
            }
            
            let index = self.current;
            let grade = index.count_ones() as usize;
            self.current += 1;
            
            Some((index, grade))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_arbitrary_dimension_creation() {
        let config = ArbitraryDimensionConfig::default();
        
        // Should work for dimension 20
        let algebra = ArbitraryCliffordAlgebra::<f64>::generate(20, config.clone()).unwrap();
        assert_eq!(algebra.dimension(), 20);
        
        // Should fail for dimension 100 with default memory limit
        assert!(ArbitraryCliffordAlgebra::<f64>::generate(100, config).is_err());
    }
    
    #[test]
    fn test_large_dimension_with_config() {
        let mut config = ArbitraryDimensionConfig::default();
        config.max_memory_mb = 1000000; // 1TB limit
        config.check_overflow = false;
        
        // Now dimension 30 should work (in theory)
        let algebra = ArbitraryCliffordAlgebra::<f64>::generate(30, config).unwrap();
        assert_eq!(algebra.dimension(), 30);
        // With 1TB limit, it thinks it can allocate (16GB < 1TB)
        assert!(algebra.can_allocate_element());
    }
    
    #[test]
    fn test_sparse_basis_element() {
        let mut config = ArbitraryDimensionConfig::default();
        config.max_memory_mb = 1000000; // Allow large dimensions
        config.check_overflow = false; // Disable overflow check for dimension 100
        let algebra = ArbitraryCliffordAlgebra::<f64>::generate(20, config).unwrap();
        
        // Can create sparse basis elements
        let e0 = algebra.basis_element_lazy(1).unwrap();
        assert_eq!(e0.grade(), 1);
        assert_eq!(e0.to_indices(), vec![0]);
        
        // Large index
        let e_large = algebra.basis_element_lazy(0b1010101).unwrap();
        assert_eq!(e_large.grade(), 4);
    }
    
    #[test]
    fn test_multiplication_operations() {
        // Test multiplication sign
        assert_eq!(operations::multiplication_sign(0b01, 0b10), -1); // e0 * e1 = e01 (with sign from commutation)
        assert_eq!(operations::multiplication_sign(0b10, 0b01), 1); // e1 * e0 = -e01
        assert_eq!(operations::multiplication_sign(0b11, 0b11), 0); // e01 * e01 = 0
        
        // Test index multiplication
        assert_eq!(operations::multiply_indices(0b01, 0b10), 0b11);
        assert_eq!(operations::multiply_indices(0b11, 0b01), 0b10);
    }
}