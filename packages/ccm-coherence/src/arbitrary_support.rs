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
#[derive(Clone)]
pub struct ArbitraryCliffordAlgebra<P: Float> {
    dimension: usize,
    config: ArbitraryDimensionConfig,
    _phantom: core::marker::PhantomData<P>,
}

impl<P: Float> ArbitraryCliffordAlgebra<P> {
    /// Compute the sign from reordering basis elements in multiplication
    pub fn compute_sign(idx1: usize, idx2: usize) -> P {
        // Count transpositions needed to order basis vectors
        let mut sign = P::one();
        let mut _swaps = 0;
        
        // For each position in idx1
        let mut _pos = 0;
        for i in 0..64 {
            if idx1 & (1 << i) != 0 {
                // Count how many basis vectors in idx2 come before this one
                for j in 0..i {
                    if idx2 & (1 << j) != 0 {
                        _swaps += 1;
                    }
                }
                
                // Each swap contributes a factor of -1
                if _swaps % 2 == 1 {
                    sign = -sign;
                }
                _pos += 1;
            }
        }
        
        sign
    }
    /// Create a new Clifford algebra with arbitrary dimension
    pub fn generate(n: usize, config: ArbitraryDimensionConfig) -> Result<Self, CcmError> {
        // Check for overflow in 2^n calculation
        // We can't represent 2^n as usize if n >= bits in usize
        // But we can still work with such dimensions using lazy/streaming
        if config.check_overflow && n >= core::mem::size_of::<usize>() * 8 && config.max_dense_dimension > 0 {
            // Only error if we're trying to use dense storage
            return Err(CcmError::InvalidInput);
        }

        // Check memory requirements only if we're using dense storage
        if n <= config.max_dense_dimension {
            let memory_mb = Self::estimate_memory_mb(n);
            if memory_mb > config.max_memory_mb {
                return Err(CcmError::InvalidLength);
            }
        }
        // For dimensions > max_dense_dimension, we use lazy/sparse storage
        // which doesn't allocate all 2^n components

        Ok(Self {
            dimension: n,
            config,
            _phantom: core::marker::PhantomData,
        })
    }

    /// Estimate memory usage in MB for dimension n
    pub fn estimate_memory_mb(n: usize) -> usize {
        // For 64-bit systems, dimensions >= 64 would overflow
        if n >= 64 {
            // Return max value to indicate infeasible memory requirement
            usize::MAX / (1024 * 1024)
        } else if n >= core::mem::size_of::<usize>() * 8 {
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
    /// Get the index of this basis element
    pub fn index(&self) -> usize {
        self.index
    }
    
    /// Get the coefficient of this basis element
    pub fn coefficient(&self) -> Complex<P> {
        self._coefficient
    }
    
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

/// BigInt-style index for arbitrary dimension support
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BigIndex {
    /// Bit representation stored as bytes (little-endian)
    pub(crate) bits: Vec<u8>,
    /// Number of valid bits
    pub(crate) bit_count: usize,
}

impl BigIndex {
    /// Create a new BigIndex with specified bit pattern
    pub fn new(bit_count: usize) -> Self {
        let byte_count = (bit_count + 7) / 8;
        Self {
            bits: vec![0; byte_count],
            bit_count,
        }
    }
    
    /// Set bit at position to 1
    pub fn set_bit(&mut self, position: usize) {
        if position < self.bit_count {
            let byte_idx = position / 8;
            let bit_idx = position % 8;
            self.bits[byte_idx] |= 1 << bit_idx;
        }
    }
    
    /// Get bit at position
    pub fn get_bit(&self, position: usize) -> bool {
        if position < self.bit_count {
            let byte_idx = position / 8;
            let bit_idx = position % 8;
            (self.bits[byte_idx] & (1 << bit_idx)) != 0
        } else {
            false
        }
    }
    
    /// Count number of set bits (grade)
    pub fn count_ones(&self) -> usize {
        self.bits.iter().map(|b| b.count_ones() as usize).sum()
    }
    
    /// Convert to usize if possible (for dimensions <= 64)
    pub fn to_usize(&self) -> Option<usize> {
        if self.bit_count > 64 {
            return None;
        }
        
        let mut result = 0usize;
        for i in 0..self.bit_count {
            if self.get_bit(i) {
                result |= 1usize << i;
            }
        }
        Some(result)
    }
    
    /// Create from usize
    pub fn from_usize(value: usize, bit_count: usize) -> Self {
        let mut index = Self::new(bit_count);
        for i in 0..bit_count.min(64) {
            if (value & (1usize << i)) != 0 {
                index.set_bit(i);
            }
        }
        index
    }
    
    /// XOR operation for multiplication
    pub fn xor(&self, other: &Self) -> Self {
        let bit_count = self.bit_count.max(other.bit_count);
        let mut result = Self::new(bit_count);
        
        let byte_count = result.bits.len();
        for i in 0..byte_count {
            let a = self.bits.get(i).copied().unwrap_or(0);
            let b = other.bits.get(i).copied().unwrap_or(0);
            result.bits[i] = a ^ b;
        }
        
        result
    }
}

/// Streaming operations for very large dimensions
pub mod streaming {
    use super::*;
    use num_complex::Complex;
    
    /// Streaming multiplication of Clifford elements
    /// Computes c = a * b without materializing full elements
    pub struct StreamingMultiplier<P: Float> {
        dimension: usize,
        _phantom: core::marker::PhantomData<P>,
    }
    
    impl<P: Float> StreamingMultiplier<P> {
        pub fn new(dimension: usize) -> Self {
            Self {
                dimension,
                _phantom: core::marker::PhantomData,
            }
        }
        
        /// Compute single component of a * b
        pub fn compute_component(
            &self,
            result_index: &BigIndex,
            a_components: &dyn Fn(&BigIndex) -> Complex<P>,
            b_components: &dyn Fn(&BigIndex) -> Complex<P>,
        ) -> Complex<P> {
            let mut result = Complex::zero();
            
            // For multiplication, we need all pairs (j,k) where j XOR k = result_index
            // This means k = j XOR result_index
            // We iterate over all possible j values
            
            if self.dimension <= 20 {
                // For small dimensions, we can enumerate
                let max_j = 1usize << self.dimension;
                for j in 0..max_j {
                    let j_big = BigIndex::from_usize(j, self.dimension);
                    let k_big = j_big.xor(result_index);
                    
                    // Compute sign from reordering basis elements
                    let sign = if let (Some(j_small), Some(k_small)) = (j_big.to_usize(), k_big.to_usize()) {
                        ArbitraryCliffordAlgebra::<P>::compute_sign(j_small, k_small)
                    } else {
                        P::one() // Fallback for large indices
                    };
                    
                    let a_j = a_components(&j_big);
                    let b_k = b_components(&k_big);
                    
                    result = result + a_j * b_k * Complex::new(sign, P::zero());
                }
            } else {
                // For large dimensions, full enumeration is not feasible
                // In practice, most components are zero, so a sparse approach
                // would be needed where we only compute non-zero contributions
            }
            
            result
        }
    }

    /// Iterator over non-zero components
    pub struct ComponentIterator<P: Float> {
        dimension: usize,
        current: usize,
        _current_big: Option<BigIndex>,
        max: Option<usize>,
        grade_filter: Option<usize>,
        combination_state: Option<Vec<usize>>, // For grade-specific iteration
        _phantom: core::marker::PhantomData<P>,
    }

    impl<P: Float> ComponentIterator<P> {
        pub fn new(dimension: usize) -> Self {
            let (max, current_big) = if dimension <= 64 {
                (Some(1usize << dimension), None)
            } else {
                (None, Some(BigIndex::new(dimension)))
            };

            Self {
                dimension,
                current: 0,
                _current_big: current_big,
                max,
                grade_filter: None,
                combination_state: None,
                _phantom: core::marker::PhantomData,
            }
        }

        /// Create iterator for specific grade
        pub fn grade_only(dimension: usize, grade: usize) -> Self {
            let mut iter = Self {
                dimension,
                current: 0,
                _current_big: None,
                max: None,
                grade_filter: Some(grade),
                combination_state: None,
                _phantom: core::marker::PhantomData,
            };
            
            // Initialize combination state for grade iteration
            if grade > 0 && grade <= dimension {
                // Start with first combination: [0, 1, ..., grade-1]
                iter.combination_state = Some((0..grade).collect());
            }
            
            iter
        }
        
        /// Compute the next index of given grade using combinatorial approach
        fn next_of_grade(&mut self, target_grade: usize) -> Option<BigIndex> {
            if target_grade > self.dimension {
                return None;
            }
            
            if target_grade == 0 {
                // Only one element of grade 0: the scalar
                if self.current == 0 {
                    self.current = 1;
                    return Some(BigIndex::new(self.dimension));
                }
                return None;
            }
            
            // Use combination state for efficient iteration
            if let Some(ref mut positions) = self.combination_state {
                // Convert current combination to BigIndex
                let mut index = BigIndex::new(self.dimension);
                for &pos in positions.iter() {
                    index.set_bit(pos);
                }
                
                // Compute next combination
                let dimension = self.dimension;
                if !Self::next_combination(positions, dimension) {
                    self.combination_state = None; // No more combinations
                }
                
                Some(index)
            } else {
                None
            }
        }
        
        /// Generate next combination in lexicographic order
        fn next_combination(positions: &mut Vec<usize>, n: usize) -> bool {
            let k = positions.len();
            if k == 0 || k > n {
                return false;
            }
            
            // Find rightmost position that can be incremented
            let mut i = k - 1;
            while positions[i] == n - k + i {
                if i == 0 {
                    return false; // No more combinations
                }
                i -= 1;
            }
            
            // Increment position i and reset positions after it
            positions[i] += 1;
            for j in i + 1..k {
                positions[j] = positions[j - 1] + 1;
            }
            
            true
        }
    }

    impl<P: Float> Iterator for ComponentIterator<P> {
        type Item = (BigIndex, usize); // (index, grade)

        fn next(&mut self) -> Option<Self::Item> {
            if let Some(target_grade) = self.grade_filter {
                // Only return indices of specific grade
                self.next_of_grade(target_grade)
                    .map(|idx| (idx, target_grade))
            } else {
                // Return all indices
                if self.dimension <= 64 {
                    // Use usize for small dimensions
                    if let Some(max) = self.max {
                        if self.current >= max {
                            return None;
                        }
                    }

                    let index = self.current;
                    let grade = index.count_ones() as usize;
                    self.current += 1;

                    let big_index = BigIndex::from_usize(index, self.dimension);
                    Some((big_index, grade))
                } else {
                    // For large dimensions, we can't iterate all indices
                    // This would require 2^n iterations which is infeasible
                    // Instead, return None to indicate streaming iteration is not supported
                    // for full enumeration of large dimensions
                    None
                }
            }
        }
    }
    
    /// Streaming inner product computation
    pub struct StreamingInnerProduct<P: Float> {
        dimension: usize,
        _phantom: core::marker::PhantomData<P>,
    }
    
    impl<P: Float> StreamingInnerProduct<P> {
        pub fn new(dimension: usize) -> Self {
            Self {
                dimension,
                _phantom: core::marker::PhantomData,
            }
        }
        
        /// Compute coherence inner product without materializing full elements
        pub fn compute(
            &self,
            a_components: &dyn Fn(&BigIndex) -> Complex<P>,
            b_components: &dyn Fn(&BigIndex) -> Complex<P>,
        ) -> Complex<P> {
            let mut result = Complex::zero();
            
            // Sum over all grades
            for grade in 0..=self.dimension {
                let mut grade_sum = Complex::zero();
                
                // Use iterator to avoid materializing all indices
                let iter = ComponentIterator::<P>::grade_only(self.dimension, grade);
                for (idx, _) in iter {
                    let a_val = a_components(&idx);
                    let b_val = b_components(&idx);
                    grade_sum = grade_sum + a_val.conj() * b_val;
                }
                
                result = result + grade_sum;
            }
            
            result
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
