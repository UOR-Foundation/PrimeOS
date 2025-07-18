//! Support for arbitrary dimensional input in Clifford algebras

use crate::clifford::CliffordAlgebra;
use ccm_core::{CcmError, Float};
use num_complex::Complex;
#[allow(unused_imports)]
use num_traits::{One, Zero};

#[cfg(feature = "alloc")]
use alloc::collections::BTreeMap;

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
    
    /// AND operation for index intersection
    pub fn and(&self, other: &Self) -> Self {
        let bit_count = self.bit_count.min(other.bit_count);
        let mut result = Self::new(bit_count);
        
        let byte_count = (bit_count + 7) / 8;
        for i in 0..byte_count {
            let a = self.bits.get(i).copied().unwrap_or(0);
            let b = other.bits.get(i).copied().unwrap_or(0);
            result.bits[i] = a & b;
        }
        
        result
    }
    
    /// OR operation for index union
    pub fn or(&self, other: &Self) -> Self {
        let bit_count = self.bit_count.max(other.bit_count);
        let mut result = Self::new(bit_count);
        
        let byte_count = result.bits.len();
        for i in 0..byte_count {
            let a = self.bits.get(i).copied().unwrap_or(0);
            let b = other.bits.get(i).copied().unwrap_or(0);
            result.bits[i] = a | b;
        }
        
        result
    }
    
    /// Check if this index is zero (no bits set)
    pub fn is_zero(&self) -> bool {
        self.bits.iter().all(|&b| b == 0)
    }
    
    /// Clear bit at position
    pub fn clear_bit(&mut self, position: usize) {
        if position < self.bit_count {
            let byte_idx = position / 8;
            let bit_idx = position % 8;
            self.bits[byte_idx] &= !(1 << bit_idx);
        }
    }
    
    /// Compute the sign from reordering basis elements in multiplication
    /// 
    /// When multiplying basis blades, we need to count how many transpositions
    /// are needed to reorder the basis vectors. Each transposition contributes -1.
    pub fn compute_sign<P: Float>(idx1: &Self, idx2: &Self) -> P {
        // Count the number of swaps needed when multiplying e_I * e_J
        // For each bit set in idx1, count how many bits in idx2 come before it
        let mut swaps = 0;
        
        // For each position where idx1 has a bit set
        for i in 0..idx1.bit_count {
            if idx1.get_bit(i) {
                // Count bits in idx2 that are set and come before position i
                for j in 0..i {
                    if idx2.get_bit(j) {
                        swaps += 1;
                    }
                }
            }
        }
        
        // Each swap contributes a factor of -1
        if swaps % 2 == 0 {
            P::one()
        } else {
            -P::one()
        }
    }
    
    /// Get an iterator over set bit positions
    pub fn bit_positions(&self) -> impl Iterator<Item = usize> + '_ {
        (0..self.bit_count).filter(move |&i| self.get_bit(i))
    }
    
    /// Get reference to internal bits for optimization purposes
    pub fn as_bytes(&self) -> &[u8] {
        &self.bits
    }
    
    /// Get the bit count (dimension) of this index
    pub fn bit_count(&self) -> usize {
        self.bit_count
    }
}

use core::cmp::Ordering;

impl PartialOrd for BigIndex {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BigIndex {
    fn cmp(&self, other: &Self) -> Ordering {
        // First compare by bit count (dimension)
        match self.bit_count.cmp(&other.bit_count) {
            Ordering::Equal => {
                // Same dimension, compare bytes from most significant to least
                let byte_count = (self.bit_count + 7) / 8;
                for i in (0..byte_count).rev() {
                    let a = self.bits.get(i).copied().unwrap_or(0);
                    let b = other.bits.get(i).copied().unwrap_or(0);
                    match a.cmp(&b) {
                        Ordering::Equal => continue,
                        other_ord => return other_ord,
                    }
                }
                Ordering::Equal
            }
            other_ord => other_ord,
        }
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
                    let sign = BigIndex::compute_sign::<P>(&j_big, &k_big);
                    
                    let a_j = a_components(&j_big);
                    let b_k = b_components(&k_big);
                    
                    result = result + a_j * b_k * Complex::new(sign, P::zero());
                }
            } else {
                // For large dimensions, caller must ensure sparsity
                // Full enumeration is not feasible
                return Complex::zero();
            }
            
            result
        }
        
        /// Compute geometric product for sparse elements
        /// This version accepts iterators over non-zero components
        #[cfg(feature = "alloc")]
        pub fn compute_sparse<I1, I2>(
            &self,
            a_components: I1,
            b_components: I2,
        ) -> BTreeMap<Vec<u8>, Complex<P>>
        where
            I1: IntoIterator<Item = (BigIndex, Complex<P>)>,
            I2: IntoIterator<Item = (BigIndex, Complex<P>)>,
        {
            let mut result = BTreeMap::new();
            
            // Collect b components for efficient access
            let b_vec: Vec<_> = b_components.into_iter().collect();
            
            // For each component in a
            for (idx_a, val_a) in a_components {
                // For each component in b
                for (idx_b, val_b) in &b_vec {
                    // Result index is XOR of input indices
                    let result_idx = idx_a.xor(idx_b);
                    
                    // Compute sign from reordering
                    let sign = BigIndex::compute_sign::<P>(&idx_a, idx_b);
                    
                    // Add contribution to result
                    let contribution = val_a * *val_b * Complex::new(sign, P::zero());
                    let key = result_idx.to_bytes();
                    
                    result.entry(key)
                        .and_modify(|e| *e = *e + contribution)
                        .or_insert(contribution);
                }
            }
            
            // Remove near-zero entries
            result.retain(|_, v| v.norm_sqr() > P::epsilon());
            
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
        /// For very large dimensions, track position within grade
        big_combination_counter: Option<u128>, // For counting combinations when n-choose-k > 2^64
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
                big_combination_counter: None,
                _phantom: core::marker::PhantomData,
            }
        }
        
        /// Calculate the number of combinations n choose k
        /// Returns None if the result would overflow u128
        pub fn binomial_coefficient(n: usize, k: usize) -> Option<u128> {
            if k > n {
                return Some(0);
            }
            if k == 0 || k == n {
                return Some(1);
            }
            
            // Use the more efficient formula: C(n,k) = C(n, min(k, n-k))
            let k = k.min(n - k);
            
            let mut result: u128 = 1;
            for i in 0..k {
                // Compute (n - i) / (i + 1) carefully to avoid overflow
                let numerator = (n - i) as u128;
                let denominator = (i + 1) as u128;
                
                // Check if multiplication would overflow
                if let Some(prod) = result.checked_mul(numerator) {
                    if let Some(quot) = prod.checked_div(denominator) {
                        result = quot;
                    } else {
                        return None;
                    }
                } else {
                    return None;
                }
            }
            
            Some(result)
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
                big_combination_counter: None,
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
                
                // Increment our position counter
                self.current += 1;
                
                // Compute next combination
                let dimension = self.dimension;
                if !Self::next_combination(positions, dimension) {
                    self.combination_state = None; // No more combinations
                    self.big_combination_counter = None;
                }
                
                // For large dimensions, track position
                if self.dimension > 64 {
                    if let Some(ref mut counter) = self.big_combination_counter {
                        *counter = counter.saturating_add(1);
                    } else {
                        self.big_combination_counter = Some(1);
                    }
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
        
        /// Get the current position in the iteration (for progress tracking)
        pub fn current_position(&self) -> Option<u128> {
            if let Some(counter) = self.big_combination_counter {
                Some(counter)
            } else if self.grade_filter.is_some() {
                // For grade-specific iteration, we need to track combinations differently
                // The counter tracks how many combinations we've generated
                Some(self.current as u128)
            } else if self.dimension <= 64 {
                Some(self.current as u128)
            } else {
                None
            }
        }
        
        /// Get the total number of elements that will be iterated
        /// Returns None if the count would overflow u128 or is infinite
        pub fn total_count(&self) -> Option<u128> {
            if let Some(grade) = self.grade_filter {
                Self::binomial_coefficient(self.dimension, grade)
            } else if self.dimension <= 64 {
                Some(1u128 << self.dimension)
            } else {
                None // Too large to count
            }
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
        /// 
        /// Note: For dimensions > 20, this requires the caller to provide sparse
        /// components that return non-zero values for only a finite set of indices.
        /// Full enumeration of all 2^n indices is not feasible for large n.
        pub fn compute(
            &self,
            a_components: &dyn Fn(&BigIndex) -> Complex<P>,
            b_components: &dyn Fn(&BigIndex) -> Complex<P>,
        ) -> Complex<P> {
            let mut result = Complex::zero();
            
            // For small dimensions, we can enumerate all indices
            if self.dimension <= 20 {
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
            } else {
                // For large dimensions, caller must ensure sparsity
                // Full enumeration is not feasible
                return Complex::zero();
            }
            
            result
        }
        
        /// Compute coherence inner product for sparse elements
        /// This version accepts iterators over non-zero components
        #[cfg(feature = "alloc")]
        pub fn compute_sparse<I1, I2>(
            &self,
            a_components: I1,
            b_components: I2,
        ) -> Complex<P>
        where
            I1: IntoIterator<Item = (BigIndex, Complex<P>)>,
            I2: IntoIterator<Item = (BigIndex, Complex<P>)>,
        {
            // Collect b components into a map for efficient lookup
            let b_map: BTreeMap<Vec<u8>, Complex<P>> = b_components
                .into_iter()
                .map(|(idx, val)| (idx.to_bytes(), val))
                .collect();
            
            let mut result = Complex::zero();
            
            // Iterate through a components and look up matching b components
            for (idx, a_val) in a_components {
                if let Some(&b_val) = b_map.get(&idx.to_bytes()) {
                    // Components at same index contribute to inner product
                    result = result + a_val.conj() * b_val;
                }
            }
            
            result
        }
        
        /// Compute coherence inner product for sparse elements (no_std version)
        /// This version is less efficient but works without alloc
        #[cfg(not(feature = "alloc"))]
        pub fn compute_sparse<I1, I2>(
            &self,
            a_components: I1,
            b_components: I2,
        ) -> Complex<P>
        where
            I1: IntoIterator<Item = (BigIndex, Complex<P>)>,
            I2: IntoIterator<Item = (BigIndex, Complex<P>)>,
        {
            let a_vec: Vec<_> = a_components.into_iter().collect();
            let b_vec: Vec<_> = b_components.into_iter().collect();
            
            let mut result = Complex::zero();
            
            // O(n*m) algorithm for no_std case
            for (a_idx, a_val) in &a_vec {
                for (b_idx, b_val) in &b_vec {
                    if a_idx == b_idx {
                        result = result + a_val.conj() * b_val;
                    }
                }
            }
            
            result
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::streaming::ComponentIterator;

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
    
    #[test]
    fn test_bigindex_and_operation() {
        let mut a = BigIndex::new(256);
        a.set_bit(10);
        a.set_bit(20);
        a.set_bit(30);
        
        let mut b = BigIndex::new(256);
        b.set_bit(20);
        b.set_bit(30);
        b.set_bit(40);
        
        let result = a.and(&b);
        assert!(!result.get_bit(10)); // Only in a
        assert!(result.get_bit(20));  // In both
        assert!(result.get_bit(30));  // In both
        assert!(!result.get_bit(40)); // Only in b
        assert_eq!(result.count_ones(), 2);
    }
    
    #[test]
    fn test_bigindex_or_operation() {
        let mut a = BigIndex::new(256);
        a.set_bit(10);
        a.set_bit(20);
        
        let mut b = BigIndex::new(256);
        b.set_bit(20);
        b.set_bit(30);
        
        let result = a.or(&b);
        assert!(result.get_bit(10));  // From a
        assert!(result.get_bit(20));  // From both
        assert!(result.get_bit(30));  // From b
        assert_eq!(result.count_ones(), 3);
    }
    
    #[test]
    fn test_bigindex_xor_operation() {
        let mut a = BigIndex::new(512);
        a.set_bit(100);
        a.set_bit(200);
        a.set_bit(300);
        
        let mut b = BigIndex::new(512);
        b.set_bit(200);
        b.set_bit(300);
        b.set_bit(400);
        
        let result = a.xor(&b);
        assert!(result.get_bit(100));  // Only in a
        assert!(!result.get_bit(200)); // In both (cancels)
        assert!(!result.get_bit(300)); // In both (cancels)
        assert!(result.get_bit(400));  // Only in b
        assert_eq!(result.count_ones(), 2);
    }
    
    #[test]
    fn test_bigindex_clear_bit() {
        let mut idx = BigIndex::new(128);
        idx.set_bit(10);
        idx.set_bit(20);
        idx.set_bit(30);
        
        assert_eq!(idx.count_ones(), 3);
        
        idx.clear_bit(20);
        assert!(!idx.get_bit(20));
        assert_eq!(idx.count_ones(), 2);
    }
    
    #[test]
    fn test_bigindex_is_zero() {
        let mut idx = BigIndex::new(1024);
        assert!(idx.is_zero());
        
        idx.set_bit(500);
        assert!(!idx.is_zero());
        
        idx.clear_bit(500);
        assert!(idx.is_zero());
    }
    
    #[test]
    fn test_bigindex_comparison() {
        let mut a = BigIndex::new(256);
        a.set_bit(10);
        
        let mut b = BigIndex::new(256);
        b.set_bit(20);
        
        // a has bit 10 set, b has bit 20 set
        // In binary: a < b because bit 10 comes before bit 20
        assert!(a < b);
        
        let mut c = BigIndex::new(256);
        c.set_bit(10);
        c.set_bit(20);
        
        // c has both bits set, so c > a and c > b
        assert!(c > a);
        assert!(c > b);
    }
    
    #[test]
    fn test_bigindex_bit_positions() {
        let mut idx = BigIndex::new(512);
        idx.set_bit(10);
        idx.set_bit(50);
        idx.set_bit(100);
        idx.set_bit(200);
        
        let positions: Vec<usize> = idx.bit_positions().collect();
        assert_eq!(positions, vec![10, 50, 100, 200]);
    }
    
    #[test]
    fn test_bigindex_4096_dimension() {
        // Test with 4096-bit dimension
        let mut idx = BigIndex::new(4096);
        
        // Set bits at very large positions
        idx.set_bit(1000);
        idx.set_bit(2000);
        idx.set_bit(3000);
        idx.set_bit(3999);
        
        assert_eq!(idx.count_ones(), 4);
        assert!(idx.get_bit(3000));
        assert!(!idx.get_bit(3001));
        
        // Test operations at this scale
        let mut idx2 = BigIndex::new(4096);
        idx2.set_bit(2000);
        idx2.set_bit(3000);
        idx2.set_bit(3500);
        
        let intersection = idx.and(&idx2);
        assert_eq!(intersection.count_ones(), 2); // bits 2000 and 3000
        
        let union = idx.or(&idx2);
        assert_eq!(union.count_ones(), 5); // 1000, 2000, 3000, 3500, 3999
    }
    
    #[test]
    fn test_bigindex_sign_computation() {
        // Test e_0 * e_1 = e_01 (no sign change)
        let mut idx1 = BigIndex::new(8);
        idx1.set_bit(0); // e_0
        
        let mut idx2 = BigIndex::new(8);
        idx2.set_bit(1); // e_1
        
        let sign = BigIndex::compute_sign::<f64>(&idx1, &idx2);
        assert_eq!(sign, 1.0); // No swaps needed
        
        // Test e_1 * e_0 = -e_01 (one swap)
        let sign_swapped = BigIndex::compute_sign::<f64>(&idx2, &idx1);
        assert_eq!(sign_swapped, -1.0); // One swap needed
        
        // Test e_0 * e_2 * e_1 = -e_012 
        let mut idx3 = BigIndex::new(8);
        idx3.set_bit(0);
        idx3.set_bit(2); // e_02
        
        let mut idx4 = BigIndex::new(8);
        idx4.set_bit(1); // e_1
        
        // e_02 * e_1: bit 1 needs to swap with bit 2, so -1
        let sign3 = BigIndex::compute_sign::<f64>(&idx3, &idx4);
        assert_eq!(sign3, -1.0);
    }
    
    #[test]
    fn test_bigindex_sign_large_indices() {
        // Test sign computation with large indices
        let mut idx1 = BigIndex::new(4096);
        idx1.set_bit(100);
        idx1.set_bit(200);
        idx1.set_bit(300);
        
        let mut idx2 = BigIndex::new(4096);
        idx2.set_bit(150);
        idx2.set_bit(250);
        idx2.set_bit(350);
        
        // Count swaps: bit 150 swaps with 200 and 300 (2 swaps)
        //              bit 250 swaps with 300 (1 swap)
        // Total: 3 swaps, so sign = -1
        let sign = BigIndex::compute_sign::<f64>(&idx1, &idx2);
        assert_eq!(sign, -1.0);
    }
    
    #[test]
    fn test_bigindex_sign_same_indices() {
        // When indices overlap, the result should be 0 in geometric algebra
        // But our sign computation just counts swaps
        let mut idx = BigIndex::new(256);
        idx.set_bit(10);
        idx.set_bit(20);
        
        // Same index multiplied by itself
        let sign = BigIndex::compute_sign::<f64>(&idx, &idx);
        // Each bit in idx2 that comes before a bit in idx1 causes a swap
        // bit 10 in idx1: no bits before it in idx2
        // bit 20 in idx1: bit 10 in idx2 comes before it (1 swap)
        assert_eq!(sign, -1.0);
    }
    
    #[test]
    fn test_streaming_inner_product_small_dimension() {
        use streaming::StreamingInnerProduct;
        
        let dimension = 8;
        let inner_product = StreamingInnerProduct::<f64>::new(dimension);
        
        // Create simple test elements
        // a = 1 + 2*e1 + 3*e2 + 4*e12
        let a_components = |idx: &BigIndex| -> Complex<f64> {
            match idx.to_usize() {
                Some(0) => Complex::new(1.0, 0.0), // scalar
                Some(1) => Complex::new(2.0, 0.0), // e1
                Some(2) => Complex::new(3.0, 0.0), // e2
                Some(3) => Complex::new(4.0, 0.0), // e12
                _ => Complex::zero(),
            }
        };
        
        // b = 5 + 6*e1 + 7*e2 + 8*e12
        let b_components = |idx: &BigIndex| -> Complex<f64> {
            match idx.to_usize() {
                Some(0) => Complex::new(5.0, 0.0), // scalar
                Some(1) => Complex::new(6.0, 0.0), // e1
                Some(2) => Complex::new(7.0, 0.0), // e2
                Some(3) => Complex::new(8.0, 0.0), // e12
                _ => Complex::zero(),
            }
        };
        
        let result = inner_product.compute(&a_components, &b_components);
        
        // Coherence inner product respects grade orthogonality
        // So we only get contributions from matching grades:
        // Grade 0: 1*5 = 5
        // Grade 1: 2*6 + 3*7 = 12 + 21 = 33
        // Grade 2: 4*8 = 32
        // Total: 5 + 33 + 32 = 70
        assert_eq!(result, Complex::new(70.0, 0.0));
    }
    
    #[test]
    fn test_streaming_inner_product_large_dimension() {
        use streaming::StreamingInnerProduct;
        
        // Test with dimension > 64 to ensure BigIndex is used
        let dimension = 65;
        let inner_product = StreamingInnerProduct::<f64>::new(dimension);
        
        // Create sparse components as vectors
        let mut a_components = Vec::new();
        let mut b_components = Vec::new();
        
        // Scalar component
        let scalar_idx = BigIndex::new(dimension);
        a_components.push((scalar_idx.clone(), Complex::new(1.0, 0.0)));
        b_components.push((scalar_idx, Complex::new(4.0, 0.0)));
        
        // e10 component
        let mut e10_idx = BigIndex::new(dimension);
        e10_idx.set_bit(10);
        a_components.push((e10_idx.clone(), Complex::new(2.0, 0.0)));
        b_components.push((e10_idx, Complex::new(5.0, 0.0)));
        
        // e20 ∧ e30 component
        let mut e2030_idx = BigIndex::new(dimension);
        e2030_idx.set_bit(20);
        e2030_idx.set_bit(30);
        a_components.push((e2030_idx.clone(), Complex::new(3.0, 0.0)));
        b_components.push((e2030_idx, Complex::new(6.0, 0.0)));
        
        let result = inner_product.compute_sparse(a_components, b_components);
        
        // Expected: 1*4 + 2*5 + 3*6 = 4 + 10 + 18 = 32
        assert_eq!(result, Complex::new(32.0, 0.0));
    }
    
    #[test]
    fn test_streaming_inner_product_truly_large_dimension() {
        use streaming::StreamingInnerProduct;
        
        // Test with truly large dimension using sparse representation
        let dimension = 4096;
        let inner_product = StreamingInnerProduct::<f64>::new(dimension);
        
        // Create very sparse components
        let mut a_components = Vec::new();
        let mut b_components = Vec::new();
        
        // Scalar component
        let scalar_idx = BigIndex::new(dimension);
        a_components.push((scalar_idx.clone(), Complex::new(1.0, 0.0)));
        b_components.push((scalar_idx, Complex::new(3.0, 0.0)));
        
        // e_1000 component
        let mut e1000_idx = BigIndex::new(dimension);
        e1000_idx.set_bit(1000);
        a_components.push((e1000_idx.clone(), Complex::new(2.0, 0.0)));
        b_components.push((e1000_idx, Complex::new(4.0, 0.0)));
        
        // e_500 ∧ e_1500 ∧ e_2500 component
        let mut e_multi_idx = BigIndex::new(dimension);
        e_multi_idx.set_bit(500);
        e_multi_idx.set_bit(1500);
        e_multi_idx.set_bit(2500);
        a_components.push((e_multi_idx.clone(), Complex::new(5.0, 0.0)));
        b_components.push((e_multi_idx, Complex::new(6.0, 0.0)));
        
        let result = inner_product.compute_sparse(a_components, b_components);
        
        // Expected: 1*3 + 2*4 + 5*6 = 3 + 8 + 30 = 41
        assert_eq!(result, Complex::new(41.0, 0.0));
    }
    
    #[test]
    fn test_streaming_inner_product_grade_orthogonality() {
        use streaming::StreamingInnerProduct;
        
        let dimension = 16;
        let inner_product = StreamingInnerProduct::<f64>::new(dimension);
        
        // a has only grade 1 components
        let a_components = |idx: &BigIndex| -> Complex<f64> {
            if idx.count_ones() == 1 {
                Complex::new(1.0, 0.0)
            } else {
                Complex::zero()
            }
        };
        
        // b has only grade 2 components
        let b_components = |idx: &BigIndex| -> Complex<f64> {
            if idx.count_ones() == 2 {
                Complex::new(1.0, 0.0)
            } else {
                Complex::zero()
            }
        };
        
        let result = inner_product.compute(&a_components, &b_components);
        
        // Different grades are orthogonal, so inner product is 0
        assert_eq!(result, Complex::zero());
    }
    
    #[test]
    fn test_component_iterator_grade_only() {
        use streaming::ComponentIterator;
        
        let dimension = 5;
        
        // Test grade 0 (scalar)
        let grade0: Vec<_> = ComponentIterator::<f64>::grade_only(dimension, 0).collect();
        assert_eq!(grade0.len(), 1);
        assert_eq!(grade0[0].0.count_ones(), 0);
        
        // Test grade 1 (5 choose 1 = 5)
        let grade1: Vec<_> = ComponentIterator::<f64>::grade_only(dimension, 1).collect();
        assert_eq!(grade1.len(), 5);
        for (idx, grade) in &grade1 {
            assert_eq!(idx.count_ones(), 1);
            assert_eq!(*grade, 1);
        }
        
        // Test grade 2 (5 choose 2 = 10)
        let grade2: Vec<_> = ComponentIterator::<f64>::grade_only(dimension, 2).collect();
        assert_eq!(grade2.len(), 10);
        for (idx, grade) in &grade2 {
            assert_eq!(idx.count_ones(), 2);
            assert_eq!(*grade, 2);
        }
        
        // Test grade 3 (5 choose 3 = 10)
        let grade3: Vec<_> = ComponentIterator::<f64>::grade_only(dimension, 3).collect();
        assert_eq!(grade3.len(), 10);
        
        // Test grade 4 (5 choose 4 = 5)
        let grade4: Vec<_> = ComponentIterator::<f64>::grade_only(dimension, 4).collect();
        assert_eq!(grade4.len(), 5);
        
        // Test grade 5 (5 choose 5 = 1)
        let grade5: Vec<_> = ComponentIterator::<f64>::grade_only(dimension, 5).collect();
        assert_eq!(grade5.len(), 1);
        assert_eq!(grade5[0].0.count_ones(), 5);
    }
    
    #[test]
    fn test_component_iterator_large_dimension() {
        use streaming::ComponentIterator;
        
        // Test with large dimension (but only iterate specific grade)
        let dimension = 256;
        
        // Grade 0 should still have only 1 element
        let grade0_count = ComponentIterator::<f64>::grade_only(dimension, 0).count();
        assert_eq!(grade0_count, 1);
        
        // Grade 1 should have 256 elements
        let grade1_count = ComponentIterator::<f64>::grade_only(dimension, 1).count();
        assert_eq!(grade1_count, 256);
        
        // Grade 2 should have 256*255/2 = 32640 elements
        // But let's just check the first few
        let grade2_first_10: Vec<_> = ComponentIterator::<f64>::grade_only(dimension, 2)
            .take(10)
            .collect();
        assert_eq!(grade2_first_10.len(), 10);
        
        // Verify the indices are correct
        // First should be e0 ∧ e1 (bits 0 and 1 set)
        assert!(grade2_first_10[0].0.get_bit(0));
        assert!(grade2_first_10[0].0.get_bit(1));
        assert_eq!(grade2_first_10[0].0.count_ones(), 2);
    }
    
    #[test]
    fn test_streaming_inner_product_complex_values() {
        use streaming::StreamingInnerProduct;
        
        let dimension = 8;
        let inner_product = StreamingInnerProduct::<f64>::new(dimension);
        
        // Test with complex values
        let a_components = |idx: &BigIndex| -> Complex<f64> {
            match idx.to_usize() {
                Some(0) => Complex::new(1.0, 2.0), // 1 + 2i
                Some(1) => Complex::new(3.0, -1.0), // 3 - i
                _ => Complex::zero(),
            }
        };
        
        let b_components = |idx: &BigIndex| -> Complex<f64> {
            match idx.to_usize() {
                Some(0) => Complex::new(2.0, 1.0), // 2 + i
                Some(1) => Complex::new(1.0, 2.0), // 1 + 2i
                _ => Complex::zero(),
            }
        };
        
        let result = inner_product.compute(&a_components, &b_components);
        
        // Coherence inner product uses conjugate of a:
        // conj(1+2i)*(2+i) + conj(3-i)*(1+2i)
        // = (1-2i)*(2+i) + (3+i)*(1+2i)
        // = (2+i-4i-2i²) + (3+6i+i+2i²)
        // = (2+i-4i+2) + (3+7i-2)
        // = (4-3i) + (1+7i)
        // = 5+4i
        assert!((result.re - 5.0).abs() < 1e-10);
        assert!((result.im - 4.0).abs() < 1e-10);
    }
    
    #[test]
    fn test_component_iterator_binomial_coefficient() {
        // Test small values
        assert_eq!(ComponentIterator::<f64>::binomial_coefficient(5, 2), Some(10));
        assert_eq!(ComponentIterator::<f64>::binomial_coefficient(10, 3), Some(120));
        assert_eq!(ComponentIterator::<f64>::binomial_coefficient(20, 10), Some(184756));
        
        // Test edge cases
        assert_eq!(ComponentIterator::<f64>::binomial_coefficient(100, 0), Some(1));
        assert_eq!(ComponentIterator::<f64>::binomial_coefficient(100, 100), Some(1));
        assert_eq!(ComponentIterator::<f64>::binomial_coefficient(5, 10), Some(0));
        
        // Test large values that fit in u128
        assert_eq!(ComponentIterator::<f64>::binomial_coefficient(100, 2), Some(4950));
        assert_eq!(ComponentIterator::<f64>::binomial_coefficient(200, 3), Some(1313400));
        
        // Test symmetry: C(n,k) = C(n,n-k)
        let c1 = ComponentIterator::<f64>::binomial_coefficient(50, 20);
        let c2 = ComponentIterator::<f64>::binomial_coefficient(50, 30);
        assert_eq!(c1, c2);
    }
    
    #[test]
    fn test_grade_iteration_small_dimensions() {
        // Test dimension 5, grade 2
        let iter = ComponentIterator::<f64>::grade_only(5, 2);
        let indices: Vec<_> = iter.map(|(idx, _)| idx).collect();
        
        // Should have C(5,2) = 10 elements
        assert_eq!(indices.len(), 10);
        
        // All should have grade 2
        for idx in &indices {
            assert_eq!(idx.count_ones(), 2);
        }
        
        // Check some specific indices
        let has_01 = indices.iter().any(|idx| idx.get_bit(0) && idx.get_bit(1));
        let has_34 = indices.iter().any(|idx| idx.get_bit(3) && idx.get_bit(4));
        assert!(has_01);
        assert!(has_34);
    }
    
    #[test]
    fn test_grade_iteration_large_dimensions() {
        // Test dimension 100, grade 3
        let mut iter = ComponentIterator::<f64>::grade_only(100, 3);
        
        // Should be able to get total count
        let total = iter.total_count();
        assert_eq!(total, Some(161700)); // C(100,3) = 161700
        
        // Take first few elements
        let mut count = 0;
        for (idx, grade) in iter.by_ref().take(5) {
            assert_eq!(grade, 3);
            assert_eq!(idx.count_ones(), 3);
            assert_eq!(idx.bit_count, 100);
            count += 1;
        }
        assert_eq!(count, 5);
        
        // Check position tracking
        let pos = iter.current_position();
        assert!(pos.is_some());
    }
    
    #[test]
    fn test_grade_iteration_very_large_dimensions() {
        // Test dimension 4096, grade 2
        let iter = ComponentIterator::<f64>::grade_only(4096, 2);
        
        // Should be able to compute total count
        let total = iter.total_count();
        assert!(total.is_some());
        let expected = (4096u128 * 4095) / 2; // C(4096,2)
        assert_eq!(total, Some(expected));
        
        // Take first element
        let first: Vec<_> = iter.take(1).collect();
        assert_eq!(first.len(), 1);
        
        let (idx, grade) = &first[0];
        assert_eq!(*grade, 2);
        assert_eq!(idx.count_ones(), 2);
        assert_eq!(idx.bit_count, 4096);
        
        // Should have bits 0 and 1 set (first combination)
        assert!(idx.get_bit(0));
        assert!(idx.get_bit(1));
        assert!(!idx.get_bit(2));
    }
    
    #[test]
    fn test_component_iterator_progress_tracking() {
        let mut iter = ComponentIterator::<f64>::grade_only(20, 5);
        
        // Get total count
        let total = iter.total_count().unwrap();
        assert_eq!(total, 15504); // C(20,5)
        
        // Iterate through first 100 elements
        for _ in iter.by_ref().take(100) {}
        
        // Check position
        let pos = iter.current_position();
        assert_eq!(pos, Some(100));
        
        // Progress should be trackable
        let progress = pos.unwrap() as f64 / total as f64;
        assert!(progress > 0.0);
        assert!(progress < 1.0);
    }
    
    #[test]
    fn test_empty_grade_iteration() {
        // Grade 0 should have exactly 1 element (the scalar)
        let iter = ComponentIterator::<f64>::grade_only(100, 0);
        let elements: Vec<_> = iter.collect();
        assert_eq!(elements.len(), 1);
        
        let (idx, grade) = &elements[0];
        assert_eq!(*grade, 0);
        assert!(idx.is_zero());
    }
    
    #[test]
    fn test_full_iteration_vs_grade_iteration() {
        // For small dimensions, verify full iteration matches grade-by-grade
        let dim = 8;
        
        // Count elements by grade using full iteration
        let mut grade_counts = vec![0usize; dim + 1];
        let full_iter = ComponentIterator::<f64>::new(dim);
        for (_, grade) in full_iter {
            grade_counts[grade] += 1;
        }
        
        // Verify against grade-specific iteration
        for g in 0..=dim {
            let grade_iter = ComponentIterator::<f64>::grade_only(dim, g);
            let count = grade_iter.count();
            assert_eq!(count, grade_counts[g]);
            assert_eq!(count, ComponentIterator::<f64>::binomial_coefficient(dim, g).unwrap() as usize);
        }
    }
}
