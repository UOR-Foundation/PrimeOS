//! Lazy evaluation for Clifford algebra basis generation

use crate::clifford::CliffordAlgebra;
use crate::element::CliffordElement;
use ccm_core::{CcmError, Float};
use num_complex::Complex;
#[allow(unused_imports)]
use num_traits::{One, Zero};

use core::cell::RefCell;

#[cfg(feature = "alloc")]
use alloc::collections::BTreeMap;

/// Lazy basis generator for Clifford algebras
///
/// Generates basis elements on demand rather than pre-computing all 2^n elements
#[derive(Clone)]
pub struct LazyBasis<P: Float> {
    /// The dimension of the underlying vector space
    dimension: usize,
    /// Cache of already computed basis elements
    #[cfg(feature = "alloc")]
    cache: RefCell<BTreeMap<usize, CliffordElement<P>>>,
    /// Fixed-size cache for no_std environments
    #[cfg(not(feature = "alloc"))]
    cache: RefCell<[(usize, Option<CliffordElement<P>>); 64]>,
    #[cfg(not(feature = "alloc"))]
    cache_size: RefCell<usize>,
    /// The parent algebra for metric information
    _algebra: CliffordAlgebra<P>,
}

impl<P: Float> LazyBasis<P> {
    /// Create a new lazy basis generator
    pub fn new(algebra: CliffordAlgebra<P>) -> Self {
        let dimension = algebra.dimension();

        Self {
            dimension,
            #[cfg(feature = "alloc")]
            cache: RefCell::new(BTreeMap::new()),
            #[cfg(not(feature = "alloc"))]
            cache: RefCell::new(core::array::from_fn(|_| (0, None))),
            #[cfg(not(feature = "alloc"))]
            cache_size: RefCell::new(0),
            _algebra: algebra,
        }
    }

    /// Get a basis element by index, computing it if necessary
    pub fn get(&self, index: usize) -> Result<CliffordElement<P>, CcmError> {
        if index >= (1usize << self.dimension) {
            return Err(CcmError::InvalidInput);
        }

        // Check cache first
        #[cfg(feature = "alloc")]
        {
            if let Some(element) = self.cache.borrow().get(&index) {
                return Ok(element.clone());
            }
        }

        #[cfg(not(feature = "alloc"))]
        {
            let cache = self.cache.borrow();
            for i in 0..*self.cache_size.borrow() {
                if cache[i].0 == index {
                    if let Some(ref element) = cache[i].1 {
                        return Ok(element.clone());
                    }
                }
            }
        }

        // Compute the basis element
        let element = self.compute_basis_element(index)?;

        // Store in cache
        #[cfg(feature = "alloc")]
        {
            self.cache.borrow_mut().insert(index, element.clone());
        }

        #[cfg(not(feature = "alloc"))]
        {
            let mut cache = self.cache.borrow_mut();
            let mut cache_size = self.cache_size.borrow_mut();

            if *cache_size < 64 {
                cache[*cache_size] = (index, Some(element.clone()));
                *cache_size += 1;
            } else {
                // Simple LRU: replace the first element
                for i in 0..63 {
                    cache[i] = cache[i + 1].clone();
                }
                cache[63] = (index, Some(element.clone()));
            }
        }

        Ok(element)
    }

    /// Compute a basis element from its index
    fn compute_basis_element(&self, index: usize) -> Result<CliffordElement<P>, CcmError> {
        let mut element = CliffordElement::zero(self.dimension);
        element.set_component(index, Complex::one())?;
        Ok(element)
    }

    /// Get basis element by grade and position within that grade
    pub fn get_by_grade(
        &self,
        grade: usize,
        position: usize,
    ) -> Result<CliffordElement<P>, CcmError> {
        if grade > self.dimension {
            return Err(CcmError::InvalidInput);
        }

        // Find the position-th element of the given grade
        let mut count = 0;
        for i in 0..(1usize << self.dimension) {
            if i.count_ones() as usize == grade {
                if count == position {
                    return self.get(i);
                }
                count += 1;
            }
        }

        Err(CcmError::InvalidInput)
    }

    /// Iterate over all basis elements of a given grade
    pub fn grade_iterator(&self, grade: usize) -> GradeIterator<P> {
        GradeIterator {
            basis: self,
            grade,
            current: 0,
            max: 1usize << self.dimension,
        }
    }

    /// Clear the cache to free memory
    pub fn clear_cache(&self) {
        #[cfg(feature = "alloc")]
        {
            self.cache.borrow_mut().clear();
        }

        #[cfg(not(feature = "alloc"))]
        {
            *self.cache_size.borrow_mut() = 0;
        }
    }

    /// Get the number of cached elements
    pub fn cache_size(&self) -> usize {
        #[cfg(feature = "alloc")]
        {
            self.cache.borrow().len()
        }

        #[cfg(not(feature = "alloc"))]
        {
            *self.cache_size.borrow()
        }
    }
}

/// Iterator over basis elements of a specific grade
pub struct GradeIterator<'a, P: Float> {
    basis: &'a LazyBasis<P>,
    grade: usize,
    current: usize,
    max: usize,
}

impl<'a, P: Float> Iterator for GradeIterator<'a, P> {
    type Item = Result<CliffordElement<P>, CcmError>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.current < self.max {
            let index = self.current;
            self.current += 1;

            if index.count_ones() as usize == self.grade {
                return Some(self.basis.get(index));
            }
        }

        None
    }
}

/// Lazy Clifford algebra that generates operations on demand
#[derive(Clone)]
pub struct LazyCliffordAlgebra<P: Float> {
    /// The underlying algebra
    algebra: CliffordAlgebra<P>,
    /// Lazy basis generator
    basis: LazyBasis<P>,
}

impl<P: Float> LazyCliffordAlgebra<P> {
    /// Create a new lazy Clifford algebra
    pub fn generate(n: usize) -> Result<Self, CcmError> {
        // Use generate_with_limit to allow larger dimensions
        let algebra = CliffordAlgebra::generate_with_limit(n, n)?;
        let basis = LazyBasis::new(algebra.clone());

        Ok(Self { algebra, basis })
    }

    /// Get the dimension
    pub fn dimension(&self) -> usize {
        self.algebra.dimension()
    }
    
    /// Get the metric signature
    pub fn signature(&self) -> (usize, usize, usize) {
        self.algebra.signature()
    }

    /// Get a basis element lazily
    pub fn basis_element(&self, index: usize) -> Result<CliffordElement<P>, CcmError> {
        self.basis.get(index)
    }

    /// Create a basis blade lazily
    pub fn basis_blade(&self, indices: &[usize]) -> Result<CliffordElement<P>, CcmError> {
        // Convert indices to bit pattern
        let mut bit_pattern = 0usize;
        for &i in indices {
            if i >= self.dimension() {
                return Err(CcmError::InvalidInput);
            }
            if bit_pattern & (1 << i) != 0 {
                return Err(CcmError::InvalidInput);
            }
            bit_pattern |= 1 << i;
        }

        self.basis_element(bit_pattern)
    }

    /// Iterate over basis elements of a specific grade
    pub fn grade_elements(&self, grade: usize) -> GradeIterator<P> {
        self.basis.grade_iterator(grade)
    }

    /// Geometric product using lazy evaluation
    pub fn geometric_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        self.algebra.geometric_product(a, b)
    }
    
    /// Wedge product using lazy evaluation
    pub fn wedge_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        self.algebra.wedge_product(a, b)
    }
    
    /// Inner product using lazy evaluation
    pub fn inner_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        self.algebra.inner_product(a, b)
    }
    
    /// Scalar product using lazy evaluation
    pub fn scalar_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<Complex<P>, CcmError> {
        self.algebra.scalar_product(a, b)
    }

    /// Get memory usage statistics
    pub fn memory_stats(&self) -> MemoryStats {
        MemoryStats {
            dimension: self.dimension(),
            total_basis_elements: 1usize << self.dimension(),
            cached_elements: self.basis.cache_size(),
            cache_hit_rate: 0.0, // Would need to track this
        }
    }
}

/// Memory usage statistics for lazy evaluation
#[derive(Debug, Clone)]
pub struct MemoryStats {
    /// Dimension of the vector space
    pub dimension: usize,
    /// Total number of basis elements (2^n)
    pub total_basis_elements: usize,
    /// Number of currently cached elements
    pub cached_elements: usize,
    /// Cache hit rate (if tracked)
    pub cache_hit_rate: f64,
}

impl MemoryStats {
    /// Estimate memory saved by lazy evaluation
    pub fn memory_saved_bytes(&self) -> usize {
        // Each CliffordElement has 2^n complex numbers
        // Complex<f64> is 16 bytes (8 bytes real + 8 bytes imaginary)
        let bytes_per_element = self.total_basis_elements * 16;
        let total_bytes = self.total_basis_elements * bytes_per_element;
        let cached_bytes = self.cached_elements * bytes_per_element;

        total_bytes.saturating_sub(cached_bytes)
    }

    /// Percentage of basis elements that are cached
    pub fn cache_percentage(&self) -> f64 {
        if self.total_basis_elements == 0 {
            0.0
        } else {
            (self.cached_elements as f64 / self.total_basis_elements as f64) * 100.0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lazy_basis_generation() {
        let algebra = CliffordAlgebra::<f64>::generate(4).unwrap();
        let lazy_basis = LazyBasis::new(algebra);

        // Should start with empty cache
        assert_eq!(lazy_basis.cache_size(), 0);

        // Get a basis element
        let e0 = lazy_basis.get(1).unwrap(); // e₀
        assert_eq!(e0.component(1), Some(Complex::one()));

        // Cache should now have one element
        assert_eq!(lazy_basis.cache_size(), 1);

        // Getting the same element should use cache
        let e0_again = lazy_basis.get(1).unwrap();
        assert_eq!(e0.component(1), e0_again.component(1));
        assert_eq!(lazy_basis.cache_size(), 1);
    }

    #[test]
    fn test_grade_iterator() {
        let algebra = CliffordAlgebra::<f64>::generate(3).unwrap();
        let lazy_basis = LazyBasis::new(algebra);

        // Iterate over grade 2 elements
        let grade2_elements: Vec<_> = lazy_basis.grade_iterator(2).collect();

        // Should have C(3,2) = 3 elements
        assert_eq!(grade2_elements.len(), 3);

        // All should be grade 2
        for result in grade2_elements {
            let elem = result.unwrap();
            let non_zero_indices: Vec<_> = (0..8)
                .filter(|&i| elem.component(i).unwrap().norm() > 1e-10)
                .collect();

            assert_eq!(non_zero_indices.len(), 1);
            let idx = non_zero_indices[0];
            assert_eq!(idx.count_ones(), 2);
        }
    }

    #[test]
    fn test_lazy_algebra() {
        let lazy_algebra = LazyCliffordAlgebra::<f64>::generate(5).unwrap();

        // Should be able to get basis elements without pre-computing all 32
        let e01 = lazy_algebra.basis_blade(&[0, 1]).unwrap();
        assert_eq!(e01.component(3), Some(Complex::one())); // binary 011 = 3

        // Check memory stats
        let stats = lazy_algebra.memory_stats();
        assert_eq!(stats.dimension, 5);
        assert_eq!(stats.total_basis_elements, 32);
        assert_eq!(stats.cached_elements, 1);
        assert!(stats.cache_percentage() < 5.0);
    }

    #[test]
    fn test_memory_savings() {
        let lazy_algebra = LazyCliffordAlgebra::<f64>::generate(8).unwrap();

        // Get a few basis elements
        lazy_algebra.basis_element(0).unwrap();
        lazy_algebra.basis_element(1).unwrap();
        lazy_algebra.basis_element(15).unwrap();

        let stats = lazy_algebra.memory_stats();

        // Should have saved significant memory
        let saved = stats.memory_saved_bytes();
        let total = 256 * 256 * 16; // 256 elements, each with 256 complex numbers

        assert!(saved > total * 90 / 100); // Saved more than 90%
    }
}
