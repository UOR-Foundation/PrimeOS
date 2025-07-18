//! Scalable Clifford algebra trait for arbitrary dimensions
//!
//! This module provides a trait and implementations that can handle
//! Clifford algebras of arbitrary dimension without dense storage limitations.

use crate::{
    arbitrary_support::BigIndex,
    single_blade::SingleBlade,
    sparse::SparseCliffordElement,
    sparse_big::SparseBigElement,
};
use ccm_core::{CcmError, Float};
use num_complex::Complex;
use num_traits::{One, Zero};

/// A lazy element that computes components on demand
pub struct LazyElement<P: Float> {
    dimension: usize,
    /// Function that computes the component at a given index
    compute_fn: Box<dyn Fn(&BigIndex) -> Complex<P>>,
}

impl<P: Float> LazyElement<P> {
    pub fn new<F>(dimension: usize, compute_fn: F) -> Self
    where
        F: Fn(&BigIndex) -> Complex<P> + 'static,
    {
        Self {
            dimension,
            compute_fn: Box::new(compute_fn),
        }
    }
    
    pub fn dimension(&self) -> usize {
        self.dimension
    }
    
    pub fn component(&self, index: &BigIndex) -> Complex<P> {
        (self.compute_fn)(index)
    }
    
    /// Note: LazyElement cannot compute coherence norm efficiently for large dimensions
    /// without additional structural information. For practical use:
    /// - Use SingleBlade for single blade operations (supports arbitrary dimensions)
    /// - Use SparseBigElement for multi-blade operations (supports arbitrary dimensions)
    /// - Convert LazyElement to SparseBigElement if norm is needed
    
    /// Extract non-zero components up to a limit
    pub fn to_sparse(&self, max_components: usize) -> SparseCliffordElement<P> {
        let mut sparse = SparseCliffordElement::zero(self.dimension);
        
        // For now, we can only extract components for small dimensions
        if self.dimension <= 20 {
            let mut count = 0;
            for i in 0..(1usize << self.dimension) {
                if count >= max_components {
                    break;
                }
                let idx = BigIndex::from_usize(i, self.dimension);
                let value = self.component(&idx);
                if value.norm_sqr() > P::epsilon() {
                    if let Some(small_idx) = idx.to_usize() {
                        let _ = sparse.set_component(small_idx, value);
                        count += 1;
                    }
                }
            }
        }
        
        sparse
    }
}

/// Iterator over components of a lazy element
pub struct LazyComponentIterator<P: Float> {
    element: LazyElement<P>,
    current: BigIndex,
    dimension: usize,
}

impl<P: Float> Iterator for LazyComponentIterator<P> {
    type Item = (BigIndex, Complex<P>);
    
    fn next(&mut self) -> Option<Self::Item> {
        // This is a placeholder - real implementation would need
        // efficient iteration strategies for large dimensions
        None
    }
}

/// Trait for scalable Clifford algebra operations
///
/// Unlike `CliffordAlgebraTrait`, this trait returns lazy or sparse
/// types that don't require materializing full 2^n-dimensional elements.
///
/// ## Coherence Norm and CCM Axiom A1
///
/// This trait implements the coherence inner product from CCM Axiom A1,
/// which states that the inner product must be:
/// - Positive-definite: ⟨⟨x,x⟩⟩ > 0 for all x ≠ 0
/// - Conjugate symmetric: ⟨⟨x,y⟩⟩ = conj(⟨⟨y,x⟩⟩)
/// - Linear in second argument
/// - **Grade-orthogonal**: ⟨⟨x_i,y_j⟩⟩ = 0 if grade(x_i) ≠ grade(y_j)
///
/// The grade-orthogonality property is crucial for scalable implementations:
/// - For `SingleBlade`: Since it has only one grade, ||blade||_c = |coefficient|
/// - For `SparseBigElement`: Different basis blades have different grades,
///   so ||element||²_c = Σ|component_i|² (no cross terms)
///
/// This allows efficient norm computation without materializing cross products.
pub trait ScalableCliffordAlgebraTrait<P: Float> {
    /// Get the dimension of the underlying vector space
    fn dimension(&self) -> usize;
    
    /// Get the signature (p, q, r) where p+q+r = n
    fn signature(&self) -> (usize, usize, usize);
    
    /// Create a basis element as a single blade
    fn basis_element_lazy(&self, index: usize) -> Result<SingleBlade<P>, CcmError>;
    
    /// Create a basis element with BigIndex for very large dimensions
    fn basis_element_big(&self, index: &BigIndex) -> Result<SingleBlade<P>, CcmError>;
    
    /// Create a basis blade from multiple indices
    fn basis_blade_lazy(&self, indices: &[usize]) -> Result<SingleBlade<P>, CcmError>;
    
    /// Geometric product returning a lazy element
    fn geometric_product_lazy(
        &self,
        a: &SingleBlade<P>,
        b: &SingleBlade<P>,
    ) -> Result<LazyElement<P>, CcmError>;
    
    /// Wedge product returning a single blade (if result is a blade)
    fn wedge_product_lazy(
        &self,
        a: &SingleBlade<P>,
        b: &SingleBlade<P>,
    ) -> Result<SingleBlade<P>, CcmError>;
    
    /// Inner product returning a lazy element
    fn inner_product_lazy(
        &self,
        a: &SingleBlade<P>,
        b: &SingleBlade<P>,
    ) -> Result<LazyElement<P>, CcmError>;
    
    /// Compute coherence inner product without materialization
    fn coherence_inner_product_sparse(
        &self,
        a: &SparseCliffordElement<P>,
        b: &SparseCliffordElement<P>,
    ) -> Complex<P>;
    
    /// Iterator over basis elements of a specific grade
    fn grade_iterator(&self, grade: usize) -> GradeIterator<P>;
    
    /// Memory usage estimate in bytes
    fn memory_usage_bytes(&self) -> usize;
    
    /// Compute coherence norm for a single blade
    /// For single blades, this is just |coefficient|
    fn single_blade_norm(&self, blade: &SingleBlade<P>) -> P {
        blade.coherence_norm()
    }
    
    /// Compute coherence norm for a sparse element
    /// This respects grade-orthogonality (Axiom A1)
    fn sparse_element_norm(&self, element: &SparseBigElement<P>) -> P {
        element.coherence_norm()
    }
}

/// Iterator over basis elements of a specific grade
pub struct GradeIterator<P: Float> {
    dimension: usize,
    grade: usize,
    current_combination: Vec<usize>,
    finished: bool,
    _phantom: core::marker::PhantomData<P>,
}

impl<P: Float> GradeIterator<P> {
    pub fn new(dimension: usize, grade: usize) -> Self {
        if grade > dimension {
            Self {
                dimension,
                grade,
                current_combination: vec![],
                finished: true,
                _phantom: core::marker::PhantomData,
            }
        } else if grade == 0 {
            Self {
                dimension,
                grade,
                current_combination: vec![],
                finished: false,
                _phantom: core::marker::PhantomData,
            }
        } else {
            // Initialize with first combination [0, 1, ..., grade-1]
            let current_combination = (0..grade).collect();
            Self {
                dimension,
                grade,
                current_combination,
                finished: false,
                _phantom: core::marker::PhantomData,
            }
        }
    }
    
    fn advance_combination(&mut self) -> bool {
        if self.current_combination.is_empty() {
            return false;
        }
        
        let k = self.current_combination.len();
        let n = self.dimension;
        
        // Find rightmost element that can be incremented
        let mut i = k - 1;
        while self.current_combination[i] == n - k + i {
            if i == 0 {
                return false;
            }
            i -= 1;
        }
        
        // Increment and reset following elements
        self.current_combination[i] += 1;
        for j in i + 1..k {
            self.current_combination[j] = self.current_combination[j - 1] + 1;
        }
        
        true
    }
}

impl<P: Float> Iterator for GradeIterator<P> {
    type Item = SingleBlade<P>;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }
        
        if self.grade == 0 {
            self.finished = true;
            // Return scalar element
            let index = BigIndex::new(self.dimension);
            return Some(SingleBlade::new(index, Complex::one(), self.dimension));
        }
        
        // Create blade from current combination
        let mut index = BigIndex::new(self.dimension);
        for &pos in &self.current_combination {
            index.set_bit(pos);
        }
        
        let blade = SingleBlade::new(index, Complex::one(), self.dimension);
        
        // Advance to next combination
        if !self.advance_combination() {
            self.finished = true;
        }
        
        Some(blade)
    }
}

/// Scalable Clifford algebra implementation
#[derive(Clone)]
pub struct ScalableAlgebra<P: Float> {
    pub(crate) dimension: usize,
    pub(crate) signature: (usize, usize, usize),
    _phantom: core::marker::PhantomData<P>,
}

impl<P: Float> ScalableAlgebra<P> {
    /// Create a new scalable Clifford algebra
    pub fn new(dimension: usize) -> Self {
        Self {
            dimension,
            signature: (dimension, 0, 0), // Euclidean by default
            _phantom: core::marker::PhantomData,
        }
    }
    
    /// Create with custom signature
    pub fn with_signature(p: usize, q: usize, r: usize) -> Result<Self, CcmError> {
        if p + q + r == 0 {
            return Err(CcmError::InvalidInput);
        }
        
        Ok(Self {
            dimension: p + q + r,
            signature: (p, q, r),
            _phantom: core::marker::PhantomData,
        })
    }
    
    /// Get memory usage in bytes (minimal for scalable algebra)
    pub fn memory_usage_bytes(&self) -> usize {
        // Scalable algebra uses minimal memory - just struct overhead
        core::mem::size_of::<Self>()
    }
}

impl<P: Float + 'static> ScalableCliffordAlgebraTrait<P> for ScalableAlgebra<P> {
    fn dimension(&self) -> usize {
        self.dimension
    }
    
    fn signature(&self) -> (usize, usize, usize) {
        self.signature
    }
    
    fn basis_element_lazy(&self, index: usize) -> Result<SingleBlade<P>, CcmError> {
        if index >= self.dimension {
            return Err(CcmError::InvalidInput);
        }
        
        let mut big_index = BigIndex::new(self.dimension);
        big_index.set_bit(index);
        
        Ok(SingleBlade::new(big_index, Complex::one(), self.dimension))
    }
    
    fn basis_element_big(&self, index: &BigIndex) -> Result<SingleBlade<P>, CcmError> {
        Ok(SingleBlade::new(index.clone(), Complex::one(), self.dimension))
    }
    
    fn basis_blade_lazy(&self, indices: &[usize]) -> Result<SingleBlade<P>, CcmError> {
        // Check indices are valid and unique
        let mut seen = vec![false; self.dimension];
        for &idx in indices {
            if idx >= self.dimension {
                return Err(CcmError::InvalidInput);
            }
            if seen[idx] {
                return Err(CcmError::InvalidInput); // Repeated index
            }
            seen[idx] = true;
        }
        
        // Create blade
        let mut index = BigIndex::new(self.dimension);
        for &idx in indices {
            index.set_bit(idx);
        }
        
        Ok(SingleBlade::new(index, Complex::one(), self.dimension))
    }
    
    fn geometric_product_lazy(
        &self,
        a: &SingleBlade<P>,
        b: &SingleBlade<P>,
    ) -> Result<LazyElement<P>, CcmError> {
        if a.dimension() != self.dimension || b.dimension() != self.dimension {
            return Err(CcmError::InvalidInput);
        }
        
        // For single blade product, result is also a single blade
        let result_blade = a.multiply(b)?;
        
        // Convert to lazy element
        let dimension = self.dimension;
        let result_index = result_blade.index.clone();
        let result_coeff = result_blade.coefficient();
        
        Ok(LazyElement::new(dimension, move |idx| {
            if idx == &result_index {
                result_coeff
            } else {
                Complex::zero()
            }
        }))
    }
    
    fn wedge_product_lazy(
        &self,
        a: &SingleBlade<P>,
        b: &SingleBlade<P>,
    ) -> Result<SingleBlade<P>, CcmError> {
        // For blades, wedge product is 0 if they share indices
        // Otherwise it's the same as geometric product
        
        // Check for shared indices by seeing if any bits overlap
        let a_bits = &a.index;
        let b_bits = &b.index;
        
        // If XOR gives same number of bits as sum, no overlap
        let xor_result = a_bits.xor(b_bits);
        if xor_result.count_ones() != a.grade() + b.grade() {
            // Overlapping indices, wedge product is zero
            Ok(SingleBlade::zero(self.dimension))
        } else {
            // No overlap, same as geometric product
            a.multiply(b)
        }
    }
    
    fn inner_product_lazy(
        &self,
        a: &SingleBlade<P>,
        b: &SingleBlade<P>,
    ) -> Result<LazyElement<P>, CcmError> {
        // Inner product of blades:
        // If |grade(a) - grade(b)| is the grade of result
        let grade_diff = (a.grade() as isize - b.grade() as isize).abs() as usize;
        
        let result_blade = a.multiply(b)?;
        if result_blade.grade() != grade_diff {
            // Result is zero
            let dimension = self.dimension;
            Ok(LazyElement::new(dimension, move |_| Complex::zero()))
        } else {
            let dimension = self.dimension;
            let result_index = result_blade.index().clone();
            let result_coeff = result_blade.coefficient();
            
            Ok(LazyElement::new(dimension, move |idx| {
                if idx == &result_index {
                    result_coeff
                } else {
                    Complex::zero()
                }
            }))
        }
    }
    
    fn coherence_inner_product_sparse(
        &self,
        a: &SparseCliffordElement<P>,
        b: &SparseCliffordElement<P>,
    ) -> Complex<P> {
        // For sparse elements, only non-zero components contribute
        let mut result = Complex::zero();
        
        // For small dimensions, check all components
        if self.dimension <= 20 {
            for i in 0..(1usize << self.dimension) {
                if let (Some(a_val), Some(b_val)) = (a.component(i), b.component(i)) {
                    result = result + a_val.conj() * b_val;
                }
            }
        } else {
            // For large dimensions, we need to extend SparseCliffordElement
            // to expose an iterator over non-zero components
            return Complex::zero();
        }
        
        result
    }
    
    fn grade_iterator(&self, grade: usize) -> GradeIterator<P> {
        GradeIterator::new(self.dimension, grade)
    }
    
    fn memory_usage_bytes(&self) -> usize {
        // Scalable algebra uses minimal memory
        core::mem::size_of::<Self>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_scalable_algebra_creation() {
        let algebra = ScalableAlgebra::<f64>::new(4096);
        assert_eq!(algebra.dimension(), 4096);
        assert_eq!(algebra.signature(), (4096, 0, 0));
    }
    
    #[test]
    fn test_grade_iterator() {
        let algebra = ScalableAlgebra::<f64>::new(5);
        
        // Test grade 2 elements (should be C(5,2) = 10 elements)
        let grade_2: Vec<_> = algebra.grade_iterator(2).collect();
        assert_eq!(grade_2.len(), 10);
        
        // Check first few elements
        assert_eq!(grade_2[0].grade(), 2);
        // First element should be e_0 ∧ e_1 (bits 0 and 1 set)
    }
    
    #[test]
    fn test_lazy_element() {
        let dimension = 64;
        let elem = LazyElement::new(dimension, |idx| {
            if idx.to_usize() == Some(5) {
                Complex::new(2.5, 0.0)
            } else {
                Complex::zero()
            }
        });
        
        let idx5 = BigIndex::from_usize(5, dimension);
        assert_eq!(elem.component(&idx5), Complex::new(2.5, 0.0));
    }
}