//! Sparse representation for Clifford elements

use ccm_core::{CcmError, Float};
use num_complex::Complex;
#[allow(unused_imports)]
use num_traits::{One, Zero};

#[cfg(feature = "alloc")]
use alloc::collections::BTreeMap;

#[cfg(not(feature = "alloc"))]
use core::array;

/// Sparse representation of a Clifford element
/// Only stores non-zero components
#[derive(Debug, Clone, PartialEq)]
pub struct SparseCliffordElement<P: Float> {
    /// Non-zero components indexed by basis element
    #[cfg(feature = "alloc")]
    components: BTreeMap<usize, Complex<P>>,

    /// Fixed-size storage for no_std environments
    #[cfg(not(feature = "alloc"))]
    components: [(usize, Complex<P>); 32],

    #[cfg(not(feature = "alloc"))]
    len: usize,

    /// The dimension of the underlying vector space
    dimension: usize,
}

impl<P: Float> SparseCliffordElement<P> {
    /// Create a new zero element
    pub fn zero(dimension: usize) -> Self {
        Self {
            #[cfg(feature = "alloc")]
            components: BTreeMap::new(),
            #[cfg(not(feature = "alloc"))]
            components: array::from_fn(|_| (0, Complex::zero())),
            #[cfg(not(feature = "alloc"))]
            len: 0,
            dimension,
        }
    }

    /// Create a scalar element
    pub fn scalar(value: P, dimension: usize) -> Self {
        let mut element = Self::zero(dimension);
        element
            .set_component(0, Complex::new(value, P::zero()))
            .unwrap();
        element
    }

    /// Get the dimension
    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// Get a component by index
    pub fn component(&self, index: usize) -> Option<Complex<P>> {
        #[cfg(feature = "alloc")]
        {
            self.components.get(&index).copied()
        }

        #[cfg(not(feature = "alloc"))]
        {
            for i in 0..self.len {
                if self.components[i].0 == index {
                    return Some(self.components[i].1);
                }
            }
            None
        }
    }

    /// Set a component by index
    pub fn set_component(&mut self, index: usize, value: Complex<P>) -> Result<(), CcmError> {
        // For large dimensions, we can't check against 2^n
        // Instead, check if the index could be valid based on dimension
        if self.dimension < 64 && index >= (1usize << self.dimension) {
            return Err(CcmError::InvalidInput);
        }

        // Only store non-zero components
        if value.norm_sqr() < P::epsilon() {
            self.remove_component(index);
            return Ok(());
        }

        #[cfg(feature = "alloc")]
        {
            self.components.insert(index, value);
        }

        #[cfg(not(feature = "alloc"))]
        {
            // Check if component already exists
            for i in 0..self.len {
                if self.components[i].0 == index {
                    self.components[i].1 = value;
                    return Ok(());
                }
            }

            // Add new component if space available
            if self.len < 32 {
                self.components[self.len] = (index, value);
                self.len += 1;
            } else {
                return Err(CcmError::InvalidLength);
            }
        }

        Ok(())
    }

    /// Remove a component
    pub fn remove_component(&mut self, index: usize) {
        #[cfg(feature = "alloc")]
        {
            self.components.remove(&index);
        }

        #[cfg(not(feature = "alloc"))]
        {
            let mut found = false;
            let mut pos = 0;

            for i in 0..self.len {
                if self.components[i].0 == index {
                    found = true;
                    pos = i;
                    break;
                }
            }

            if found && pos < self.len - 1 {
                // Shift elements left
                for i in pos..self.len - 1 {
                    self.components[i] = self.components[i + 1];
                }
                self.len -= 1;
            } else if found {
                self.len -= 1;
            }
        }
    }

    /// Get the number of non-zero components
    pub fn nnz(&self) -> usize {
        #[cfg(feature = "alloc")]
        {
            self.components.len()
        }

        #[cfg(not(feature = "alloc"))]
        {
            self.len
        }
    }

    /// Check if the element is sparse (less than 10% non-zero)
    pub fn is_sparse(&self) -> bool {
        let total_components = 1usize << self.dimension;
        self.nnz() < total_components / 10
    }

    /// Iterate over non-zero components
    #[cfg(feature = "alloc")]
    pub fn iter(&self) -> impl Iterator<Item = (usize, Complex<P>)> + '_ {
        self.components.iter().map(|(&idx, &val)| (idx, val))
    }

    /// Iterate over non-zero components (no_std version)
    #[cfg(not(feature = "alloc"))]
    pub fn iter(&self) -> impl Iterator<Item = (usize, Complex<P>)> + '_ {
        (0..self.len).map(move |i| (self.components[i].0, self.components[i].1))
    }

    /// Convert to dense representation
    pub fn to_dense(&self) -> crate::element::CliffordElement<P> {
        use crate::element::CliffordElement;

        let mut dense = CliffordElement::zero(self.dimension);

        #[cfg(feature = "alloc")]
        {
            for (&index, &value) in &self.components {
                dense.set_component(index, value).unwrap();
            }
        }

        #[cfg(not(feature = "alloc"))]
        {
            for i in 0..self.len {
                let (index, value) = self.components[i];
                dense.set_component(index, value).unwrap();
            }
        }

        dense
    }

    /// Create from dense representation
    pub fn from_dense(dense: &crate::element::CliffordElement<P>) -> Self {
        let mut sparse = Self::zero(dense.dimension());

        for i in 0..dense.num_components() {
            if let Some(value) = dense.component(i) {
                if value.norm_sqr() > P::epsilon() {
                    sparse.set_component(i, value).unwrap();
                }
            }
        }

        sparse
    }

    /// Create a basis vector
    pub fn basis_vector(i: usize, dimension: usize) -> Result<Self, CcmError> {
        if i >= dimension {
            return Err(CcmError::InvalidInput);
        }

        let mut element = Self::zero(dimension);
        // Check for overflow before shifting
        if i >= 64 {
            return Err(CcmError::Custom("Basis vector index too large for sparse storage"));
        }
        let index = 1usize << i;
        element.set_component(index, Complex::one())?;
        Ok(element)
    }

    /// Create a basis blade
    pub fn basis_blade(indices: &[usize], dimension: usize) -> Result<Self, CcmError> {
        // Check all indices are valid
        for &i in indices {
            if i >= dimension {
                return Err(CcmError::InvalidInput);
            }
        }

        // Convert indices to bit pattern
        let mut bit_pattern = 0usize;
        for &i in indices {
            if i >= 64 {
                return Err(CcmError::Custom("Basis blade index too large for sparse storage"));
            }
            if bit_pattern & (1 << i) != 0 {
                // Repeated index
                return Err(CcmError::InvalidInput);
            }
            bit_pattern |= 1 << i;
        }

        let mut element = Self::zero(dimension);
        element.set_component(bit_pattern, Complex::one())?;
        Ok(element)
    }
}

// Arithmetic operations
use core::ops::{Add, Mul, Neg, Sub};

impl<P: Float> Add for SparseCliffordElement<P> {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        if self.dimension != rhs.dimension {
            panic!("Cannot add Clifford elements of different dimensions");
        }

        #[cfg(feature = "alloc")]
        {
            for (index, value) in rhs.components {
                if let Some(existing) = self.components.get_mut(&index) {
                    *existing = *existing + value;
                    if existing.norm_sqr() < P::epsilon() {
                        self.components.remove(&index);
                    }
                } else {
                    self.components.insert(index, value);
                }
            }
        }

        #[cfg(not(feature = "alloc"))]
        {
            for i in 0..rhs.len {
                let (index, value) = rhs.components[i];

                // Try to find existing component
                let mut found = false;
                for j in 0..self.len {
                    if self.components[j].0 == index {
                        self.components[j].1 = self.components[j].1 + value;
                        if self.components[j].1.norm_sqr() < P::epsilon() {
                            self.remove_component(index);
                        }
                        found = true;
                        break;
                    }
                }

                if !found && self.len < 32 {
                    self.components[self.len] = (index, value);
                    self.len += 1;
                }
            }
        }

        self
    }
}

impl<P: Float> Sub for SparseCliffordElement<P> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl<P: Float> Neg for SparseCliffordElement<P> {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        #[cfg(feature = "alloc")]
        {
            for value in self.components.values_mut() {
                *value = -*value;
            }
        }

        #[cfg(not(feature = "alloc"))]
        {
            for i in 0..self.len {
                self.components[i].1 = -self.components[i].1;
            }
        }

        self
    }
}

impl<P: Float> Mul<P> for SparseCliffordElement<P> {
    type Output = Self;

    fn mul(mut self, scalar: P) -> Self::Output {
        if scalar.abs() < P::epsilon() {
            return Self::zero(self.dimension);
        }

        #[cfg(feature = "alloc")]
        {
            for value in self.components.values_mut() {
                *value = value.scale(scalar);
            }
        }

        #[cfg(not(feature = "alloc"))]
        {
            for i in 0..self.len {
                self.components[i].1 = self.components[i].1.scale(scalar);
            }
        }

        self
    }
}

impl<P: Float> Mul<Complex<P>> for SparseCliffordElement<P> {
    type Output = Self;

    fn mul(mut self, scalar: Complex<P>) -> Self::Output {
        if scalar.norm_sqr() < P::epsilon() {
            return Self::zero(self.dimension);
        }

        #[cfg(feature = "alloc")]
        {
            for value in self.components.values_mut() {
                *value = *value * scalar;
            }
        }

        #[cfg(not(feature = "alloc"))]
        {
            for i in 0..self.len {
                self.components[i].1 = self.components[i].1 * scalar;
            }
        }

        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sparse_creation() {
        let sparse = SparseCliffordElement::<f64>::zero(3);
        assert_eq!(sparse.dimension(), 3);
        assert_eq!(sparse.nnz(), 0);
        assert_eq!(sparse.component(0), None);
    }

    #[test]
    fn test_sparse_scalar() {
        let sparse = SparseCliffordElement::scalar(2.5, 3);
        assert_eq!(sparse.nnz(), 1);
        assert_eq!(sparse.component(0), Some(Complex::new(2.5, 0.0)));
        assert_eq!(sparse.component(1), None);
    }

    #[test]
    fn test_sparse_set_component() {
        let mut sparse = SparseCliffordElement::<f64>::zero(3);

        sparse.set_component(3, Complex::new(1.5, 0.0)).unwrap();
        assert_eq!(sparse.nnz(), 1);
        assert_eq!(sparse.component(3), Some(Complex::new(1.5, 0.0)));

        // Setting to zero should remove component
        sparse.set_component(3, Complex::zero()).unwrap();
        assert_eq!(sparse.nnz(), 0);
        assert_eq!(sparse.component(3), None);
    }

    #[test]
    fn test_sparse_dense_conversion() {
        let mut sparse = SparseCliffordElement::<f64>::zero(3);
        sparse.set_component(1, Complex::one()).unwrap();
        sparse.set_component(5, Complex::new(2.0, 0.0)).unwrap();

        let dense = sparse.to_dense();
        assert_eq!(dense.component(1), Some(Complex::one()));
        assert_eq!(dense.component(5), Some(Complex::new(2.0, 0.0)));
        assert_eq!(dense.component(0), Some(Complex::zero()));

        let sparse2 = SparseCliffordElement::from_dense(&dense);
        assert_eq!(sparse2.nnz(), 2);
        assert_eq!(sparse2.component(1), Some(Complex::one()));
        assert_eq!(sparse2.component(5), Some(Complex::new(2.0, 0.0)));
    }

    #[test]
    fn test_sparse_arithmetic() {
        let mut a = SparseCliffordElement::<f64>::zero(3);
        a.set_component(1, Complex::one()).unwrap();
        a.set_component(3, Complex::new(2.0, 0.0)).unwrap();

        let mut b = SparseCliffordElement::<f64>::zero(3);
        b.set_component(1, Complex::new(0.5, 0.0)).unwrap();
        b.set_component(4, Complex::new(1.0, 0.0)).unwrap();

        let sum = a.clone() + b.clone();
        assert_eq!(sum.component(1), Some(Complex::new(1.5, 0.0)));
        assert_eq!(sum.component(3), Some(Complex::new(2.0, 0.0)));
        assert_eq!(sum.component(4), Some(Complex::new(1.0, 0.0)));
        assert_eq!(sum.nnz(), 3);

        let diff = a - b;
        assert_eq!(diff.component(1), Some(Complex::new(0.5, 0.0)));
        assert_eq!(diff.component(4), Some(Complex::new(-1.0, 0.0)));
    }

    #[test]
    fn test_sparse_basis_elements() {
        let e1 = SparseCliffordElement::<f64>::basis_vector(0, 3).unwrap();
        assert_eq!(e1.nnz(), 1);
        assert_eq!(e1.component(1), Some(Complex::one()));

        let e12 = SparseCliffordElement::<f64>::basis_blade(&[0, 1], 3).unwrap();
        assert_eq!(e12.nnz(), 1);
        assert_eq!(e12.component(3), Some(Complex::one()));
    }
}
