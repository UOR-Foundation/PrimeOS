//! Clifford algebra elements with complex coefficients

use ccm_core::{CcmError, Float};
use num_complex::Complex;
use num_traits::{One, Zero};

#[cfg(feature = "alloc")]
use alloc::{boxed::Box, vec::Vec};

/// A Clifford algebra element with complex coefficients
#[derive(Debug, PartialEq)]
pub struct CliffordElement<P: Float> {
    /// Coefficients for each basis element
    /// For n dimensions, there are 2^n basis elements
    pub(crate) components: Box<[Complex<P>]>,
    /// The dimension of the underlying vector space
    pub(crate) dimension: usize,
}

/// Type alias for a section in CCM (Clifford element at a point)
pub type Section<P> = CliffordElement<P>;

impl<P: Float> CliffordElement<P> {
    /// Create a new zero element in n-dimensional Clifford algebra
    pub fn zero(dimension: usize) -> Self {
        Self::zero_with_capacity(dimension, None)
    }
    
    /// Create a zero element with optional capacity limit
    /// If capacity is provided, creates a sparse-like element that only stores non-zero components
    pub fn zero_with_capacity(dimension: usize, max_capacity: Option<usize>) -> Self {
        // Check for overflow before shifting
        if dimension >= core::mem::size_of::<usize>() * 8 {
            // For very large dimensions, create a minimal element
            if let Some(capacity) = max_capacity {
                // Create with limited capacity - acts like a sparse element
                let components = vec![Complex::zero(); capacity.min(1024)].into_boxed_slice();
                return Self {
                    components,
                    dimension,
                };
            } else {
                panic!("Dimension {} is too large for dense storage. Use SparseCliffordElement or LazyCliffordAlgebra instead.", dimension);
            }
        }
        
        let num_components = 1usize << dimension; // 2^n
        
        // Additional safety check for memory allocation
        const MAX_COMPONENTS: usize = 1 << 20; // 1M components = 16MB for Complex<f64>
        if num_components > MAX_COMPONENTS {
            if let Some(capacity) = max_capacity {
                // Create with limited capacity
                let components = vec![Complex::zero(); capacity.min(MAX_COMPONENTS)].into_boxed_slice();
                return Self {
                    components,
                    dimension,
                };
            } else {
                panic!("Dimension {} requires {} components, exceeding the maximum of {}. Use SparseCliffordElement or LazyCliffordAlgebra instead.", 
                       dimension, num_components, MAX_COMPONENTS);
            }
        }
        
        let components = vec![Complex::zero(); num_components].into_boxed_slice();
        Self {
            components,
            dimension,
        }
    }

    /// Create a scalar element (grade 0)
    pub fn scalar(value: P, dimension: usize) -> Self {
        let mut element = Self::zero(dimension);
        element.components[0] = Complex::new(value, P::zero());
        element
    }

    /// Create from a list of real coefficients
    pub fn from_real_coefficients(coeffs: &[P], dimension: usize) -> Result<Self, CcmError> {
        let expected_len = 1usize << dimension;
        if coeffs.len() != expected_len {
            return Err(CcmError::InvalidLength);
        }

        let components: Vec<Complex<P>> =
            coeffs.iter().map(|&c| Complex::new(c, P::zero())).collect();

        Ok(Self {
            components: components.into_boxed_slice(),
            dimension,
        })
    }

    /// Get the dimension of the underlying vector space
    pub fn dimension(&self) -> usize {
        self.dimension
    }
    
    /// Check if this element is zero
    pub fn is_zero(&self) -> bool {
        for component in self.components.iter() {
            if component.norm_sqr() > P::epsilon() {
                return false;
            }
        }
        true
    }
    
    /// Compute coherence inner product with another element
    pub fn coherence_inner_product(&self, other: &Self) -> P {
        let complex_result = crate::metric::coherence_product(self, other);
        // For real-valued Clifford elements, the inner product is real
        complex_result.re
    }

    /// Get the number of components (2^n)
    pub fn num_components(&self) -> usize {
        self.components.len()
    }

    /// Get component by index
    pub fn component(&self, index: usize) -> Option<Complex<P>> {
        self.components.get(index).copied()
    }

    /// Set component by index
    pub fn set_component(&mut self, index: usize, value: Complex<P>) -> Result<(), CcmError> {
        if index >= self.components.len() {
            return Err(CcmError::InvalidInput);
        }
        self.components[index] = value;
        Ok(())
    }

    /// Get the grade of a basis element by its index
    pub fn grade_of_index(index: usize) -> usize {
        // The grade is the number of 1s in the binary representation
        index.count_ones() as usize
    }

    /// Check if the norm is finite (required constraint)
    pub fn norm_finite(&self) -> bool {
        self.components.iter().all(|c| {
            let norm_sq = c.norm_sqr();
            norm_sq.is_finite() && norm_sq >= P::zero()
        })
    }

    /// Get all indices that correspond to a specific grade
    pub fn indices_of_grade(grade: usize, dimension: usize) -> Vec<usize> {
        // Check for overflow before shifting
        if dimension >= core::mem::size_of::<usize>() * 8 {
            panic!("Dimension {} is too large for index enumeration", dimension);
        }
        
        let max_index = 1usize << dimension;
        (0..max_index)
            .filter(|&i| Self::grade_of_index(i) == grade)
            .collect()
    }

    /// Create a basis vector e_i
    pub fn basis_vector(i: usize, dimension: usize) -> Result<Self, CcmError> {
        if i >= dimension {
            return Err(CcmError::InvalidInput);
        }

        let mut element = Self::zero(dimension);
        // e_i has index 2^i in the basis ordering
        let index = 1usize << i;
        element.components[index] = Complex::one();
        Ok(element)
    }

    /// Create a basis blade from multiple indices
    /// For example, e_1 ∧ e_2 has indices [1, 2]
    pub fn basis_blade(indices: &[usize], dimension: usize) -> Result<Self, CcmError> {
        // Check all indices are valid and unique
        for &i in indices {
            if i >= dimension {
                return Err(CcmError::InvalidInput);
            }
        }

        // Convert indices to bit pattern
        let mut bit_pattern = 0usize;
        for &i in indices {
            if bit_pattern & (1 << i) != 0 {
                // Repeated index
                return Err(CcmError::InvalidInput);
            }
            bit_pattern |= 1 << i;
        }

        let mut element = Self::zero(dimension);
        element.components[bit_pattern] = Complex::one();
        Ok(element)
    }

    /// Check if this element is sparse (most components are zero)
    pub fn is_sparse(&self, threshold: P) -> bool {
        let non_zero_count = self
            .components
            .iter()
            .filter(|c| c.norm_sqr() > threshold)
            .count();

        // Consider sparse if less than 10% of components are non-zero
        non_zero_count < self.components.len() / 10
    }
}

// Arithmetic operations
use core::ops::{Add, Mul, Neg, Sub};

impl<P: Float> Add for CliffordElement<P> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        if self.dimension != rhs.dimension {
            panic!("Cannot add Clifford elements of different dimensions");
        }

        let mut result = self.clone();
        for i in 0..result.components.len() {
            result.components[i] = result.components[i] + rhs.components[i];
        }
        result
    }
}

impl<P: Float> Sub for CliffordElement<P> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        if self.dimension != rhs.dimension {
            panic!("Cannot subtract Clifford elements of different dimensions");
        }

        let mut result = self.clone();
        for i in 0..result.components.len() {
            result.components[i] = result.components[i] - rhs.components[i];
        }
        result
    }
}

impl<P: Float> Neg for CliffordElement<P> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let mut result = self.clone();
        for i in 0..result.components.len() {
            result.components[i] = -result.components[i];
        }
        result
    }
}

impl<P: Float> Mul<P> for CliffordElement<P> {
    type Output = Self;

    fn mul(self, scalar: P) -> Self::Output {
        let mut result = self.clone();
        for i in 0..result.components.len() {
            result.components[i] = result.components[i].scale(scalar);
        }
        result
    }
}

impl<P: Float> Mul<Complex<P>> for CliffordElement<P> {
    type Output = Self;

    fn mul(self, scalar: Complex<P>) -> Self::Output {
        let mut result = self.clone();
        for i in 0..result.components.len() {
            result.components[i] = result.components[i] * scalar;
        }
        result
    }
}

// Implement Clone manually to ensure deep copy
impl<P: Float> Clone for CliffordElement<P> {
    fn clone(&self) -> Self {
        Self {
            components: self.components.clone(),
            dimension: self.dimension,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zero_element() {
        let elem = CliffordElement::<f64>::zero(3);
        assert_eq!(elem.dimension(), 3);
        assert_eq!(elem.num_components(), 8); // 2^3
        assert_eq!(elem.component(0), Some(Complex::zero()));
    }

    #[test]
    fn test_scalar_element() {
        let elem = CliffordElement::scalar(2.5, 3);
        assert_eq!(elem.component(0), Some(Complex::new(2.5, 0.0)));
        for i in 1..8 {
            assert_eq!(elem.component(i), Some(Complex::zero()));
        }
    }

    #[test]
    fn test_basis_vector() {
        let e1 = CliffordElement::<f64>::basis_vector(0, 3).unwrap();
        assert_eq!(e1.component(1), Some(Complex::one())); // 2^0 = 1

        let e2 = CliffordElement::<f64>::basis_vector(1, 3).unwrap();
        assert_eq!(e2.component(2), Some(Complex::one())); // 2^1 = 2

        let e3 = CliffordElement::<f64>::basis_vector(2, 3).unwrap();
        assert_eq!(e3.component(4), Some(Complex::one())); // 2^2 = 4
    }

    #[test]
    fn test_basis_blade() {
        // e1 ∧ e2 in 3D
        let e12 = CliffordElement::<f64>::basis_blade(&[0, 1], 3).unwrap();
        assert_eq!(e12.component(3), Some(Complex::one())); // binary 011 = 3

        // e1 ∧ e2 ∧ e3
        let e123 = CliffordElement::<f64>::basis_blade(&[0, 1, 2], 3).unwrap();
        assert_eq!(e123.component(7), Some(Complex::one())); // binary 111 = 7
    }

    #[test]
    fn test_grade_of_index() {
        assert_eq!(CliffordElement::<f64>::grade_of_index(0), 0); // scalar
        assert_eq!(CliffordElement::<f64>::grade_of_index(1), 1); // e1
        assert_eq!(CliffordElement::<f64>::grade_of_index(3), 2); // e1e2
        assert_eq!(CliffordElement::<f64>::grade_of_index(7), 3); // e1e2e3
    }

    #[test]
    fn test_indices_of_grade() {
        let grade_1 = CliffordElement::<f64>::indices_of_grade(1, 3);
        assert_eq!(grade_1, vec![1, 2, 4]); // e1, e2, e3

        let grade_2 = CliffordElement::<f64>::indices_of_grade(2, 3);
        assert_eq!(grade_2, vec![3, 5, 6]); // e1e2, e1e3, e2e3
    }
}
