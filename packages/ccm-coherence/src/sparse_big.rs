//! Sparse Clifford element with BigIndex support for arbitrary dimensions
//!
//! This module extends sparse storage to support dimensions beyond 64 bits.

use crate::arbitrary_support::BigIndex;
use ccm_core::{CcmError, Float};
use num_complex::Complex;
use num_traits::{Zero, One};

#[cfg(feature = "alloc")]
use alloc::collections::BTreeMap;

/// Sparse Clifford element that can handle arbitrary dimension indices
#[derive(Debug, Clone, PartialEq)]
pub struct SparseBigElement<P: Float> {
    /// Non-zero components stored as (BigIndex, Complex<P>) pairs
    #[cfg(feature = "alloc")]
    components: BTreeMap<Vec<u8>, Complex<P>>, // Key is BigIndex serialized as bytes
    
    /// Fixed-size storage for no_std environments
    #[cfg(not(feature = "alloc"))]
    components: [(Vec<u8>, Complex<P>); 128], // Increased from 32 to 128
    
    #[cfg(not(feature = "alloc"))]
    num_components: usize,
    
    /// The dimension of the space
    dimension: usize,
}

impl<P: Float> SparseBigElement<P> {
    /// Create a zero element
    pub fn zero(dimension: usize) -> Self {
        Self {
            #[cfg(feature = "alloc")]
            components: BTreeMap::new(),
            #[cfg(not(feature = "alloc"))]
            components: core::array::from_fn(|_| (Vec::new(), Complex::zero())),
            #[cfg(not(feature = "alloc"))]
            num_components: 0,
            dimension,
        }
    }
    
    /// Create a scalar element
    pub fn scalar(value: P, dimension: usize) -> Self {
        let mut element = Self::zero(dimension);
        let scalar_index = BigIndex::new(dimension);
        element.set_component(&scalar_index, Complex::new(value, P::zero())).unwrap();
        element
    }
    
    /// Get dimension
    pub fn dimension(&self) -> usize {
        self.dimension
    }
    
    /// Set a component by BigIndex
    pub fn set_component(&mut self, index: &BigIndex, value: Complex<P>) -> Result<(), CcmError> {
        if value.norm_sqr() < P::epsilon() {
            // Remove zero components
            self.remove_component(index);
            return Ok(());
        }
        
        let key = index.to_bytes();
        
        #[cfg(feature = "alloc")]
        {
            self.components.insert(key, value);
            Ok(())
        }
        
        #[cfg(not(feature = "alloc"))]
        {
            // Find existing or add new
            for i in 0..self.num_components {
                if self.components[i].0 == key {
                    self.components[i].1 = value;
                    return Ok(());
                }
            }
            
            // Add new component
            if self.num_components >= 128 {
                return Err(CcmError::Custom("Sparse element full (128 components)"));
            }
            
            self.components[self.num_components] = (key, value);
            self.num_components += 1;
            Ok(())
        }
    }
    
    /// Get a component by BigIndex
    pub fn component(&self, index: &BigIndex) -> Option<Complex<P>> {
        let key = index.to_bytes();
        
        #[cfg(feature = "alloc")]
        {
            self.components.get(&key).copied()
        }
        
        #[cfg(not(feature = "alloc"))]
        {
            for i in 0..self.num_components {
                if self.components[i].0 == key {
                    return Some(self.components[i].1);
                }
            }
            None
        }
    }
    
    /// Remove a component
    fn remove_component(&mut self, index: &BigIndex) {
        let key = index.to_bytes();
        
        #[cfg(feature = "alloc")]
        {
            self.components.remove(&key);
        }
        
        #[cfg(not(feature = "alloc"))]
        {
            // Find and remove by shifting remaining elements
            let mut found = false;
            for i in 0..self.num_components {
                if found {
                    if i < 127 {
                        self.components[i] = self.components[i + 1].clone();
                    }
                } else if self.components[i].0 == key {
                    found = true;
                    if i < self.num_components - 1 {
                        self.components[i] = self.components[i + 1].clone();
                    }
                }
            }
            if found {
                self.num_components -= 1;
            }
        }
    }
    
    /// Get number of non-zero components
    pub fn nnz(&self) -> usize {
        #[cfg(feature = "alloc")]
        {
            self.components.len()
        }
        
        #[cfg(not(feature = "alloc"))]
        {
            self.num_components
        }
    }
    
    /// Check if this element is zero
    pub fn is_zero(&self) -> bool {
        self.nnz() == 0
    }
    
    /// Create from a single blade
    pub fn from_blade(blade: &crate::SingleBlade<P>) -> Self {
        let mut element = Self::zero(blade.dimension());
        element.set_component(&blade.index, blade.coefficient()).unwrap();
        element
    }
    
    /// Iterate over non-zero components
    #[cfg(feature = "alloc")]
    pub fn iter(&self) -> impl Iterator<Item = (BigIndex, Complex<P>)> + '_ {
        self.components.iter().map(|(key, &value)| {
            let index = BigIndex::from_bytes(key, self.dimension);
            (index, value)
        })
    }
    
    /// Add another sparse element
    pub fn add_assign(&mut self, other: &Self) -> Result<(), CcmError> {
        if self.dimension != other.dimension {
            return Err(CcmError::InvalidInput);
        }
        
        #[cfg(feature = "alloc")]
        {
            for (index, value) in other.iter() {
                let current = self.component(&index).unwrap_or(Complex::zero());
                self.set_component(&index, current + value)?;
            }
        }
        
        #[cfg(not(feature = "alloc"))]
        {
            // For no_std, we need to be careful about capacity
            for i in 0..other.num_components {
                let key = &other.components[i].0;
                let value = other.components[i].1;
                let index = BigIndex::from_bytes(key, self.dimension);
                let current = self.component(&index).unwrap_or(Complex::zero());
                self.set_component(&index, current + value)?;
            }
        }
        
        Ok(())
    }
    
    /// Scale by a scalar
    pub fn scale(&mut self, scalar: P) {
        if scalar.abs() < P::epsilon() {
            // Scaling by zero clears the element
            *self = Self::zero(self.dimension);
            return;
        }
        
        #[cfg(feature = "alloc")]
        {
            for value in self.components.values_mut() {
                *value = value.scale(scalar);
            }
        }
        
        #[cfg(not(feature = "alloc"))]
        {
            for i in 0..self.num_components {
                self.components[i].1 = self.components[i].1.scale(scalar);
            }
        }
    }
    
    /// Compute coherence norm squared
    pub fn coherence_norm_squared(&self) -> P {
        let mut sum = P::zero();
        
        #[cfg(feature = "alloc")]
        {
            for value in self.components.values() {
                sum = sum + value.norm_sqr();
            }
        }
        
        #[cfg(not(feature = "alloc"))]
        {
            for i in 0..self.num_components {
                sum = sum + self.components[i].1.norm_sqr();
            }
        }
        
        sum
    }
    
    /// Compute coherence norm
    pub fn coherence_norm(&self) -> P {
        self.coherence_norm_squared().sqrt()
    }
    
    /// Create a basis vector e_i
    pub fn basis_vector(i: usize, dimension: usize) -> Result<Self, CcmError> {
        if i >= dimension {
            return Err(CcmError::InvalidInput);
        }
        
        let mut element = Self::zero(dimension);
        let mut index = BigIndex::new(dimension);
        index.set_bit(i);
        element.set_component(&index, Complex::one())?;
        Ok(element)
    }
    
    /// Create a basis blade from multiple indices
    pub fn basis_blade(indices: &[usize], dimension: usize) -> Result<Self, CcmError> {
        // Check all indices are valid and unique
        for &i in indices {
            if i >= dimension {
                return Err(CcmError::InvalidInput);
            }
        }
        
        // Check for duplicates
        let mut sorted = indices.to_vec();
        sorted.sort_unstable();
        for i in 1..sorted.len() {
            if sorted[i] == sorted[i-1] {
                return Err(CcmError::InvalidInput);
            }
        }
        
        let mut element = Self::zero(dimension);
        let mut index = BigIndex::new(dimension);
        for &i in indices {
            index.set_bit(i);
        }
        element.set_component(&index, Complex::one())?;
        Ok(element)
    }
}

// Arithmetic trait implementations
use core::ops::{Add, Sub, Neg, Mul};

impl<P: Float> Add for SparseBigElement<P> {
    type Output = Self;
    
    fn add(mut self, rhs: Self) -> Self::Output {
        // Use the add_assign method, ignore error (dimension mismatch would panic)
        let _ = self.add_assign(&rhs);
        self
    }
}

impl<P: Float> Sub for SparseBigElement<P> {
    type Output = Self;
    
    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl<P: Float> Neg for SparseBigElement<P> {
    type Output = Self;
    
    fn neg(mut self) -> Self::Output {
        self.scale(-P::one());
        self
    }
}

impl<P: Float> Mul<P> for SparseBigElement<P> {
    type Output = Self;
    
    fn mul(mut self, scalar: P) -> Self::Output {
        self.scale(scalar);
        self
    }
}

impl<P: Float> Mul<Complex<P>> for SparseBigElement<P> {
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
            for i in 0..self.num_components {
                self.components[i].1 = self.components[i].1 * scalar;
            }
        }
        
        self
    }
}

impl<P: Float> Mul for SparseBigElement<P> {
    type Output = Self;
    
    fn mul(self, rhs: Self) -> Self::Output {
        // Use the geometric_product method
        self.geometric_product(&rhs).unwrap_or_else(|_| Self::zero(self.dimension))
    }
}

impl<P: Float> SparseBigElement<P> {
    /// Compute the geometric product of two sparse elements
    /// 
    /// The geometric product satisfies:
    /// - e_i * e_i = 1 (or -1 depending on metric)
    /// - e_i * e_j = -e_j * e_i for i ≠ j
    /// 
    /// For basis blades: (e_I)(e_J) = sign(I,J) * e_(I XOR J)
    pub fn geometric_product(&self, other: &Self) -> Result<Self, CcmError> {
        if self.dimension != other.dimension {
            return Err(CcmError::InvalidInput);
        }
        
        let mut result = Self::zero(self.dimension);
        
        #[cfg(feature = "alloc")]
        {
            // Iterate through all pairs of components
            for (idx_a, val_a) in self.iter() {
                for (idx_b, val_b) in other.iter() {
                    // Result index is XOR of input indices
                    let result_idx = idx_a.xor(&idx_b);
                    
                    // Compute sign from basis vector reordering
                    let sign = BigIndex::compute_sign::<P>(&idx_a, &idx_b);
                    
                    // Add contribution to result
                    let contribution = val_a * val_b * Complex::new(sign, P::zero());
                    let current = result.component(&result_idx).unwrap_or(Complex::zero());
                    result.set_component(&result_idx, current + contribution)?;
                }
            }
        }
        
        #[cfg(not(feature = "alloc"))]
        {
            // For no_std, iterate through array components
            for i in 0..self.num_components {
                let idx_a = BigIndex::from_bytes(&self.components[i].0, self.dimension);
                let val_a = self.components[i].1;
                
                for j in 0..other.num_components {
                    let idx_b = BigIndex::from_bytes(&other.components[j].0, other.dimension);
                    let val_b = other.components[j].1;
                    
                    // Result index is XOR of input indices
                    let result_idx = idx_a.xor(&idx_b);
                    
                    // Compute sign from basis vector reordering
                    let sign = BigIndex::compute_sign::<P>(&idx_a, &idx_b);
                    
                    // Add contribution to result
                    let contribution = val_a * val_b * Complex::new(sign, P::zero());
                    let current = result.component(&result_idx).unwrap_or(Complex::zero());
                    result.set_component(&result_idx, current + contribution)?;
                }
            }
        }
        
        Ok(result)
    }
    
    /// Compute the wedge (outer) product of two sparse elements
    /// 
    /// The wedge product is the antisymmetric part of the geometric product.
    /// For blades a and b: a ∧ b = 0 if they share any basis vectors
    pub fn wedge_product(&self, other: &Self) -> Result<Self, CcmError> {
        if self.dimension != other.dimension {
            return Err(CcmError::InvalidInput);
        }
        
        let mut result = Self::zero(self.dimension);
        
        #[cfg(feature = "alloc")]
        {
            for (idx_a, val_a) in self.iter() {
                for (idx_b, val_b) in other.iter() {
                    // Check if indices share any basis vectors
                    let intersection = idx_a.and(&idx_b);
                    if !intersection.is_zero() {
                        // Shared basis vectors means wedge product is zero
                        continue;
                    }
                    
                    // Result index is XOR (which equals OR when no overlap)
                    let result_idx = idx_a.xor(&idx_b);
                    
                    // Compute sign
                    let sign = BigIndex::compute_sign::<P>(&idx_a, &idx_b);
                    
                    // Add contribution
                    let contribution = val_a * val_b * Complex::new(sign, P::zero());
                    let current = result.component(&result_idx).unwrap_or(Complex::zero());
                    result.set_component(&result_idx, current + contribution)?;
                }
            }
        }
        
        #[cfg(not(feature = "alloc"))]
        {
            for i in 0..self.num_components {
                let idx_a = BigIndex::from_bytes(&self.components[i].0, self.dimension);
                let val_a = self.components[i].1;
                
                for j in 0..other.num_components {
                    let idx_b = BigIndex::from_bytes(&other.components[j].0, other.dimension);
                    let val_b = other.components[j].1;
                    
                    // Check if indices share any basis vectors
                    let intersection = idx_a.and(&idx_b);
                    if !intersection.is_zero() {
                        continue;
                    }
                    
                    let result_idx = idx_a.xor(&idx_b);
                    let sign = BigIndex::compute_sign::<P>(&idx_a, &idx_b);
                    
                    let contribution = val_a * val_b * Complex::new(sign, P::zero());
                    let current = result.component(&result_idx).unwrap_or(Complex::zero());
                    result.set_component(&result_idx, current + contribution)?;
                }
            }
        }
        
        Ok(result)
    }
}

// Add serialization helpers for BigIndex
impl BigIndex {
    /// Convert to byte representation for use as map key
    pub fn to_bytes(&self) -> Vec<u8> {
        self.bits.clone()
    }
    
    /// Create from byte representation
    pub fn from_bytes(bytes: &[u8], bit_count: usize) -> Self {
        Self {
            bits: bytes.to_vec(),
            bit_count,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_sparse_big_creation() {
        let elem = SparseBigElement::<f64>::zero(4096);
        assert_eq!(elem.dimension(), 4096);
        assert!(elem.is_zero());
    }
    
    #[test]
    fn test_sparse_big_set_component() {
        let mut elem = SparseBigElement::<f64>::zero(1024);
        
        // Set component at index with bits 100, 200, 300 set
        let mut index = BigIndex::new(1024);
        index.set_bit(100);
        index.set_bit(200);
        index.set_bit(300);
        
        elem.set_component(&index, Complex::new(2.5, 0.0)).unwrap();
        assert_eq!(elem.nnz(), 1);
        assert_eq!(elem.component(&index), Some(Complex::new(2.5, 0.0)));
    }
    
    #[test]
    fn test_sparse_big_arithmetic() {
        let mut a = SparseBigElement::<f64>::zero(512);
        let mut b = SparseBigElement::<f64>::zero(512);
        
        let mut idx1 = BigIndex::new(512);
        idx1.set_bit(10);
        idx1.set_bit(20);
        
        let mut idx2 = BigIndex::new(512);
        idx2.set_bit(30);
        idx2.set_bit(40);
        
        a.set_component(&idx1, Complex::new(1.0, 0.0)).unwrap();
        b.set_component(&idx2, Complex::new(2.0, 0.0)).unwrap();
        
        // Add b to a
        a.add_assign(&b).unwrap();
        assert_eq!(a.nnz(), 2);
        assert_eq!(a.component(&idx1), Some(Complex::new(1.0, 0.0)));
        assert_eq!(a.component(&idx2), Some(Complex::new(2.0, 0.0)));
    }
    
    #[test]
    fn test_sparse_big_scale() {
        let mut elem = SparseBigElement::<f64>::zero(256);
        
        let mut index = BigIndex::new(256);
        index.set_bit(50);
        
        elem.set_component(&index, Complex::new(3.0, 0.0)).unwrap();
        elem.scale(2.0);
        
        assert_eq!(elem.component(&index), Some(Complex::new(6.0, 0.0)));
    }
    
    #[test]
    fn test_large_dimension_4096() {
        // Test with 4096-bit dimension
        let dimension = 4096;
        let mut elem = SparseBigElement::<f64>::zero(dimension);
        
        // Set components at very large indices
        let mut idx1 = BigIndex::new(dimension);
        idx1.set_bit(1000);
        idx1.set_bit(2000);
        idx1.set_bit(3000);
        
        let mut idx2 = BigIndex::new(dimension);
        idx2.set_bit(500);
        idx2.set_bit(1500);
        idx2.set_bit(2500);
        idx2.set_bit(3500);
        
        elem.set_component(&idx1, Complex::new(1.5, 0.0)).unwrap();
        elem.set_component(&idx2, Complex::new(2.5, 0.0)).unwrap();
        
        assert_eq!(elem.nnz(), 2);
        assert_eq!(elem.dimension(), 4096);
        
        // Test coherence norm
        let expected_norm_sq = 1.5 * 1.5 + 2.5 * 2.5;
        assert!((elem.coherence_norm_squared() - expected_norm_sq).abs() < 1e-10);
    }
    
    #[test]
    fn test_basis_creation() {
        let dimension = 1024;
        
        // Test basis vector
        let e100 = SparseBigElement::<f64>::basis_vector(100, dimension).unwrap();
        assert_eq!(e100.nnz(), 1);
        let mut expected_idx = BigIndex::new(dimension);
        expected_idx.set_bit(100);
        assert_eq!(e100.component(&expected_idx), Some(Complex::one()));
        
        // Test basis blade
        let e_multi = SparseBigElement::<f64>::basis_blade(&[10, 20, 30], dimension).unwrap();
        assert_eq!(e_multi.nnz(), 1);
        let mut expected_blade = BigIndex::new(dimension);
        expected_blade.set_bit(10);
        expected_blade.set_bit(20);
        expected_blade.set_bit(30);
        assert_eq!(e_multi.component(&expected_blade), Some(Complex::one()));
    }
    
    #[test]
    fn test_arithmetic_traits() {
        let dimension = 512;
        let mut a = SparseBigElement::<f64>::zero(dimension);
        let mut b = SparseBigElement::<f64>::zero(dimension);
        
        let mut idx = BigIndex::new(dimension);
        idx.set_bit(100);
        idx.set_bit(200);
        
        a.set_component(&idx, Complex::new(3.0, 0.0)).unwrap();
        b.set_component(&idx, Complex::new(2.0, 0.0)).unwrap();
        
        // Test addition
        let sum = a.clone() + b.clone();
        assert_eq!(sum.component(&idx), Some(Complex::new(5.0, 0.0)));
        
        // Test subtraction
        let diff = a.clone() - b.clone();
        assert_eq!(diff.component(&idx), Some(Complex::new(1.0, 0.0)));
        
        // Test negation
        let neg = -a.clone();
        assert_eq!(neg.component(&idx), Some(Complex::new(-3.0, 0.0)));
        
        // Test scalar multiplication
        let scaled = a.clone() * 2.0;
        assert_eq!(scaled.component(&idx), Some(Complex::new(6.0, 0.0)));
        
        // Test complex scalar multiplication
        let complex_scaled = a * Complex::new(2.0, 1.0);
        let expected = Complex::new(3.0, 0.0) * Complex::new(2.0, 1.0);
        assert_eq!(complex_scaled.component(&idx), Some(expected));
    }
    
    #[test]
    fn test_from_blade() {
        use crate::SingleBlade;
        
        let dimension = 2048;
        let mut idx = BigIndex::new(dimension);
        idx.set_bit(500);
        idx.set_bit(1000);
        idx.set_bit(1500);
        
        let blade = SingleBlade::new(idx.clone(), Complex::new(3.5, 0.0), dimension);
        let sparse = SparseBigElement::from_blade(&blade);
        
        assert_eq!(sparse.dimension(), dimension);
        assert_eq!(sparse.nnz(), 1);
        assert_eq!(sparse.component(&idx), Some(Complex::new(3.5, 0.0)));
    }
    
    #[test]
    #[should_panic(expected = "InvalidInput")]
    fn test_basis_vector_out_of_bounds() {
        let _ = SparseBigElement::<f64>::basis_vector(1024, 1024).unwrap();
    }
    
    #[test]
    #[should_panic(expected = "InvalidInput")]
    fn test_basis_blade_duplicate_indices() {
        let _ = SparseBigElement::<f64>::basis_blade(&[10, 20, 10], 100).unwrap();
    }
    
    #[test]
    fn test_coherence_norm_grade_orthogonality() {
        // Test that coherence norm respects grade orthogonality
        // Create element with components of different grades
        let dimension = 256;
        let mut elem = SparseBigElement::<f64>::zero(dimension);
        
        // Grade 0 component (scalar)
        let scalar_idx = BigIndex::new(dimension);
        elem.set_component(&scalar_idx, Complex::new(3.0, 0.0)).unwrap();
        
        // Grade 1 component (e_5)
        let mut grade1_idx = BigIndex::new(dimension);
        grade1_idx.set_bit(5);
        elem.set_component(&grade1_idx, Complex::new(4.0, 0.0)).unwrap();
        
        // Grade 2 component (e_3 ∧ e_7)
        let mut grade2_idx = BigIndex::new(dimension);
        grade2_idx.set_bit(3);
        grade2_idx.set_bit(7);
        elem.set_component(&grade2_idx, Complex::new(0.0, 5.0)).unwrap();
        
        // Grade 3 component (e_1 ∧ e_4 ∧ e_8)
        let mut grade3_idx = BigIndex::new(dimension);
        grade3_idx.set_bit(1);
        grade3_idx.set_bit(4);
        grade3_idx.set_bit(8);
        elem.set_component(&grade3_idx, Complex::new(12.0, 0.0)).unwrap();
        
        // Coherence norm squared should be sum of squared magnitudes
        // because different grades are orthogonal
        let expected_norm_sq = 3.0*3.0 + 4.0*4.0 + 5.0*5.0 + 12.0*12.0;
        assert!((elem.coherence_norm_squared() - expected_norm_sq).abs() < 1e-10);
        
        // Coherence norm should be sqrt of that
        let expected_norm = expected_norm_sq.sqrt();
        assert!((elem.coherence_norm() - expected_norm).abs() < 1e-10);
    }
    
    #[test]
    fn test_coherence_norm_4096_dimension() {
        // Test coherence norm with 4096-bit dimension
        let dimension = 4096;
        let mut elem = SparseBigElement::<f64>::zero(dimension);
        
        // Add several components at very large indices
        for i in 0..10 {
            let mut idx = BigIndex::new(dimension);
            // Set bits at positions i*400, i*400+100, i*400+200
            idx.set_bit(i * 400);
            idx.set_bit(i * 400 + 100);
            idx.set_bit(i * 400 + 200);
            
            let value = (i + 1) as f64;
            elem.set_component(&idx, Complex::new(value, 0.0)).unwrap();
        }
        
        // Compute expected norm: sqrt(1^2 + 2^2 + ... + 10^2) = sqrt(385)
        let expected_norm_sq = (1..=10).map(|i| (i * i) as f64).sum::<f64>();
        let expected_norm = expected_norm_sq.sqrt();
        
        assert!((elem.coherence_norm() - expected_norm).abs() < 1e-10);
        assert_eq!(elem.nnz(), 10);
        assert_eq!(elem.dimension(), 4096);
    }
    
    #[test]
    fn test_geometric_product_basic() {
        // Test basic geometric product e_i * e_j = e_{i,j} for i ≠ j
        let dimension = 8;
        let e1 = SparseBigElement::<f64>::basis_vector(1, dimension).unwrap();
        let e2 = SparseBigElement::<f64>::basis_vector(2, dimension).unwrap();
        
        let result = e1.geometric_product(&e2).unwrap();
        
        // e1 * e2 should give e12 with coefficient 1
        let mut expected_idx = BigIndex::new(dimension);
        expected_idx.set_bit(1);
        expected_idx.set_bit(2);
        
        assert_eq!(result.nnz(), 1);
        assert_eq!(result.component(&expected_idx), Some(Complex::one()));
    }
    
    #[test]
    fn test_geometric_product_anticommutation() {
        // Test e_i * e_j = -e_j * e_i for i ≠ j
        let dimension = 8;
        let e1 = SparseBigElement::<f64>::basis_vector(1, dimension).unwrap();
        let e2 = SparseBigElement::<f64>::basis_vector(2, dimension).unwrap();
        
        let result12 = e1.geometric_product(&e2).unwrap();
        let result21 = e2.geometric_product(&e1).unwrap();
        
        // Check they have opposite signs
        let mut expected_idx = BigIndex::new(dimension);
        expected_idx.set_bit(1);
        expected_idx.set_bit(2);
        
        let val12 = result12.component(&expected_idx).unwrap();
        let val21 = result21.component(&expected_idx).unwrap();
        
        assert_eq!(val12, -val21);
        assert_eq!(val12, Complex::one());
        assert_eq!(val21, Complex::new(-1.0, 0.0));
    }
    
    #[test]
    fn test_geometric_product_self_squared() {
        // Test e_i * e_i = 1 (Euclidean metric)
        let dimension = 16;
        let e5 = SparseBigElement::<f64>::basis_vector(5, dimension).unwrap();
        
        let result = e5.geometric_product(&e5).unwrap();
        
        // Should give scalar component with value 1
        let scalar_idx = BigIndex::new(dimension);
        assert_eq!(result.nnz(), 1);
        assert_eq!(result.component(&scalar_idx), Some(Complex::one()));
    }
    
    #[test]
    fn test_geometric_product_large_dimension() {
        // Test geometric product with large dimensions
        let dimension = 512;
        
        // Create e_{100} and e_{200}
        let e100 = SparseBigElement::<f64>::basis_vector(100, dimension).unwrap();
        let e200 = SparseBigElement::<f64>::basis_vector(200, dimension).unwrap();
        
        let result = e100.geometric_product(&e200).unwrap();
        
        // Should give e_{100,200}
        let mut expected_idx = BigIndex::new(dimension);
        expected_idx.set_bit(100);
        expected_idx.set_bit(200);
        
        assert_eq!(result.nnz(), 1);
        assert_eq!(result.component(&expected_idx), Some(Complex::one()));
    }
    
    #[test]
    fn test_geometric_product_4096_dimension() {
        // Test with 4096-bit dimension
        let dimension = 4096;
        
        // Create sparse elements with large indices
        let mut a = SparseBigElement::<f64>::zero(dimension);
        let mut b = SparseBigElement::<f64>::zero(dimension);
        
        // a = e_{1000} + 2*e_{2000}
        let mut idx1000 = BigIndex::new(dimension);
        idx1000.set_bit(1000);
        a.set_component(&idx1000, Complex::new(1.0, 0.0)).unwrap();
        
        let mut idx2000 = BigIndex::new(dimension);
        idx2000.set_bit(2000);
        a.set_component(&idx2000, Complex::new(2.0, 0.0)).unwrap();
        
        // b = 3*e_{1500} + 4*e_{2500}
        let mut idx1500 = BigIndex::new(dimension);
        idx1500.set_bit(1500);
        b.set_component(&idx1500, Complex::new(3.0, 0.0)).unwrap();
        
        let mut idx2500 = BigIndex::new(dimension);
        idx2500.set_bit(2500);
        b.set_component(&idx2500, Complex::new(4.0, 0.0)).unwrap();
        
        let result = a.geometric_product(&b).unwrap();
        
        // Expected components:
        // e_{1000} * e_{1500} = e_{1000,1500} with coeff 1*3 = 3
        // e_{1000} * e_{2500} = e_{1000,2500} with coeff 1*4 = 4
        // e_{2000} * e_{1500} = e_{1500,2000} with coeff 2*3 = 6
        // e_{2000} * e_{2500} = e_{2000,2500} with coeff 2*4 = 8
        
        assert_eq!(result.nnz(), 4);
        
        let mut idx1000_1500 = BigIndex::new(dimension);
        idx1000_1500.set_bit(1000);
        idx1000_1500.set_bit(1500);
        assert_eq!(result.component(&idx1000_1500), Some(Complex::new(3.0, 0.0)));
        
        let mut idx1000_2500 = BigIndex::new(dimension);
        idx1000_2500.set_bit(1000);
        idx1000_2500.set_bit(2500);
        assert_eq!(result.component(&idx1000_2500), Some(Complex::new(4.0, 0.0)));
        
        let mut idx1500_2000 = BigIndex::new(dimension);
        idx1500_2000.set_bit(1500);
        idx1500_2000.set_bit(2000);
        // Note: e_{2000} * e_{1500} = -e_{1500} * e_{2000} = -e_{1500,2000}
        // Since 2000 > 1500, we need one transposition, so sign = -1
        assert_eq!(result.component(&idx1500_2000), Some(Complex::new(-6.0, 0.0)));
        
        let mut idx2000_2500 = BigIndex::new(dimension);
        idx2000_2500.set_bit(2000);
        idx2000_2500.set_bit(2500);
        assert_eq!(result.component(&idx2000_2500), Some(Complex::new(8.0, 0.0)));
    }
    
    #[test]
    fn test_wedge_product_basic() {
        // Test wedge product of orthogonal basis vectors
        let dimension = 8;
        let e1 = SparseBigElement::<f64>::basis_vector(1, dimension).unwrap();
        let e2 = SparseBigElement::<f64>::basis_vector(2, dimension).unwrap();
        
        let result = e1.wedge_product(&e2).unwrap();
        
        // e1 ∧ e2 = e12
        let mut expected_idx = BigIndex::new(dimension);
        expected_idx.set_bit(1);
        expected_idx.set_bit(2);
        
        assert_eq!(result.nnz(), 1);
        assert_eq!(result.component(&expected_idx), Some(Complex::one()));
    }
    
    #[test]
    fn test_wedge_product_self() {
        // Test wedge product of a vector with itself is zero
        let dimension = 8;
        let e1 = SparseBigElement::<f64>::basis_vector(1, dimension).unwrap();
        
        let result = e1.wedge_product(&e1).unwrap();
        
        // e1 ∧ e1 = 0
        assert_eq!(result.nnz(), 0);
        assert!(result.is_zero());
    }
    
    #[test]
    fn test_wedge_product_overlapping() {
        // Test wedge product when basis vectors overlap
        let dimension = 16;
        
        // Create e12 and e23
        let e12 = SparseBigElement::<f64>::basis_blade(&[1, 2], dimension).unwrap();
        let e23 = SparseBigElement::<f64>::basis_blade(&[2, 3], dimension).unwrap();
        
        let result = e12.wedge_product(&e23).unwrap();
        
        // e12 ∧ e23 = 0 (they share e2)
        assert_eq!(result.nnz(), 0);
        assert!(result.is_zero());
    }
    
    #[test]
    fn test_mul_trait() {
        // Test the Mul trait implementation
        let dimension = 8;
        let e1 = SparseBigElement::<f64>::basis_vector(1, dimension).unwrap();
        let e2 = SparseBigElement::<f64>::basis_vector(2, dimension).unwrap();
        
        // Use the * operator
        let result = e1 * e2;
        
        let mut expected_idx = BigIndex::new(dimension);
        expected_idx.set_bit(1);
        expected_idx.set_bit(2);
        
        assert_eq!(result.nnz(), 1);
        assert_eq!(result.component(&expected_idx), Some(Complex::one()));
    }
}