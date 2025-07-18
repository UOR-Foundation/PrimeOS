//! Sparse Clifford element with BigIndex support for arbitrary dimensions
//!
//! This module extends sparse storage to support dimensions beyond 64 bits.

use crate::arbitrary_support::BigIndex;
use ccm_core::{CcmError, Float};
use num_complex::Complex;
use num_traits::Zero;

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
    pub fn add(&mut self, other: &Self) -> Result<(), CcmError> {
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
        a.add(&b).unwrap();
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
}