//! Group element representation and basic operations
//! 
//! This module defines the GroupElement struct which represents
//! elements of symmetry groups in various representations.

use num_traits::Float;

/// Represents an element of a symmetry group
/// 
/// Elements can be represented in multiple ways:
/// - Abstract parameter vector (most general)
/// - Matrix representation (for matrix groups)
/// - Permutation representation (for permutation groups)
/// - Generator word (for finitely presented groups)
#[derive(Debug, Clone, PartialEq)]
pub struct GroupElement<P: Float> {
    /// Parameters defining the group element
    pub params: Vec<P>,
    /// Cached order of this element (if computed)
    pub(crate) cached_order: Option<usize>,
}

impl<P: Float> GroupElement<P> {
    /// Create identity element
    pub fn identity(dimension: usize) -> Self {
        Self {
            params: vec![P::one(); dimension],
            cached_order: Some(1),
        }
    }

    /// Check if this is the identity element
    pub fn is_identity(&self) -> bool {
        self.params
            .iter()
            .all(|&p| (p - P::one()).abs() < P::epsilon())
    }

    /// Get dimension
    pub fn dimension(&self) -> usize {
        self.params.len()
    }
    
    /// Get the order of this element (smallest n where g^n = e)
    pub fn order(&self) -> Option<usize> {
        self.cached_order
    }
    
    /// Create a group element representing a bit flip
    pub fn from_bit_flip(bit_position: usize, dimension: usize) -> Self {
        let mut params = vec![P::one(); dimension];
        if bit_position < dimension {
            params[bit_position] = -P::one(); // Negative indicates bit flip
        }
        Self {
            params,
            cached_order: Some(2), // Bit flip has order 2
        }
    }
    
    /// Create a cyclic permutation element
    /// 
    /// This represents a cyclic shift of bit positions by 'shift' positions
    pub fn cyclic_shift(shift: usize, dimension: usize) -> Self {
        // Encode permutation in params
        // For a cyclic shift, params[i] encodes where position i maps to
        let mut params = vec![P::zero(); dimension];
        
        for i in 0..dimension {
            let target = (i + shift) % dimension;
            params[i] = P::from(target).unwrap();
        }
        
        // The order of a cyclic shift is dimension/gcd(shift, dimension)
        let order = dimension / gcd(shift, dimension);
        
        Self {
            params,
            cached_order: Some(order),
        }
    }
}

/// Compute greatest common divisor
fn gcd(mut a: usize, mut b: usize) -> usize {
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}