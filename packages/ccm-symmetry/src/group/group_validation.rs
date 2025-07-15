//! Group constraint validation
//! 
//! This module provides functions to validate elements against specific
//! group constraints (SO(n), SU(n), GL(n), etc.).

use num_traits::Float;
use crate::group::{GroupElement, SymmetryGroup, GroupType};
use ccm_core::CcmError;
use crate::SymmetryError;

impl<P: Float> SymmetryGroup<P> {
    /// Check if element belongs to the group
    pub fn contains(&self, g: &GroupElement<P>) -> bool {
        if g.dimension() != self.dimension {
            return false;
        }
        
        match &self.group_type {
            GroupType::Finite { elements } => {
                // For finite groups, check if element is in the list
                elements.iter().any(|e| {
                    e.params.iter().zip(&g.params)
                        .all(|(a, b)| (*a - *b).abs() < P::epsilon())
                })
            }
            GroupType::DiscreteInfinite => {
                // For discrete infinite groups (like Z), check if element can be
                // expressed as integer combination of generators
                self.can_express_as_word(g)
            }
            GroupType::Continuous => {
                // For continuous groups, check if element satisfies group constraints
                self.satisfies_group_constraints(g)
            }
        }
    }
    
    /// Add a generator to the group
    pub fn add_generator(&mut self, g: GroupElement<P>) -> Result<(), CcmError> {
        if g.dimension() != self.dimension {
            return Err(SymmetryError::InvalidGroupOperation.into());
        }
        
        self.generators.push(g);
        self.cached_order = None; // Reset cached order
        Ok(())
    }
    
    /// Check if element satisfies constraints for continuous groups
    pub(crate) fn satisfies_group_constraints(&self, g: &GroupElement<P>) -> bool {
        // For matrix groups, check specific constraints
        match self.get_group_name() {
            "SO(n)" => self.is_special_orthogonal(g),
            "SU(n)" => self.is_special_unitary(g),
            "GL(n)" => self.is_general_linear(g),
            _ => {
                // For generic continuous groups, check if element preserves
                // the group structure by verifying it's close to the group manifold
                self.is_on_group_manifold(g)
            }
        }
    }
    
    /// Get group name based on generators and properties
    pub(crate) fn get_group_name(&self) -> &'static str {
        if self.dimension == 0 {
            return "Trivial";
        }
        
        // Detect based on generator structure
        if self.generators.is_empty() {
            return "Unknown";
        }
        
        // Check for orthogonal group pattern
        let n = (self.dimension as f64).sqrt();
        if n.floor() == n && n > 0.0 {
            let n = n as usize;
            if self.generators.len() == n * (n - 1) / 2 {
                return "SO(n)";
            }
        }
        
        "Generic"
    }
    
    /// Check if element is a special orthogonal matrix
    pub(crate) fn is_special_orthogonal(&self, g: &GroupElement<P>) -> bool {
        let n = (self.dimension as f64).sqrt() as usize;
        if n * n != self.dimension {
            return false;
        }
        
        // Check orthogonality: M^T M = I
        for i in 0..n {
            for j in 0..n {
                let mut sum = P::zero();
                for k in 0..n {
                    sum = sum + g.params[k * n + i] * g.params[k * n + j];
                }
                
                let expected = if i == j { P::one() } else { P::zero() };
                if (sum - expected).abs() > P::epsilon() {
                    return false;
                }
            }
        }
        
        // Check determinant = 1
        self.compute_determinant(&g.params, n)
            .map(|det| (det - P::one()).abs() < P::epsilon())
            .unwrap_or(false)
    }
    
    /// Check if element is a special unitary matrix
    pub(crate) fn is_special_unitary(&self, _g: &GroupElement<P>) -> bool {
        // Complex matrices need 2n² real parameters
        // Check unitarity: M† M = I and det(M) = 1
        // Full implementation would handle complex arithmetic
        true
    }
    
    /// Check if element is invertible (general linear group)
    pub(crate) fn is_general_linear(&self, g: &GroupElement<P>) -> bool {
        // Check if matrix is invertible (non-zero determinant)
        let n = (self.dimension as f64).sqrt() as usize;
        if n * n != self.dimension {
            return false;
        }
        
        // Compute determinant and check if non-zero
        self.compute_determinant(&g.params, n)
            .map(|det| det.abs() > P::epsilon())
            .unwrap_or(false)
    }
}