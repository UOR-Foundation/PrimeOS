//! Coherence engine wrapper for ccm-coherence functionality

use crate::cache::CcmCache;
use ccm_coherence::{
    coherence_norm, coherence_product,
    optimization::{minimize_coherence, Constraint, MinimizationOptions},
    CliffordAlgebra, CliffordElement,
};
use ccm_core::{CcmError, Float};
use num_complex::Complex;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Engine for coherence operations (Axiom A1)
pub struct CoherenceEngine<P: Float> {
    algebra: Option<CliffordAlgebra<P>>,
    dimension: usize,
}

impl<P: Float> CoherenceEngine<P> {
    /// Create a new coherence engine
    pub fn new(dimension: usize) -> Result<Self, CcmError> {
        let algebra = if dimension <= 12 {
            Some(CliffordAlgebra::generate(dimension)?)
        } else {
            None // Use lazy evaluation for large dimensions
        };

        Ok(Self { algebra, dimension })
    }

    /// Get or create the Clifford algebra
    pub fn algebra(&mut self) -> Result<&CliffordAlgebra<P>, CcmError> {
        if self.algebra.is_none() && self.dimension <= 12 {
            self.algebra = Some(CliffordAlgebra::generate(self.dimension)?);
        }
        self.algebra.as_ref().ok_or(CcmError::NotImplemented)
    }

    /// Get the algebra if it exists (const method)
    pub fn get_algebra(&self) -> Option<&CliffordAlgebra<P>> {
        self.algebra.as_ref()
    }

    /// Ensure algebra is created and return reference
    pub fn ensure_algebra(&mut self) -> Result<&CliffordAlgebra<P>, CcmError> {
        self.algebra()
    }

    /// Create a Clifford element from basis index
    pub fn basis_element(&self, index: usize) -> Result<CliffordElement<P>, CcmError> {
        // Use basis_blade to create element for given index
        let mut indices = Vec::new();
        let mut idx = index;
        let mut bit_pos = 0;

        while idx > 0 {
            if idx & 1 == 1 {
                indices.push(bit_pos);
            }
            idx >>= 1;
            bit_pos += 1;
        }

        CliffordElement::basis_blade(&indices, self.dimension)
    }

    /// Compute coherence norm
    pub fn coherence_norm(&self, section: &CliffordElement<P>) -> P {
        coherence_norm(section)
    }

    /// Compute coherence inner product
    pub fn coherence_product(&self, a: &CliffordElement<P>, b: &CliffordElement<P>) -> Complex<P> {
        coherence_product(a, b)
    }

    /// Minimize coherence with constraints
    pub fn minimize_coherence(
        &self,
        initial: &CliffordElement<P>,
        constraint: Option<&dyn Constraint<P>>,
    ) -> Result<CliffordElement<P>, CcmError> {
        if let Some(c) = constraint {
            let options = MinimizationOptions::default();
            minimize_coherence(initial, c, options).map(|result| result.minimizer)
        } else {
            // No constraint - just return the input
            Ok(initial.clone())
        }
    }

    /// Get dimension
    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// Create a Clifford element from basis index with caching
    pub fn basis_element_cached(
        &self,
        index: usize,
        cache: &CcmCache<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        // Check cache first
        if let Some(cached_element) = cache.get_basis_element(self.dimension, index) {
            return Ok(cached_element);
        }

        // Create basis element
        let element = self.basis_element(index)?;

        // Store in cache
        cache.put_basis_element(self.dimension, index, element.clone());

        Ok(element)
    }
}
