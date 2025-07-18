//! Unified API for Clifford algebras with automatic implementation selection
//!
//! This module provides a trait-based abstraction over different Clifford algebra
//! implementations, automatically selecting the most appropriate one based on
//! dimension and usage patterns.

use crate::{
    arbitrary_support::{ArbitraryCliffordAlgebra, ArbitraryDimensionConfig},
    clifford::CliffordAlgebra,
    element::CliffordElement,
    lazy::LazyCliffordAlgebra,
};
use ccm_core::{CcmError, Float};
use num_complex::Complex;
use num_traits::One;

/// Trait unifying all Clifford algebra implementations
pub trait CliffordAlgebraTrait<P: Float> {
    /// Get the dimension of the underlying vector space
    fn dimension(&self) -> usize;
    
    /// Get the metric signature (p, q, r)
    fn signature(&self) -> (usize, usize, usize);
    
    /// Get the total number of basis elements (2^n)
    /// Returns None if the number would overflow usize
    fn num_basis_elements(&self) -> Option<usize>;
    
    /// Get a specific basis element by its index
    /// May return sparse representation for large dimensions
    fn basis_element(&self, index: usize) -> Result<CliffordElement<P>, CcmError>;
    
    /// Get a basis blade from a list of vector indices
    fn basis_blade(&self, indices: &[usize]) -> Result<CliffordElement<P>, CcmError>;
    
    /// Compute the geometric product of two elements
    fn geometric_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError>;
    
    /// Compute the wedge product a ∧ b
    fn wedge_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError>;
    
    /// Compute the inner product a · b
    fn inner_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError>;
    
    /// Compute the scalar product ⟨a, b⟩
    fn scalar_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<Complex<P>, CcmError>;
    
    /// Check if this algebra supports dense element storage
    fn supports_dense(&self) -> bool;
    
    /// Get memory estimate in MB for a full element
    fn memory_estimate_mb(&self) -> usize;
}

/// Implementation for standard CliffordAlgebra (dimensions ≤ 12)
impl<P: Float> CliffordAlgebraTrait<P> for CliffordAlgebra<P> {
    fn dimension(&self) -> usize {
        self.dimension()
    }
    
    fn signature(&self) -> (usize, usize, usize) {
        self.signature()
    }
    
    fn num_basis_elements(&self) -> Option<usize> {
        Some(self.num_basis_elements())
    }
    
    fn basis_element(&self, index: usize) -> Result<CliffordElement<P>, CcmError> {
        self.basis_element(index)
    }
    
    fn basis_blade(&self, indices: &[usize]) -> Result<CliffordElement<P>, CcmError> {
        self.basis_blade(indices)
    }
    
    fn geometric_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        self.geometric_product(a, b)
    }
    
    fn wedge_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        self.wedge_product(a, b)
    }
    
    fn inner_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        self.inner_product(a, b)
    }
    
    fn scalar_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<Complex<P>, CcmError> {
        self.scalar_product(a, b)
    }
    
    fn supports_dense(&self) -> bool {
        true
    }
    
    fn memory_estimate_mb(&self) -> usize {
        let bytes = self.num_basis_elements() * 16; // Complex<f64>
        bytes / (1024 * 1024)
    }
}

/// Implementation for ArbitraryCliffordAlgebra (dimensions > 12)
impl<P: Float> CliffordAlgebraTrait<P> for ArbitraryCliffordAlgebra<P> {
    fn dimension(&self) -> usize {
        self.dimension()
    }
    
    fn signature(&self) -> (usize, usize, usize) {
        // Default to Euclidean signature
        (self.dimension(), 0, 0)
    }
    
    fn num_basis_elements(&self) -> Option<usize> {
        if self.dimension() < 64 {
            Some(1usize << self.dimension())
        } else {
            None // Would overflow
        }
    }
    
    fn basis_element(&self, index: usize) -> Result<CliffordElement<P>, CcmError> {
        // For large dimensions, check if we can allocate
        if self.can_allocate_element() {
            // If we can use standard algebra, delegate to it
            let std_algebra = self.as_standard()?;
            std_algebra.basis_element(index)
        } else {
            // For large dimensions, create a sparse element
            use crate::sparse::SparseCliffordElement;
            let mut sparse = SparseCliffordElement::zero(self.dimension());
            sparse.set_component(index, Complex::one())?;
            // Convert to dense representation
            Ok(sparse.to_dense())
        }
    }
    
    fn basis_blade(&self, indices: &[usize]) -> Result<CliffordElement<P>, CcmError> {
        // Convert indices to bit pattern
        let mut pattern = 0usize;
        for &i in indices {
            if i >= self.dimension() {
                return Err(CcmError::InvalidInput);
            }
            if pattern & (1 << i) != 0 {
                return Err(CcmError::InvalidInput); // Repeated index
            }
            pattern |= 1 << i;
        }
        
        self.basis_element(pattern)
    }
    
    fn geometric_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        // For large dimensions, use standard algebra if possible
        if self.can_allocate_element() {
            let std_algebra = self.as_standard()?;
            std_algebra.geometric_product(a, b)
        } else {
            // TODO: Implement sparse geometric product
            Err(CcmError::NotImplemented)
        }
    }
    
    fn wedge_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        if self.can_allocate_element() {
            let std_algebra = self.as_standard()?;
            std_algebra.wedge_product(a, b)
        } else {
            Err(CcmError::NotImplemented)
        }
    }
    
    fn inner_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        if self.can_allocate_element() {
            let std_algebra = self.as_standard()?;
            std_algebra.inner_product(a, b)
        } else {
            Err(CcmError::NotImplemented)
        }
    }
    
    fn scalar_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<Complex<P>, CcmError> {
        if self.can_allocate_element() {
            let std_algebra = self.as_standard()?;
            std_algebra.scalar_product(a, b)
        } else {
            // Scalar product only needs the grade-0 component
            use num_traits::Zero;
            Ok(a.component(0).unwrap_or(Complex::zero()) * b.component(0).unwrap_or(Complex::zero()))
        }
    }
    
    fn supports_dense(&self) -> bool {
        self.can_allocate_element()
    }
    
    fn memory_estimate_mb(&self) -> usize {
        ArbitraryCliffordAlgebra::<P>::estimate_memory_mb(self.dimension())
    }
}

/// Implementation for LazyCliffordAlgebra
impl<P: Float> CliffordAlgebraTrait<P> for LazyCliffordAlgebra<P> {
    fn dimension(&self) -> usize {
        self.dimension()
    }
    
    fn signature(&self) -> (usize, usize, usize) {
        self.signature()
    }
    
    fn num_basis_elements(&self) -> Option<usize> {
        if self.dimension() < 64 {
            Some(1usize << self.dimension())
        } else {
            None
        }
    }
    
    fn basis_element(&self, index: usize) -> Result<CliffordElement<P>, CcmError> {
        self.basis_element(index)
    }
    
    fn basis_blade(&self, indices: &[usize]) -> Result<CliffordElement<P>, CcmError> {
        self.basis_blade(indices)
    }
    
    fn geometric_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        self.geometric_product(a, b)
    }
    
    fn wedge_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        self.wedge_product(a, b)
    }
    
    fn inner_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        self.inner_product(a, b)
    }
    
    fn scalar_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<Complex<P>, CcmError> {
        self.scalar_product(a, b)
    }
    
    fn supports_dense(&self) -> bool {
        self.dimension() <= 12 // Conservative estimate
    }
    
    fn memory_estimate_mb(&self) -> usize {
        let cached = self.memory_stats().cached_elements;
        let bytes = cached * 16; // Only cached elements use memory
        bytes / (1024 * 1024)
    }
}

/// Enum wrapper for different Clifford algebra implementations
#[derive(Clone)]
pub enum UnifiedCliffordAlgebra<P: Float> {
    Standard(CliffordAlgebra<P>),
    Arbitrary(ArbitraryCliffordAlgebra<P>),
    Lazy(LazyCliffordAlgebra<P>),
}

impl<P: Float> CliffordAlgebraTrait<P> for UnifiedCliffordAlgebra<P> {
    fn dimension(&self) -> usize {
        match self {
            Self::Standard(a) => a.dimension(),
            Self::Arbitrary(a) => a.dimension(),
            Self::Lazy(a) => a.dimension(),
        }
    }
    
    fn signature(&self) -> (usize, usize, usize) {
        match self {
            Self::Standard(a) => a.signature(),
            Self::Arbitrary(a) => a.signature(),
            Self::Lazy(a) => a.signature(),
        }
    }
    
    fn num_basis_elements(&self) -> Option<usize> {
        match self {
            Self::Standard(a) => Some(a.num_basis_elements()),
            Self::Arbitrary(a) => a.num_basis_elements(),
            Self::Lazy(a) => a.num_basis_elements(),
        }
    }
    
    fn basis_element(&self, index: usize) -> Result<CliffordElement<P>, CcmError> {
        match self {
            Self::Standard(a) => a.basis_element(index),
            Self::Arbitrary(a) => a.basis_element(index),
            Self::Lazy(a) => a.basis_element(index),
        }
    }
    
    fn basis_blade(&self, indices: &[usize]) -> Result<CliffordElement<P>, CcmError> {
        match self {
            Self::Standard(a) => a.basis_blade(indices),
            Self::Arbitrary(a) => a.basis_blade(indices),
            Self::Lazy(a) => a.basis_blade(indices),
        }
    }
    
    fn geometric_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        match self {
            Self::Standard(alg) => alg.geometric_product(a, b),
            Self::Arbitrary(alg) => alg.geometric_product(a, b),
            Self::Lazy(alg) => alg.geometric_product(a, b),
        }
    }
    
    fn wedge_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        match self {
            Self::Standard(alg) => alg.wedge_product(a, b),
            Self::Arbitrary(alg) => alg.wedge_product(a, b),
            Self::Lazy(alg) => alg.wedge_product(a, b),
        }
    }
    
    fn inner_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        match self {
            Self::Standard(alg) => alg.inner_product(a, b),
            Self::Arbitrary(alg) => alg.inner_product(a, b),
            Self::Lazy(alg) => alg.inner_product(a, b),
        }
    }
    
    fn scalar_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<Complex<P>, CcmError> {
        match self {
            Self::Standard(alg) => alg.scalar_product(a, b),
            Self::Arbitrary(alg) => alg.scalar_product(a, b),
            Self::Lazy(alg) => alg.scalar_product(a, b),
        }
    }
    
    fn supports_dense(&self) -> bool {
        match self {
            Self::Standard(_) => true,
            Self::Arbitrary(a) => a.supports_dense(),
            Self::Lazy(_) => false,
        }
    }
    
    fn memory_estimate_mb(&self) -> usize {
        match self {
            Self::Standard(a) => a.memory_estimate_mb(),
            Self::Arbitrary(a) => a.memory_estimate_mb(),
            Self::Lazy(a) => a.memory_estimate_mb(),
        }
    }
}

/// Factory for creating appropriate Clifford algebra implementation
pub struct CliffordAlgebraFactory;

impl CliffordAlgebraFactory {
    /// Create the most appropriate Clifford algebra for the given dimension
    pub fn create<P: Float>(dimension: usize) -> Result<UnifiedCliffordAlgebra<P>, CcmError> {
        Self::create_with_config(dimension, Default::default())
    }
    
    /// Create with custom configuration
    pub fn create_with_config<P: Float>(
        dimension: usize,
        mut config: ArbitraryDimensionConfig,
    ) -> Result<UnifiedCliffordAlgebra<P>, CcmError> {
        if dimension <= config.max_dense_dimension && dimension <= 12 {
            // For small dimensions, use standard dense algebra
            let algebra = CliffordAlgebra::generate(dimension)?;
            Ok(UnifiedCliffordAlgebra::Standard(algebra))
        } else {
            // For large dimensions (>= 64), disable overflow check
            if dimension >= 64 {
                config.check_overflow = false;
                config.max_dense_dimension = 0; // Force sparse/lazy only
            }
            
            // For all other cases, use arbitrary dimension support
            // which can handle any dimension within memory constraints
            let algebra = ArbitraryCliffordAlgebra::generate(dimension, config)?;
            Ok(UnifiedCliffordAlgebra::Arbitrary(algebra))
        }
    }
    
    /// Create a Clifford algebra specifically optimized for BJC usage
    /// (single blade operations with large dimensions)
    pub fn create_for_bjc<P: Float>(dimension: usize) -> Result<UnifiedCliffordAlgebra<P>, CcmError> {
        let config = ArbitraryDimensionConfig {
            max_dense_dimension: 0, // Never use dense storage
            max_memory_mb: 10, // Minimal memory since we only need single blades
            check_overflow: true,
        };
        
        let algebra = ArbitraryCliffordAlgebra::generate(dimension, config)?;
        Ok(UnifiedCliffordAlgebra::Arbitrary(algebra))
    }
}

/// Extension trait for sparse basis elements
pub trait SparseBasisElementExt<P: Float> {
    /// Convert to a full CliffordElement
    fn to_clifford_element(&self) -> Result<CliffordElement<P>, CcmError>;
}


#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_factory_small_dimension() {
        let algebra = CliffordAlgebraFactory::create::<f64>(4).unwrap();
        assert_eq!(algebra.dimension(), 4);
        assert!(algebra.supports_dense());
    }
    
    #[test]
    fn test_factory_large_dimension() {
        // For dimension 32, we should get an arbitrary algebra (not dense)
        let algebra = CliffordAlgebraFactory::create::<f64>(32).unwrap();
        assert_eq!(algebra.dimension(), 32);
        assert!(!algebra.supports_dense());
        
        // For truly large dimensions like 64, we need special config
        let mut config = ArbitraryDimensionConfig::default();
        config.check_overflow = false;
        config.max_dense_dimension = 0; // Force sparse/lazy only
        let large_algebra = CliffordAlgebraFactory::create_with_config::<f64>(64, config).unwrap();
        assert_eq!(large_algebra.dimension(), 64);
    }
    
    #[test]
    fn test_bjc_optimized() {
        let algebra = CliffordAlgebraFactory::create_for_bjc::<f64>(256).unwrap();
        assert_eq!(algebra.dimension(), 256);
        assert!(!algebra.supports_dense());
    }
}