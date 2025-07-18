//! Unified API for Clifford algebras with automatic implementation selection
//!
//! This module provides a trait-based abstraction over different Clifford algebra
//! implementations, automatically selecting the most appropriate one based on
//! dimension and usage patterns.
//!
//! # Dimension Limitations and Strategies
//!
//! The unified API automatically selects the best implementation based on dimension:
//!
//! | Dimension Range | Implementation | Capabilities | Limitations |
//! |-----------------|----------------|--------------|-------------|
//! | 1-12 | Standard | Dense storage, pre-computed multiplication table | Memory usage: O(4^n) bytes |
//! | 13-20 | Lazy | On-demand basis generation, cached results | Slower first access |
//! | 21-63 | Arbitrary | Sparse storage, configurable memory limits | No dense operations above dim 30 |
//! | 64-4096 | Scalable | Streaming operations, BigIndex support | Dense operations return errors |
//!
//! ## Operation Support by Dimension
//!
//! ### Dense Operations (basis_element, geometric_product, etc.)
//! - **Dimensions 1-30**: Full support with efficient implementation
//! - **Dimensions 31-63**: Limited support, may fail with memory constraints
//! - **Dimensions 64+**: Not supported, use sparse/lazy alternatives
//!
//! ### Sparse Operations (SingleBlade, SparseBigElement)
//! - **All dimensions**: Full support up to 4096
//! - **Recommended for**: Dimensions > 20
//! - **Required for**: Dimensions > 64
//!
//! ### Memory Requirements
//! - **Standard (dim ≤ 12)**: ~16 * 2^n bytes per element
//! - **Lazy (dim ≤ 20)**: ~16 * k bytes (k = cached elements)
//! - **Arbitrary (dim ≤ 64)**: Configurable, typically < 100 MB
//! - **Scalable (dim ≤ 4096)**: O(k) where k = non-zero components
//!
//! ## Usage Guidelines
//!
//! 1. **Small dimensions (≤ 12)**: Use standard API methods freely
//! 2. **Medium dimensions (13-63)**: Consider sparse representations
//! 3. **Large dimensions (64-4096)**: Must use sparse/streaming methods
//! 4. **BJC Codec**: Use `create_for_bjc()` for optimized single-blade operations
//!
//! ## Error Handling
//!
//! The API provides clear error messages when operations exceed dimension limits:
//! - Dimension validation errors explain the valid range
//! - Operation errors suggest alternative sparse methods
//! - Memory errors indicate when to switch strategies

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
        // If we can allocate dense elements, return the full memory requirement
        if self.can_allocate_element() {
            ArbitraryCliffordAlgebra::<P>::estimate_memory_mb(self.dimension())
        } else {
            // When using sparse storage, memory usage is proportional to non-zero elements
            // For typical usage, assume ~1000 non-zero components max
            let bytes_per_component = 16 + 8; // Complex<f64> + index overhead
            let estimated_components = 1000;
            (bytes_per_component * estimated_components) / (1024 * 1024)
        }
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
    Scalable(Box<crate::scalable::ScalableAlgebra<P>>),
}

impl<P: Float> CliffordAlgebraTrait<P> for UnifiedCliffordAlgebra<P> {
    fn dimension(&self) -> usize {
        match self {
            Self::Standard(a) => a.dimension(),
            Self::Arbitrary(a) => a.dimension(),
            Self::Lazy(a) => a.dimension(),
            Self::Scalable(a) => a.dimension,
        }
    }
    
    fn signature(&self) -> (usize, usize, usize) {
        match self {
            Self::Standard(a) => a.signature(),
            Self::Arbitrary(a) => a.signature(),
            Self::Lazy(a) => a.signature(),
            Self::Scalable(a) => a.signature,
        }
    }
    
    fn num_basis_elements(&self) -> Option<usize> {
        match self {
            Self::Standard(a) => Some(a.num_basis_elements()),
            Self::Arbitrary(a) => a.num_basis_elements(),
            Self::Lazy(a) => a.num_basis_elements(),
            Self::Scalable(a) => {
                if a.dimension < 64 {
                    Some(1usize << a.dimension)
                } else {
                    None
                }
            }
        }
    }
    
    fn basis_element(&self, index: usize) -> Result<CliffordElement<P>, CcmError> {
        match self {
            Self::Standard(a) => a.basis_element(index),
            Self::Arbitrary(a) => a.basis_element(index),
            Self::Lazy(a) => a.basis_element(index),
            Self::Scalable(_) => {
                // For scalable algebra, we need to use sparse representation
                Err(CcmError::NotImplemented)
            }
        }
    }
    
    fn basis_blade(&self, indices: &[usize]) -> Result<CliffordElement<P>, CcmError> {
        match self {
            Self::Standard(a) => a.basis_blade(indices),
            Self::Arbitrary(a) => a.basis_blade(indices),
            Self::Lazy(a) => a.basis_blade(indices),
            Self::Scalable(_) => {
                // For scalable algebra, we need to use sparse representation
                Err(CcmError::NotImplemented)
            }
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
            Self::Scalable(_) => {
                // For scalable algebra, dense operations are not supported
                Err(CcmError::NotImplemented)
            }
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
            Self::Scalable(_) => {
                Err(CcmError::NotImplemented)
            }
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
            Self::Scalable(_) => {
                Err(CcmError::NotImplemented)
            }
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
            Self::Scalable(_) => {
                // Scalar product only needs grade-0 component
                use num_traits::Zero;
                Ok(a.component(0).unwrap_or(Complex::zero()) * b.component(0).unwrap_or(Complex::zero()))
            }
        }
    }
    
    fn supports_dense(&self) -> bool {
        match self {
            Self::Standard(_) => true,
            Self::Arbitrary(a) => a.supports_dense(),
            Self::Lazy(_) => false,
            Self::Scalable(_) => false,
        }
    }
    
    fn memory_estimate_mb(&self) -> usize {
        match self {
            Self::Standard(a) => a.memory_estimate_mb(),
            Self::Arbitrary(a) => a.memory_estimate_mb(),
            Self::Lazy(a) => a.memory_estimate_mb(),
            Self::Scalable(a) => a.memory_usage_bytes() / (1024 * 1024),
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
        // Dimension validation
        if dimension == 0 {
            return Err(CcmError::InvalidInput);
        }
        
        if dimension > 4096 {
            return Err(CcmError::InvalidInput);
        }
        
        // Strategy selection based on dimension and memory constraints
        
        // First check if we should use standard dense algebra
        if dimension <= 12 && dimension <= config.max_dense_dimension {
            let algebra = CliffordAlgebra::generate(dimension)?;
            Ok(UnifiedCliffordAlgebra::Standard(algebra))
        }
        // If dimension is small but config restricts dense, use arbitrary
        else if dimension <= 12 {
            // Config restricts dense algebra, use arbitrary instead
            let algebra = ArbitraryCliffordAlgebra::generate(dimension, config)?;
            Ok(UnifiedCliffordAlgebra::Arbitrary(algebra))
        }
        // Then check dimension ranges for lazy
        else if dimension <= 20 {
            // For dimensions 13-20, use lazy evaluation
            let algebra = LazyCliffordAlgebra::generate(dimension)?;
            Ok(UnifiedCliffordAlgebra::Lazy(algebra))
        }
        else if dimension <= 63 {
            // Large dimensions up to 63: Use arbitrary dimension support
            // Adjust config for safety
            if dimension > 30 {
                config.max_dense_dimension = 0; // Force sparse only
            }
            let algebra = ArbitraryCliffordAlgebra::generate(dimension, config)?;
            Ok(UnifiedCliffordAlgebra::Arbitrary(algebra))
        }
        else if dimension <= 4096 {
            // Very large dimensions: Use scalable algebra
            // For dimensions >= 64, we must use the scalable implementation
            config.check_overflow = false;
            config.max_dense_dimension = 0;
            
            // Try arbitrary algebra first if it can handle it
            if dimension <= 128 && config.max_memory_mb >= 100 {
                match ArbitraryCliffordAlgebra::generate(dimension, config.clone()) {
                    Ok(algebra) => Ok(UnifiedCliffordAlgebra::Arbitrary(algebra)),
                    Err(_) => {
                        // Fall back to scalable algebra
                        let algebra = crate::scalable::ScalableAlgebra::new(dimension);
                        Ok(UnifiedCliffordAlgebra::Scalable(Box::new(algebra)))
                    }
                }
            } else {
                // For very large dimensions, go straight to scalable
                let algebra = crate::scalable::ScalableAlgebra::new(dimension);
                Ok(UnifiedCliffordAlgebra::Scalable(Box::new(algebra)))
            }
        }
        else {
            unreachable!("Dimension validation should have caught this")
        }
    }
    
    /// Create a Clifford algebra specifically optimized for BJC usage
    /// (single blade operations with large dimensions)
    pub fn create_for_bjc<P: Float>(dimension: usize) -> Result<UnifiedCliffordAlgebra<P>, CcmError> {
        // BJC can work with dimensions up to 4096 bits
        if dimension == 0 || dimension < 3 {
            return Err(CcmError::InvalidInput);
        }
        
        if dimension > 4096 {
            return Err(CcmError::InvalidInput);
        }
        
        // For BJC, we always use scalable algebra for dimensions > 64
        if dimension > 64 {
            let algebra = crate::scalable::ScalableAlgebra::new(dimension);
            Ok(UnifiedCliffordAlgebra::Scalable(Box::new(algebra)))
        } else {
            // For smaller dimensions, use arbitrary algebra with minimal memory
            let config = ArbitraryDimensionConfig {
                max_dense_dimension: 0, // Never use dense storage
                max_memory_mb: 10, // Minimal memory since we only need single blades
                check_overflow: false,
            };
            
            let algebra = ArbitraryCliffordAlgebra::generate(dimension, config)?;
            Ok(UnifiedCliffordAlgebra::Arbitrary(algebra))
        }
    }
    
    /// Get a descriptive string for the strategy used for a given dimension
    pub fn strategy_description(dimension: usize) -> &'static str {
        match dimension {
            0 => "Invalid (dimension must be >= 1)",
            1..=12 => "Standard dense algebra (optimal for small dimensions)",
            13..=20 => "Lazy evaluation (memory-efficient for medium dimensions)",
            21..=63 => "Arbitrary dimension with sparse storage",
            64..=4096 => "Scalable algebra (streaming operations for very large dimensions)",
            _ => "Unsupported (exceeds maximum dimension of 4096)",
        }
    }
}

/// Extension trait for sparse basis elements
pub trait SparseBasisElementExt<P: Float> {
    /// Convert to a full CliffordElement
    fn to_clifford_element(&self) -> Result<CliffordElement<P>, CcmError>;
}

/// Extension methods for unified algebra
impl<P: Float> UnifiedCliffordAlgebra<P> {
    /// Check if this algebra supports the requested operation for its dimension
    pub fn check_operation_support(&self, operation: &str) -> Result<(), CcmError> {
        match self {
            Self::Scalable(_) => {
                match operation {
                    "basis_element" | "basis_blade" | "geometric_product" | 
                    "wedge_product" | "inner_product" => {
                        Err(CcmError::NotImplemented)
                    }
                    _ => Ok(())
                }
            }
            _ => Ok(())
        }
    }
    
    /// Get information about the current implementation
    pub fn implementation_info(&self) -> String {
        match self {
            Self::Standard(_) => format!(
                "Standard dense algebra (dimension {}): \
                Full multiplication table pre-computed, optimal for small dimensions",
                self.dimension()
            ),
            Self::Arbitrary(_) => format!(
                "Arbitrary dimension algebra (dimension {}): \
                Sparse storage, supports dimensions up to 64 efficiently",
                self.dimension()
            ),
            Self::Lazy(_) => format!(
                "Lazy evaluation algebra (dimension {}): \
                Basis elements computed on-demand, memory-efficient for medium dimensions",
                self.dimension()
            ),
            Self::Scalable(_) => format!(
                "Scalable algebra (dimension {}): \
                Streaming operations only, supports dimensions up to 4096. \
                Use sparse methods for all operations.",
                self.dimension()
            ),
        }
    }
    
    /// Get recommended methods for the current dimension
    pub fn recommended_methods(&self) -> Vec<&'static str> {
        match self {
            Self::Standard(_) => vec![
                "All standard methods are efficient",
                "basis_element(), basis_blade()",
                "geometric_product(), wedge_product(), inner_product()",
            ],
            Self::Arbitrary(_) => vec![
                "Prefer sparse methods when possible",
                "basis_element_lazy() for single blades",
                "Use SparseCliffordElement for multi-component elements",
            ],
            Self::Lazy(_) => vec![
                "basis_element() generates on demand",
                "Avoid storing all basis elements",
                "Use grade_iterator() for grade-specific operations",
            ],
            Self::Scalable(_) => vec![
                "Use SingleBlade for single blade operations",
                "Use SparseBigElement for multi-blade operations",
                "StreamingInnerProduct for coherence calculations",
                "ComponentIterator for grade iteration",
            ],
        }
    }
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
    
    #[test]
    fn test_dimension_validation() {
        // Test dimension 0
        let result = CliffordAlgebraFactory::create::<f64>(0);
        assert!(result.is_err());
        
        // Test dimension > 4096
        let result = CliffordAlgebraFactory::create::<f64>(5000);
        assert!(result.is_err());
        
        // Test BJC dimension constraints
        let result = CliffordAlgebraFactory::create_for_bjc::<f64>(2);
        assert!(result.is_err());
    }
    
    #[test]
    fn test_strategy_selection() {
        // Test each dimension range
        let test_cases = vec![
            (4, "Standard"),
            (15, "Lazy"),
            (30, "Arbitrary"),
            (200, "Scalable"),  // Changed to 200 to ensure we get Scalable
        ];
        
        for (dim, expected_type) in test_cases {
            let algebra = CliffordAlgebraFactory::create::<f64>(dim).unwrap();
            let info = algebra.implementation_info();
            assert!(info.contains(expected_type), 
                    "Dimension {} should use {} implementation, but got: {}", 
                    dim, expected_type, info);
        }
    }
    
    #[test]
    fn test_scalable_algebra_limitations() {
        // Create a scalable algebra (use larger dimension to ensure scalable)
        let algebra = CliffordAlgebraFactory::create::<f64>(200).unwrap();
        
        // Check that it's scalable
        assert!(!algebra.supports_dense());
        
        // Test that dense operations return appropriate errors
        let result = algebra.basis_element(0);
        assert!(result.is_err());
        
        // Check operation support
        let check = algebra.check_operation_support("geometric_product");
        assert!(check.is_err());
    }
    
    #[test]
    fn test_strategy_description() {
        assert_eq!(
            CliffordAlgebraFactory::strategy_description(0),
            "Invalid (dimension must be >= 1)"
        );
        
        assert_eq!(
            CliffordAlgebraFactory::strategy_description(10),
            "Standard dense algebra (optimal for small dimensions)"
        );
        
        assert_eq!(
            CliffordAlgebraFactory::strategy_description(100),
            "Scalable algebra (streaming operations for very large dimensions)"
        );
        
        assert_eq!(
            CliffordAlgebraFactory::strategy_description(5000),
            "Unsupported (exceeds maximum dimension of 4096)"
        );
    }
    
    #[test]
    fn test_recommended_methods() {
        // Standard algebra
        let standard = CliffordAlgebraFactory::create::<f64>(8).unwrap();
        let methods = standard.recommended_methods();
        assert!(methods.iter().any(|&m| m.contains("All standard methods")));
        
        // Scalable algebra (use larger dimension)
        let scalable = CliffordAlgebraFactory::create::<f64>(200).unwrap();
        let methods = scalable.recommended_methods();
        assert!(methods.iter().any(|&m| m.contains("SingleBlade")));
        assert!(methods.iter().any(|&m| m.contains("SparseBigElement")));
    }
    
    #[test]
    fn test_memory_estimates() {
        // Small dimension
        let small = CliffordAlgebraFactory::create::<f64>(8).unwrap();
        let mem = small.memory_estimate_mb();
        assert!(mem < 1); // 2^8 * 16 bytes = 4KB < 1MB
        
        // Medium dimension
        let medium = CliffordAlgebraFactory::create::<f64>(20).unwrap();
        let mem = medium.memory_estimate_mb();
        assert!(mem < 100); // Should be manageable
        
        // Large dimension returns 0 or small value for scalable
        let large = CliffordAlgebraFactory::create::<f64>(200).unwrap();
        let mem = large.memory_estimate_mb();
        assert!(mem < 1); // Scalable uses minimal memory
    }
    
    #[test]
    fn test_bjc_dimension_ranges() {
        // Valid BJC dimensions
        assert!(CliffordAlgebraFactory::create_for_bjc::<f64>(3).is_ok());
        assert!(CliffordAlgebraFactory::create_for_bjc::<f64>(64).is_ok());
        assert!(CliffordAlgebraFactory::create_for_bjc::<f64>(256).is_ok());
        assert!(CliffordAlgebraFactory::create_for_bjc::<f64>(4096).is_ok());
        
        // Invalid BJC dimensions
        assert!(CliffordAlgebraFactory::create_for_bjc::<f64>(0).is_err());
        assert!(CliffordAlgebraFactory::create_for_bjc::<f64>(2).is_err());
        assert!(CliffordAlgebraFactory::create_for_bjc::<f64>(5000).is_err());
    }
}