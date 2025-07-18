//! Tests for arbitrary input handling in ccm-coherence

#[cfg(test)]
mod tests {
    use crate::lazy::LazyCliffordAlgebra;
    use crate::sparse::SparseCliffordElement;
    use crate::{CliffordAlgebra, CliffordElement};
    use num_complex::Complex;

    #[test]
    fn test_dimension_limits() {
        // Test current limit of 12
        assert!(CliffordAlgebra::<f64>::generate(12).is_ok());
        assert!(CliffordAlgebra::<f64>::generate(13).is_err());

        // Test with different signatures
        assert!(CliffordAlgebra::<f64>::with_signature(6, 6, 0).is_ok());
        assert!(CliffordAlgebra::<f64>::with_signature(7, 6, 0).is_err());
    }

    #[test]
    fn test_large_dimension_overflow() {
        // This would overflow: 1usize << 64
        let dimension = 64;

        // Currently this is prevented by the n > 12 check,
        // but if we removed that check, we'd need overflow protection
        assert!(CliffordAlgebra::<f64>::generate(dimension).is_err());
    }

    #[test]
    fn test_element_scalability() {
        // Test how element creation scales with dimension
        for n in 1..=12 {
            let elem = CliffordElement::<f64>::zero(n);
            assert_eq!(elem.num_components(), 1usize << n);

            // Memory usage: each component is 16 bytes (Complex<f64>)
            let memory_bytes = elem.num_components() * 16;
            println!(
                "Dimension {}: {} components, {} bytes",
                n,
                elem.num_components(),
                memory_bytes
            );
        }
    }

    #[test]
    fn test_sparse_representation_limits() {
        // Test sparse representation for various dimensions
        for n in 1..=12 {
            let sparse = SparseCliffordElement::<f64>::zero(n);
            assert_eq!(sparse.dimension(), n);

            // Add components up to limit
            let mut sparse_test = SparseCliffordElement::<f64>::zero(n);
            let max_components = if cfg!(feature = "alloc") { 100 } else { 32 };

            for i in 0..max_components.min(1usize << n) {
                sparse_test
                    .set_component(i, Complex::new(1.0, 0.0))
                    .unwrap();
            }
        }
    }

    #[test]
    #[cfg(not(feature = "alloc"))]
    fn test_no_std_sparse_limits() {
        // In no_std, sparse is limited to 32 components
        let mut sparse = SparseCliffordElement::<f64>::zero(8);

        // Fill up to 32 components
        for i in 0..32 {
            assert!(sparse.set_component(i, Complex::new(1.0, 0.0)).is_ok());
        }

        // 33rd component should fail
        assert!(sparse.set_component(32, Complex::new(1.0, 0.0)).is_err());
    }

    #[test]
    fn test_lazy_evaluation_limits() {
        // Lazy evaluation allows larger dimensions than standard algebra
        assert!(LazyCliffordAlgebra::<f64>::generate(12).is_ok());
        assert!(LazyCliffordAlgebra::<f64>::generate(20).is_ok());
        // But still has practical limits
        assert!(LazyCliffordAlgebra::<f64>::generate(64).is_err());

        // Test that lazy evaluation actually saves memory
        if let Ok(lazy) = LazyCliffordAlgebra::<f64>::generate(10) {
            // Initially no elements cached
            let stats = lazy.memory_stats();
            assert_eq!(stats.cached_elements, 0);

            // Access a few elements
            lazy.basis_element(0).unwrap();
            lazy.basis_element(10).unwrap();
            lazy.basis_element(100).unwrap();

            let stats = lazy.memory_stats();
            assert_eq!(stats.cached_elements, 3);
            assert!(stats.cached_elements < stats.total_basis_elements);
        }
    }

    #[test]
    fn test_operation_complexity() {
        // Test how operations scale with dimension
        for n in 1..=8 {
            let algebra = CliffordAlgebra::<f64>::generate(n).unwrap();
            let e1 = CliffordElement::<f64>::basis_vector(0, n).unwrap();

            // Geometric product complexity: O(4^n) for dense elements
            let start = std::time::Instant::now();
            let _ = algebra.geometric_product(&e1, &e1).unwrap();
            let duration = start.elapsed();

            println!("Dimension {}: geometric product took {:?}", n, duration);
        }
    }

    #[test]
    fn test_arbitrary_precision_floats() {
        // Test with different float types
        let algebra_f32 = CliffordAlgebra::<f32>::generate(4).unwrap();
        let algebra_f64 = CliffordAlgebra::<f64>::generate(4).unwrap();

        // Both should work
        assert_eq!(algebra_f32.dimension(), 4);
        assert_eq!(algebra_f64.dimension(), 4);
    }

    #[test]
    fn test_memory_estimation() {
        // Calculate memory requirements for different dimensions
        println!("\nMemory requirements for CliffordElement:");
        for n in 1..=20 {
            let components = 1usize << n;
            let bytes_per_component = 16; // Complex<f64>
            let total_bytes = components * bytes_per_component;
            let mb = total_bytes as f64 / (1024.0 * 1024.0);

            println!(
                "n={:2}: 2^{:2} = {:8} components, {:8} bytes ({:.2} MB)",
                n, n, components, total_bytes, mb
            );

            if n > 12 {
                println!("     ^ Currently not supported due to hard limit");
            }
        }
    }

    #[test]
    fn test_dimension_independent_operations() {
        // Some operations should work regardless of dimension

        // Grade computation works for any index
        assert_eq!(CliffordElement::<f64>::grade_of_index(0), 0);
        assert_eq!(CliffordElement::<f64>::grade_of_index(7), 3); // 111 binary
        assert_eq!(CliffordElement::<f64>::grade_of_index(255), 8); // 11111111 binary

        // Bit pattern conversions work for any size
        use crate::clifford::CliffordAlgebra;
        assert_eq!(
            CliffordAlgebra::<f64>::bit_pattern_to_indices(5),
            vec![0, 2]
        );
        assert_eq!(CliffordAlgebra::<f64>::indices_to_bit_pattern(&[0, 2]), 5);
    }

    #[test]
    fn test_edge_case_dimensions() {
        // Test dimension 0 (should this be allowed?)
        assert!(CliffordAlgebra::<f64>::generate(0).is_ok());
        let elem = CliffordElement::<f64>::zero(0);
        assert_eq!(elem.num_components(), 1); // 2^0 = 1

        // Test dimension 1 (minimal non-trivial case)
        assert!(CliffordAlgebra::<f64>::generate(1).is_ok());
        let elem = CliffordElement::<f64>::zero(1);
        assert_eq!(elem.num_components(), 2); // 2^1 = 2
    }
}

#[cfg(all(test, feature = "std"))]
mod arbitrary_input_proposals {
    //! Proposals for handling truly arbitrary input

    use ccm_core::{CcmError, Float};
    use core::marker::PhantomData;

    /// Proposed: Element with configurable storage strategy
    pub enum StorageStrategy {
        Dense(usize),          // Up to n dimensions
        Sparse(usize),         // Sparse with dimension
        Implicit(usize),       // Don't store zeros at all
        Chunked(usize, usize), // Dimension and chunk size
    }

    /// Proposed: Dimension-aware element that chooses strategy
    pub struct AdaptiveCliffordElement<P: Float> {
        dimension: usize,
        strategy: StorageStrategy,
        _phantom: PhantomData<P>,
    }

    impl<P: Float> AdaptiveCliffordElement<P> {
        pub fn new(dimension: usize) -> Result<Self, CcmError> {
            let strategy = match dimension {
                0..=8 => StorageStrategy::Dense(dimension),
                9..=12 => StorageStrategy::Sparse(dimension),
                13..=20 => StorageStrategy::Implicit(dimension),
                _ => StorageStrategy::Chunked(dimension, 1024),
            };

            Ok(Self {
                dimension,
                strategy,
                _phantom: PhantomData,
            })
        }
    }

    /// Proposed: Builder pattern for large algebras
    pub struct CliffordAlgebraBuilder {
        dimension: Option<usize>,
        max_memory_mb: Option<usize>,
        storage_hint: Option<StorageStrategy>,
    }

    impl CliffordAlgebraBuilder {
        pub fn new() -> Self {
            Self {
                dimension: None,
                max_memory_mb: None,
                storage_hint: None,
            }
        }

        pub fn dimension(mut self, n: usize) -> Self {
            self.dimension = Some(n);
            self
        }

        pub fn max_memory_mb(mut self, mb: usize) -> Self {
            self.max_memory_mb = Some(mb);
            self
        }

        pub fn storage_hint(mut self, hint: StorageStrategy) -> Self {
            self.storage_hint = Some(hint);
            self
        }

        pub fn build<P: Float>(self) -> Result<Box<dyn CliffordAlgebraTrait<P>>, CcmError> {
            // Would create appropriate implementation based on constraints
            todo!("Implement adaptive algebra creation")
        }
    }

    /// Proposed: Trait for different algebra implementations
    pub trait CliffordAlgebraTrait<P: Float> {
        fn dimension(&self) -> usize;
        fn can_allocate_element(&self) -> bool;
        fn memory_estimate_mb(&self) -> usize;
    }
}
