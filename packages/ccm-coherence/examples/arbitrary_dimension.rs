//! Example demonstrating support for arbitrary dimensions

use ccm_coherence::arbitrary_support::{ArbitraryCliffordAlgebra, ArbitraryDimensionConfig};
use ccm_coherence::lazy::LazyCliffordAlgebra;
use ccm_coherence::sparse::SparseCliffordElement;
use ccm_coherence::{CliffordAlgebra, CliffordElement};

fn main() {
    println!("=== Arbitrary Dimension Support ===\n");

    // Example 1: Standard limit (12 dimensions)
    println!("1. Standard dimension limit:");
    match CliffordAlgebra::<f64>::generate(12) {
        Ok(_) => println!("   ✓ Dimension 12: Success"),
        Err(e) => println!("   ✗ Dimension 12: Failed - {:?}", e),
    }

    match CliffordAlgebra::<f64>::generate(13) {
        Ok(_) => println!("   ✗ Dimension 13: Should have failed!"),
        Err(_) => println!("   ✓ Dimension 13: Correctly rejected (exceeds default limit)"),
    }

    // Example 2: Custom limit
    println!("\n2. Custom dimension limit:");
    match CliffordAlgebra::<f64>::generate_with_limit(16, 20) {
        Ok(algebra) => {
            println!("   ✓ Dimension 16 with limit 20: Success");
            println!("   Total basis elements: {}", algebra.num_basis_elements());
        }
        Err(e) => println!("   ✗ Dimension 16: Failed - {:?}", e),
    }

    // Example 3: Arbitrary dimension support
    println!("\n3. Arbitrary dimension algebra:");
    let config = ArbitraryDimensionConfig {
        max_dense_dimension: 12,
        max_memory_mb: 1000,
        check_overflow: true,
    };

    match ArbitraryCliffordAlgebra::<f64>::generate(20, config.clone()) {
        Ok(algebra) => {
            println!("   ✓ Dimension 20: Success");
            println!(
                "   Can allocate full element: {}",
                algebra.can_allocate_element()
            );
            println!(
                "   Estimated memory: {} MB",
                ArbitraryCliffordAlgebra::<f64>::estimate_memory_mb(20)
            );

            // Create sparse basis elements
            if let Ok(e0) = algebra.basis_element_lazy(1) {
                println!("   Created sparse basis element e₀");
                println!("   Grade: {}", e0.grade());
            }
        }
        Err(e) => println!("   ✗ Dimension 20: Failed - {:?}", e),
    }

    // Example 4: Lazy evaluation for large dimensions
    println!("\n4. Lazy evaluation:");
    match LazyCliffordAlgebra::<f64>::generate(10) {
        Ok(lazy) => {
            println!("   ✓ Created lazy algebra with dimension 10");

            // Access specific elements without allocating all 1024
            let _ = lazy.basis_element(0);
            let _ = lazy.basis_element(100);
            let _ = lazy.basis_element(500);

            let stats = lazy.memory_stats();
            println!("   Total basis elements: {}", stats.total_basis_elements);
            println!("   Cached elements: {}", stats.cached_elements);
            println!("   Cache percentage: {:.1}%", stats.cache_percentage());
            println!("   Memory saved: {} bytes", stats.memory_saved_bytes());
        }
        Err(e) => println!("   ✗ Lazy algebra failed: {:?}", e),
    }

    // Example 5: Sparse representation
    println!("\n5. Sparse representation:");
    let sparse = SparseCliffordElement::<f64>::zero(100); // 100 dimensions!
    println!("   ✓ Created sparse element with dimension 100");
    println!("   Non-zero components: {}", sparse.nnz());

    // Example 6: Memory requirements
    println!("\n6. Memory requirements for different dimensions:");
    println!("   Dim | Components | Memory (MB) | Feasible?");
    println!("   ----|------------|-------------|----------");
    for n in [8, 12, 16, 20, 24, 30, 40, 50] {
        let components = if n < 64 { 1usize << n } else { usize::MAX };
        let mb = if n < 64 {
            (components as f64 * 16.0) / (1024.0 * 1024.0)
        } else {
            f64::INFINITY
        };
        let feasible = mb < 1000.0; // 1GB threshold

        println!(
            "   {:3} | {:10} | {:11.2} | {}",
            n,
            if n < 64 {
                components.to_string()
            } else {
                "overflow".to_string()
            },
            mb,
            if feasible { "Yes" } else { "No" }
        );
    }

    // Example 7: Operations on large sparse elements
    println!("\n7. Operations on large dimensions:");
    use ccm_coherence::arbitrary_support::operations;

    // Multiply e₁ * e₂ in any dimension
    let sign = operations::multiplication_sign(0b01, 0b10);
    let result_idx = operations::multiply_indices(0b01, 0b10);
    println!("   e₁ * e₂ = {}e₁₂", if sign > 0 { "+" } else { "-" });
    println!("   Result index: {} (binary: {:b})", result_idx, result_idx);
}

#[cfg(feature = "std")]
fn print_separator() {
    println!("{}", "-".repeat(50));
}
