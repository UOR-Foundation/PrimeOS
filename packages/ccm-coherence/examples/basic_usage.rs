//! Basic usage examples for ccm-coherence

use ccm_coherence::{coherence_norm, coherence_product, CliffordAlgebra, CliffordElement};
use num_complex::Complex;

fn main() {
    println!("=== CCM Coherence Examples ===\n");

    // Example 1: Create a Clifford algebra
    println!("1. Creating Clifford algebra Cl(3)");
    let algebra = CliffordAlgebra::<f64>::generate(3).unwrap();
    println!("   Dimension: {}", algebra.dimension());
    println!(
        "   Number of basis elements: {}\n",
        algebra.num_basis_elements()
    );

    // Example 2: Create basis vectors
    println!("2. Creating basis vectors");
    let e1 = CliffordElement::<f64>::basis_vector(0, 3).unwrap();
    let e2 = CliffordElement::<f64>::basis_vector(1, 3).unwrap();
    println!("   e₁ has {} non-zero component(s)", count_nonzero(&e1));
    println!("   e₂ has {} non-zero component(s)\n", count_nonzero(&e2));

    // Example 3: Geometric product
    println!("3. Computing geometric product e₁ * e₂");
    let e12 = algebra.geometric_product(&e1, &e2).unwrap();
    println!("   Result is a bivector (grade 2)");
    println!("   Non-zero at index: {}\n", find_nonzero_index(&e12));

    // Example 4: Coherence inner product
    println!("4. Coherence inner product examples");
    let prod11 = coherence_product(&e1, &e1);
    let prod12 = coherence_product(&e1, &e2);
    println!("   ⟨⟨e₁, e₁⟩⟩ = {:.2}", prod11.re);
    println!("   ⟨⟨e₁, e₂⟩⟩ = {:.2} (orthogonal)\n", prod12.norm());

    // Example 5: Wedge and inner products
    println!("5. Wedge and inner products");
    let wedge = algebra.wedge_product(&e1, &e2).unwrap();
    let inner = algebra.inner_product(&e1, &e12).unwrap();
    println!(
        "   e₁ ∧ e₂ gives bivector at index {}",
        find_nonzero_index(&wedge)
    );
    println!(
        "   e₁ · (e₁e₂) gives vector at index {}\n",
        find_nonzero_index(&inner)
    );

    // Example 6: Create a general element
    println!("6. Creating a general Clifford element");
    let mut general = CliffordElement::<f64>::zero(3);
    general.set_component(0, Complex::new(2.0, 0.0)).unwrap(); // scalar
    general.set_component(1, Complex::new(3.0, 0.0)).unwrap(); // e₁
    general.set_component(3, Complex::new(1.0, 0.0)).unwrap(); // e₁e₂

    let norm = coherence_norm(&general);
    println!("   Element: 2 + 3e₁ + e₁e₂");
    println!("   Coherence norm: {:.2}\n", norm);

    // Example 7: Grade decomposition
    println!("7. Grade decomposition");
    let grade0 = general.grade(0);
    let grade1 = general.grade(1);
    let grade2 = general.grade(2);
    println!("   Grade 0 (scalar): norm = {:.2}", coherence_norm(&grade0));
    println!("   Grade 1 (vector): norm = {:.2}", coherence_norm(&grade1));
    println!(
        "   Grade 2 (bivector): norm = {:.2}",
        coherence_norm(&grade2)
    );
}

// Helper functions
fn count_nonzero<T: ccm_core::Float>(elem: &CliffordElement<T>) -> usize {
    (0..elem.num_components())
        .filter(|&i| {
            elem.component(i)
                .map(|c| c.norm() > T::epsilon())
                .unwrap_or(false)
        })
        .count()
}

fn find_nonzero_index<T: ccm_core::Float>(elem: &CliffordElement<T>) -> usize {
    (0..elem.num_components())
        .find(|&i| {
            elem.component(i)
                .map(|c| c.norm() > T::epsilon())
                .unwrap_or(false)
        })
        .unwrap_or(0)
}
