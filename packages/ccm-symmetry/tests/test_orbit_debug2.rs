use ccm_symmetry::{SymmetryGroup, SymmetricDecomposition, CliffordAction};
use ccm_coherence::{CliffordElement, CliffordAlgebra};

#[test]
fn debug_orbit_decomposition_detailed() {
    let group = SymmetryGroup::<f64>::klein_group(3).unwrap();
    
    // Create a simple element
    let mut element = CliffordElement::<f64>::zero(3);
    element.set_component(1, num_complex::Complex::new(1.0, 0.0)).unwrap();
    
    println!("Starting element dimension: {}", element.dimension());
    
    // Manually test the orbit computation
    if let Some(elements) = group.elements() {
        let algebra = CliffordAlgebra::generate(element.dimension()).unwrap();
        let action = CliffordAction::new(algebra);
        
        let mut count = 0;
        for g in elements {
            println!("Applying group element {} to Clifford element", count);
            match group.apply(&g, &element, &action) {
                Ok(transformed) => {
                    println!("  Success! Transformed norm: {}", transformed.coherence_norm());
                },
                Err(e) => {
                    println!("  Failed with error: {:?}", e);
                }
            }
            count += 1;
        }
    }
    
    // Now test the full orbit_decompose
    let orbits = element.orbit_decompose(&group);
    println!("\nFinal orbit count: {}", orbits.len());
}