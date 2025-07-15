use ccm_symmetry::{SymmetryGroup, SymmetricDecomposition, CliffordAction};
use ccm_coherence::{CliffordElement, CliffordAlgebra};
use ccm_symmetry::decomposition::utils::elements_equal;

#[test]
fn debug_orbit_logic() {
    let group = SymmetryGroup::<f64>::klein_group(3).unwrap();
    
    // Create a simple element
    let mut element = CliffordElement::<f64>::zero(3);
    element.set_component(1, num_complex::Complex::new(1.0, 0.0)).unwrap();
    
    // Manually simulate the orbit decomposition logic
    let mut components = Vec::new();
    let mut processed = Vec::new();
    
    if let Some(elements) = group.elements() {
        let algebra = CliffordAlgebra::generate(element.dimension()).unwrap();
        let action = CliffordAction::new(algebra);
        
        for (idx, g) in elements.enumerate() {
            println!("\nProcessing group element {}", idx);
            let transformed = group.apply(&g, &element, &action).unwrap();
            println!("  Transformed norm: {}", transformed.coherence_norm());
            
            // Check against components
            let mut already_in_components = false;
            for (i, comp) in components.iter().enumerate() {
                if elements_equal(&comp, &transformed) {
                    println!("  Already in components at index {}", i);
                    already_in_components = true;
                    break;
                }
            }
            
            // Check against processed
            let mut already_in_processed = false;
            for (i, proc) in processed.iter().enumerate() {
                if elements_equal(&proc, &transformed) {
                    println!("  Already in processed at index {}", i);
                    already_in_processed = true;
                    break;
                }
            }
            
            if !already_in_components && !already_in_processed {
                println!("  New orbit found! Adding to components.");
                components.push(transformed.clone());
                processed.push(transformed);
            } else {
                println!("  Already seen, skipping.");
            }
        }
    }
    
    println!("\nFinal component count: {}", components.len());
    
    // Test elements_equal function
    println!("\nTesting elements_equal:");
    let mut elem1 = CliffordElement::<f64>::zero(3);
    elem1.set_component(1, num_complex::Complex::new(1.0, 0.0)).unwrap();
    let elem2 = elem1.clone();
    println!("elem1 == elem2: {}", elements_equal(&elem1, &elem2));
    
    let mut elem3 = CliffordElement::<f64>::zero(3);
    elem3.set_component(1, num_complex::Complex::new(1.1, 0.0)).unwrap();
    println!("elem1 == elem3: {}", elements_equal(&elem1, &elem3));
}