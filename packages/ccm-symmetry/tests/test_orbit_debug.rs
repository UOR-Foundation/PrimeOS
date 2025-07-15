use ccm_symmetry::{SymmetryGroup, SymmetricDecomposition};
use ccm_coherence::CliffordElement;

#[test]
fn debug_orbit_decomposition() {
    let group = SymmetryGroup::<f64>::klein_group(3).unwrap();
    
    println!("Group order: {:?}", group.order());
    
    if let Some(elements) = group.elements() {
        let elem_vec: Vec<_> = elements.collect();
        println!("Number of group elements: {}", elem_vec.len());
        for (i, g) in elem_vec.iter().enumerate() {
            println!("  Element {}: dimension = {}", i, g.dimension());
        }
    } else {
        println!("No elements available!");
    }
    
    // Create a simple element
    let mut element = CliffordElement::<f64>::zero(3);
    element.set_component(1, num_complex::Complex::new(1.0, 0.0)).unwrap();
    
    let orbits = element.orbit_decompose(&group);
    
    println!("Number of orbits: {}", orbits.len());
    for (i, orbit) in orbits.iter().enumerate() {
        println!("Orbit {}: size = {}, stabilizer generators = {}", 
                 i, orbit.orbit_size, orbit.stabilizer_generators.len());
    }
}