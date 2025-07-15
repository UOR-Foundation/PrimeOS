//! Tests for symmetry-based decomposition

use ccm_symmetry::{SymmetricDecomposition, SymmetryGroup, SymmetryType, SymmetryBoundaryType};
use ccm_coherence::{CliffordElement, CoherentDecomposition};

#[test]
fn test_symmetry_boundaries() {
    // Create element with grade transitions
    let mut element = CliffordElement::<f64>::zero(3);
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap(); // grade 0
    element.set_component(3, num_complex::Complex::new(10.0, 0.0)).unwrap(); // grade 2 (bivector)
    element.set_component(7, num_complex::Complex::new(5.0, 0.0)).unwrap(); // grade 3 (trivector)
    
    let group = SymmetryGroup::<f64>::generate(3).unwrap();
    let boundaries = element.find_symmetry_boundaries(&group);
    
    // Should find boundaries due to grade transitions and magnitude jumps
    assert!(!boundaries.is_empty());
    
    // Should find at least one Klein break (grade 2 is special for Klein)
    assert!(boundaries.iter().any(|b| b.broken_symmetry == SymmetryType::Klein));
}

#[test]
fn test_klein_preserving_decomposition() {
    // Create element with even grades (Klein-compatible)
    let mut element = CliffordElement::<f64>::zero(3);
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap(); // grade 0
    element.set_component(3, num_complex::Complex::new(2.0, 0.0)).unwrap(); // grade 2 (e1e2)
    
    // Use Klein group which is finite and has proper Klein symmetry detection
    let group = SymmetryGroup::<f64>::klein_group(3).unwrap();
    let result = element.symmetry_preserving_decompose(&group, &[SymmetryType::Klein]);
    
    assert!(result.is_ok());
    let parts = result.unwrap();
    
    // Should have non-empty decomposition
    assert!(!parts.is_empty());
    
    // Each part should have even grade
    for part in &parts {
        let grades = part.grade_decompose();
        assert!(grades.iter().all(|gc| gc.grade % 2 == 0 || gc.coherence_norm < 1e-10));
    }
}

#[test]
fn test_symmetric_decomposition_verification() {
    // Create an element with more symmetry - a scalar plus a bivector
    let mut element = CliffordElement::<f64>::zero(3);
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap(); // scalar
    element.set_component(3, num_complex::Complex::new(2.0, 0.0)).unwrap(); // e1e2 bivector
    
    // Decompose by grades
    let parts = element.grade_decompose()
        .into_iter()
        .map(|gc| gc.component)
        .collect::<Vec<_>>();
    
    // Verify the decomposition
    let group = SymmetryGroup::<f64>::generate(3).unwrap();
    assert!(element.verify_symmetric_decomposition(&parts, &group));
    
    // Invalid decomposition (missing parts)
    let incomplete = vec![parts[0].clone()];
    assert!(!element.verify_symmetric_decomposition(&incomplete, &group));
}

#[test]
fn test_orbit_decomposition() {
    let group = SymmetryGroup::<f64>::klein_group(3).unwrap();
    
    // Create a simple element
    let mut element = CliffordElement::<f64>::zero(3);
    element.set_component(1, num_complex::Complex::new(1.0, 0.0)).unwrap();
    
    let orbits = element.orbit_decompose(&group);
    
    // Should have at least one orbit component
    assert!(!orbits.is_empty());
    
    // Each orbit should have valid size
    for orbit in &orbits {
        assert!(orbit.orbit_size > 0);
        assert!(orbit.orbit_size <= 4); // Klein group has order 4
    }
}

#[test]
fn test_grade_structure_conservation() {
    use ccm_symmetry::decomposition::conservation::{verify_symmetry_conservation, SymmetryConservationMode};
    
    // Create element with multiple grades
    let mut whole = CliffordElement::<f64>::zero(3);
    whole.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap(); // grade 0
    whole.set_component(1, num_complex::Complex::new(2.0, 0.0)).unwrap(); // grade 1
    whole.set_component(3, num_complex::Complex::new(3.0, 0.0)).unwrap(); // grade 2
    
    // Decompose by grades
    let parts = whole.grade_decompose()
        .into_iter()
        .map(|gc| gc.component)
        .collect::<Vec<_>>();
    
    // Check invariants are preserved
    let group = SymmetryGroup::<f64>::generate(3).unwrap();
    assert!(verify_symmetry_conservation(
        &whole,
        &parts,
        &group,
        SymmetryConservationMode::Invariants
    ));
}

#[test]
fn test_norm_preservation() {
    use ccm_symmetry::decomposition::conservation::{verify_symmetry_conservation, SymmetryConservationMode};
    
    // Create orthogonal components
    let mut part1 = CliffordElement::<f64>::zero(3);
    part1.set_component(1, num_complex::Complex::new(3.0, 0.0)).unwrap(); // e1
    
    let mut part2 = CliffordElement::<f64>::zero(3);
    part2.set_component(2, num_complex::Complex::new(4.0, 0.0)).unwrap(); // e2
    
    let whole = part1.clone() + part2.clone();
    let parts = vec![part1, part2];
    
    // For orthogonal components, invariants should be preserved
    // (OrbitSize doesn't make sense for continuous groups)
    let group = SymmetryGroup::<f64>::generate(3).unwrap();
    assert!(verify_symmetry_conservation(
        &whole,
        &parts,
        &group,
        SymmetryConservationMode::Invariants
    ));
}

#[test]
fn test_symmetry_breaking_boundaries() {
    // Create element with symmetry breaking
    let mut element = CliffordElement::<f64>::zero(4);
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap(); // grade 0
    element.set_component(3, num_complex::Complex::new(100.0, 0.0)).unwrap(); // grade 2 - large jump
    
    let group = SymmetryGroup::<f64>::generate(4).unwrap();
    let boundaries = element.find_symmetry_boundaries(&group);
    
    // Should find Klein break due to large grade 2 component
    let klein_breaks: Vec<_> = boundaries.iter()
        .filter(|b| b.broken_symmetry == SymmetryType::Klein)
        .collect();
    
    assert!(!klein_breaks.is_empty());
    assert!(klein_breaks[0].breaking_strength > 10.0); // Large magnitude change
}

#[test]
fn test_maximal_symmetric_decomposition() {
    use ccm_symmetry::decomposition::strategies::maximal_symmetric_decomposition;
    
    // Create element with mixed symmetries
    let mut element = CliffordElement::<f64>::zero(3);
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap(); // scalar - high symmetry
    element.set_component(1, num_complex::Complex::new(0.1, 0.0)).unwrap(); // vector - lower symmetry
    element.set_component(3, num_complex::Complex::new(2.0, 0.0)).unwrap(); // bivector - Klein symmetry
    
    let group = SymmetryGroup::<f64>::generate(3).unwrap();
    let parts = maximal_symmetric_decomposition(&element, &group);
    
    // Should decompose into parts with different symmetry levels
    assert!(!parts.is_empty());
    assert!(parts.len() <= 3); // At most one part per grade in this case
}

#[test]
fn test_klein_symmetric_decomposition() {
    use ccm_symmetry::decomposition::strategies::klein_symmetric_decomposition;
    
    // Create element with Klein-compatible structure
    let mut element = CliffordElement::<f64>::zero(4);
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap(); // grade 0
    element.set_component(3, num_complex::Complex::new(2.0, 0.0)).unwrap(); // grade 2 (e1e2)
    element.set_component(5, num_complex::Complex::new(3.0, 0.0)).unwrap(); // grade 2 (e1e3)
    element.set_component(15, num_complex::Complex::new(4.0, 0.0)).unwrap(); // grade 4
    
    let parts = klein_symmetric_decomposition(&element);
    
    // Should extract even-grade components
    assert!(!parts.is_empty());
    
    // Verify all parts have even grades
    for part in &parts {
        let grades = part.grade_decompose();
        for gc in grades {
            if gc.coherence_norm > 1e-10 {
                assert_eq!(gc.grade % 2, 0);
            }
        }
    }
}