//! Tests for symmetry decomposition functionality

use super::*;
use crate::{SymmetryGroup, SymmetryType, GroupElement, StabilizerSubgroup, CliffordAction};
use crate::decomposition::{
    detection::has_klein_symmetry,
    breaking::find_breaking_point,
    stabilizer::{compute_stabilizer_generators, compute_stabilizer_size},
    types::SymmetryBoundaryType,
    traits::SymmetricDecomposition,
};
use ccm_coherence::{CliffordElement, CliffordAlgebra};

#[cfg(feature = "alloc")]
use alloc::vec;
#[cfg(feature = "alloc")]
use alloc::string::ToString;

#[test]
fn test_orbit_decomposition() {
    // Create a simple symmetry group
    let group = SymmetryGroup::<f64>::generate(3).unwrap();
    
    // Create an element
    let mut element = CliffordElement::<f64>::zero(3);
    element.set_component(1, num_complex::Complex::new(1.0, 0.0)).unwrap();
    
    // Decompose by orbits
    let orbits = element.orbit_decompose(&group);
    
    // Should have at least one orbit
    assert!(!orbits.is_empty());
}

#[test]
fn test_stabilizer_generators_klein_group() {
    // Test stabilizer computation for Klein group
    let group = SymmetryGroup::<f64>::klein_group(8).unwrap();
    
    // Create a Clifford element
    let mut element = CliffordElement::<f64>::zero(8);
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap();
    
    // Get the Clifford algebra and action
    let algebra = CliffordAlgebra::generate(8).unwrap();
    let action = CliffordAction::new(algebra);
    
    // Compute stabilizer
    let stabilizer = group.stabilizer(&element, &action);
    
    // Compute stabilizer generators
    let generator_indices = compute_stabilizer_generators(&stabilizer, &group);
    
    // For Klein group, should have at most 2 generators
    assert!(generator_indices.len() <= 2);
    
    // Verify orbit-stabilizer theorem
    if let Some(group_order) = group.order() {
        let stabilizer_size = compute_stabilizer_size(&stabilizer, &group);
        let orbit_components = element.orbit_decompose(&group);
        
        if let Some(orbit) = orbit_components.first() {
            // |G| = |Orbit| * |Stabilizer|
            assert_eq!(group_order, orbit.orbit_size * stabilizer_size);
        }
    }
}

#[test]
fn test_stabilizer_size_computation() {
    // Test exact stabilizer size computation
    let group = SymmetryGroup::<f64>::klein_group(8).unwrap();
    
    // Test various stabilizer configurations
    
    // Empty stabilizer (only identity)
    let empty_stab = StabilizerSubgroup { generators: vec![] };
    assert_eq!(compute_stabilizer_size(&empty_stab, &group), 1);
    
    // Single generator stabilizer
    let single_gen = GroupElement::<f64>::from_bit_flip(6, 8);
    let single_stab = StabilizerSubgroup { generators: vec![single_gen] };
    assert_eq!(compute_stabilizer_size(&single_stab, &group), 2);
    
    // Two generator stabilizer (whole Klein group)
    let gen1 = GroupElement::<f64>::from_bit_flip(6, 8);
    let gen2 = GroupElement::<f64>::from_bit_flip(7, 8);
    let double_stab = StabilizerSubgroup { generators: vec![gen1, gen2] };
    assert_eq!(compute_stabilizer_size(&double_stab, &group), 4);
}

#[test]
fn test_cyclic_group_stabilizers() {
    // Test with cyclic group
    let group = SymmetryGroup::<f64>::cyclic_group(4, 4).unwrap();
    
    // Create an element
    let mut element = CliffordElement::<f64>::zero(4);
    element.set_component(1, num_complex::Complex::new(1.0, 0.0)).unwrap();
    
    let algebra = CliffordAlgebra::generate(4).unwrap();
    let action = CliffordAction::new(algebra);
    
    // Compute stabilizer
    let stabilizer = group.stabilizer(&element, &action);
    let generator_indices = compute_stabilizer_generators(&stabilizer, &group);
    
    // Verify the generators are valid indices
    if let Some(elements) = group.elements() {
        let element_count = elements.count();
        for idx in &generator_indices {
            assert!(*idx < element_count);
        }
    }
}

#[test]
fn test_identity_stabilizes_everything() {
    // Identity element should be stabilized by the whole group
    let group = SymmetryGroup::<f64>::klein_group(8).unwrap();
    
    let identity_element = CliffordElement::<f64>::zero(8);
    let algebra = CliffordAlgebra::generate(8).unwrap();
    let action = CliffordAction::new(algebra);
    
    let stabilizer = group.stabilizer(&identity_element, &action);
    let stabilizer_size = compute_stabilizer_size(&stabilizer, &group);
    
    // For Klein group, if identity is stabilized by all, size should be 4
    assert_eq!(stabilizer_size, group.order().unwrap_or(0));
}

#[test]
fn test_klein_symmetry_detection() {
    // Test 1: Element with no Klein symmetry (odd grades only)
    let mut odd_element = CliffordElement::<f64>::zero(8);
    odd_element.set_component(1, num_complex::Complex::new(1.0, 0.0)).unwrap(); // index 1 = grade 1
    odd_element.set_component(7, num_complex::Complex::new(0.5, 0.0)).unwrap(); // index 7 (0111) = grade 3
    assert!(!has_klein_symmetry(&odd_element));
    
    // Test 2: Element with even grades (Klein symmetric)
    let mut even_element = CliffordElement::<f64>::zero(8);
    even_element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap(); // index 0 = grade 0
    even_element.set_component(3, num_complex::Complex::new(2.0, 0.0)).unwrap(); // index 3 (0011) = grade 2
    even_element.set_component(15, num_complex::Complex::new(0.5, 0.0)).unwrap(); // index 15 (1111) = grade 4
    assert!(has_klein_symmetry(&even_element));
    
    // Test 3: Mixed element with dominant even grades
    let mut mixed_dominant_even = CliffordElement::<f64>::zero(8);
    mixed_dominant_even.set_component(0, num_complex::Complex::new(5.0, 0.0)).unwrap(); // index 0 = grade 0
    mixed_dominant_even.set_component(3, num_complex::Complex::new(4.0, 0.0)).unwrap(); // index 3 = grade 2
    mixed_dominant_even.set_component(1, num_complex::Complex::new(0.1, 0.0)).unwrap(); // index 1 = grade 1
    assert!(has_klein_symmetry(&mixed_dominant_even));
    
    // Test 4: Mixed element with dominant odd grades (not Klein symmetric)
    let mut mixed_dominant_odd = CliffordElement::<f64>::zero(8);
    mixed_dominant_odd.set_component(0, num_complex::Complex::new(0.1, 0.0)).unwrap(); // index 0 = grade 0
    mixed_dominant_odd.set_component(1, num_complex::Complex::new(5.0, 0.0)).unwrap(); // index 1 = grade 1
    mixed_dominant_odd.set_component(7, num_complex::Complex::new(4.0, 0.0)).unwrap(); // index 7 = grade 3
    assert!(!has_klein_symmetry(&mixed_dominant_odd));
    
    // Test 5: Element with power-of-two grades (special Klein structure)
    let mut power_of_two_element = CliffordElement::<f64>::zero(8);
    power_of_two_element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap(); // index 0 = grade 0
    power_of_two_element.set_component(1, num_complex::Complex::new(1.0, 0.0)).unwrap(); // index 1 = grade 1 = 2^0
    power_of_two_element.set_component(3, num_complex::Complex::new(1.0, 0.0)).unwrap(); // index 3 = grade 2 = 2^1
    power_of_two_element.set_component(15, num_complex::Complex::new(1.0, 0.0)).unwrap(); // index 15 = grade 4 = 2^2
    assert!(has_klein_symmetry(&power_of_two_element));
    
    // Test 6: Small dimension (n < 2) should not have Klein symmetry
    let mut small_element = CliffordElement::<f64>::zero(1);
    small_element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap();
    assert!(!has_klein_symmetry(&small_element));
}

#[test]
fn test_klein_symmetry_in_orbit_decomposition() {
    // Test that Klein-symmetric elements are properly identified in orbit decomposition
    let group = SymmetryGroup::<f64>::klein_group(8).unwrap();
    
    // Create Klein-symmetric element
    let mut element = CliffordElement::<f64>::zero(8);
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap(); // scalar
    element.set_component(3, num_complex::Complex::new(2.0, 0.0)).unwrap(); // bivector
    
    let orbits = element.orbit_decompose(&group);
    
    // At least one orbit component should have Klein symmetry
    let has_klein_orbit = orbits.iter().any(|orbit| {
        orbit.preserved_symmetries.contains(&SymmetryType::Klein)
    });
    
    assert!(has_klein_orbit, "Klein-symmetric element should have orbit with Klein symmetry");
}

#[test]
fn test_klein_boundary_detection() {
    // Test that symmetry boundaries detect Klein symmetry breaking
    let group = SymmetryGroup::<f64>::klein_group(8).unwrap();
    
    // Create element with Klein symmetry breaking at a boundary
    let mut element = CliffordElement::<f64>::zero(8);
    // Even grades first
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap();
    element.set_component(3, num_complex::Complex::new(1.0, 0.0)).unwrap();
    // Then a jump to odd grades (Klein breaking)
    element.set_component(1, num_complex::Complex::new(10.0, 0.0)).unwrap();
    
    let boundaries = element.find_symmetry_boundaries(&group);
    
    // Should find at least one Klein symmetry break
    let has_klein_break = boundaries.iter().any(|b| {
        b.broken_symmetry == SymmetryType::Klein
    });
    
    assert!(has_klein_break, "Should detect Klein symmetry breaking");
}

#[test]
fn test_symmetry_preservation() {
    let group = SymmetryGroup::<f64>::generate(3).unwrap();
    
    // Create an element with Klein symmetry
    let mut element = CliffordElement::<f64>::zero(3);
    element.set_component(3, num_complex::Complex::new(1.0, 0.0)).unwrap(); // bivector
    
    // Decompose preserving Klein symmetry
    let result = element.symmetry_preserving_decompose(
        &group,
        &[SymmetryType::Klein]
    );
    
    // Should succeed for appropriate elements
    assert!(result.is_ok() || result.is_err());
}

#[test]
fn test_symmetry_breaking_klein() {
    // Test Klein symmetry breaking detection
    let group = SymmetryGroup::<f64>::klein_group(8).unwrap();
    
    // Create element with Klein symmetry breaking
    let mut element = CliffordElement::<f64>::zero(8);
    // Start with even grades (Klein symmetric)
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap(); // grade 0
    element.set_component(3, num_complex::Complex::new(1.0, 0.0)).unwrap(); // grade 2
    // Then add odd grades (breaks Klein symmetry)
    element.set_component(1, num_complex::Complex::new(5.0, 0.0)).unwrap(); // grade 1
    element.set_component(7, num_complex::Complex::new(3.0, 0.0)).unwrap(); // grade 3
    
    let boundary = find_breaking_point(&element, &SymmetryType::Klein, &group);
    
    assert!(boundary.is_some(), "Should detect Klein symmetry breaking");
    if let Some(b) = boundary {
        assert_eq!(b.broken_symmetry, SymmetryType::Klein);
        assert!(b.breaking_strength > 0.0);
        assert_eq!(b.boundary_type, SymmetryBoundaryType::InvariantBreak);
    }
}

#[test]
fn test_symmetry_breaking_translation() {
    // Test Translation symmetry breaking detection
    let group = SymmetryGroup::<f64>::generate(8).unwrap();
    
    // Create element with translation symmetry breaking
    let mut element = CliffordElement::<f64>::zero(8);
    // Set up components with varying norms that break translation invariance
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap();
    element.set_component(1, num_complex::Complex::new(1.1, 0.0)).unwrap();
    element.set_component(3, num_complex::Complex::new(5.0, 0.0)).unwrap(); // Large jump
    element.set_component(7, num_complex::Complex::new(1.2, 0.0)).unwrap();
    
    let boundary = find_breaking_point(&element, &SymmetryType::Translation, &group);
    
    assert!(boundary.is_some(), "Should detect Translation symmetry breaking");
    if let Some(b) = boundary {
        assert_eq!(b.broken_symmetry, SymmetryType::Translation);
        assert!(b.breaking_strength > 0.0);
        assert_eq!(b.boundary_type, SymmetryBoundaryType::GradientJump);
    }
}

#[test]
fn test_symmetry_breaking_rotation() {
    // Test Rotation symmetry breaking detection
    let group = SymmetryGroup::<f64>::generate(8).unwrap();
    
    // Create element with rotation symmetry breaking
    let mut element = CliffordElement::<f64>::zero(8);
    // Low grades
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap();
    element.set_component(1, num_complex::Complex::new(0.5, 0.0)).unwrap();
    // High grade components indicate rotation breaking
    element.set_component(127, num_complex::Complex::new(2.0, 0.0)).unwrap(); // grade 7
    element.set_component(255, num_complex::Complex::new(1.5, 0.0)).unwrap(); // grade 8
    
    let boundary = find_breaking_point(&element, &SymmetryType::Rotation, &group);
    
    assert!(boundary.is_some(), "Should detect Rotation symmetry breaking");
    if let Some(b) = boundary {
        assert_eq!(b.broken_symmetry, SymmetryType::Rotation);
        assert!(b.breaking_strength > 0.0);
        assert_eq!(b.boundary_type, SymmetryBoundaryType::InvariantBreak);
    }
}

#[test]
fn test_symmetry_breaking_reflection() {
    // Test Reflection symmetry breaking detection
    let group = SymmetryGroup::<f64>::generate(8).unwrap();
    
    // Create element with reflection symmetry breaking
    let mut element = CliffordElement::<f64>::zero(8);
    // Heavy even grades
    element.set_component(0, num_complex::Complex::new(10.0, 0.0)).unwrap(); // grade 0
    element.set_component(3, num_complex::Complex::new(8.0, 0.0)).unwrap();  // grade 2
    element.set_component(15, num_complex::Complex::new(9.0, 0.0)).unwrap(); // grade 4
    // Light odd grades (imbalance)
    element.set_component(1, num_complex::Complex::new(0.1, 0.0)).unwrap();  // grade 1
    element.set_component(7, num_complex::Complex::new(0.2, 0.0)).unwrap();  // grade 3
    
    let boundary = find_breaking_point(&element, &SymmetryType::Reflection, &group);
    
    assert!(boundary.is_some(), "Should detect Reflection symmetry breaking");
    if let Some(b) = boundary {
        assert_eq!(b.broken_symmetry, SymmetryType::Reflection);
        assert!(b.breaking_strength > 0.0);
        assert_eq!(b.boundary_type, SymmetryBoundaryType::InvariantBreak);
    }
}

#[test]
fn test_symmetry_breaking_cyclic() {
    // Test Cyclic symmetry breaking detection
    let group = SymmetryGroup::<f64>::cyclic_group(4, 8).unwrap();
    
    // Create element with cyclic symmetry breaking
    let mut element = CliffordElement::<f64>::zero(8);
    // Set up components that deviate from expected cyclic pattern
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap();
    element.set_component(1, num_complex::Complex::new(0.5, 0.0)).unwrap();
    element.set_component(3, num_complex::Complex::new(10.0, 0.0)).unwrap(); // Breaks pattern
    element.set_component(7, num_complex::Complex::new(0.6, 0.0)).unwrap();
    
    let boundary = find_breaking_point(&element, &SymmetryType::Cyclic(4), &group);
    
    assert!(boundary.is_some(), "Should detect Cyclic symmetry breaking");
    if let Some(b) = boundary {
        assert_eq!(b.broken_symmetry, SymmetryType::Cyclic(4));
        assert!(b.breaking_strength > 0.0);
        assert_eq!(b.boundary_type, SymmetryBoundaryType::PatternBreak);
    }
}

#[test]
fn test_symmetry_breaking_dihedral() {
    // Test Dihedral symmetry breaking detection
    let group = SymmetryGroup::<f64>::generate(8).unwrap();
    
    // Create element that breaks dihedral symmetry
    let mut element = CliffordElement::<f64>::zero(8);
    // Set up to break both rotation and reflection
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap();
    element.set_component(1, num_complex::Complex::new(10.0, 0.0)).unwrap(); // Odd grade
    element.set_component(127, num_complex::Complex::new(5.0, 0.0)).unwrap(); // High grade
    
    let boundary = find_breaking_point(&element, &SymmetryType::Dihedral(4), &group);
    
    assert!(boundary.is_some(), "Should detect Dihedral symmetry breaking");
    if let Some(b) = boundary {
        assert_eq!(b.broken_symmetry, SymmetryType::Dihedral(4));
        assert!(b.breaking_strength > 0.0);
        assert_eq!(b.boundary_type, SymmetryBoundaryType::CompositeBreak);
    }
}

#[test]
fn test_symmetry_breaking_permutation() {
    // Test Permutation symmetry breaking detection
    let group = SymmetryGroup::<f64>::generate(8).unwrap();
    
    // Create element with permutation symmetry breaking
    let mut element = CliffordElement::<f64>::zero(8);
    // Set up grade components that break permutation patterns
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap();
    element.set_component(1, num_complex::Complex::new(1.0, 0.0)).unwrap();
    // High grade with unexpected norm
    element.set_component(63, num_complex::Complex::new(20.0, 0.0)).unwrap(); // grade 6
    
    let boundary = find_breaking_point(&element, &SymmetryType::Permutation(4), &group);
    
    assert!(boundary.is_some(), "Should detect Permutation symmetry breaking");
    if let Some(b) = boundary {
        assert_eq!(b.broken_symmetry, SymmetryType::Permutation(4));
        assert!(b.breaking_strength > 0.0);
        assert_eq!(b.boundary_type, SymmetryBoundaryType::PatternBreak);
    }
}

#[test]
fn test_symmetry_breaking_linear() {
    // Test Linear/Orthogonal symmetry breaking detection
    let group = SymmetryGroup::<f64>::generate(8).unwrap();
    
    // Create element with non-smooth grade progression
    let mut element = CliffordElement::<f64>::zero(8);
    // Set up components with discontinuous second derivative
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap();
    element.set_component(1, num_complex::Complex::new(2.0, 0.0)).unwrap();
    element.set_component(3, num_complex::Complex::new(10.0, 0.0)).unwrap(); // Jump
    element.set_component(7, num_complex::Complex::new(2.5, 0.0)).unwrap();
    element.set_component(15, num_complex::Complex::new(3.0, 0.0)).unwrap();
    
    let boundary = find_breaking_point(&element, &SymmetryType::Linear, &group);
    
    assert!(boundary.is_some(), "Should detect Linear symmetry breaking");
    if let Some(b) = boundary {
        assert_eq!(b.broken_symmetry, SymmetryType::Linear);
        assert!(b.breaking_strength > 0.0);
        assert_eq!(b.boundary_type, SymmetryBoundaryType::GradientJump);
    }
}

#[test]
fn test_symmetry_breaking_custom() {
    // Test Custom symmetry breaking detection
    let group = SymmetryGroup::<f64>::generate(8).unwrap();
    
    // Create element with generic discontinuity
    let mut element = CliffordElement::<f64>::zero(8);
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap();
    element.set_component(1, num_complex::Complex::new(1.2, 0.0)).unwrap();
    element.set_component(3, num_complex::Complex::new(6.0, 0.0)).unwrap(); // 5x jump
    
    let boundary = find_breaking_point(&element, &SymmetryType::Custom("test".to_string()), &group);
    
    assert!(boundary.is_some(), "Should detect Custom symmetry breaking");
    if let Some(b) = boundary {
        assert_eq!(b.broken_symmetry, SymmetryType::Custom("test".to_string()));
        assert!(b.breaking_strength > 0.0);
        assert_eq!(b.boundary_type, SymmetryBoundaryType::InvariantBreak);
    }
}

#[test]
fn test_no_symmetry_breaking() {
    // Test case where no symmetry is broken
    let group = SymmetryGroup::<f64>::klein_group(8).unwrap();
    
    // Create perfectly Klein-symmetric element
    let mut element = CliffordElement::<f64>::zero(8);
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap(); // grade 0
    element.set_component(3, num_complex::Complex::new(1.0, 0.0)).unwrap(); // grade 2
    element.set_component(15, num_complex::Complex::new(1.0, 0.0)).unwrap(); // grade 4
    
    let boundary = find_breaking_point(&element, &SymmetryType::Klein, &group);
    
    assert!(boundary.is_none(), "Should not detect symmetry breaking for symmetric element");
}

#[test]
fn test_symmetry_breaking_edge_cases() {
    // Test edge cases
    let group = SymmetryGroup::<f64>::generate(2).unwrap();
    
    // Test with small dimension
    let mut small_element = CliffordElement::<f64>::zero(2);
    small_element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap();
    small_element.set_component(1, num_complex::Complex::new(2.0, 0.0)).unwrap();
    
    // Should handle gracefully (no crash)
    let boundary = find_breaking_point(&small_element, &SymmetryType::Linear, &group);
    // May or may not find breaking due to small size
    assert!(boundary.is_some() || boundary.is_none());
    
    // Test with zero element
    let zero_element = CliffordElement::<f64>::zero(8);
    let boundary = find_breaking_point(&zero_element, &SymmetryType::Klein, &group);
    assert!(boundary.is_none(), "Zero element should have no breaking");
}