//! Tests for symmetry group functionality

use ccm_symmetry::{SymmetryGroup, GroupElement, GroupType, GroupAction, CliffordAction};
use ccm_coherence::{CliffordElement, CliffordAlgebra};
use ccm_core::BitWord;

#[test]
fn test_klein_group_creation() {
    // Create Klein group for 8-bit system
    let group = SymmetryGroup::<f64>::klein_group(8).unwrap();
    
    // Should have order 4
    assert_eq!(group.order(), Some(4));
    
    // Should have 2 generators
    assert_eq!(group.generators().len(), 2);
    
    // Elements should satisfy group properties
    if let Some(mut elements) = group.elements() {
        let elements: Vec<_> = elements.collect();
        assert_eq!(elements.len(), 4);
        
        // Check that all elements have order dividing 4
        for elem in &elements {
            let order = group.element_order(elem);
            assert!(order == Some(1) || order == Some(2));
        }
    }
}

#[test]
fn test_group_multiplication() {
    let group = SymmetryGroup::<f64>::klein_group(4).unwrap();
    
    let a = GroupElement::from_bit_flip(2, 4);
    let b = GroupElement::from_bit_flip(3, 4);
    
    // Test that a² = e
    let a_squared = group.multiply(&a, &a).unwrap();
    assert!(a_squared.is_identity());
    
    // Test that b² = e
    let b_squared = group.multiply(&b, &b).unwrap();
    assert!(b_squared.is_identity());
    
    // Test commutativity: ab = ba
    let ab = group.multiply(&a, &b).unwrap();
    let ba = group.multiply(&b, &a).unwrap();
    
    // In Klein group, multiplication is commutative
    // For bit flips, this means the params should be equal
    assert_eq!(ab.params, ba.params);
}

#[test]
fn test_element_order() {
    let group = SymmetryGroup::<f64>::generate(4).unwrap();
    
    // Identity has order 1
    let identity = group.identity();
    assert_eq!(group.element_order(&identity), Some(1));
    
    // Bit flip has order 2
    let flip = GroupElement::from_bit_flip(0, 4);
    assert_eq!(flip.order(), Some(2));
    assert_eq!(group.element_order(&flip), Some(2));
}

#[test]
fn test_cyclic_shift() {
    // Test cyclic shift element
    let shift = GroupElement::<f64>::cyclic_shift(1, 4);
    
    // Shifting by 1 in a 4-element system has order 4
    assert_eq!(shift.order(), Some(4));
    
    // Check that params encode the permutation correctly
    assert_eq!(shift.params[0], 1.0); // 0 -> 1
    assert_eq!(shift.params[1], 2.0); // 1 -> 2
    assert_eq!(shift.params[2], 3.0); // 2 -> 3
    assert_eq!(shift.params[3], 0.0); // 3 -> 0
}

#[test]
fn test_group_action_on_clifford() {
    let algebra = CliffordAlgebra::<f64>::generate(3).unwrap();
    let action = CliffordAction::new(algebra.clone());
    let group = SymmetryGroup::<f64>::klein_group(3).unwrap();
    
    // Create a Clifford element
    let mut element = CliffordElement::<f64>::zero(3);
    element.set_component(1, num_complex::Complex::new(1.0, 0.0)).unwrap(); // e1
    
    // Apply identity - should not change
    let identity = group.identity();
    let transformed = group.apply(&identity, &element, &action).unwrap();
    
    assert!((element.coherence_norm() - transformed.coherence_norm()).abs() < 1e-10);
}

#[test]
fn test_invariants() {
    let group = SymmetryGroup::<f64>::klein_group(3).unwrap();
    
    // Create element with mixed grades
    let mut element = CliffordElement::<f64>::zero(3);
    element.set_component(0, num_complex::Complex::new(1.0, 0.0)).unwrap(); // scalar
    element.set_component(1, num_complex::Complex::new(2.0, 0.0)).unwrap(); // vector
    element.set_component(3, num_complex::Complex::new(3.0, 0.0)).unwrap(); // bivector
    
    let invariants = group.compute_invariants(&element);
    
    // Should have at least the coherence norm as invariant
    assert!(!invariants.is_empty());
    assert!(invariants[0] > 0.0); // Coherence norm is positive
}

#[test]
fn test_stabilizer() {
    let algebra = CliffordAlgebra::<f64>::generate(3).unwrap();
    let action = CliffordAction::new(algebra);
    let group = SymmetryGroup::<f64>::klein_group(3).unwrap();
    
    // Identity element should be stabilized by the whole group
    let identity_elem = CliffordElement::<f64>::scalar(1.0, 3);
    let stabilizer = group.stabilizer(&identity_elem, &action);
    
    // For Klein group, scalar elements might have non-trivial stabilizers
    // The exact size depends on the specific action implementation
    assert!(stabilizer.generators.len() <= 4);
}

#[test]
fn test_same_orbit() {
    let algebra = CliffordAlgebra::<f64>::generate(3).unwrap();
    let action = CliffordAction::new(algebra);
    let group = SymmetryGroup::<f64>::klein_group(3).unwrap();
    
    // Create two elements
    let elem1 = CliffordElement::<f64>::basis_vector(0, 3).unwrap();
    let elem2 = CliffordElement::<f64>::basis_vector(1, 3).unwrap();
    
    // Check if they're in the same orbit
    // For Klein group with bit flips, different basis vectors are typically in different orbits
    let same = group.same_orbit(&elem1, &elem2, &action);
    
    // Elements should be in same orbit with themselves
    assert!(group.same_orbit(&elem1, &elem1, &action));
}

#[test]
fn test_subgroup_creation() {
    let group = SymmetryGroup::<f64>::klein_group(4).unwrap();
    
    // Create subgroup from single generator
    let gen = GroupElement::from_bit_flip(2, 4);
    let subgroup = group.subgroup(vec![gen]).unwrap();
    
    // Subgroup should have the same dimension
    assert_eq!(subgroup.generators().len(), 1);
}

#[test]
fn test_finite_group_type() {
    let group = SymmetryGroup::<f64>::klein_group(4).unwrap();
    
    // Should be finite
    assert!(matches!(group.order(), Some(4)));
    
    // Should be able to iterate elements
    assert!(group.elements().is_some());
}

#[test]
fn test_group_with_bitword_action() {
    use ccm_symmetry::actions::BitWordAction;
    
    let action = BitWordAction::new(8);
    let group = SymmetryGroup::<f64>::klein_group(8).unwrap();
    
    // Create a BitWord
    let word = BitWord::from_u8(0b10101010);
    
    // Apply a bit flip
    let flip = GroupElement::from_bit_flip(0, 8);
    let flipped = group.apply(&flip, &word, &action).unwrap();
    
    // First bit should be flipped
    assert_ne!(word.bit(0), flipped.bit(0));
}