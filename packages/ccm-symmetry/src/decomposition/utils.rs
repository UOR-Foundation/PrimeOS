//! Utility functions for decomposition operations
//!
//! This module provides common helper functions used throughout the
//! decomposition system.

use ccm_coherence::CliffordElement;
use ccm_core::Float;


/// Check if two Clifford elements are equal within tolerance
///
/// Elements are considered equal if their difference has a coherence norm
/// smaller than a small multiple of machine epsilon.
///
/// # Arguments
///
/// * `a` - First element to compare
/// * `b` - Second element to compare
///
/// # Returns
///
/// `true` if the elements are equal within tolerance, `false` otherwise
pub fn elements_equal<P: Float>(a: &CliffordElement<P>, b: &CliffordElement<P>) -> bool {
    let diff = a.clone() - b.clone();
    diff.coherence_norm() < P::epsilon() * P::from(10.0).unwrap()
}

/// Check if two parameter vectors are equal within tolerance
///
/// Parameter vectors are considered equal if they have the same length and
/// all corresponding elements differ by less than machine epsilon.
///
/// # Arguments
///
/// * `a` - First parameter vector
/// * `b` - Second parameter vector
///
/// # Returns
///
/// `true` if the vectors are equal within tolerance, `false` otherwise
pub fn elements_equal_params<P: Float>(a: &[P], b: &[P]) -> bool {
    a.len() == b.len() && 
    a.iter().zip(b.iter()).all(|(x, y)| (*x - *y).abs() < P::epsilon())
}

/// Compute the sum of a collection of Clifford elements
///
/// # Arguments
///
/// * `parts` - Slice of Clifford elements to sum
///
/// # Returns
///
/// The sum of all elements
///
/// # Panics
///
/// Panics if the slice is empty
pub fn parts_sum<P: Float>(parts: &[CliffordElement<P>]) -> CliffordElement<P> {
    assert!(!parts.is_empty(), "Cannot sum empty collection");
    
    let mut sum = CliffordElement::zero(parts[0].dimension());
    for part in parts {
        sum = sum + part.clone();
    }
    sum
}

/// Check if two invariant vectors are equal within tolerance
///
/// Invariant vectors are considered equal if they have the same length and
/// all corresponding elements differ by less than a larger tolerance suitable
/// for numerical computations.
///
/// # Arguments
///
/// * `a` - First invariant vector
/// * `b` - Second invariant vector
///
/// # Returns
///
/// `true` if the invariants are equal within tolerance, `false` otherwise
pub fn invariants_equal<P: Float>(a: &[P], b: &[P]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let tolerance = P::epsilon() * P::from(100.0).unwrap();
    a.iter().zip(b.iter()).all(|(x, y)| (*x - *y).abs() < tolerance)
}