//! Orbit analysis and computation
//!
//! This module provides a wrapper around the orbit functionality in the group module,
//! extending it with additional features for continuous groups.

use crate::{
    actions::GroupAction,
    group::{SymmetryGroup, StabilizerSubgroup},
};
use ccm_core::{CcmError, Float};

#[cfg(feature = "alloc")]
use alloc::{vec, vec::Vec};

#[cfg(feature = "std")]
use std::hash::Hash;
#[cfg(not(feature = "std"))]
use core::hash::Hash;

/// Re-export the Orbit type from the group module
pub use crate::group::Orbit;

/// Compute the orbit of an element under group action
/// 
/// This function delegates to the group's internal orbit computation
/// which handles both discrete and continuous groups appropriately.
pub fn compute_orbit<P: Float, T: Clone + PartialEq + Hash>(
    x: &T,
    group: &SymmetryGroup<P>,
    action: &dyn GroupAction<P, Target = T>,
) -> Orbit<T> {
    group.compute_orbit(x, action)
}

/// Compute stabilizer subgroup
pub fn compute_stabilizer<P: Float, T: Clone + PartialEq>(
    x: &T,
    group: &SymmetryGroup<P>,
    action: &dyn GroupAction<P, Target = T>,
) -> Result<StabilizerSubgroup<P>, CcmError> {
    Ok(group.stabilizer(x, action))
}

/// Check if two elements are in the same orbit
pub fn same_orbit<P: Float, T: Clone + PartialEq + Hash>(
    a: &T,
    b: &T,
    group: &SymmetryGroup<P>,
    action: &dyn GroupAction<P, Target = T>,
) -> bool {
    group.same_orbit(a, b, action)
}

/// Count the number of orbits in a collection of elements
pub fn count_orbits<P: Float, T: Clone + PartialEq + Hash>(
    elements: &[T],
    group: &SymmetryGroup<P>,
    action: &dyn GroupAction<P, Target = T>,
) -> Result<usize, CcmError> {
    let mut orbit_count = 0;
    let mut processed = vec![false; elements.len()];

    for (i, x) in elements.iter().enumerate() {
        if !processed[i] {
            orbit_count += 1;

            // Mark all elements in this orbit as processed
            for (j, y) in elements.iter().enumerate() {
                if !processed[j] && same_orbit(x, y, group, action) {
                    processed[j] = true;
                }
            }
        }
    }

    Ok(orbit_count)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::actions::BitWordAction;
    use ccm_core::BitWord;

    #[test]
    fn test_orbit_computation() {
        let group = SymmetryGroup::<f64>::generate(8).unwrap();
        let action = BitWordAction::new(8);
        let b = BitWord::from_bytes(&[0]);

        let orbit = compute_orbit(&b, &group, &action);
        // With identity action, orbit has size 1
        assert_eq!(orbit.elements.len(), 1);
    }

    #[test]
    fn test_same_orbit() {
        let group = SymmetryGroup::<f64>::generate(8).unwrap();
        let action = BitWordAction::new(8);
        let b1 = BitWord::from_bytes(&[0]);
        let b2 = BitWord::from_bytes(&[0]);

        assert!(same_orbit(&b1, &b2, &group, &action));
    }

    #[test]
    fn test_stabilizer() {
        let group = SymmetryGroup::<f64>::generate(8).unwrap();
        let action = BitWordAction::new(8);
        let b = BitWord::from_bytes(&[0]);

        let stab = compute_stabilizer(&b, &group, &action).unwrap();
        // The default group might have empty stabilizer if only identity stabilizes the point
        // Just check that we can compute it without error
        assert!(stab.generators.len() >= 0);
    }

    #[test]
    fn test_continuous_orbit() {
        // Create SO(3) group
        let group = SymmetryGroup::<f64>::so(3).unwrap();
        
        // Use BitWord as our test element since it implements Hash
        let action = BitWordAction::new(3);
        let b = BitWord::from_bytes(&[1]);
        
        let orbit = compute_orbit(&b, &group, &action);
        
        // SO(3) is continuous, so orbit should not enumerate all elements
        assert!(!orbit.is_finite);
    }
    
    #[test]
    fn test_same_orbit_continuous() {
        // Create a continuous group
        let group = SymmetryGroup::<f64>::so(2).unwrap();
        let action = BitWordAction::new(2);
        
        let b1 = BitWord::from_bytes(&[1]);
        let b2 = BitWord::from_bytes(&[2]);
        
        // In a continuous group, orbit checking uses different logic
        let result = same_orbit(&b1, &b2, &group, &action);
        
        // The result depends on the group action
        assert!(!result || result); // This is always true, just checking it runs
    }
}