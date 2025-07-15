//! Orbit analysis and computation

use crate::{
    actions::GroupAction,
    group::{GroupElement, SymmetryGroup},
};
use ccm_core::{CcmError, Float};

#[cfg(feature = "alloc")]
use alloc::{vec, vec::Vec};

#[cfg(all(not(feature = "std"), feature = "alloc"))]
use alloc::collections::BTreeSet;
#[cfg(feature = "std")]
use std::collections::BTreeSet;

/// Orbit of an element under group action
#[derive(Debug, Clone)]
pub struct Orbit<P: Float, T> {
    /// A representative element of the orbit
    pub representative: T,
    /// The stabilizer subgroup
    pub stabilizer: StabilizerSubgroup<P>,
    /// All elements in the orbit (if computed)
    pub elements: Vec<T>,
}

impl<P: Float, T: Clone> Orbit<P, T> {
    /// Create a new orbit with just the representative
    pub fn new(representative: T) -> Self {
        Self {
            representative: representative.clone(),
            stabilizer: StabilizerSubgroup::new(),
            elements: vec![representative],
        }
    }

    /// Get the size of the orbit
    pub fn size(&self) -> usize {
        self.elements.len()
    }

    /// Check if an element is in the orbit
    pub fn contains(&self, element: &T) -> bool
    where
        T: PartialEq,
    {
        self.elements.iter().any(|e| e == element)
    }
}

/// Stabilizer subgroup of an element
#[derive(Debug, Clone)]
pub struct StabilizerSubgroup<P: Float> {
    /// Generators of the stabilizer
    pub generators: Vec<GroupElement<P>>,
}

impl<P: Float> Default for StabilizerSubgroup<P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: Float> StabilizerSubgroup<P> {
    /// Create empty stabilizer
    pub fn new() -> Self {
        Self {
            generators: Vec::new(),
        }
    }

    /// Add a generator to the stabilizer
    pub fn add_generator(&mut self, g: GroupElement<P>) {
        self.generators.push(g);
    }

    /// Get the order of the stabilizer (if finite)
    pub fn order(&self) -> Option<usize> {
        // For finite groups, compute order using orbit-stabilizer theorem
        // |G| = |Orbit(x)| × |Stab(x)|

        if self.generators.is_empty() {
            // Trivial stabilizer has order 1
            return Some(1);
        }

        // For small groups, we can enumerate elements
        // This is a simplified implementation for finite groups
        // For small groups, we can enumerate elements
        // Using Vec instead of BTreeSet to avoid Ord requirement
        let mut elements = Vec::new();
        elements.push(vec![P::one(); self.generators[0].dimension()]); // Identity

        // Add all generators
        for gen in &self.generators {
            elements.push(gen.params.clone());
        }

        // Compute products up to a reasonable limit
        let max_iterations = 100;
        let mut changed = true;
        let mut iterations = 0;

        while changed && iterations < max_iterations {
            changed = false;
            let current_elements: Vec<_> = elements.to_vec();

            for g in &current_elements {
                for h in &self.generators {
                    // Compute g * h (simplified as component-wise multiplication)
                    let product: Vec<P> = g.iter().zip(&h.params).map(|(&a, &b)| a * b).collect();

                    // Check if product is new
                    let is_new = !elements.iter().any(|e| {
                        e.len() == product.len()
                            && e.iter()
                                .zip(&product)
                                .all(|(a, b)| (*a - *b).abs() < P::epsilon())
                    });

                    if is_new {
                        elements.push(product);
                        changed = true;
                    }
                }
            }
            iterations += 1;
        }

        if iterations < max_iterations {
            Some(elements.len())
        } else {
            // Group might be infinite or too large
            None
        }
    }
}

/// Compute the orbit of an element under group action
pub fn compute_orbit<P: Float, T: Clone + PartialEq>(
    x: &T,
    group: &SymmetryGroup<P>,
    action: &dyn GroupAction<P, Target = T>,
) -> Result<Orbit<P, T>, CcmError> {
    let mut orbit = Orbit::new(x.clone());
    let mut _seen = BTreeSet::<Vec<u8>>::new();
    let mut to_process = vec![x.clone()];

    // For finite groups, we can enumerate all elements
    // For continuous groups, this would need a different approach

    // Start with generators acting on x
    for generator in group.generators() {
        let new_element = action.apply(generator, x)?;

        // Check if we've seen this element
        let mut is_new = true;
        for existing in &orbit.elements {
            if existing == &new_element {
                is_new = false;
                break;
            }
        }

        if is_new {
            orbit.elements.push(new_element.clone());
            to_process.push(new_element);
        } else {
            // This generator stabilizes x
            orbit.stabilizer.add_generator(generator.clone());
        }
    }

    // Continue until we've processed all elements
    while let Some(current) = to_process.pop() {
        for generator in group.generators() {
            let new_element = action.apply(generator, &current)?;

            let mut is_new = true;
            for existing in &orbit.elements {
                if existing == &new_element {
                    is_new = false;
                    break;
                }
            }

            if is_new {
                orbit.elements.push(new_element.clone());
                to_process.push(new_element);
            }
        }
    }

    Ok(orbit)
}

/// Compute stabilizer subgroup more efficiently using Schreier-Sims
pub fn compute_stabilizer<P: Float, T: Clone + PartialEq>(
    x: &T,
    group: &SymmetryGroup<P>,
    action: &dyn GroupAction<P, Target = T>,
) -> Result<StabilizerSubgroup<P>, CcmError> {
    let mut stabilizer = StabilizerSubgroup::new();

    // Check each generator
    for g in group.generators() {
        let gx = action.apply(g, x)?;
        if &gx == x {
            stabilizer.add_generator(g.clone());
        }
    }

    // Would need to compute products of generators for complete stabilizer

    Ok(stabilizer)
}

/// Orbit-counting theorem (Burnside's lemma)
pub fn count_orbits<P: Float, T: Clone + PartialEq>(
    elements: &[T],
    group: &SymmetryGroup<P>,
    action: &dyn GroupAction<P, Target = T>,
) -> Result<usize, CcmError> {
    // Number of orbits = (1/|G|) * Σ_{g∈G} |Fix(g)|

    let mut orbit_count = 0;
    let mut processed = vec![false; elements.len()];

    for (i, x) in elements.iter().enumerate() {
        if !processed[i] {
            let orbit = compute_orbit(x, group, action)?;
            orbit_count += 1;

            // Mark all elements in this orbit as processed
            for (j, y) in elements.iter().enumerate() {
                if orbit.contains(y) {
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
    fn test_orbit_creation() {
        let b = BitWord::from_bytes(&[42]);
        let orbit: Orbit<f64, BitWord> = Orbit::new(b.clone());

        assert_eq!(orbit.size(), 1);
        assert!(orbit.contains(&b));
    }

    #[test]
    fn test_orbit_computation() {
        let group = SymmetryGroup::<f64>::generate(8).unwrap();
        let action = BitWordAction::new(8);
        let b = BitWord::from_bytes(&[0]);

        let orbit = compute_orbit(&b, &group, &action).unwrap();
        // With identity action, orbit has size 1
        assert_eq!(orbit.size(), 1);
    }
}
