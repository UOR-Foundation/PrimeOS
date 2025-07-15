//! Stabilizer computation functions
//!
//! This module provides functions for computing and analyzing stabilizer subgroups
//! of Clifford elements under group actions.

use crate::{SymmetryGroup, StabilizerSubgroup, CliffordAction, GroupElement};
use ccm_coherence::{CliffordElement, CliffordAlgebra};
use ccm_core::Float;
use num_traits::FromPrimitive;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Compute a minimal generating set for the stabilizer subgroup
/// 
/// Given all elements that stabilize a point, this function extracts
/// a minimal set of generators that can produce the entire stabilizer.
/// 
/// # Algorithm
/// 
/// 1. Start with empty generator set and subgroup containing only identity
/// 2. For each stabilizing element not yet in our subgroup:
///    - Add it as a generator
///    - Expand the subgroup by computing all products with existing generators
/// 3. Continue until all stabilizing elements are in the generated subgroup
/// 
/// # Arguments
///
/// * `stabilizer` - The stabilizer subgroup containing generators
/// * `group` - The parent symmetry group
///
/// # Returns
/// 
/// Vector of indices into the group's element list representing the generators
pub fn compute_stabilizer_generators<P: Float>(
    stabilizer: &StabilizerSubgroup<P>,
    group: &SymmetryGroup<P>,
) -> Vec<usize> {
    let mut generator_indices = Vec::new();
    
    // If no generators in stabilizer, return empty (only identity stabilizes)
    if stabilizer.generators.is_empty() {
        return generator_indices;
    }
    
    // For finite groups, we can enumerate and find minimal generators
    if let Some(group_elements) = group.elements() {
        let group_vec: Vec<_> = group_elements.collect();
        
        // Find indices of stabilizer generators in the group
        for stab_gen in &stabilizer.generators {
            for (idx, group_elem) in group_vec.iter().enumerate() {
                if elements_equal_params(&stab_gen.params, &group_elem.params) {
                    generator_indices.push(idx);
                    break;
                }
            }
        }
        
        // For Klein group optimization: if we have both bit flips, we don't need their product
        if group.order() == Some(4) && generator_indices.len() > 2 {
            // Klein group has at most 2 generators
            generator_indices.truncate(2);
        }
    }
    
    generator_indices
}

/// Compute the size of the stabilizer subgroup
/// 
/// For finite groups, this counts all elements in the stabilizer.
/// Uses the generators to build the complete subgroup.
///
/// # Arguments
///
/// * `stabilizer` - The stabilizer subgroup
/// * `group` - The parent symmetry group
///
/// # Returns
///
/// The number of elements in the stabilizer subgroup
pub fn compute_stabilizer_size<P: Float>(
    stabilizer: &StabilizerSubgroup<P>,
    group: &SymmetryGroup<P>,
) -> usize {
    // Identity is always in the stabilizer
    let mut size = 1;
    
    // Add the number of non-identity generators
    size += stabilizer.generators.len();
    
    // For Klein group, handle special cases
    if group.order() == Some(4) {
        // Klein group stabilizers can only be:
        // - {e} (size 1)
        // - {e, a} or {e, b} or {e, ab} (size 2)
        // - {e, a, b, ab} (size 4)
        if stabilizer.generators.len() == 2 {
            // Two generators means the whole Klein group
            size = 4;
        }
        // Otherwise size is already correct (1 or 2)
    } else if stabilizer.generators.len() > 1 {
        // For other finite groups, compute the actual subgroup size
        // by generating all elements from the generators
        
        // Track all subgroup elements starting with identity
        let mut subgroup_elements = Vec::new();
        subgroup_elements.push(group.identity());
        
        // Add all generators
        for gen in &stabilizer.generators {
            subgroup_elements.push(gen.clone());
        }
        
        // Compute closure under group operation
        let mut changed = true;
        while changed {
            changed = false;
            let current_size = subgroup_elements.len();
            
            // Try all products of existing elements
            for i in 0..current_size {
                for j in 0..current_size {
                    if let Ok(product) = group.multiply(&subgroup_elements[i], &subgroup_elements[j]) {
                        // Check if this product is new
                        let mut is_new = true;
                        for existing in &subgroup_elements {
                            if elements_equal_params(&product.params, &existing.params) {
                                is_new = false;
                                break;
                            }
                        }
                        
                        if is_new {
                            subgroup_elements.push(product);
                            changed = true;
                        }
                    }
                }
            }
        }
        
        size = subgroup_elements.len();
    }
    
    size
}

/// Count the number of group elements that stabilize the given element
///
/// This function tests each group element to see if it fixes the given
/// Clifford element under the group action.
///
/// # Arguments
///
/// * `element` - The Clifford element to test
/// * `group` - The symmetry group
///
/// # Returns
///
/// The number of group elements that stabilize the element
pub fn count_stabilizer_elements<P: Float + FromPrimitive>(
    element: &CliffordElement<P>,
    group: &SymmetryGroup<P>,
) -> usize {
    if let Some(elements) = group.elements() {
        let algebra = CliffordAlgebra::generate(element.dimension()).unwrap();
        let action = CliffordAction::new(algebra);
        
        elements.filter(|g| {
            match group.apply(g, element, &action) {
                Ok(transformed) => elements_equal(&transformed, element),
                Err(_) => false,
            }
        })
        .count()
    } else {
        1 // Only identity for infinite groups
    }
}

/// Calculate the size of the orbit of an element
///
/// Uses the orbit-stabilizer theorem: |Orbit| = |G| / |Stabilizer|
///
/// # Arguments
///
/// * `element` - The Clifford element
/// * `group` - The symmetry group
///
/// # Returns
///
/// The size of the orbit
pub fn calculate_orbit_size<P: Float + FromPrimitive>(
    element: &CliffordElement<P>,
    group: &SymmetryGroup<P>,
) -> usize {
    // By orbit-stabilizer theorem: |Orbit| = |G| / |Stabilizer|
    let group_order = group.order().unwrap_or(1);
    let stabilizer_size = count_stabilizer_elements(element, group);
    group_order / stabilizer_size
}

/// Verify that stabilizers of parts are compatible with the whole
///
/// For a valid decomposition: Stab_G(whole) contains intersection of Stab_G(part_i)
///
/// # Mathematical Foundation
///
/// The stabilizer compatibility theorem states that for a decomposition
/// whole = sum(parts), we must have:
/// 
/// Stab_G(whole) ⊇ ∩_i Stab_G(part_i)
///
/// This is because if g stabilizes all parts:
/// - g·part_i = part_i for all i
/// - g·whole = g·sum(part_i) = sum(g·part_i) = sum(part_i) = whole
/// - Therefore g ∈ Stab_G(whole)
///
/// # Algorithm
///
/// 1. Compute stabilizer of the whole element
/// 2. Compute stabilizers of each part
/// 3. Find intersection of part stabilizers
/// 4. Verify that Stab(whole) contains the intersection
///
/// # Special Cases
///
/// - Klein group: Use optimized bit operations
/// - Trivial stabilizers: If any part has Stab = {e}, intersection is {e}
/// - Full stabilizer: If whole has Stab = G, compatibility is automatic
///
/// # Arguments
///
/// * `whole` - The complete element that was decomposed
/// * `parts` - The decomposed parts that sum to whole
/// * `group` - The symmetry group acting on the elements
///
/// # Returns
///
/// `true` if Stab(whole) ⊇ ∩ Stab(part_i), `false` otherwise
///
/// # Example
///
/// ```ignore
/// // For Klein group decomposition
/// let whole = /* element with Klein symmetry */;
/// let parts = /* Klein-symmetric decomposition */;
/// let group = SymmetryGroup::klein_group(8)?;
/// 
/// // Verify that stabilizers are compatible
/// assert!(verify_stabilizer_compatibility(&whole, &parts, &group));
/// ```
pub fn verify_stabilizer_compatibility<P: Float + FromPrimitive>(
    whole: &CliffordElement<P>,
    parts: &[CliffordElement<P>],
    group: &SymmetryGroup<P>,
) -> bool {
    // Stabilizer compatibility verification algorithm:
    //
    // 1. Compute Stab_G(whole) = {g ∈ G : g·whole = whole}
    //    - For finite groups: test each element
    //    - For Klein group: use XOR properties
    //    - For continuous groups: use Lie algebra methods
    //
    // 2. Compute each Stab_G(part_i)
    //    - Same methods as above
    //    - Early exit if any stabilizer is trivial
    //
    // 3. Compute intersection ∩_i Stab_G(part_i)
    //    - Start with first stabilizer
    //    - Iteratively intersect with remaining stabilizers
    //    - Result is a subgroup (closed under multiplication)
    //
    // 4. Verify Stab(whole) ⊇ intersection
    //    - Generate all elements from generators
    //    - Check each intersection element is in Stab(whole)
    //    - Use efficient containment check for finite groups
    //
    // Implementation notes:
    // - Use generator representation for efficiency
    // - Cache subgroup elements to avoid recomputation
    // - Handle numerical tolerance in element comparisons
    // - Optimize for Klein group (most common case)
    
    // Handle edge cases
    if parts.is_empty() {
        // No parts means trivial decomposition, always valid
        return true;
    }
    
    // Create Clifford action for the group
    let algebra = match CliffordAlgebra::generate(whole.dimension()) {
        Ok(alg) => alg,
        Err(_) => return false, // Cannot verify without valid algebra
    };
    let action = CliffordAction::new(algebra);
    
    // Step 1: Compute stabilizer of the whole element
    let whole_stabilizer = group.stabilizer(whole, &action);
    
    // If whole is stabilized by the entire group, compatibility is automatic
    if whole_stabilizer.generators.len() == group.generators().len() {
        return true;
    }
    
    // Step 2: Compute stabilizers of each part
    let mut part_stabilizers = Vec::new();
    
    for part in parts {
        let part_stab = group.stabilizer(part, &action);
        
        // Early exit: if any part has trivial stabilizer, intersection is trivial
        if part_stab.generators.is_empty() {
            // Trivial stabilizer means only identity stabilizes
            // The intersection will also be trivial, which is always contained
            return true;
        }
        
        part_stabilizers.push(part_stab);
    }
    
    // Step 3: Compute intersection of all part stabilizers
    let intersection = compute_stabilizer_intersection(&part_stabilizers, group);
    
    // Step 4: Verify that Stab(whole) contains the intersection
    is_subgroup_contained(&intersection, &whole_stabilizer, group)
}

// Helper functions

/// Check if two Clifford elements are equal within tolerance
fn elements_equal<P: Float>(a: &CliffordElement<P>, b: &CliffordElement<P>) -> bool {
    let diff = a.clone() - b.clone();
    diff.coherence_norm() < P::epsilon() * P::from(10.0).unwrap()
}

/// Check if two parameter vectors are equal within tolerance
fn elements_equal_params<P: Float>(a: &[P], b: &[P]) -> bool {
    a.len() == b.len() && 
    a.iter().zip(b.iter()).all(|(x, y)| (*x - *y).abs() < P::epsilon())
}

// Additional helper functions needed for stabilizer compatibility

/// Compute the intersection of multiple stabilizer subgroups
///
/// # Algorithm
/// 
/// 1. Start with elements from the first stabilizer
/// 2. Keep only elements that appear in ALL stabilizers
/// 3. Extract minimal generators for the intersection
///
/// # Arguments
///
/// * `stabilizers` - Vector of stabilizer subgroups to intersect
/// * `group` - The parent symmetry group
///
/// # Returns
///
/// A new StabilizerSubgroup containing generators of the intersection
fn compute_stabilizer_intersection<P: Float>(
    stabilizers: &[StabilizerSubgroup<P>],
    group: &SymmetryGroup<P>,
) -> StabilizerSubgroup<P> {
    if stabilizers.is_empty() {
        // Empty intersection is the whole group
        return StabilizerSubgroup { 
            generators: group.generators().to_vec() 
        };
    }
    
    if stabilizers.len() == 1 {
        // Single stabilizer is its own intersection
        return StabilizerSubgroup {
            generators: stabilizers[0].generators.clone()
        };
    }
    
    // Generate all elements of the first stabilizer
    let mut intersection_elements = generate_subgroup_elements(&stabilizers[0], group);
    
    // Keep only elements that are in ALL stabilizers
    for stab in &stabilizers[1..] {
        let stab_elements = generate_subgroup_elements(stab, group);
        
        intersection_elements.retain(|elem| {
            stab_elements.iter().any(|s| elements_equal_params(&elem.params, &s.params))
        });
        
        // Early exit if intersection becomes trivial
        if intersection_elements.len() == 1 {
            // Only identity remains
            return StabilizerSubgroup { generators: Vec::new() };
        }
    }
    
    // Extract minimal generators for the intersection
    extract_minimal_generators(&intersection_elements, group)
}

/// Generate all elements of a subgroup from its generators
///
/// Uses the subgroup generation algorithm:
/// 1. Start with identity
/// 2. Add all generators
/// 3. Compute closure under group multiplication
///
/// # Arguments
///
/// * `stabilizer` - Subgroup defined by generators
/// * `group` - Parent group for multiplication operation
///
/// # Returns
///
/// Vector containing all elements of the subgroup
fn generate_subgroup_elements<P: Float>(
    stabilizer: &StabilizerSubgroup<P>,
    group: &SymmetryGroup<P>,
) -> Vec<GroupElement<P>> {
    let mut elements = Vec::new();
    
    // Always include identity
    elements.push(group.identity());
    
    // Add all generators
    for gen in &stabilizer.generators {
        if !elements.iter().any(|e| elements_equal_params(&e.params, &gen.params)) {
            elements.push(gen.clone());
        }
    }
    
    // Special case for Klein group optimization
    if group.order() == Some(4) && stabilizer.generators.len() == 2 {
        // For Klein group with 2 generators, we know we have all 4 elements
        // Just need to compute the product of the two generators
        if let Ok(product) = group.multiply(&stabilizer.generators[0], &stabilizer.generators[1]) {
            if !elements.iter().any(|e| elements_equal_params(&e.params, &product.params)) {
                elements.push(product);
            }
        }
        return elements;
    }
    
    // General case: compute closure under multiplication
    // Use Lagrange's theorem: |H| divides |G|, so we have an upper bound
    let max_subgroup_size = match group.order() {
        Some(order) => order,
        None => {
            // For infinite groups, we need a different approach
            // This should be handled by the caller, but we set a reasonable limit
            1024
        }
    };
    
    let mut changed = true;
    let mut iterations = 0;
    
    while changed && elements.len() < max_subgroup_size {
        changed = false;
        iterations += 1;
        
        // Prevent runaway computation
        if iterations > elements.len() * 2 {
            // If we've done more iterations than twice the current size,
            // something is wrong (possibly numerical issues)
            break;
        }
        
        let current_size = elements.len();
        
        // Try all products of existing elements
        for i in 0..current_size {
            for j in 0..current_size {
                if let Ok(product) = group.multiply(&elements[i], &elements[j]) {
                    // Check if this product is new
                    if !elements.iter().any(|e| elements_equal_params(&e.params, &product.params)) {
                        elements.push(product);
                        changed = true;
                        
                        // Early exit if we've reached the maximum possible size
                        if elements.len() >= max_subgroup_size {
                            return elements;
                        }
                    }
                }
            }
            
            // Also try inverse if the group has them
            if let Ok(inverse) = group.inverse(&elements[i]) {
                if !elements.iter().any(|e| elements_equal_params(&e.params, &inverse.params)) {
                    elements.push(inverse);
                    changed = true;
                    
                    // Early exit if we've reached the maximum possible size
                    if elements.len() >= max_subgroup_size {
                        return elements;
                    }
                }
            }
        }
        
        // Check if the subgroup size divides the group order (Lagrange's theorem)
        if let Some(order) = group.order() {
            if order % elements.len() == 0 && !changed {
                // We have a valid subgroup size and no new elements, we're done
                break;
            }
        }
    }
    
    elements
}

/// Check if a subgroup is contained in another subgroup
///
/// Verifies that H ⊆ K by checking if every element of H is in K
///
/// # Arguments
///
/// * `subgroup` - The potentially smaller subgroup H
/// * `supergroup` - The potentially larger subgroup K
/// * `group` - Parent group for operations
///
/// # Returns
///
/// `true` if subgroup ⊆ supergroup, `false` otherwise
fn is_subgroup_contained<P: Float>(
    subgroup: &StabilizerSubgroup<P>,
    supergroup: &StabilizerSubgroup<P>,
    group: &SymmetryGroup<P>,
) -> bool {
    // Trivial case: empty subgroup is contained in everything
    if subgroup.generators.is_empty() {
        return true;
    }
    
    // Generate all elements of both subgroups
    let sub_elements = generate_subgroup_elements(subgroup, group);
    let super_elements = generate_subgroup_elements(supergroup, group);
    
    // Check if every element of subgroup is in supergroup
    sub_elements.iter().all(|sub_elem| {
        super_elements.iter().any(|super_elem| {
            elements_equal_params(&sub_elem.params, &super_elem.params)
        })
    })
}

/// Extract minimal generators from a set of group elements
///
/// Finds a minimal generating set for the subgroup generated by the given elements
///
/// # Arguments
///
/// * `elements` - All elements of the subgroup
/// * `group` - Parent group for operations
///
/// # Returns
///
/// A StabilizerSubgroup with minimal generators
fn extract_minimal_generators<P: Float>(
    elements: &[GroupElement<P>],
    group: &SymmetryGroup<P>,
) -> StabilizerSubgroup<P> {
    let mut generators = Vec::new();
    let mut generated = vec![group.identity()];
    
    // Skip the identity element
    for elem in elements {
        if elem.is_identity() {
            continue;
        }
        
        // Check if this element can be generated by existing generators
        let mut can_generate = false;
        for existing in &generated {
            if elements_equal_params(&elem.params, &existing.params) {
                can_generate = true;
                break;
            }
        }
        
        if !can_generate {
            // Add as a new generator
            generators.push(elem.clone());
            
            // Update the generated subgroup
            let temp_stab = StabilizerSubgroup { 
                generators: generators.clone() 
            };
            generated = generate_subgroup_elements(&temp_stab, group);
        }
    }
    
    StabilizerSubgroup { generators }
}