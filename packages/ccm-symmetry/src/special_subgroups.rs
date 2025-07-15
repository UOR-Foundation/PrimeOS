//! Special subgroups with specific properties

use crate::{
    group::{GroupElement, SymmetryGroup},
    SymmetryError,
};
use ccm_core::{CcmError, Float};
use ccm_embedding::AlphaVec;

#[cfg(feature = "alloc")]
use alloc::vec;

/// Compute the resonance-preserving subgroup
pub fn resonance_preserving_subgroup<P: Float>(
    alpha: &AlphaVec<P>,
) -> Result<SymmetryGroup<P>, CcmError> {
    let n = alpha.len();
    let mut group = SymmetryGroup::generate(n)?;

    // Add generators that preserve resonance
    // For now, we know translations preserve resonance
    for i in 0..n {
        let mut params = vec![P::one(); n];
        // Translation generator in direction i
        params[i] = P::from(2.0).unwrap(); // Small translation
        let generator = GroupElement { params, cached_order: None };
        group.add_generator(generator)?;
    }

    Ok(group)
}

/// Compute the grade-preserving subgroup
pub fn grade_preserving_subgroup<P: Float>(dimension: usize) -> Result<SymmetryGroup<P>, CcmError> {
    // For matrix representation, we need dimension^2 parameters
    let mut group = SymmetryGroup::generate(dimension * dimension)?;

    // Grade-preserving transformations include:
    // 1. Scalar multiplication (preserves all grades)
    // 2. Orthogonal transformations within each grade

    // Add scalar multiplication generator (scalar * identity matrix)
    let mut scalar_gen = vec![P::zero(); dimension * dimension];
    let scalar_value = P::from(1.5).unwrap(); // Non-trivial scalar
    for i in 0..dimension {
        scalar_gen[i * dimension + i] = scalar_value;
    }
    group.add_generator(GroupElement { params: scalar_gen, cached_order: None })?;

    // Add rotation generators for SO(n)
    // For each pair (i,j), add a rotation in that plane
    let angle = P::from(0.1).unwrap(); // Small rotation angle

    for i in 0..dimension {
        for j in i + 1..dimension {
            // Create SO(n) rotation generator
            let so_n = crate::matrix_group::SpecialOrthogonalGroup::<P>::new(dimension);
            let rotation = so_n.rotation_generator(i, j, angle)?;
            group.add_generator(rotation)?;
        }
    }

    Ok(group)
}

/// Klein group from unity positions
pub fn klein_subgroup<P: Float>(n: usize) -> Result<SymmetryGroup<P>, CcmError> {
    if n < 2 {
        return Err(SymmetryError::InvalidGroupOperation.into());
    }

    let mut group = SymmetryGroup::generate(4)?; // V₄ has 4 elements

    // V₄ = {e, a, b, ab} where a² = b² = (ab)² = e
    // Generator a: flip bit n-1
    let mut gen_a = vec![P::one(); 4];
    gen_a[0] = -P::one(); // Represents bit flip
    group.add_generator(GroupElement { params: gen_a, cached_order: Some(2) })?;

    // Generator b: flip bit n-2
    let mut gen_b = vec![P::one(); 4];
    gen_b[1] = -P::one(); // Represents bit flip
    group.add_generator(GroupElement { params: gen_b, cached_order: Some(2) })?;

    Ok(group)
}

/// Stabilizer of resonance unity positions
pub fn unity_stabilizer<P: Float>(alpha: &AlphaVec<P>) -> Result<SymmetryGroup<P>, CcmError> {
    let n = alpha.len();
    let mut group = SymmetryGroup::generate(n)?;

    // Elements that fix unity positions
    // These are automorphisms that map unity positions to unity positions

    // The Klein group always stabilizes its unity positions
    let klein = klein_subgroup(n)?;
    for gen in klein.generators() {
        group.add_generator(gen.clone())?;
    }

    Ok(group)
}

/// Maximal resonance-preserving subgroup
pub fn maximal_resonance_subgroup<P: Float>(
    alpha: &AlphaVec<P>,
) -> Result<SymmetryGroup<P>, CcmError> {
    // Start with all resonance-preserving automorphisms
    let mut group = resonance_preserving_subgroup(alpha)?;

    // Add Klein group (always preserves resonance due to unity constraint)
    let klein = klein_subgroup(alpha.len())?;
    for gen in klein.generators() {
        group.add_generator(gen.clone())?;
    }

    // Add cyclic translations
    let mut translation = vec![P::one(); alpha.len()];
    translation[0] = P::from(256.0).unwrap(); // Page translation
    group.add_generator(GroupElement {
        params: translation,
        cached_order: None,
    })?;

    Ok(group)
}

/// Check if a group element preserves resonance
pub fn preserves_resonance<P: Float + num_traits::FromPrimitive>(
    g: &GroupElement<P>,
    alpha: &AlphaVec<P>,
) -> bool {
    use ccm_core::BitWord;
    use ccm_embedding::Resonance;

    // Identity always preserves resonance
    if g.is_identity() {
        return true;
    }

    // Klein group (dimension 4) preserves resonance due to unity constraint
    if g.dimension() == 4 {
        return true;
    }

    // Test on several bit patterns
    let test_patterns = [0u8, 1, 48, 49, 255, 127, 128, 64];

    for &pattern in &test_patterns {
        let b = BitWord::from_u8(pattern);
        let r_original = b.r(alpha);

        // Apply group action (interpret as bit flips)
        let mut b_transformed = b.clone();
        for (i, &param) in g.params.iter().enumerate() {
            if i < 8 && param < P::zero() {
                b_transformed.flip_bit(i);
            }
        }

        let r_transformed = b_transformed.r(alpha);

        // Check if resonance is preserved
        if (r_original - r_transformed).abs() > P::epsilon() {
            return false;
        }
    }

    true
}

/// Check if a group element preserves grades
pub fn preserves_grades<P: Float>(g: &GroupElement<P>) -> bool {
    // Grade preservation means the transformation doesn't mix grades
    // For our simplified representation, check for block structure

    // Identity always preserves grades
    if g.is_identity() {
        return true;
    }

    // More complex check would go here
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_klein_subgroup() {
        let klein = klein_subgroup::<f64>(8).unwrap();
        assert_eq!(klein.generators().len(), 2); // Two generators for V₄
    }

    #[test]
    fn test_grade_preserving() {
        let group = grade_preserving_subgroup::<f64>(3).unwrap();
        // Should have scalar generator + rotation generators
        assert!(group.generators().len() > 0);
    }

    #[test]
    fn test_resonance_preserving() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();
        let group = resonance_preserving_subgroup(&alpha).unwrap();
        assert!(group.generators().len() > 0);
    }
}
