//! Coherence-based page operations for bit patterns
//!
//! Pages represent equivalence classes in the embedding space, organized by
//! coherence properties rather than combinatorial enumeration.

// Main coherence-based implementation
pub mod coherence;
pub use coherence::{IntrinsicPages, PageStructure, ResonancePage};

// Helper functions for page operations
use crate::AlphaVec;
use ccm_core::{BitWord, CcmError, Float};
use num_traits::FromPrimitive;

/// Get the coherence-based page index for a bit pattern
#[cfg(feature = "alloc")]
pub fn page_of<P: Float + FromPrimitive>(
    word: &BitWord,
    alpha: &AlphaVec<P>,
    structure: &PageStructure<P>,
) -> Result<usize, CcmError> {
    word.coherence_page(alpha, structure)
}

/// Create a bit pattern from a page index
/// Returns the page representative (Klein minimum)
#[cfg(feature = "alloc")]
pub fn inject_page<P: Float + FromPrimitive>(
    page: usize,
    structure: &PageStructure<P>,
    _alpha: &AlphaVec<P>,
) -> Result<BitWord, CcmError> {
    if page >= structure.total_pages {
        return Err(CcmError::InvalidInput);
    }

    // Extract resonance class and Klein orbit
    let resonance_class = page >> 2;
    let klein_orbit = (page & 0b11) as u8;

    // Get the representative pattern for this resonance class
    let representative = structure
        .representatives
        .get(resonance_class)
        .ok_or(CcmError::InvalidInput)?;

    // Get the current Klein orbit of the representative
    let current_orbit = <BitWord as IntrinsicPages<P>>::klein_orbit_position(representative);

    // To transform from current_orbit to klein_orbit, we need to XOR with the difference
    // Since Klein group is Z/2Z × Z/2Z with XOR operation
    let transform = current_orbit ^ klein_orbit;
    let result = <BitWord as IntrinsicPages<P>>::apply_klein_transform(representative, transform);

    Ok(result)
}

/// Get the total number of pages for a given bit length
#[cfg(feature = "alloc")]
pub fn page_count<P: Float + FromPrimitive>(
    n: usize,
    alpha: &AlphaVec<P>,
) -> Result<usize, CcmError> {
    let structure = PageStructure::for_bit_length(n, alpha)?;
    Ok(structure.total_pages)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_page_operations() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();
        let structure = PageStructure::for_bit_length(8, &alpha).unwrap();

        // Test page_of
        let word = BitWord::from_u8(42);
        let page = page_of(&word, &alpha, &structure).unwrap();
        assert!(page < structure.total_pages);

        // Test Klein group orbit functionality
        // With dynamic alpha, Klein members may be in different resonance classes

        for i in 0..4 {
            let member = <BitWord as IntrinsicPages<f64>>::apply_klein_transform(&word, i);
            let member_page = page_of(&member, &alpha, &structure).unwrap();

            // Klein orbit should match the transform index
            let klein_orbit = member_page & 0b11;
            assert_eq!(klein_orbit, i as usize);

            // Page should be valid
            assert!(member_page < structure.total_pages);

            // Verify consistency: applying the same transform should give same result
            let member2 = <BitWord as IntrinsicPages<f64>>::apply_klein_transform(&word, i);
            let member_page2 = page_of(&member2, &alpha, &structure).unwrap();
            assert_eq!(
                member_page, member_page2,
                "Klein transform should be deterministic"
            );
        }
    }

    #[test]
    fn test_page_count() {
        // Test various bit lengths with dynamic alpha
        let alpha_8 = AlphaVec::<f64>::for_bit_length(8).unwrap();
        let count_8 = page_count(8, &alpha_8).unwrap();
        assert!(count_8 > 0);
        assert!(count_8 % 4 == 0); // Should be multiple of 4 (Klein orbits)

        let alpha_4 = AlphaVec::<f64>::for_bit_length(4).unwrap();
        let count_4 = page_count(4, &alpha_4).unwrap();
        assert!(count_4 > 0);
        assert!(count_4 % 4 == 0); // Should be multiple of 4 (Klein orbits)

        // Larger bit length should generally have more pages
        let alpha_6 = AlphaVec::<f64>::for_bit_length(6).unwrap();
        let count_6 = page_count(6, &alpha_6).unwrap();
        assert!(count_6 >= count_4); // More bits, more or equal pages
    }

    #[test]
    fn test_inject_page_basic() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();
        let structure = PageStructure::for_bit_length(8, &alpha).unwrap();

        // Test Klein orbit patterns
        let page0 = inject_page(0, &structure, &alpha).unwrap();
        assert_eq!(
            <BitWord as IntrinsicPages<f64>>::klein_orbit_position(&page0),
            0
        );

        let page1 = inject_page(1, &structure, &alpha).unwrap();
        assert_eq!(
            <BitWord as IntrinsicPages<f64>>::klein_orbit_position(&page1),
            1
        );

        let page2 = inject_page(2, &structure, &alpha).unwrap();
        assert_eq!(
            <BitWord as IntrinsicPages<f64>>::klein_orbit_position(&page2),
            2
        );

        let page3 = inject_page(3, &structure, &alpha).unwrap();
        assert_eq!(
            <BitWord as IntrinsicPages<f64>>::klein_orbit_position(&page3),
            3
        );
    }
}
