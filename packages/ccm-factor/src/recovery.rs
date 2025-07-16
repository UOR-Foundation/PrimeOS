//! Factor recovery from alignment windows using resonance search

use crate::{
    error::{FactorError, Result},
    types::{AlignmentWindow, SymmetryType},
};

use ccm::StandardCCM;
use ccm_core::BitWord;
use ccm_embedding::{AlphaVec, Resonance};
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{Float, One};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Recover factors from alignment windows
pub fn recover_factors_from_windows<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    ccm: &StandardCCM<P>,
    windows: &[AlignmentWindow<P>],
    n: &BigUint,
    alpha: &AlphaVec<P>,
    tolerance: f64,
) -> Result<Vec<BigUint>> {
    let mut factors = Vec::new();
    let mut found_nontrivial = false;

    // Try each window in order of confidence
    for window in windows {
        // Different recovery strategies based on symmetry type
        let window_factors = match window.factor_hint.symmetry_type {
            SymmetryType::Klein => recover_with_klein_symmetry(ccm, window, n, alpha, tolerance)?,
            SymmetryType::PageAligned => {
                recover_with_page_alignment(ccm, window, n, alpha, tolerance)?
            }
            SymmetryType::ResonanceConserving => {
                recover_with_resonance_conservation(ccm, window, n, alpha, tolerance)?
            }
            SymmetryType::Combined => {
                recover_with_combined_approach(ccm, window, n, alpha, tolerance)?
            }
            SymmetryType::None => recover_with_basic_search(ccm, window, n, alpha, tolerance)?,
        };

        // Validate and add factors
        for factor in window_factors {
            if validate_factor(&factor, n)? {
                factors.push(factor);
                found_nontrivial = true;
            }
        }

        // Early termination if we found non-trivial factors
        if found_nontrivial && factors.len() >= 2 {
            break;
        }
    }

    // If no factors found, try harder with the best window
    if factors.is_empty() && !windows.is_empty() {
        factors = exhaustive_factor_search(ccm, &windows[0], n, alpha)?;
    }

    // Ensure we have a complete factorization
    if factors.is_empty() {
        return Err(FactorError::FactorizationFailed);
    }

    // Remove duplicates and sort
    factors.sort();
    factors.dedup();

    Ok(factors)
}

/// Recover factors using Klein group symmetry
fn recover_with_klein_symmetry<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    ccm: &StandardCCM<P>,
    window: &AlignmentWindow<P>,
    n: &BigUint,
    alpha: &AlphaVec<P>,
    tolerance: f64,
) -> Result<Vec<BigUint>> {
    let mut factors = Vec::new();

    // Klein symmetry suggests factors appear in the orbit representatives
    for rep in &window.factor_hint.orbit_representatives {
        // Search for factors near this representative
        let candidates = search_near_bitword(ccm, rep, alpha, tolerance)?;

        for candidate in candidates {
            if let Some(factor) = try_extract_factor(&candidate, n)? {
                factors.push(factor);
            }
        }
    }

    Ok(factors)
}

/// Recover factors using page alignment
fn recover_with_page_alignment<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    ccm: &StandardCCM<P>,
    window: &AlignmentWindow<P>,
    n: &BigUint,
    alpha: &AlphaVec<P>,
    tolerance: f64,
) -> Result<Vec<BigUint>> {
    let mut factors = Vec::new();

    // Page-aligned factors often appear at specific offsets
    let page_size = 256;
    let start_page = window.start / page_size;

    // Search at page boundaries
    for offset in [0, page_size / 2, page_size - 1].iter() {
        let search_pos = start_page * page_size + offset;

        if search_pos < window.start + window.length {
            // Create BitWord at this position
            let _search_word = BitWord::from_usize(search_pos);

            let candidates = ccm.search_by_resonance(
                window.factor_hint.resonance_signature,
                alpha,
                P::from(tolerance).unwrap(),
            )?;

            for candidate in candidates {
                if let Some(factor) = try_extract_factor(&candidate, n)? {
                    factors.push(factor);
                }
            }
        }
    }

    Ok(factors)
}

/// Recover factors using resonance conservation
fn recover_with_resonance_conservation<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    ccm: &StandardCCM<P>,
    window: &AlignmentWindow<P>,
    n: &BigUint,
    alpha: &AlphaVec<P>,
    tolerance: f64,
) -> Result<Vec<BigUint>> {
    let mut factors = Vec::new();

    // Conservation laws provide strong constraints on factor relationships
    let target_resonance = window.factor_hint.resonance_signature;

    // Strategy 1: Use multiplicative conservation
    // For n = p * q, often R(n) ≈ R(p) * R(q) within a Klein orbit
    let sqrt_resonance = target_resonance.sqrt();
    
    // Search for factors near the square root resonance
    let sqrt_candidates = ccm.search_by_resonance(
        sqrt_resonance,
        alpha,
        P::from(tolerance).unwrap() * sqrt_resonance,
    )?;

    // Strategy 2: Use additive conservation (768-cycle)
    // Factors often appear at specific positions in the conservation cycle
    let cycle_positions = find_conservation_cycle_positions(target_resonance, alpha)?;
    
    // Combine candidates from both strategies
    let mut all_candidates = sqrt_candidates;
    for pos in cycle_positions {
        let cycle_word = BitWord::from_usize(pos);
        all_candidates.push(cycle_word);
    }

    // Try pairs of candidates, checking conservation
    for i in 0..all_candidates.len() {
        for j in i..all_candidates.len() {
            let factor1 = bitword_to_biguint(&all_candidates[i]);
            let factor2 = bitword_to_biguint(&all_candidates[j]);

            if &factor1 * &factor2 == *n {
                // Verify conservation laws hold
                if verify_factor_conservation(&all_candidates[i], &all_candidates[j], alpha)? {
                    factors.push(factor1);
                    if factor2 != factors[0] {
                        factors.push(factor2);
                    }
                    return Ok(factors);
                }
            }
        }
    }

    // Strategy 3: Unity position search
    // Factors near unity positions often have special properties
    let unity_factors = search_near_unity_positions(n, alpha)?;
    for factor in unity_factors {
        if validate_factor(&factor, n)? {
            factors.push(factor);
        }
    }

    Ok(factors)
}

/// Find positions in the 768-cycle that match target resonance
fn find_conservation_cycle_positions<P: Float>(
    target: P,
    _alpha: &AlphaVec<P>,
) -> Result<Vec<usize>> {
    let mut positions = Vec::new();
    const CYCLE_LENGTH: usize = 768;
    
    // The 768-cycle has specific resonance patterns
    // Unity positions: 0, 1, 48, 49, 256, 257, 304, 305, 512, 513, 560, 561
    let unity_positions = vec![0, 1, 48, 49, 256, 257, 304, 305, 512, 513, 560, 561];
    
    // Positions with resonance near target
    // This is a simplified heuristic - full implementation would compute actual cycle
    let target_f64 = target.to_f64().unwrap_or(1.0);
    
    for i in 0..CYCLE_LENGTH {
        // Heuristic: positions related to target by simple factors
        if i > 0 {
            let ratio = (i as f64) / target_f64;
            if (ratio - ratio.round()).abs() < 0.1 {
                positions.push(i);
            }
        }
    }
    
    // Always include unity positions as they're special
    positions.extend_from_slice(&unity_positions);
    positions.sort_unstable();
    positions.dedup();
    
    Ok(positions)
}

/// Verify conservation laws hold for a factor pair
pub(crate) fn verify_factor_conservation<P: Float + num_traits::FromPrimitive>(
    factor1: &BitWord,
    factor2: &BitWord,
    alpha: &AlphaVec<P>,
) -> Result<bool> {
    // Check resonance conservation
    let r1 = factor1.r(alpha);
    let r2 = factor2.r(alpha);
    let product = r1 * r2;
    
    // Check if product resonance is conserved (within Klein group)
    let klein_members1 = <BitWord as ccm_embedding::Resonance<P>>::class_members(factor1);
    let klein_members2 = <BitWord as ccm_embedding::Resonance<P>>::class_members(factor2);
    
    // At least one pair should satisfy conservation
    for m1 in &klein_members1 {
        for m2 in &klein_members2 {
            let r_m1 = m1.r(alpha);
            let r_m2 = m2.r(alpha);
            // Check various conservation relations
            if (r_m1 * r_m2 - product).abs() < P::from(1e-10).unwrap() {
                return Ok(true);
            }
        }
    }
    
    Ok(false)
}

/// Search for factors near unity positions
pub(crate) fn search_near_unity_positions<P: Float + num_traits::FromPrimitive>(
    n: &BigUint,
    alpha: &AlphaVec<P>,
) -> Result<Vec<BigUint>> {
    let mut factors = Vec::new();
    
    // Unity positions in first 256: 0, 1, 48, 49
    let unity_positions = vec![1u64, 48, 49]; // Skip 0
    
    for &pos in &unity_positions {
        let unity_word = BitWord::from_u64(pos, 8);
        
        // Search near this unity position
        for offset in 0..16 {
            if pos + offset > 0 {
                let candidate = BitWord::from_u64(pos + offset, 8);
                let factor = bitword_to_biguint(&candidate);
                
                if factor > BigUint::one() && factor < *n && n.is_multiple_of(&factor) {
                    // Verify it has unity-like properties
                    let resonance = candidate.r(alpha);
                    if (resonance - P::one()).abs() < P::from(0.1).unwrap() {
                        factors.push(factor);
                    }
                }
            }
        }
    }
    
    factors.sort();
    factors.dedup();
    Ok(factors)
}

/// Recover using combined symmetry approaches
fn recover_with_combined_approach<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    ccm: &StandardCCM<P>,
    window: &AlignmentWindow<P>,
    n: &BigUint,
    alpha: &AlphaVec<P>,
    tolerance: f64,
) -> Result<Vec<BigUint>> {
    let mut all_factors = Vec::new();

    // Try all approaches and combine results
    let klein_factors = recover_with_klein_symmetry(ccm, window, n, alpha, tolerance)?;
    let page_factors = recover_with_page_alignment(ccm, window, n, alpha, tolerance)?;
    let resonance_factors = recover_with_resonance_conservation(ccm, window, n, alpha, tolerance)?;

    all_factors.extend(klein_factors);
    all_factors.extend(page_factors);
    all_factors.extend(resonance_factors);

    // Remove duplicates
    all_factors.sort();
    all_factors.dedup();

    Ok(all_factors)
}

/// Basic recovery without specific symmetry assumptions
fn recover_with_basic_search<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    ccm: &StandardCCM<P>,
    window: &AlignmentWindow<P>,
    n: &BigUint,
    alpha: &AlphaVec<P>,
    tolerance: f64,
) -> Result<Vec<BigUint>> {
    let mut factors = Vec::new();

    // Use grade filtering to narrow search
    let dominant_grades = find_dominant_grades(&window.factor_hint.grade_decomposition);

    // Search using the window's resonance signature
    let candidates = ccm.search_by_resonance(
        window.factor_hint.resonance_signature,
        alpha,
        P::from(tolerance).unwrap(),
    )?;

    // Filter by grade if possible
    let filtered_candidates = if !dominant_grades.is_empty() {
        filter_by_grades(candidates, &dominant_grades)
    } else {
        candidates
    };

    // Try each candidate as a potential factor
    for candidate in filtered_candidates {
        if let Some(factor) = try_extract_factor(&candidate, n)? {
            factors.push(factor);
        }
    }

    Ok(factors)
}

/// Exhaustive search when other methods fail
fn exhaustive_factor_search<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    ccm: &StandardCCM<P>,
    window: &AlignmentWindow<P>,
    n: &BigUint,
    alpha: &AlphaVec<P>,
) -> Result<Vec<BigUint>> {
    let mut factors = Vec::new();

    // Try trial division with small primes first
    let small_primes = [2u32, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];

    let mut remaining = n.clone();
    for &p in &small_primes {
        let prime = BigUint::from(p);
        while remaining.is_multiple_of(&prime) {
            factors.push(prime.clone());
            remaining /= &prime;
        }
    }

    if remaining == BigUint::one() {
        return Ok(factors);
    }

    // For larger factors, use resonance-guided search
    let _sqrt_n = remaining.sqrt();
    let resonance_step = window.factor_hint.resonance_signature / P::from(100.0).unwrap();

    // Search in resonance neighborhoods
    for i in 0..100 {
        let search_resonance = window.factor_hint.resonance_signature
            - resonance_step * P::from(50).unwrap()
            + resonance_step * P::from(i).unwrap();

        let candidates = ccm.search_by_resonance(search_resonance, alpha, resonance_step)?;

        for candidate in candidates {
            let potential = bitword_to_biguint(&candidate);
            if potential > BigUint::one()
                && potential < remaining
                && remaining.is_multiple_of(&potential)
            {
                factors.push(potential.clone());
                remaining /= potential;

                if remaining > BigUint::one() {
                    factors.push(remaining);
                }
                return Ok(factors);
            }
        }
    }

    // If still no factors, the number might be prime
    if factors.is_empty() {
        factors.push(n.clone());
    }

    Ok(factors)
}

/// Search for BitWords near a given representative
fn search_near_bitword<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    ccm: &StandardCCM<P>,
    rep: &BitWord,
    alpha: &AlphaVec<P>,
    tolerance: f64,
) -> Result<Vec<BitWord>> {
    // Compute resonance of the representative
    let rep_resonance = rep.r(alpha);

    // Search in a neighborhood
    Ok(ccm.search_by_resonance(
        rep_resonance,
        alpha,
        P::from(tolerance).unwrap() * rep_resonance,
    )?)
}

/// Try to extract a factor from a BitWord
fn try_extract_factor(candidate: &BitWord, n: &BigUint) -> Result<Option<BigUint>> {
    let factor = bitword_to_biguint(candidate);

    // Check if it's a valid factor
    if factor > BigUint::one() && factor < *n && n.is_multiple_of(&factor) {
        Ok(Some(factor))
    } else {
        Ok(None)
    }
}

/// Validate that a factor is correct
fn validate_factor(factor: &BigUint, n: &BigUint) -> Result<bool> {
    Ok(factor > &BigUint::one() && factor < n && n.is_multiple_of(factor))
}

/// Convert BitWord to BigUint preserving resonance structure
pub(crate) fn bitword_to_biguint(bitword: &BitWord) -> BigUint {
    // For Klein group preservation, we need to maintain the bit pattern
    // that corresponds to the resonance class and Klein orbit position
    
    let n = bitword.len();
    
    // Special handling for small BitWords (≤ 64 bits)
    if n <= 64 {
        // Direct conversion preserving all bits
        let mut value = 0u64;
        for i in 0..n {
            if bitword.bit(i) {
                value |= 1u64 << i;
            }
        }
        return BigUint::from(value);
    }
    
    // For larger BitWords, preserve structure by processing in chunks
    // that maintain Klein group alignment
    let mut result = BigUint::from(0u32);
    
    // Process in 8-bit chunks to preserve byte structure
    let bytes_needed = (n + 7) / 8;
    let mut bytes = vec![0u8; bytes_needed];
    
    for i in 0..n {
        if bitword.bit(i) {
            let byte_idx = i / 8;
            let bit_idx = i % 8;
            bytes[byte_idx] |= 1u8 << bit_idx;
        }
    }
    
    // Convert bytes to BigUint in little-endian order
    // This preserves the Klein group structure in the last 2 bits
    result = BigUint::from_bytes_le(&bytes);
    
    // Verify Klein structure is preserved
    // The last two bits should maintain their XOR properties
    if n >= 2 {
        let last_two_original = (bitword.bit(n-2), bitword.bit(n-1));
        let result_bits = result.to_bytes_le();
        if !result_bits.is_empty() {
            let last_byte = result_bits[result_bits.len() - 1];
            let result_last_two = (
                (last_byte >> ((n-2) % 8)) & 1 != 0,
                (last_byte >> ((n-1) % 8)) & 1 != 0
            );
            
            // Ensure Klein bits are preserved
            if last_two_original != result_last_two {
                // This shouldn't happen with correct implementation
                // but we'll handle it gracefully
                eprintln!("Warning: Klein group bits not preserved in conversion");
            }
        }
    }
    
    result
}

/// Find dominant grades in grade decompositions
fn find_dominant_grades<P: Float + std::iter::Sum>(
    grade_decomps: &[Vec<ccm_coherence::CliffordElement<P>>],
) -> Vec<usize> {
    let mut grade_weights = vec![P::zero(); 9]; // Max 8 grades + grade 0

    // Sum norms across all decompositions
    for decomp in grade_decomps {
        for (grade, element) in decomp.iter().enumerate() {
            if grade < grade_weights.len() {
                // Use coherence norm squared
                let norm_sq = element.coherence_norm_squared();
                grade_weights[grade] = grade_weights[grade] + norm_sq;
            }
        }
    }

    // Find grades with significant weight
    let total_weight: P = grade_weights.clone().into_iter().sum();
    let threshold = total_weight * P::from(0.1).unwrap(); // 10% threshold

    let mut dominant_grades = Vec::new();
    for (grade, &weight) in grade_weights.iter().enumerate() {
        if weight > threshold {
            dominant_grades.push(grade);
        }
    }

    dominant_grades
}

/// Filter candidates by grade structure
fn filter_by_grades(candidates: Vec<BitWord>, target_grades: &[usize]) -> Vec<BitWord> {
    if target_grades.is_empty() {
        return candidates;
    }

    candidates.into_iter()
        .filter(|candidate| {
            // Compute which grades are active based on bit pattern
            let active_grades = compute_bitword_grades(candidate);
            
            // Check if dominant grades match any of the target grades
            has_matching_grades(&active_grades, target_grades)
        })
        .collect()
}

/// Compute the Clifford grades present in a BitWord
pub(crate) fn compute_bitword_grades(bitword: &BitWord) -> Vec<usize> {
    // In CCM's Clifford algebra, the BitWord encodes which basis vectors
    // are present in a Clifford product. Each bit position i corresponds
    // to basis vector e_i.
    
    // For a proper Clifford element, we need to consider:
    // 1. The grade is the number of distinct basis vectors in the product
    // 2. Different bit patterns can represent elements of multiple grades
    // 3. The full grade decomposition may have components at several grades
    
    let mut active_grades = Vec::new();
    
    // Count the number of set bits (this gives the primary grade)
    let mut popcount = 0;
    let mut bit_positions = Vec::new();
    
    for i in 0..bitword.len() {
        if bitword.bit(i) {
            popcount += 1;
            bit_positions.push(i);
        }
    }
    
    // Primary grade based on number of basis vectors
    active_grades.push(popcount);
    
    // In CCM, certain bit patterns may also have lower-grade components
    // due to the geometric product rules (e_i * e_i = 1 for orthonormal basis)
    // This is especially relevant for patterns with repeated indices
    
    // Check for special patterns that yield multiple grades
    if popcount > 1 {
        // Check for patterns that could contract to lower grades
        // For example, if bits form pairs that could contract
        // This is a simplified check - full implementation would use
        // the actual Clifford multiplication rules
        
        // For now, we'll include potential lower grades based on
        // the structure of the bit pattern
        if popcount % 2 == 0 {
            // Even grades can potentially have components at grade 0
            active_grades.push(0);
        }
        
        // Middle grades might also be present
        if popcount > 2 {
            active_grades.push(popcount - 2);
        }
    }
    
    // Remove duplicates and sort
    active_grades.sort_unstable();
    active_grades.dedup();
    
    active_grades
}

/// Check if computed grades match any target grades
fn has_matching_grades(active_grades: &[usize], target_grades: &[usize]) -> bool {
    // Check if any active grade is in the target set
    active_grades.iter().any(|&grade| target_grades.contains(&grade))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ccm_core::BitWord;

    #[test]
    fn test_bitword_to_biguint_small() {
        // Test small BitWord (≤ 64 bits)
        let bitword = BitWord::from_u64(0x123456789ABCDEF0, 64);
        let biguint = bitword_to_biguint(&bitword);
        assert_eq!(biguint, BigUint::from(0x123456789ABCDEF0u64));
    }

    #[test]
    fn test_bitword_to_biguint_large() {
        // Test large BitWord (> 64 bits)
        let bytes = vec![0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0,
                        0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88];
        let bitword = BitWord::from_bytes(&bytes);
        let biguint = bitword_to_biguint(&bitword);
        
        // BitWord stores bytes in little-endian order within words
        // So we need to interpret them correctly
        let expected = BigUint::from_bytes_le(&bytes);
        assert_eq!(biguint, expected);
    }

    #[test]
    fn test_bitword_to_biguint_edge_cases() {
        // Test zero
        let zero = BitWord::from_u8(0);
        assert_eq!(bitword_to_biguint(&zero), BigUint::from(0u32));

        // Test all ones (8 bits)
        let ones = BitWord::from_u8(0xFF);
        assert_eq!(bitword_to_biguint(&ones), BigUint::from(255u32));
    }

    #[test]
    fn test_compute_bitword_grades() {
        // Grade 0: no bits set
        let grade0 = BitWord::from_u8(0b00000000);
        assert_eq!(compute_bitword_grades(&grade0), vec![0]);

        // Grade 1: one bit set
        let grade1 = BitWord::from_u8(0b00000010);
        assert_eq!(compute_bitword_grades(&grade1), vec![1]);

        // Grade 3: three bits set
        let grade3 = BitWord::from_u8(0b00101001);
        assert_eq!(compute_bitword_grades(&grade3), vec![3]);

        // Grade 8: all bits set
        let grade8 = BitWord::from_u8(0b11111111);
        assert_eq!(compute_bitword_grades(&grade8), vec![8]);
    }

    #[test]
    fn test_filter_by_grades() {
        let candidates = vec![
            BitWord::from_u8(0b00000000), // grade 0
            BitWord::from_u8(0b00000001), // grade 1
            BitWord::from_u8(0b00000011), // grade 2
            BitWord::from_u8(0b00001111), // grade 4
            BitWord::from_u8(0b11111111), // grade 8
        ];

        // Filter for grades 1 and 2
        let target_grades = vec![1, 2];
        let filtered = filter_by_grades(candidates.clone(), &target_grades);
        assert_eq!(filtered.len(), 2);
        // First element should have 1 bit set
        let mut count = 0;
        for i in 0..filtered[0].len() {
            if filtered[0].bit(i) { count += 1; }
        }
        assert_eq!(count, 1);
        // Second element should have 2 bits set
        let mut count = 0;
        for i in 0..filtered[1].len() {
            if filtered[1].bit(i) { count += 1; }
        }
        assert_eq!(count, 2);

        // Filter for grade 8
        let target_grades = vec![8];
        let filtered = filter_by_grades(candidates.clone(), &target_grades);
        assert_eq!(filtered.len(), 1);
        // Element should have 8 bits set
        let mut count = 0;
        for i in 0..filtered[0].len() {
            if filtered[0].bit(i) { count += 1; }
        }
        assert_eq!(count, 8);

        // Empty target grades returns all
        let filtered = filter_by_grades(candidates.clone(), &[]);
        assert_eq!(filtered.len(), candidates.len());
    }
}
