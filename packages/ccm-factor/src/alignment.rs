//! Alignment window detection using coherence metrics

use crate::{
    error::Result,
    types::{AlignmentWindow, FactorHint, SymmetryType},
};

use ccm::{CCMCore, StandardCCM};
use ccm_coherence::{coherence_product, CliffordElement};
use ccm_core::BitWord;
use ccm_embedding::{AlphaVec, Resonance};
use num_traits::Float;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

#[cfg(feature = "std")]
use std::collections::HashSet;
#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::collections::HashSet;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Find alignment windows that may indicate factor structure
pub fn find_alignment_windows<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    ccm: &StandardCCM<P>,
    channels: &[CliffordElement<P>],
    max_window_size: usize,
    min_confidence: f64,
) -> Result<Vec<AlignmentWindow<P>>> {
    let mut windows = Vec::new();

    // Try different window sizes
    for window_size in 2..=max_window_size.min(channels.len() / 2) {
        // Slide window across channels
        for start in 0..=channels.len().saturating_sub(window_size) {
            let window_sections = &channels[start..start + window_size];

            // Compute alignment score
            let alignment_score = compute_alignment_score(window_sections)?;

            // Check for factor structure
            if let Some(factor_hint) =
                check_factor_structure(ccm, window_sections, alignment_score, min_confidence)?
            {
                windows.push(AlignmentWindow {
                    start,
                    length: window_size,
                    sections: window_sections.to_vec(),
                    factor_hint,
                });
            }
        }
    }

    // Sort by confidence (highest first)
    windows.sort_by(|a, b| {
        b.factor_hint
            .confidence
            .partial_cmp(&a.factor_hint.confidence)
            .unwrap_or(core::cmp::Ordering::Equal)
    });

    Ok(windows)
}

/// Compute coherence-based alignment score for a window
pub(crate) fn compute_alignment_score<P: Float>(sections: &[CliffordElement<P>]) -> Result<P> {
    if sections.is_empty() {
        return Ok(P::zero());
    }

    let mut total_coherence = P::zero();
    let mut count = 0;

    // Compute pairwise coherence products respecting grade orthogonality
    for i in 0..sections.len() {
        for j in i + 1..sections.len() {
            // Get grade decompositions
            let grades_i = sections[i].grade_decomposition();
            let grades_j = sections[j].grade_decomposition();
            
            // Only compute products for matching grades (grade orthogonality)
            for (k, (grade_i, grade_j)) in grades_i.iter().zip(grades_j.iter()).enumerate() {
                // Check if both have non-zero components at this grade
                if grade_i.coherence_norm_squared() > P::epsilon() && 
                   grade_j.coherence_norm_squared() > P::epsilon() {
                    // Compute grade-k coherence product
                    let grade_product = coherence_product(grade_i, grade_j);
                    
                    // For real-valued coherence in CCM, take the real part
                    let real_part = if grade_product.im.abs() < P::epsilon() {
                        grade_product.re
                    } else {
                        // If complex, use magnitude
                        grade_product.norm()
                    };
                    
                    total_coherence = total_coherence + real_part;
                    count += 1;
                }
            }
        }
    }

    // Self-coherence (always real and positive by axiom A1)
    for section in sections {
        let self_norm_sq = section.coherence_norm_squared();
        total_coherence = total_coherence + self_norm_sq.sqrt();
        count += 1;
    }

    if count > 0 {
        Ok(total_coherence / P::from(count).unwrap())
    } else {
        Ok(P::zero())
    }
}

/// Check if a window exhibits factor structure
pub fn check_factor_structure<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    ccm: &StandardCCM<P>,
    sections: &[CliffordElement<P>],
    alignment_score: P,
    min_confidence: f64,
) -> Result<Option<FactorHint<P>>> {
    // Compute various indicators of factor structure
    let resonance_sig = compute_window_resonance(ccm, sections)?;
    let symmetry_type = detect_symmetry_type(ccm, sections)?;
    let grade_decomp = compute_grade_decomposition(ccm, sections)?;

    // Calculate confidence based on multiple factors
    let mut confidence = alignment_score;

    // Boost confidence for certain symmetry types
    match symmetry_type {
        SymmetryType::Klein => confidence = confidence * P::from(1.5).unwrap(),
        SymmetryType::PageAligned => confidence = confidence * P::from(1.3).unwrap(),
        SymmetryType::ResonanceConserving => confidence = confidence * P::from(1.7).unwrap(),
        SymmetryType::Combined => confidence = confidence * P::from(2.0).unwrap(),
        SymmetryType::None => {}
    }

    // Check if confidence meets threshold
    if confidence.to_f64().unwrap_or(0.0) >= min_confidence {
        // Find orbit representatives
        let orbit_reps = find_orbit_representatives(ccm, sections)?;

        Ok(Some(FactorHint {
            confidence,
            orbit_representatives: orbit_reps,
            grade_decomposition: grade_decomp,
            resonance_signature: resonance_sig,
            symmetry_type,
        }))
    } else {
        Ok(None)
    }
}

/// Compute the resonance signature of a window
fn compute_window_resonance<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    ccm: &StandardCCM<P>,
    sections: &[CliffordElement<P>],
) -> Result<P> {
    let mut total_resonance = P::zero();

    for section in sections {
        // Extract resonance from the section's norm
        let norm = ccm.coherence_norm(section);
        total_resonance = total_resonance + norm;
    }

    Ok(total_resonance / P::from(sections.len()).unwrap())
}

/// Detect the type of symmetry in the window
fn detect_symmetry_type<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    ccm: &StandardCCM<P>,
    sections: &[CliffordElement<P>],
) -> Result<SymmetryType> {
    // Check for Klein group symmetry
    if has_klein_symmetry(ccm, sections)? {
        // Check for additional symmetries
        if is_page_aligned(sections)? {
            return Ok(SymmetryType::Combined);
        }
        return Ok(SymmetryType::Klein);
    }

    // Check for page alignment
    if is_page_aligned(sections)? {
        return Ok(SymmetryType::PageAligned);
    }

    // Check for resonance conservation
    if has_resonance_conservation(ccm, sections)? {
        return Ok(SymmetryType::ResonanceConserving);
    }

    Ok(SymmetryType::None)
}

/// Check if sections exhibit Klein group symmetry
fn has_klein_symmetry<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    ccm: &StandardCCM<P>,
    sections: &[CliffordElement<P>],
) -> Result<bool> {
    // Klein V₄ group has structure: {e, a, b, ab} where a² = b² = (ab)² = e
    // For CCM, this manifests as XOR operations on the last two bits
    
    if sections.len() < 4 {
        return Ok(false);
    }

    // Search for potential Klein quadruples
    for i in 0..sections.len().saturating_sub(3) {
        let quad = &sections[i..i + 4];
        
        if is_klein_quadruple(ccm, quad)? {
            return Ok(true);
        }
    }

    Ok(false)
}

/// Check if four sections form a Klein V₄ group
fn is_klein_quadruple<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    ccm: &StandardCCM<P>,
    quad: &[CliffordElement<P>],
) -> Result<bool> {
    if quad.len() != 4 {
        return Ok(false);
    }

    // First, check if all four elements have the same coherence norm
    // (Klein group preserves the norm)
    let norms: Vec<P> = quad.iter().map(|s| ccm.coherence_norm(s)).collect();
    let first_norm = norms[0];
    let tolerance = P::from(1e-10).unwrap();
    
    for &norm in &norms[1..] {
        if (norm - first_norm).abs() > tolerance {
            return Ok(false);
        }
    }

    // Extract the underlying bit patterns from the sections
    // This requires inverse embedding to find the BitWords
    let alpha = ccm.generate_alpha()?;
    let mut bit_patterns = Vec::new();
    
    for section in quad {
        // Try to find BitWords that could have produced this section
        let candidates = inverse_embed_section(ccm, section, &alpha)?;
        if candidates.is_empty() {
            return Ok(false);
        }
        
        // Use the first candidate (Klein minimum)
        bit_patterns.push(candidates[0].clone());
    }
    
    // Now verify Klein group structure using XOR on last 2 bits
    verify_klein_structure_xor(&bit_patterns)
}

/// Verify Klein V₄ structure using XOR operations on unity bits
fn verify_klein_structure_xor(patterns: &[BitWord]) -> Result<bool> {
    if patterns.len() != 4 {
        return Ok(false);
    }
    
    // Get the bit length (should be same for all)
    let n = patterns[0].len();
    if n < 2 {
        return Ok(false); // Need at least 2 bits for Klein group
    }
    
    // Extract last two bits for each pattern
    let mut last_two_bits = Vec::new();
    for pattern in patterns {
        let bit_n_minus_2 = pattern.bit(n - 2);
        let bit_n_minus_1 = pattern.bit(n - 1);
        last_two_bits.push((bit_n_minus_2, bit_n_minus_1));
    }
    
    // Check if we have all four Klein group elements: {00, 01, 10, 11}
    let mut seen = HashSet::new();
    for &bits in &last_two_bits {
        if !seen.insert(bits) {
            return Ok(false); // Duplicate found
        }
    }
    
    if seen.len() != 4 {
        return Ok(false);
    }
    
    // Verify XOR closure property
    for i in 0..4 {
        for j in 0..4 {
            let (a0, a1) = last_two_bits[i];
            let (b0, b1) = last_two_bits[j];
            let result = (a0 ^ b0, a1 ^ b1);
            
            if !last_two_bits.contains(&result) {
                return Ok(false);
            }
        }
    }
    
    // Verify each non-identity element has order 2
    let identity = (false, false);
    for &bits in &last_two_bits {
        if bits != identity {
            // Square should give identity
            let square = (bits.0 ^ bits.0, bits.1 ^ bits.1);
            if square != identity {
                return Ok(false);
            }
        }
    }
    
    Ok(true)
}

/// Verify that patterns satisfy Klein group axioms
fn verify_klein_properties(patterns: &[(bool, bool)]) -> Result<bool> {
    if patterns.len() != 4 {
        return Ok(false);
    }

    // Check that we have all four distinct patterns
    let mut seen = HashSet::new();
    for &pattern in patterns {
        if !seen.insert(pattern) {
            return Ok(false);
        }
    }

    // Verify XOR closure: a ⊕ b = ab
    let xor_closure = |p1: (bool, bool), p2: (bool, bool)| -> (bool, bool) {
        (p1.0 ^ p2.0, p1.1 ^ p2.1)
    };

    // Check all group operations
    for &p1 in patterns {
        for &p2 in patterns {
            let result = xor_closure(p1, p2);
            if !patterns.contains(&result) {
                return Ok(false);
            }
        }
    }

    // Verify each non-identity element has order 2
    let identity = (false, false);
    for &p in patterns {
        if p != identity {
            let square = xor_closure(p, p);
            if square != identity {
                return Ok(false);
            }
        }
    }

    Ok(true)
}

/// Check if window is page-aligned (256-period structure)
fn is_page_aligned<P: Float>(sections: &[CliffordElement<P>]) -> Result<bool> {
    // In CCM, pages have 256-byte periodicity
    // We need the actual window position to check alignment
    // Since we don't have position info here, we check structural properties
    
    const PAGE_SIZE: usize = 256;
    
    // Check if the number of sections aligns with page boundaries
    // Each section represents a channel, typically 8 bits = 1 byte
    let bytes_per_section = 1; // Assuming 8-bit channels
    let total_bytes = sections.len() * bytes_per_section;
    
    // Check if we span complete pages
    if total_bytes >= PAGE_SIZE && total_bytes % PAGE_SIZE == 0 {
        return Ok(true);
    }
    
    // Check if sections exhibit page-periodic resonance patterns
    // For smaller windows, check if they could be page-aligned fragments
    if sections.len() >= 4 {
        // Check for repeating patterns that indicate page structure
        let pattern_length = sections.len().min(PAGE_SIZE);
        if has_periodic_structure(sections, pattern_length) {
            return Ok(true);
        }
    }
    
    Ok(false)
}

/// Check if sections have periodic structure
fn has_periodic_structure<P: Float>(sections: &[CliffordElement<P>], period: usize) -> bool {
    if sections.len() < period * 2 {
        return false;
    }
    
    // Check if patterns repeat with the given period
    for offset in 0..period {
        let mut values = Vec::new();
        
        // Collect values at periodic positions
        let mut pos = offset;
        while pos < sections.len() {
            values.push(&sections[pos]);
            pos += period;
        }
        
        // Check if all values at periodic positions are similar
        if values.len() >= 2 && are_sections_similar(&values) {
            return true;
        }
    }
    
    false
}

/// Check if a set of sections are similar (have close norms)
fn are_sections_similar<P: Float>(sections: &[&CliffordElement<P>]) -> bool {
    if sections.len() < 2 {
        return false;
    }
    
    // For now, use a simple norm-based similarity check
    // In full implementation, would check deeper structural similarity
    let norms: Vec<P> = sections.iter()
        .map(|s| s.coherence_norm_squared())
        .collect();
    
    let first_norm = norms[0];
    let tolerance = P::from(0.1).unwrap() * first_norm;
    
    norms[1..].iter().all(|&norm| (norm - first_norm).abs() <= tolerance)
}

/// Check if resonance is conserved across the window
fn has_resonance_conservation<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    ccm: &StandardCCM<P>,
    sections: &[CliffordElement<P>],
) -> Result<bool> {
    if sections.len() < 3 {
        return Ok(false);
    }

    // For conservation to hold, we need to check:
    // 1. Resonance current conservation (sum of differences = 0)
    // 2. 768-cycle pattern if window is large enough
    // 3. Unity position detection
    
    // Compute resonance differences (current)
    let mut differences = Vec::new();
    let mut resonances = Vec::new();
    
    for section in sections {
        let r = ccm.coherence_norm(section);
        resonances.push(r);
    }
    
    for i in 1..resonances.len() {
        differences.push(resonances[i] - resonances[i-1]);
    }

    // Check current conservation
    let current_sum: P = differences.iter().cloned().sum();
    let current_conserved = current_sum.abs() < P::from(0.001).unwrap();
    
    // Check for 768-cycle pattern
    let cycle_conserved = if sections.len() >= 768 {
        check_768_cycle_pattern(&resonances)
    } else if sections.len() >= 12 {
        // Check for unity positions (12 per 768 cycle)
        check_unity_positions(&resonances)
    } else {
        true // Too small to check cycle patterns
    };
    
    Ok(current_conserved && cycle_conserved)
}

/// Check if resonances follow 768-cycle pattern
fn check_768_cycle_pattern<P: Float + std::iter::Sum>(resonances: &[P]) -> bool {
    const EXPECTED_SUM: f64 = 687.110133051847;
    const CYCLE_LENGTH: usize = 768;
    
    if resonances.len() < CYCLE_LENGTH {
        return true; // Can't verify full cycle
    }
    
    // Sum first complete cycle
    let cycle_sum: P = resonances[0..CYCLE_LENGTH].iter().cloned().sum();
    let expected = P::from(EXPECTED_SUM).unwrap();
    
    (cycle_sum - expected).abs() < P::from(0.01).unwrap()
}

/// Check for unity positions
fn check_unity_positions<P: Float>(resonances: &[P]) -> bool {
    // Unity positions appear at specific intervals
    // In a 768-cycle, there are 12 positions where R = 1
    let unity = P::one();
    let tolerance = P::from(1e-6).unwrap();
    
    let unity_count = resonances.iter()
        .filter(|&&r| (r - unity).abs() < tolerance)
        .count();
    
    // Expect approximately 12/768 ≈ 1.56% to be unity
    let expected_ratio = 12.0 / 768.0;
    let actual_ratio = unity_count as f64 / resonances.len() as f64;
    
    (actual_ratio - expected_ratio).abs() < 0.01
}

/// Compute grade decomposition for all sections
fn compute_grade_decomposition<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    _ccm: &StandardCCM<P>,
    sections: &[CliffordElement<P>],
) -> Result<Vec<Vec<CliffordElement<P>>>> {
    let mut decompositions = Vec::new();

    for section in sections {
        // Get grade decomposition from the section
        let grades = section.grade_decomposition();
        decompositions.push(grades);
    }

    Ok(decompositions)
}

/// Find orbit representatives under symmetry group action
fn find_orbit_representatives<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    ccm: &StandardCCM<P>,
    sections: &[CliffordElement<P>],
) -> Result<Vec<BitWord>> {
    let mut representatives = Vec::new();
    let alpha = ccm.generate_alpha()?;

    // For each section, find the minimal representative in its orbit
    for section in sections {
        // Perform inverse embedding to find possible BitWords
        let candidates = inverse_embed_section(ccm, section, &alpha)?;
        
        if candidates.is_empty() {
            // If no exact inverse found, use approximation
            let approx = approximate_inverse_embedding(section);
            representatives.push(approx);
        } else {
            // Find the minimal representative among candidates
            let min_rep = candidates.into_iter()
                .min_by_key(|b| OrderedFloat(b.r(&alpha)))
                .unwrap();
            representatives.push(min_rep);
        }
    }

    Ok(representatives)
}

/// Attempt to find BitWords that embed to the given section
fn inverse_embed_section<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    ccm: &StandardCCM<P>,
    section: &CliffordElement<P>,
    alpha: &AlphaVec<P>,
) -> Result<Vec<BitWord>> {
    let mut candidates = Vec::new();
    
    // Extract the dominant basis elements from the section
    let basis_indices = extract_dominant_basis_indices(section);
    
    // For each dominant basis index, create corresponding BitWord
    for index in basis_indices {
        // In Clifford algebra, basis index corresponds to bit pattern
        let bitword = BitWord::from_usize(index);
        
        // Verify this actually embeds to something close to our section
        let embedded = ccm.embed(&bitword, alpha)?;
        let distance = compute_section_distance(section, &embedded);
        
        if distance < P::from(1e-6).unwrap() {
            candidates.push(bitword);
        }
    }
    
    // Also check Klein group members of found candidates
    let mut klein_candidates = Vec::new();
    for candidate in &candidates {
        let members = <BitWord as Resonance<P>>::class_members(candidate);
        for member in members {
            if !candidates.contains(&member) {
                let embedded = ccm.embed(&member, alpha)?;
                let distance = compute_section_distance(section, &embedded);
                
                if distance < P::from(1e-6).unwrap() {
                    klein_candidates.push(member);
                }
            }
        }
    }
    candidates.extend(klein_candidates);
    
    Ok(candidates)
}

/// Extract indices of dominant basis elements in a Clifford element
fn extract_dominant_basis_indices<P: Float>(section: &CliffordElement<P>) -> Vec<usize> {
    let mut indices = Vec::new();
    let threshold = P::from(0.1).unwrap();
    
    // Get grade decomposition
    let grades = section.grade_decomposition();
    
    // For each grade, find significant components
    for (grade_idx, grade_component) in grades.iter().enumerate() {
        let norm = grade_component.coherence_norm_squared();
        if norm > threshold {
            // This grade has significant contribution
            // In a full implementation, we'd extract the specific basis indices
            // For now, use grade as a proxy for the dominant pattern
            indices.push(1 << grade_idx); // 2^grade gives a representative index
        }
    }
    
    indices
}

/// Compute distance between two sections
fn compute_section_distance<P: Float>(s1: &CliffordElement<P>, s2: &CliffordElement<P>) -> P {
    // Use coherence metric for distance
    let diff_norm_sq = (s1.coherence_norm_squared() - s2.coherence_norm_squared()).abs();
    diff_norm_sq.sqrt()
}

/// Approximate inverse embedding when exact inverse is not found
fn approximate_inverse_embedding<P: Float>(section: &CliffordElement<P>) -> BitWord {
    // Use the grade structure as a heuristic
    let max_grade = section.max_grade();
    
    // Create a BitWord with popcount equal to max grade
    // This is a reasonable approximation for the inverse
    if max_grade == 0 {
        BitWord::from_u8(0)
    } else if max_grade <= 8 {
        // Create a BitWord with 'max_grade' lowest bits set
        BitWord::from_u8((1u8 << max_grade) - 1)
    } else {
        // For larger grades, create an appropriate pattern
        let mut bytes = vec![0u8; (max_grade + 7) / 8];
        for i in 0..max_grade {
            bytes[i / 8] |= 1 << (i % 8);
        }
        BitWord::from_bytes(&bytes)
    }
}

// Helper for ordered floats in min_by_key
use core::cmp::Ordering;

#[derive(Copy, Clone, PartialEq)]
struct OrderedFloat<T: Float>(T);

impl<T: Float> Eq for OrderedFloat<T> {}

impl<T: Float> PartialOrd for OrderedFloat<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<T: Float> Ord for OrderedFloat<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap_or(Ordering::Equal)
    }
}

/// Parallel version of window search
#[cfg(feature = "parallel")]
pub fn find_alignment_windows_parallel<
    P: Float + num_traits::FromPrimitive + std::iter::Sum + Send + Sync,
>(
    ccm: &StandardCCM<P>,
    channels: &[CliffordElement<P>],
    max_window_size: usize,
    min_confidence: f64,
) -> Result<Vec<AlignmentWindow<P>>>
where
    CliffordElement<P>: Send + Sync,
{
    let window_sizes: Vec<_> = (2..=max_window_size.min(channels.len() / 2)).collect();

    let all_windows: Vec<_> = window_sizes
        .par_iter()
        .flat_map(|&window_size| {
            (0..=channels.len().saturating_sub(window_size))
                .into_par_iter()
                .filter_map(|start| {
                    let window_sections = &channels[start..start + window_size];

                    let alignment_score = compute_alignment_score(window_sections).ok()?;

                    check_factor_structure(ccm, window_sections, alignment_score, min_confidence)
                        .ok()
                        .flatten()
                        .map(|factor_hint| AlignmentWindow {
                            start,
                            length: window_size,
                            sections: window_sections.to_vec(),
                            factor_hint,
                        })
                })
                .collect::<Vec<_>>()
        })
        .collect();

    Ok(all_windows)
}
