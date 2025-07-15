//! Inherent decomposition properties of resonance structure
//!
//! This module implements decomposition functionality that emerges naturally from
//! the resonance algebra and Klein group structure. These are not imposed algorithms
//! but rather mathematical properties inherent to CCM's embedding axiom.
//!
//! ## Mathematical Foundation
//!
//! Decomposition in resonance space is based on:
//! 1. **Klein Group Structure**: Natural 4-element partitions via XOR on unity bits
//! 2. **Conservation Laws**: Resonance sums are preserved across decompositions
//! 3. **Natural Boundaries**: Discontinuities in resonance landscape
//!
//! ## Key Properties
//!
//! - Every bit pattern belongs to exactly one Klein group
//! - Klein groups preserve resonance relationships
//! - Conservation laws constrain valid decompositions
//! - Boundaries emerge from resonance discontinuities

use crate::{AlphaVec, Resonance};
use ccm_core::{BitWord, Float, CcmError};
use num_traits::FromPrimitive;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Natural decomposition based on resonance structure
pub trait ResonanceDecomposable<P: Float>: Resonance<P> + Sized {
    /// Decompose into Klein group partitions
    fn klein_decompose(&self, alpha: &AlphaVec<P>) -> Vec<KleinPartition<Self>>;
    
    /// Find natural boundaries based on resonance discontinuities
    fn find_resonance_boundaries(&self, alpha: &AlphaVec<P>) -> Vec<ResonanceBoundary>;
    
    /// Check if a decomposition preserves conservation laws
    fn verify_decomposition(&self, parts: &[Self], alpha: &AlphaVec<P>) -> bool;
}

/// A partition based on Klein group structure
#[derive(Clone, Debug)]
pub struct KleinPartition<T> {
    /// The Klein group members in this partition
    pub members: Vec<T>,
    /// The representative (minimal resonance member)
    pub representative: T,
    /// Shared resonance value
    pub resonance: f64,
}

/// A natural boundary in resonance space
#[derive(Clone, Debug)]
pub struct ResonanceBoundary {
    /// Position of the boundary
    pub position: usize,
    /// Magnitude of resonance discontinuity
    pub discontinuity: f64,
    /// Type of boundary
    pub boundary_type: ResonanceBoundaryType,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ResonanceBoundaryType {
    /// Large jump in resonance value
    ResonanceJump,
    /// Change in Klein group structure
    KleinTransition,
    /// Conservation law boundary (e.g., 256-period)
    ConservationBoundary,
    /// Composite of multiple indicators
    Composite,
}

/// Implementation for BitWord
#[cfg(feature = "alloc")]
impl<P: Float + FromPrimitive> ResonanceDecomposable<P> for BitWord {
    fn klein_decompose(&self, alpha: &AlphaVec<P>) -> Vec<KleinPartition<Self>> {
        let n = self.len();
        if n < 2 {
            // No Klein structure possible
            return vec![KleinPartition {
                members: vec![self.clone()],
                representative: self.clone(),
                resonance: self.r(alpha).to_f64().unwrap_or(0.0),
            }];
        }
        
        // Get Klein group members
        let members = <Self as Resonance<P>>::class_members(self);
        
        // Find the representative (minimal resonance)
        let mut min_resonance = P::infinity();
        let mut representative = self.clone();
        
        for member in &members {
            let r = member.r(alpha);
            if r < min_resonance {
                min_resonance = r;
                representative = member.clone();
            }
        }
        
        vec![KleinPartition {
            members,
            representative,
            resonance: min_resonance.to_f64().unwrap_or(0.0),
        }]
    }
    
    fn find_resonance_boundaries(&self, alpha: &AlphaVec<P>) -> Vec<ResonanceBoundary> {
        let mut boundaries = Vec::new();
        let n = self.len();
        
        // For bit patterns, boundaries occur at specific structural points
        
        // 1. Conservation boundaries (every 256 for 8-bit patterns)
        if n == 8 {
            for i in 1..=(self.to_usize() / 256) {
                boundaries.push(ResonanceBoundary {
                    position: i * 256,
                    discontinuity: 0.0, // Exact conservation
                    boundary_type: ResonanceBoundaryType::ConservationBoundary,
                });
            }
        }
        
        // 2. Klein transition boundaries
        // These occur when the Klein group structure changes significantly
        let klein_partitions = self.klein_decompose(alpha);
        if !klein_partitions.is_empty() {
            let base_resonance = klein_partitions[0].resonance;
            
            // Check neighbors for large resonance changes
            for bit in 0..n.min(20) { // Limit search for large n
                let mut neighbor = self.clone();
                neighbor.flip_bit(bit);
                
                let neighbor_partitions = neighbor.klein_decompose(alpha);
                if !neighbor_partitions.is_empty() {
                    let neighbor_resonance = neighbor_partitions[0].resonance;
                    let discontinuity = (neighbor_resonance - base_resonance).abs();
                    
                    // Threshold for significant discontinuity
                    if discontinuity > base_resonance * 0.1 {
                        boundaries.push(ResonanceBoundary {
                            position: bit,
                            discontinuity,
                            boundary_type: ResonanceBoundaryType::ResonanceJump,
                        });
                    }
                }
            }
        }
        
        boundaries.sort_by_key(|b| b.position);
        boundaries
    }
    
    fn verify_decomposition(&self, parts: &[Self], alpha: &AlphaVec<P>) -> bool {
        // A valid decomposition must:
        // 1. Preserve total resonance (within tolerance)
        // 2. Maintain Klein group structure
        // 3. Satisfy conservation laws
        
        let tolerance = P::epsilon() * P::from(1000.0).unwrap();
        
        // Check resonance conservation
        let whole_resonance = self.r(alpha);
        let parts_sum: P = parts.iter()
            .map(|p| p.r(alpha))
            .fold(P::zero(), |a, b| a + b);
        
        if (whole_resonance - parts_sum).abs() > tolerance {
            return false;
        }
        
        // Check that all parts are valid (non-empty)
        for part in parts {
            // A part is valid if it has non-zero resonance
            if part.r(alpha) <= P::zero() {
                return false;
            }
        }
        
        // All checks passed - resonance is conserved and parts are valid
        true
    }
}

/// Natural decomposition strategies based on resonance properties
pub mod strategies {
    use super::*;
    
    /// Decompose at resonance discontinuities
    pub fn decompose_at_boundaries<P: Float + FromPrimitive>(
        word: &BitWord,
        alpha: &AlphaVec<P>,
    ) -> Result<Vec<BitWord>, CcmError> {
        let boundaries = word.find_resonance_boundaries(alpha);
        
        if boundaries.is_empty() {
            // No natural decomposition points
            return Ok(vec![word.clone()]);
        }
        
        let mut parts = Vec::new();
        let mut current_start = 0;
        
        for boundary in boundaries {
            if boundary.discontinuity > 0.1 { // Significant boundary
                // Extract part from current_start to boundary.position
                let part = extract_part(word, current_start, boundary.position)?;
                parts.push(part);
                current_start = boundary.position;
            }
        }
        
        // Add final part
        if current_start < word.len() {
            let part = extract_part(word, current_start, word.len())?;
            parts.push(part);
        }
        
        // Verify the decomposition
        if word.verify_decomposition(&parts, alpha) {
            Ok(parts)
        } else {
            Err(CcmError::Custom("Invalid decomposition"))
        }
    }
    
    /// Decompose into Klein-aligned components
    pub fn klein_aligned_decomposition<P: Float + FromPrimitive>(
        word: &BitWord,
        alpha: &AlphaVec<P>,
    ) -> Result<Vec<BitWord>, CcmError> {
        let klein_partitions = word.klein_decompose(alpha);
        
        // For simple cases, return the Klein representatives
        if klein_partitions.len() <= 1 {
            return Ok(klein_partitions.into_iter()
                .map(|p| p.representative)
                .collect());
        }
        
        // For complex patterns, use Klein structure to guide decomposition
        let mut parts = Vec::new();
        for partition in klein_partitions {
            parts.push(partition.representative);
        }
        
        Ok(parts)
    }
    
    // Helper function to extract a part of a BitWord
    fn extract_part(word: &BitWord, start: usize, end: usize) -> Result<BitWord, CcmError> {
        let n = end - start;
        let mut part = BitWord::new(n);
        
        for i in start..end {
            if i < word.len() {
                part.set_bit(i - start, word.bit(i));
            }
        }
        
        Ok(part)
    }
}

/// Conservation-aware decomposition
pub mod conservation {
    use super::*;
    
    /// Decompose while maintaining conservation laws
    pub fn conservation_preserving_decomposition<P: Float + FromPrimitive>(
        word: &BitWord,
        alpha: &AlphaVec<P>,
        target_parts: usize,
    ) -> Result<Vec<BitWord>, CcmError> {
        // Start with Klein-aligned decomposition
        let mut parts = strategies::klein_aligned_decomposition(word, alpha)?;
        
        // If we need more parts, subdivide while preserving conservation
        while parts.len() < target_parts {
            // Find the part with highest resonance to split
            let (max_idx, _) = parts.iter()
                .enumerate()
                .map(|(i, p)| (i, p.r(alpha)))
                .max_by(|(_, r1), (_, r2)| r1.partial_cmp(r2).unwrap())
                .unwrap();
            
            let part_to_split = parts.remove(max_idx);
            let sub_parts = strategies::decompose_at_boundaries(&part_to_split, alpha)?;
            
            // Verify conservation is maintained
            let original_resonance = part_to_split.r(alpha);
            let sub_resonance: P = sub_parts.iter()
                .map(|p| p.r(alpha))
                .fold(P::zero(), |a, b| a + b);
            
            if (original_resonance - sub_resonance).abs() < P::epsilon() * P::from(100.0).unwrap() {
                parts.extend(sub_parts);
            } else {
                // Revert if conservation is violated
                parts.insert(max_idx, part_to_split);
                break;
            }
        }
        
        Ok(parts)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_klein_decomposition() {
        let alpha = crate::tests::testing_alpha();
        let word = BitWord::from_u8(0b11001100);
        
        let partitions = word.klein_decompose(&alpha);
        assert_eq!(partitions.len(), 1); // Single Klein group
        assert_eq!(partitions[0].members.len(), 4); // Klein group has 4 members
    }
    
    #[test]
    fn test_resonance_boundaries() {
        let alpha = crate::tests::testing_alpha();
        let word = BitWord::from_u8(255);
        
        let boundaries = word.find_resonance_boundaries(&alpha);
        // Should find boundaries based on resonance structure
        assert!(!boundaries.is_empty());
    }
    
    #[test]
    fn test_decomposition_verification() {
        let alpha = crate::tests::testing_alpha();
        let word = BitWord::from_u8(0b10101010);
        
        // Valid decomposition: the word itself
        assert!(word.verify_decomposition(&[word.clone()], &alpha));
        
        // Invalid decomposition would violate conservation
        let invalid_parts = vec![BitWord::from_u8(0), BitWord::from_u8(1)];
        assert!(!word.verify_decomposition(&invalid_parts, &alpha));
        
        // Test that empty decomposition is invalid (doesn't conserve resonance)
        assert!(!word.verify_decomposition(&[], &alpha));
    }
}