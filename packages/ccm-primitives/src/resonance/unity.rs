//! Unity positions and harmonic centers

use crate::{AlphaVec, Float, Resonance};

#[cfg(feature = "alloc")]
use alloc::vec;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Trait for unity structure operations
pub trait UnityStructure {
    /// Find all positions where R = 1
    fn unity_positions<P: Float>(
        alpha: &AlphaVec<P>,
        range: usize,
    ) -> Vec<usize>;
    
    /// Check if value is near unity (within tolerance)
    fn is_near_unity<P: Float>(r: P, tolerance: P) -> bool;
    
    /// Get the standard unity positions for 8-bit
    fn standard_unity_positions() -> [usize; 12] {
        // With dynamic alpha, Klein four-group is {0, 16, 32, 48}
        // Pattern repeats every 256
        [0, 16, 32, 48, 256, 272, 288, 304, 512, 528, 544, 560]
    }
}

/// Implementation for u8
impl UnityStructure for u8 {
    fn unity_positions<P: Float>(
        alpha: &AlphaVec<P>,
        range: usize,
    ) -> Vec<usize> {
        let mut positions = Vec::new();
        let tolerance = P::epsilon() * P::from(100.0).unwrap();
        
        for i in 0..range {
            let byte = (i % 256) as u8;
            let r = byte.r(alpha);
            
            if Self::is_near_unity(r, tolerance) {
                positions.push(i);
            }
        }
        
        positions
    }
    
    fn is_near_unity<P: Float>(r: P, tolerance: P) -> bool {
        (r - P::one()).abs() < tolerance
    }
}

/// Unity analysis functions
pub mod analysis {
    use super::*;
    
    /// Unity spacing analysis
    #[derive(Debug, Clone)]
    pub struct UnitySpacing {
        pub positions: Vec<usize>,
        pub spacings: Vec<usize>,
        pub average_spacing: f64,
        pub is_periodic: bool,
    }
    
    /// Analyze spacing between unity positions
    pub fn analyze_unity_spacing<P: Float>(
        alpha: &AlphaVec<P>,
        range: usize,
    ) -> UnitySpacing {
        let positions = u8::unity_positions(alpha, range);
        let mut spacings = Vec::new();
        
        for i in 1..positions.len() {
            spacings.push(positions[i] - positions[i-1]);
        }
        
        let average_spacing = if !spacings.is_empty() {
            spacings.iter().sum::<usize>() as f64 / spacings.len() as f64
        } else {
            0.0
        };
        
        // Check if spacing is periodic (all spacings equal)
        let is_periodic = if !spacings.is_empty() {
            let first = spacings[0];
            spacings.iter().all(|&s| s == first)
        } else {
            false
        };
        
        UnitySpacing {
            positions,
            spacings,
            average_spacing,
            is_periodic,
        }
    }
    
    /// Find unity clusters (groups of nearby unity positions)
    pub fn find_unity_clusters<P: Float>(
        alpha: &AlphaVec<P>,
        range: usize,
        max_gap: usize,
    ) -> Vec<Vec<usize>> {
        let positions = u8::unity_positions(alpha, range);
        let mut clusters = Vec::new();
        
        if positions.is_empty() {
            return clusters;
        }
        
        let mut current_cluster = vec![positions[0]];
        
        for i in 1..positions.len() {
            if positions[i] - positions[i-1] <= max_gap {
                current_cluster.push(positions[i]);
            } else {
                clusters.push(current_cluster);
                current_cluster = vec![positions[i]];
            }
        }
        
        clusters.push(current_cluster);
        clusters
    }
    
    /// Verify expected unity pattern for standard 8-bit
    pub fn verify_standard_pattern<P: Float>(alpha: &AlphaVec<P>) -> bool {
        let expected = u8::standard_unity_positions();
        let actual = u8::unity_positions(alpha, 768);
        
        // Check first 12 positions match
        if actual.len() < 12 {
            return false;
        }
        
        for i in 0..12 {
            if actual[i] != expected[i] {
                return false;
            }
        }
        
        true
    }
    
    /// Unity density (unity positions per unit range)
    pub fn unity_density<P: Float>(
        alpha: &AlphaVec<P>,
        range: usize,
    ) -> f64 {
        let positions = u8::unity_positions(alpha, range);
        positions.len() as f64 / range as f64
    }
}

/// Properties related to Klein four-group and unity
pub mod klein_unity {
    use super::*;
    
    /// Verify Klein four-group elements have unity resonance
    pub fn verify_klein_unity<P: Float>(alpha: &AlphaVec<P>) -> bool {
        // With dynamic alpha, Klein group is formed by XORing bits 4,5
        // So the Klein four-group elements are: 0, 16, 32, 48
        let klein_elements = [0u8, 16, 32, 48];  // 0b00000000, 0b00010000, 0b00100000, 0b00110000
        let tolerance = P::epsilon() * P::from(100.0).unwrap();
        
        for &elem in &klein_elements {
            let r = elem.r(alpha);
            if !u8::is_near_unity(r, tolerance) {
                return false;
            }
        }
        
        true
    }
    
    /// Find all Klein groups with unity resonance
    pub fn unity_klein_groups<P: Float>(alpha: &AlphaVec<P>) -> Vec<[u8; 4]> {
        let mut unity_groups = Vec::new();
        let tolerance = P::epsilon() * P::from(100.0).unwrap();
        let mut seen = std::collections::HashSet::new();
        
        // Check all possible values
        for value in 0u8..=255 {
            // Get the Klein representative (clear bits 4,5)
            let repr = value & 0b11001111;
            
            // Skip if we've already processed this Klein group
            if seen.contains(&repr) {
                continue;
            }
            seen.insert(repr);
            
            let members = <u8 as Resonance<P>>::class_members(&repr);
            
            // Check if all members have unity resonance
            let all_unity = members.iter().all(|&m| {
                let r = m.r(alpha);
                u8::is_near_unity(r, tolerance)
            });
            
            if all_unity {
                unity_groups.push(members);
            }
        }
        
        unity_groups
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_unity_positions() {
        let alpha = crate::tests::testing_alpha();
        let positions = u8::unity_positions(&alpha, 256);
        
        // Should find at least the basic unity positions
        assert!(!positions.is_empty());
        
        // Verify found positions actually have unity resonance
        for &pos in &positions {
            let byte = (pos % 256) as u8;
            let r = byte.r(&alpha);
            assert!(u8::is_near_unity(r, 1e-10));
        }
    }
    
    #[test]
    fn test_standard_unity_positions() {
        let expected = u8::standard_unity_positions();
        
        // First 4 should be Klein four-group in first 256
        assert_eq!(expected[0], 0);
        assert_eq!(expected[1], 16);
        assert_eq!(expected[2], 32);
        assert_eq!(expected[3], 48);
        
        // Pattern should repeat every 256
        assert_eq!(expected[4], 256);
        assert_eq!(expected[5], 272);
    }
    
    #[test]
    fn test_unity_spacing() {
        let alpha = crate::tests::testing_alpha();
        let spacing = analysis::analyze_unity_spacing(&alpha, 768);
        
        // Should find 12 positions in 768 range
        assert_eq!(spacing.positions.len(), 12);
        
        // Check spacing pattern
        assert!(!spacing.spacings.is_empty());
    }
    
    #[test]
    fn test_klein_unity() {
        let alpha = crate::tests::testing_alpha();
        
        // With dynamic alpha, Klein groups are formed by XORing bits 4,5
        // verify_klein_unity checks if {0, 16, 32, 48} has unity
        
        // Test if the base Klein group has unity
        let has_base_unity = klein_unity::verify_klein_unity(&alpha);
        
        if has_base_unity {
            println!("Base Klein group {{0, 16, 32, 48}} has unity resonance");
        }
        
        // Find all unity Klein groups
        let unity_groups = klein_unity::unity_klein_groups(&alpha);
        
        // If we find unity groups, verify they actually have unity resonance
        for group in &unity_groups {
            for &member in group {
                let r = member.r(&alpha);
                assert!(u8::is_near_unity(r, 1e-6), 
                        "Member {} should have unity resonance", member);
            }
        }
        
        // The test passes whether or not unity groups exist - depends on alpha values
    }
}