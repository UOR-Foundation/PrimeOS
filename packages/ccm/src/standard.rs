//! Standard implementation of CCMCore that integrates all three engines

use crate::cache::{CacheConfig, CcmCache};
use crate::engines::{CoherenceEngine, EmbeddingEngine, SymmetryEngine};
use ccm_coherence::{embedding::bitword_to_clifford, CliffordElement};
use ccm_core::{BitWord, CCMCore, CcmError, Float};
use ccm_embedding::AlphaVec;
use ccm_symmetry::GroupElement;

#[cfg(feature = "alloc")]
use alloc::{vec, vec::Vec};

/// Standard CCM implementation integrating all three mathematical structures
pub struct StandardCCM<P: Float> {
    embedding_engine: EmbeddingEngine<P>,
    coherence_engine: CoherenceEngine<P>,
    symmetry_engine: SymmetryEngine<P>,
    cache: CcmCache<P>,
    dimension: usize,
}

impl<P: Float + num_traits::FromPrimitive> StandardCCM<P> {
    /// Create a new StandardCCM instance for the given dimension
    pub fn new(dimension: usize) -> Result<Self, CcmError> {
        Self::with_cache_config(dimension, CacheConfig::default())
    }

    /// Create a new StandardCCM instance with custom cache configuration
    pub fn with_cache_config(
        dimension: usize,
        cache_config: CacheConfig,
    ) -> Result<Self, CcmError> {
        let embedding_engine = EmbeddingEngine::new();
        let mut coherence_engine = CoherenceEngine::new(dimension)?;

        // Pre-create algebra for small dimensions
        if dimension <= 12 {
            coherence_engine.ensure_algebra()?;
        }

        let symmetry_engine = SymmetryEngine::new(dimension)?;
        let cache = CcmCache::<P>::with_config(cache_config);

        Ok(Self {
            embedding_engine,
            coherence_engine,
            symmetry_engine,
            cache,
            dimension,
        })
    }

    /// Create with default 8-bit dimension
    pub fn with_default_dimension() -> Result<Self, CcmError> {
        Self::new(8)
    }

    /// Get dimension
    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// Create alpha values for current dimension (with caching)
    pub fn generate_alpha(&self) -> Result<AlphaVec<P>, CcmError> {
        // Check cache first
        if let Some(cached_alpha) = self.cache.get_alpha(self.dimension) {
            return Ok(cached_alpha);
        }

        // Generate new alpha values
        let alpha = self.embedding_engine.generate_alpha(self.dimension)?;

        // Store in cache
        self.cache.put_alpha(self.dimension, alpha.clone());

        Ok(alpha)
    }
}

impl<P: Float + num_traits::FromPrimitive> CCMCore<P> for StandardCCM<P> {
    type Section = CliffordElement<P>;

    fn embed(&self, object: &BitWord, alpha: &[P]) -> Result<Self::Section, CcmError> {
        // Convert slice to AlphaVec
        let _alpha_vec =
            AlphaVec::new(alpha.to_vec().into_boxed_slice()).map_err(|_| CcmError::InvalidInput)?;

        // Find minimal resonance representative (cached)
        let minimal = self.find_minimum_resonance(object, alpha)?;

        // For small dimensions, use algebra
        if self.dimension <= 12 {
            let algebra = self
                .coherence_engine
                .get_algebra()
                .ok_or(CcmError::NotImplemented)?;
            bitword_to_clifford(&minimal, algebra)
        } else {
            // For large dimensions, use cached basis element directly
            let index = minimal.to_usize();
            self.coherence_engine
                .basis_element_cached(index, &self.cache)
        }
    }

    fn coherence_norm(&self, section: &Self::Section) -> P {
        self.coherence_engine.coherence_norm(section)
    }

    fn minimize_coherence(&self, initial: &Self::Section) -> Result<Self::Section, CcmError> {
        // Use coherence engine to minimize without constraints
        self.coherence_engine.minimize_coherence(initial, None)
    }

    fn find_minimum_resonance(&self, input: &BitWord, alpha: &[P]) -> Result<BitWord, CcmError> {
        // Check cache first
        if let Some(cached_minimal) = self.cache.get_minimal(input) {
            return Ok(cached_minimal);
        }

        let alpha_vec =
            AlphaVec::new(alpha.to_vec().into_boxed_slice()).map_err(|_| CcmError::InvalidInput)?;

        let minimal = self.embedding_engine.find_minimal(input, &alpha_vec)?;

        // Store in cache
        self.cache.put_minimal(input.clone(), minimal.clone());

        Ok(minimal)
    }
}

// Extended API methods
impl<P: Float + num_traits::FromPrimitive> StandardCCM<P> {
    /// Apply symmetry transformation to a section
    pub fn apply_symmetry(
        &self,
        section: &CliffordElement<P>,
        g: &GroupElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        self.symmetry_engine.apply_to_clifford(g, section)
    }

    /// Search for BitWords with resonance near target value
    pub fn search_by_resonance(
        &self,
        target: P,
        alpha: &AlphaVec<P>,
        tolerance: P,
    ) -> Result<Vec<BitWord>, CcmError> {
        let mut results = Vec::new();

        // Scale-adaptive search strategy
        match self.dimension {
            n if n <= 20 => {
                // Direct exhaustive search for small dimensions
                let max_val = 1usize << n;
                for i in 0..max_val {
                    let word = BitWord::from_usize(i);
                    let resonance =
                        self.embedding_engine
                            .resonance_cached(&word, alpha, &self.cache);
                    if (resonance - target).abs() <= tolerance {
                        results.push(word);
                    }
                }
            }
            n if n <= 64 => {
                // Algebraic search using Klein groups
                // Sample representative elements and expand via Klein groups
                let samples = 1000; // Configurable sampling rate
                for i in 0..samples {
                    let word = BitWord::from_usize(i * (1 << (n - 2)));
                    let resonance =
                        self.embedding_engine
                            .resonance_cached(&word, alpha, &self.cache);
                    if (resonance - target).abs() <= tolerance {
                        // Add all Klein members
                        let members = self
                            .embedding_engine
                            .klein_members_cached(&word, &self.cache);
                        results.extend(members);
                    }
                }
            }
            _ => {
                // Full geometric search for large dimensions
                return Err(CcmError::NotImplemented);
            }
        }

        Ok(results)
    }

    /// Get embedding engine reference
    pub fn embedding(&self) -> &EmbeddingEngine<P> {
        &self.embedding_engine
    }

    /// Get coherence engine reference
    pub fn coherence(&self) -> &CoherenceEngine<P> {
        &self.coherence_engine
    }

    /// Get symmetry engine reference
    pub fn symmetry(&self) -> &SymmetryEngine<P> {
        &self.symmetry_engine
    }

    /// Get Klein group members for a BitWord (with caching)
    pub fn klein_members(&self, word: &BitWord) -> Vec<BitWord> {
        self.embedding_engine
            .klein_members_cached(word, &self.cache)
    }

    /// Clear all caches
    pub fn clear_cache(&self) {
        self.cache.clear();
    }

    /// Get cache statistics (only available with std feature)
    #[cfg(feature = "std")]
    pub fn cache_stats(&self) -> crate::cache::CacheStats {
        self.cache.stats()
    }

    /// Reset cache statistics
    #[cfg(feature = "std")]
    pub fn reset_cache_stats(&self) {
        self.cache.reset_stats();
    }

    /// Warm cache with common values for the current dimension
    pub fn warm_cache(&self) -> Result<(), CcmError> {
        // Pre-generate and cache alpha values
        let alpha = self.generate_alpha()?;

        // Pre-cache Klein members for common bit patterns
        let common_patterns = vec![
            BitWord::from_u8(0),   // All zeros
            BitWord::from_u8(1),   // Single bit
            BitWord::from_u8(255), // All ones
            BitWord::from_u8(170), // Alternating bits (10101010)
            BitWord::from_u8(85),  // Alternating bits (01010101)
        ];

        for pattern in &common_patterns {
            // Cache Klein members
            let _ = self.klein_members(pattern);

            // Cache minimal resonance
            let _ = self.find_minimum_resonance(pattern, &alpha)?;

            // Cache resonance values
            let _ = self
                .embedding_engine
                .resonance_cached(pattern, &alpha, &self.cache);
        }

        // Pre-cache common basis elements if dimension is small
        if self.dimension <= 12 {
            // Cache single-bit basis elements
            for i in 0..self.dimension.min(8) {
                let _ = self
                    .coherence_engine
                    .basis_element_cached(1 << i, &self.cache)?;
            }

            // Cache identity element
            let _ = self.coherence_engine.basis_element_cached(0, &self.cache)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_standard_ccm_creation() {
        let ccm = StandardCCM::<f64>::new(8).unwrap();
        assert_eq!(ccm.dimension(), 8);
    }

    #[test]
    fn test_embed_operation() {
        let ccm = StandardCCM::<f64>::new(8).unwrap();
        let alpha = ccm.generate_alpha().unwrap();
        let word = BitWord::from_u8(42);

        let section = ccm.embed(&word, &alpha).unwrap();
        assert!(ccm.coherence_norm(&section) > 0.0);
    }
}
