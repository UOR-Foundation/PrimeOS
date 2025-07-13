//! Embedding engine wrapper for ccm-embedding functionality

use crate::cache::CcmCache;
use ccm_core::{BitWord, CcmError, Float};
use ccm_embedding::{embed, AlphaVec, Resonance};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Engine for minimal embedding operations (Axiom A2)
pub struct EmbeddingEngine<P: Float> {
    _phantom: core::marker::PhantomData<P>,
}

impl<P: Float + num_traits::FromPrimitive> Default for EmbeddingEngine<P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: Float + num_traits::FromPrimitive> EmbeddingEngine<P> {
    /// Create a new embedding engine
    pub fn new() -> Self {
        Self {
            _phantom: core::marker::PhantomData,
        }
    }

    /// Generate alpha values for the given bit length
    pub fn generate_alpha(&self, n: usize) -> Result<AlphaVec<P>, CcmError> {
        AlphaVec::for_bit_length(n).map_err(|_| CcmError::InvalidInput)
    }

    /// Find the minimal embedding in the Klein group
    pub fn find_minimal(&self, object: &BitWord, alpha: &AlphaVec<P>) -> Result<BitWord, CcmError> {
        embed::minimal_embedding(object, alpha)
    }

    /// Compute resonance value
    pub fn resonance(&self, object: &BitWord, alpha: &AlphaVec<P>) -> P {
        object.r(alpha)
    }

    /// Check if object is a Klein minimum
    pub fn is_klein_minimum(&self, object: &BitWord, alpha: &AlphaVec<P>) -> bool {
        object.is_klein_minimum(alpha)
    }

    /// Get all Klein group members
    pub fn klein_members(&self, object: &BitWord) -> Vec<BitWord> {
        <BitWord as Resonance<P>>::class_members(object)
    }

    /// Get all Klein group members with caching
    pub fn klein_members_cached(&self, object: &BitWord, cache: &CcmCache<P>) -> Vec<BitWord> {
        // Check cache first
        if let Some(cached_members) = cache.get_klein_members(object) {
            return cached_members;
        }

        // Compute Klein members
        let members = self.klein_members(object);

        // Store in cache
        cache.put_klein_members(object.clone(), members.clone());

        members
    }

    /// Compute resonance value with caching
    pub fn resonance_cached(
        &self,
        object: &BitWord,
        alpha: &AlphaVec<P>,
        cache: &CcmCache<P>,
    ) -> P {
        let alpha_dim = alpha.len();

        // Check cache first
        if let Some(cached_resonance) = cache.get_resonance(object, alpha_dim) {
            return cached_resonance;
        }

        // Compute resonance
        let resonance = self.resonance(object, alpha);

        // Store in cache
        cache.put_resonance(object.clone(), alpha_dim, resonance);

        resonance
    }
}
