//! Embedding engine wrapper for ccm-embedding functionality

use ccm_core::{BitWord, CcmError, Float};
use ccm_embedding::{AlphaVec, Resonance, embed};

/// Engine for minimal embedding operations (Axiom A2)
pub struct EmbeddingEngine<P: Float> {
    _phantom: core::marker::PhantomData<P>,
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
        AlphaVec::for_bit_length(n)
            .map_err(|_| CcmError::InvalidInput)
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
}