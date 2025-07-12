//! Core CCM API
//!
//! This module provides the fundamental operations of Coherence-Centric Mathematics (CCM)
//! that applications can use to build higher-level functionality.
//!
//! The core API provides:
//! - Embedding of mathematical objects into CCM sections
//! - Coherence norm computation and minimization
//! - Resonance-based search and optimization
//! - Symmetry group actions
//!
//! Applications like the BJC codec, factoring algorithms, and quantum neural networks
//! build upon these core operations.

use crate::{AlphaVec, BitWord, CcmError, Float, Resonance};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

// Sub-modules for different aspects of CCM
pub mod embed;
pub mod optimize;
pub mod search;
pub mod symmetry;

// Re-export key types
pub use embed::{Embedding, Section};
pub use optimize::{CoherenceMinimizer, OptimizationStrategy};
pub use search::{ResonanceSearch, SearchStrategy};
pub use symmetry::{GroupAction, SymmetryGroup};

/// Core CCM operations trait
///
/// This trait provides the fundamental operations of CCM that all applications use.
/// Implementations may vary based on precision requirements, performance characteristics,
/// or specific mathematical properties.
pub trait CCMCore<P: Float> {
    /// The section type representing embedded mathematical objects
    type Section: Clone;
    
    /// Embed a mathematical object into a CCM section
    ///
    /// This operation finds the minimal coherence norm representation
    /// of the given object according to CCM axiom A2.
    fn embed(&self, object: &BitWord, alpha: &AlphaVec<P>) -> Result<Self::Section, CcmError>;
    
    /// Compute the coherence norm of a section
    ///
    /// The coherence norm is defined as ‖x‖_c = √⟨⟨x,x⟩⟩ where ⟨⟨·,·⟩⟩
    /// is the coherence inner product from axiom A1.
    fn coherence_norm(&self, section: &Self::Section) -> P;
    
    /// Minimize coherence norm of a section
    ///
    /// Given an initial section, find a nearby section with minimal coherence norm
    /// that represents the same mathematical object.
    fn minimize_coherence(
        &self,
        initial: &Self::Section,
        strategy: OptimizationStrategy,
    ) -> Result<Self::Section, CcmError>;
    
    /// Search for elements with specific resonance value
    ///
    /// Find all BitWords whose resonance value matches the target within tolerance.
    /// This is the inverse resonance problem.
    #[cfg(feature = "alloc")]
    fn search_by_resonance(
        &self,
        target: P,
        alpha: &AlphaVec<P>,
        tolerance: P,
        strategy: SearchStrategy,
    ) -> Result<Vec<BitWord>, CcmError>;
    
    /// Find minimum resonance element in an equivalence class
    ///
    /// Given an input, find the element with minimum resonance in its Klein group
    /// or other equivalence class structure.
    fn find_minimum_resonance(
        &self,
        input: &BitWord,
        alpha: &AlphaVec<P>,
    ) -> Result<BitWord, CcmError>;
    
    /// Apply symmetry group action
    ///
    /// Transform a section according to a symmetry group element while preserving
    /// all CCM structure (coherence product, grades, embeddings).
    fn apply_symmetry(
        &self,
        section: &Self::Section,
        group_element: &dyn GroupAction<P>,
    ) -> Result<Self::Section, CcmError>;
}

/// Standard implementation of CCM core operations
///
/// This implementation provides the standard algorithms for CCM operations,
/// suitable for most applications.
#[derive(Debug, Clone)]
pub struct StandardCCM<P: Float> {
    /// Configuration for optimization strategies
    pub optimization_config: optimize::Config,
    /// Configuration for search strategies
    pub search_config: search::Config,
    _phantom: core::marker::PhantomData<P>,
}

impl<P: Float> Default for StandardCCM<P> {
    fn default() -> Self {
        Self {
            optimization_config: optimize::Config::default(),
            search_config: search::Config::default(),
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<P: Float> StandardCCM<P> {
    /// Create a new StandardCCM instance with default configuration
    pub fn new() -> Self {
        Self::default()
    }
    
    /// Create with custom configuration
    pub fn with_config(
        optimization_config: optimize::Config,
        search_config: search::Config,
    ) -> Self {
        Self {
            optimization_config,
            search_config,
            _phantom: core::marker::PhantomData,
        }
    }
}

// The actual implementation will be in the sub-modules
impl<P: Float> CCMCore<P> for StandardCCM<P> {
    type Section = Section<P>;
    
    fn embed(&self, object: &BitWord, alpha: &AlphaVec<P>) -> Result<Self::Section, CcmError> {
        embed::minimal_embedding(object, alpha)
    }
    
    fn coherence_norm(&self, section: &Self::Section) -> P {
        section.coherence_norm()
    }
    
    fn minimize_coherence(
        &self,
        initial: &Self::Section,
        strategy: OptimizationStrategy,
    ) -> Result<Self::Section, CcmError> {
        optimize::minimize_coherence(initial, strategy, &self.optimization_config)
    }
    
    #[cfg(feature = "alloc")]
    fn search_by_resonance(
        &self,
        target: P,
        alpha: &AlphaVec<P>,
        tolerance: P,
        strategy: SearchStrategy,
    ) -> Result<Vec<BitWord>, CcmError> {
        search::find_by_resonance(target, alpha, tolerance, strategy, &self.search_config)
    }
    
    fn find_minimum_resonance(
        &self,
        input: &BitWord,
        alpha: &AlphaVec<P>,
    ) -> Result<BitWord, CcmError> {
        search::find_klein_minimum(input, alpha)
    }
    
    fn apply_symmetry(
        &self,
        section: &Self::Section,
        group_element: &dyn GroupAction<P>,
    ) -> Result<Self::Section, CcmError> {
        symmetry::apply_group_action(section, group_element)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_standard_ccm_creation() {
        let ccm = StandardCCM::<f64>::new();
        // Basic creation test
        assert!(matches!(ccm.optimization_config, optimize::Config { .. }));
    }
}