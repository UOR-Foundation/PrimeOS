//! Standard implementation of CCMCore that integrates all three engines

use crate::engines::{EmbeddingEngine, CoherenceEngine, SymmetryEngine};
use ccm_core::{BitWord, CcmError, CCMCore, Float};
use ccm_embedding::AlphaVec;
use ccm_coherence::{CliffordElement, embedding::bitword_to_clifford};
use ccm_symmetry::GroupElement;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Standard CCM implementation integrating all three mathematical structures
pub struct StandardCCM<P: Float> {
    embedding_engine: EmbeddingEngine<P>,
    coherence_engine: CoherenceEngine<P>,
    symmetry_engine: SymmetryEngine<P>,
    dimension: usize,
}

impl<P: Float + num_traits::FromPrimitive> StandardCCM<P> {
    /// Create a new StandardCCM instance for the given dimension
    pub fn new(dimension: usize) -> Result<Self, CcmError> {
        let embedding_engine = EmbeddingEngine::new();
        let mut coherence_engine = CoherenceEngine::new(dimension)?;
        
        // Pre-create algebra for small dimensions
        if dimension <= 12 {
            coherence_engine.ensure_algebra()?;
        }
        
        let symmetry_engine = SymmetryEngine::new(dimension)?;
        
        Ok(Self {
            embedding_engine,
            coherence_engine,
            symmetry_engine,
            dimension,
        })
    }

    /// Create with default 8-bit dimension
    pub fn default() -> Result<Self, CcmError> {
        Self::new(8)
    }

    /// Get dimension
    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// Create alpha values for current dimension
    pub fn generate_alpha(&self) -> Result<AlphaVec<P>, CcmError> {
        self.embedding_engine.generate_alpha(self.dimension)
    }
}

impl<P: Float + num_traits::FromPrimitive> CCMCore<P> for StandardCCM<P> {
    type Section = CliffordElement<P>;

    fn embed(&self, object: &BitWord, alpha: &[P]) -> Result<Self::Section, CcmError> {
        // Convert slice to AlphaVec
        let alpha_vec = AlphaVec::new(alpha.to_vec().into_boxed_slice())
            .map_err(|_| CcmError::InvalidInput)?;
        
        // Find minimal resonance representative
        let minimal = self.embedding_engine.find_minimal(object, &alpha_vec)?;
        
        // Get the Clifford algebra for embedding
        let algebra = self.coherence_engine.get_algebra()
            .ok_or(CcmError::NotImplemented)?;
        
        // Convert to Clifford element
        bitword_to_clifford(&minimal, algebra)
    }

    fn coherence_norm(&self, section: &Self::Section) -> P {
        self.coherence_engine.coherence_norm(section)
    }

    fn minimize_coherence(&self, initial: &Self::Section) -> Result<Self::Section, CcmError> {
        // Use coherence engine to minimize without constraints
        self.coherence_engine.minimize_coherence(initial, None)
    }

    fn find_minimum_resonance(&self, input: &BitWord, alpha: &[P]) -> Result<BitWord, CcmError> {
        let alpha_vec = AlphaVec::new(alpha.to_vec().into_boxed_slice())
            .map_err(|_| CcmError::InvalidInput)?;
        
        self.embedding_engine.find_minimal(input, &alpha_vec)
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
                    let resonance = self.embedding_engine.resonance(&word, alpha);
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
                    let word = BitWord::from_usize(i * (1 << (n-2)));
                    let resonance = self.embedding_engine.resonance(&word, alpha);
                    if (resonance - target).abs() <= tolerance {
                        // Add all Klein members
                        let members = self.embedding_engine.klein_members(&word);
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