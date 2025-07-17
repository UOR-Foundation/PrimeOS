//! Symmetry engine wrapper for ccm-symmetry functionality

use ccm_coherence::{CliffordAlgebra, CliffordElement};
use ccm_core::{BitWord, CcmError, Float};
use ccm_embedding::AlphaVec;
use ccm_symmetry::{CliffordAction, GroupAction, GroupElement, KleinSymmetry, SymmetryGroup};

/// Engine for symmetry operations (Axiom A3)
pub struct SymmetryEngine<P: Float> {
    group: SymmetryGroup<P>,
    clifford_action: Option<CliffordAction<P>>,
}

impl<P: Float + num_traits::FromPrimitive> SymmetryEngine<P> {
    /// Create a new symmetry engine
    pub fn new(dimension: usize) -> Result<Self, CcmError> {
        let group = SymmetryGroup::generate(dimension)?;
        
        // Create default CliffordAction if dimension is reasonable
        let clifford_action = if dimension <= 20 {
            // For reasonable dimensions, create the Clifford algebra and action
            match CliffordAlgebra::<P>::generate(dimension) {
                Ok(algebra) => Some(CliffordAction::new(algebra)),
                Err(_) => None, // Fall back to None if algebra creation fails
            }
        } else {
            // For very large dimensions, defer creation
            None
        };
        
        Ok(Self {
            group,
            clifford_action,
        })
    }

    /// Set up Clifford action
    pub fn with_clifford_action(mut self, action: CliffordAction<P>) -> Self {
        self.clifford_action = Some(action);
        self
    }

    /// Apply group element to Clifford element
    pub fn apply_to_clifford(
        &self,
        g: &GroupElement<P>,
        x: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        if let Some(action) = &self.clifford_action {
            action.apply(g, x)
        } else {
            // Try to create CliffordAction on demand
            let dimension = x.dimension();
            match CliffordAlgebra::<P>::generate(dimension) {
                Ok(algebra) => {
                    let action = CliffordAction::new(algebra);
                    action.apply(g, x)
                }
                Err(_) => Err(CcmError::InvalidInput),
            }
        }
    }

    /// Get Klein symmetry generators
    pub fn klein_generators(&self, n: usize) -> Result<KleinSymmetry, CcmError> {
        KleinSymmetry::new(n)
    }

    /// Apply Klein group element to BitWord
    pub fn apply_klein(&self, b: &BitWord, generator: u8) -> BitWord {
        // Apply XOR with Klein generator (bits n-2 and n-1)
        let n = b.len();
        let mut result = b.clone();

        match generator {
            1 => result.flip_bit(n - 2), // Flip bit n-2
            2 => result.flip_bit(n - 1), // Flip bit n-1
            3 => {
                result.flip_bit(n - 2);
                result.flip_bit(n - 1);
            }
            _ => {} // Identity
        }

        result
    }

    /// Check if transformation preserves resonance
    pub fn preserves_resonance(
        &self,
        transform: &dyn Fn(&BitWord) -> BitWord,
        test_word: &BitWord,
        alpha: &AlphaVec<P>,
    ) -> bool {
        use ccm_embedding::Resonance;

        let original_resonance = test_word.r(alpha);
        let transformed = transform(test_word);
        let new_resonance = transformed.r(alpha);

        (original_resonance - new_resonance).abs() < P::epsilon()
    }

    /// Get the symmetry group
    pub fn group(&self) -> &SymmetryGroup<P> {
        &self.group
    }

    /// Create a group element from parameters
    pub fn element(&self, params: &[P]) -> Result<GroupElement<P>, CcmError> {
        self.group.element(params)
    }
    
    /// Ensure CliffordAction is initialized for the given dimension
    pub fn ensure_clifford_action(&mut self, dimension: usize) -> Result<(), CcmError> {
        if self.clifford_action.is_none() {
            let algebra = CliffordAlgebra::<P>::generate(dimension)?;
            self.clifford_action = Some(CliffordAction::new(algebra));
        }
        Ok(())
    }
}
