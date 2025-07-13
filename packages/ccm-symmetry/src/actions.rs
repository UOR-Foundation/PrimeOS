//! Group actions on various structures

use crate::group::GroupElement;
use ccm_core::{BitWord, CcmError, Float};
use ccm_coherence::{CliffordAlgebra, CliffordElement};


/// Trait for group actions on various structures
pub trait GroupAction<P: Float> {
    /// The type being acted upon
    type Target;

    /// Apply group element to target
    fn apply(&self, g: &GroupElement<P>, target: &Self::Target) -> Result<Self::Target, CcmError>;

    /// Check if action preserves structure
    fn verify_invariance(&self, g: &GroupElement<P>) -> bool;
}

/// Action on BitWords by bit flips
pub struct BitWordAction {
    /// Which bits to flip (encoded in group element params)
    dimension: usize,
}

impl BitWordAction {
    /// Create a new BitWord action for n-bit words
    pub fn new(dimension: usize) -> Self {
        Self { dimension }
    }
}

impl<P: Float> GroupAction<P> for BitWordAction {
    type Target = BitWord;

    fn apply(&self, g: &GroupElement<P>, target: &Self::Target) -> Result<Self::Target, CcmError> {
        let mut result = target.clone();
        
        // Group element params encode which bits to flip
        // param[i] < 0 means flip bit i
        for (i, &param) in g.params.iter().enumerate() {
            if i < self.dimension && param < P::zero() {
                result.flip_bit(i);
            }
        }
        
        Ok(result)
    }

    fn verify_invariance(&self, _g: &GroupElement<P>) -> bool {
        // Bit flips preserve the number of bits
        true
    }
}

/// Action on Clifford elements preserving grade and norm
pub struct CliffordAction<P: Float> {
    /// The Clifford algebra
    algebra: CliffordAlgebra<P>,
}

impl<P: Float> CliffordAction<P> {
    /// Create a new Clifford action
    pub fn new(algebra: CliffordAlgebra<P>) -> Self {
        Self { algebra }
    }
    
    /// Convert group element parameters to a rotor
    fn params_to_rotor(&self, g: &GroupElement<P>) -> Result<ccm_coherence::rotor::Rotor<P>, CcmError> {
        use ccm_coherence::rotor::Rotor;
        use num_complex::Complex;
        
        let dim = self.algebra.dimension();
        
        // Build bivector from parameters
        // For n dimensions, we have n(n-1)/2 bivector components
        let mut bivector = CliffordElement::zero(dim);
        
        let mut param_idx = 0;
        for i in 0..dim {
            for j in i+1..dim {
                if param_idx < g.params.len() {
                    // Basis bivector e_i ∧ e_j has index 2^i + 2^j
                    let index = (1 << i) | (1 << j);
                    bivector.set_component(index, Complex::new(g.params[param_idx], P::zero()))?;
                    param_idx += 1;
                }
            }
        }
        
        // Create rotor as exp(B/2)
        Rotor::from_bivector(&bivector, &self.algebra)
    }
}

impl<P: Float> GroupAction<P> for CliffordAction<P> {
    type Target = CliffordElement<P>;

    fn apply(&self, g: &GroupElement<P>, x: &Self::Target) -> Result<Self::Target, CcmError> {
        // Apply transformation using rotors (elements of Spin group)
        
        // Identity transformation
        if g.is_identity() {
            return Ok(x.clone());
        }
        
        // Construct rotor from group element parameters
        // Parameters encode bivector components for rotation
        let rotor = self.params_to_rotor(g)?;
        
        // Apply rotor transformation: x' = R x R†
        rotor.apply(x, &self.algebra)
    }

    fn verify_invariance(&self, g: &GroupElement<P>) -> bool {
        // Check that the action preserves:
        // 1. Coherence inner product
        // 2. Grade structure
        // 3. Minimal embeddings
        
        // For identity, this is always true
        if g.is_identity() {
            return true;
        }
        
        // More complex verification would go here
        true
    }
}
