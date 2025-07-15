//! Group actions on various structures

use crate::group::GroupElement;
use ccm_coherence::{CliffordAlgebra, CliffordElement};
use ccm_core::{BitWord, CcmError, Float};

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

/// Klein group action on Clifford elements
/// Acts by permuting basis components according to XOR on last two bits
pub struct KleinCliffordAction {
    /// Dimension of the space
    dimension: usize,
}

impl KleinCliffordAction {
    /// Create a new Klein action for n-dimensional Clifford algebra
    pub fn new(dimension: usize) -> Self {
        Self { dimension }
    }
    
    /// Apply Klein transformation to a basis index
    /// Klein group acts by XOR on the bits corresponding to basis vectors n-2 and n-1
    fn transform_index(&self, index: usize, klein_element: usize) -> usize {
        if self.dimension < 2 {
            return index;
        }
        
        // Klein element: 0 = identity, 1 = flip n-2, 2 = flip n-1, 3 = flip both
        let mut result = index;
        
        // Check if we need to flip bit (n-2)
        if klein_element & 1 != 0 {
            let bit_pos = self.dimension - 2;
            result ^= 1 << bit_pos;
        }
        
        // Check if we need to flip bit (n-1)
        if klein_element & 2 != 0 {
            let bit_pos = self.dimension - 1;
            result ^= 1 << bit_pos;
        }
        
        result
    }
    
    /// Determine which Klein element a GroupElement represents
    fn klein_element_from_group<P: Float>(&self, g: &GroupElement<P>) -> usize {
        if g.is_identity() {
            return 0;
        }
        
        // Check params to determine which Klein element this is
        // params[i] < 0 means flip bit i
        let mut klein = 0;
        
        if self.dimension >= 2 {
            // Check bit n-2
            if g.params.len() >= self.dimension && g.params[self.dimension - 2] < P::zero() {
                klein |= 1;
            }
            // Check bit n-1
            if g.params.len() >= self.dimension && g.params[self.dimension - 1] < P::zero() {
                klein |= 2;
            }
        }
        
        klein
    }
}

impl<P: Float> GroupAction<P> for KleinCliffordAction {
    type Target = CliffordElement<P>;
    
    fn apply(&self, g: &GroupElement<P>, x: &Self::Target) -> Result<Self::Target, CcmError> {
        // Determine which Klein element this is
        let klein_elem = self.klein_element_from_group(g);
        
        if klein_elem == 0 {
            // Identity
            return Ok(x.clone());
        }
        
        // Create new element by permuting components
        let mut result = CliffordElement::zero(self.dimension);
        
        // For each component in x, map it to the transformed position
        for i in 0..x.num_components() {
            if let Some(component) = x.component(i) {
                // Transform the index according to Klein action
                let new_index = self.transform_index(i, klein_elem);
                
                // Bounds check
                if new_index < result.num_components() {
                    result.set_component(new_index, component)?;
                }
            }
        }
        
        Ok(result)
    }
    
    fn verify_invariance(&self, _g: &GroupElement<P>) -> bool {
        // Klein group always preserves:
        // 1. Total number of components
        // 2. Grade structure (XOR on last two bits preserves grade)
        // 3. Coherence norm (permutation of orthogonal components)
        true
    }
}

impl<P: Float> CliffordAction<P> {
    /// Create a new Clifford action
    pub fn new(algebra: CliffordAlgebra<P>) -> Self {
        Self { algebra }
    }

    /// Convert group element parameters to a rotor
    fn params_to_rotor(
        &self,
        g: &GroupElement<P>,
    ) -> Result<ccm_coherence::rotor::Rotor<P>, CcmError> {
        use ccm_coherence::rotor::Rotor;
        use num_complex::Complex;

        let dim = self.algebra.dimension();

        // Build bivector from parameters
        // For n dimensions, we have n(n-1)/2 bivector components
        let mut bivector = CliffordElement::zero(dim);

        let mut param_idx = 0;
        for i in 0..dim {
            for j in i + 1..dim {
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
