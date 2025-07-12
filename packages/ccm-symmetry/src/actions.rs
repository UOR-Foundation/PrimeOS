//! Group actions on various structures

use crate::{GroupAction, GroupElement};
use ccm_core::{BitWord, Float};

/// Action on BitWords
pub struct BitWordAction;

impl<P: Float> GroupAction<P> for BitWordAction {
    type Target = BitWord;

    fn apply(&self, _g: &GroupElement<P>, target: &Self::Target) -> Self::Target {
        // Placeholder: return unchanged for now
        target.clone()
    }

    fn verify_invariance(&self, _g: &GroupElement<P>) -> bool {
        true
    }
}
