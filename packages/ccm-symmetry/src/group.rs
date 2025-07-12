//! Symmetry group structure

use crate::GroupElement;
use ccm_core::{CcmError, Float};

/// Symmetry group generator and operations
pub struct GroupGenerator<P: Float> {
    dimension: usize,
    _phantom: core::marker::PhantomData<P>,
}

impl<P: Float> GroupGenerator<P> {
    pub fn new(dimension: usize) -> Self {
        Self {
            dimension,
            _phantom: core::marker::PhantomData,
        }
    }

    pub fn identity(&self) -> GroupElement<P> {
        GroupElement {
            params: alloc::vec![P::one(); self.dimension],
        }
    }
}
