//! Clifford algebra implementation

use ccm_core::{CcmError, Float};

/// Clifford algebra basis and operations
pub struct CliffordBasis<P: Float> {
    dimension: usize,
    _phantom: core::marker::PhantomData<P>,
}

impl<P: Float> CliffordBasis<P> {
    pub fn new(dimension: usize) -> Self {
        Self {
            dimension,
            _phantom: core::marker::PhantomData,
        }
    }
}
