//! Orbit analysis and computation

use crate::{GroupAction, GroupElement};
use ccm_core::Float;

/// Orbit of an element under group action
pub struct Orbit<P: Float, T> {
    pub representative: T,
    pub elements: alloc::vec::Vec<T>,
    _phantom: core::marker::PhantomData<P>,
}

impl<P: Float, T: Clone> Orbit<P, T> {
    pub fn new(representative: T) -> Self {
        Self {
            representative: representative.clone(),
            elements: alloc::vec![representative],
            _phantom: core::marker::PhantomData,
        }
    }
}
