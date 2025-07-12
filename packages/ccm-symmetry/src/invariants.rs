//! Invariant quantities under group action

use ccm_core::Float;

/// Trait for invariant quantities
pub trait Invariant<P: Float> {
    /// Check if this quantity is invariant
    fn is_invariant(&self) -> bool;

    /// Compute the invariant value
    fn value(&self) -> P;
}
