//! Coherence metric and inner product

use ccm_core::Float;

/// Coherence inner product implementation
pub fn coherence_inner_product<P: Float>(a: &[P], b: &[P]) -> P {
    // Placeholder implementation
    a.iter()
        .zip(b.iter())
        .map(|(x, y)| *x * *y)
        .fold(P::zero(), |acc, x| acc + x)
}
