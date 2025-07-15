//! Invariant computation for group actions
//! 
//! This module provides methods to compute invariants under group actions.

use num_traits::{Float, FromPrimitive};
use crate::group::SymmetryGroup;
use ccm_coherence::{CliffordElement, CoherentDecomposition};

impl<P: Float> SymmetryGroup<P> {
    /// Compute invariants of a Clifford element under group action
    /// 
    /// Invariants are quantities preserved by all group elements
    pub fn compute_invariants(&self, element: &CliffordElement<P>) -> Vec<P> 
    where
        P: FromPrimitive,
    {
        let mut invariants = Vec::new();
        
        // Universal invariant: coherence norm
        invariants.push(element.coherence_norm());
        
        // Grade-based invariants
        let grades = element.grade_decompose();
        for gc in &grades {
            invariants.push(P::from_f64(gc.coherence_norm).unwrap_or(P::zero()));
        }
        
        // For Klein group: resonance-like invariants
        if self.cached_order == Some(4) {
            // Klein group preserves certain grade combinations
            let even_grade_norm = grades.iter()
                .filter(|gc| gc.grade % 2 == 0usize)
                .map(|gc| gc.coherence_norm)
                .sum::<f64>();
            invariants.push(P::from_f64(even_grade_norm).unwrap_or(P::zero()));
        }
        
        invariants
    }
}