//! Window extraction system

use crate::boundary::Boundary;
use ccm::{StandardCCM, CliffordElement};
use ccm_core::Float;
use ccm_symmetry::SymmetryType;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{vec::Vec, string::String, collections::BTreeMap};
#[cfg(feature = "std")]
use std::{vec::Vec, string::String, collections::HashMap};

#[cfg(not(feature = "std"))]
use hashbrown::HashMap;

pub mod extractors;

/// Represents a window of sections that might form a coherent part
#[derive(Clone, Debug)]
pub struct Window<P: Float> {
    /// Starting index
    pub start: usize,
    /// Number of sections
    pub length: usize,
    /// The sections in this window
    pub sections: Vec<CliffordElement<P>>,
    /// Confidence that this is a coherent unit
    pub coherence_score: P,
    /// Additional analysis results
    pub analysis: WindowAnalysis<P>,
}

/// Analysis results for a window
#[derive(Clone, Debug)]
pub struct WindowAnalysis<P: Float> {
    /// Total resonance of the window
    pub resonance: P,
    /// Dominant grades in the window
    pub grade_signature: Vec<usize>,
    /// Symmetry properties
    pub symmetries: Vec<SymmetryType>,
    /// Conservation properties
    #[cfg(feature = "std")]
    pub conserved_quantities: HashMap<String, P>,
    #[cfg(not(feature = "std"))]
    pub conserved_quantities: HashMap<String, P>,
}

impl<P: Float> WindowAnalysis<P> {
    /// Create a new empty analysis
    pub fn new() -> Self {
        Self {
            resonance: P::zero(),
            grade_signature: Vec::new(),
            symmetries: Vec::new(),
            conserved_quantities: HashMap::new(),
        }
    }
}

impl<P: Float> Default for WindowAnalysis<P> {
    fn default() -> Self {
        Self::new()
    }
}

/// Strategy for extracting windows from sections
pub trait WindowExtractor<P: Float>: Send + Sync {
    /// Extract candidate windows from sections given boundaries
    fn extract_windows(
        &self,
        sections: &[CliffordElement<P>],
        boundaries: &[Boundary],
        ccm: &StandardCCM<P>,
    ) -> Vec<Window<P>>;
    
    /// Get the name of this extractor
    fn name(&self) -> &str;
}