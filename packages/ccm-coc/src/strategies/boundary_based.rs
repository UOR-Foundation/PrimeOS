//! Boundary-based decomposition strategy

use crate::{
    COC, CoherentObject, CocError, Result,
    strategies::DecompositionStrategy,
    boundary::BoundaryDetector,
    window::WindowExtractor,
};
use ccm_core::Float;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{boxed::Box, vec::Vec};
#[cfg(feature = "std")]
use std::{boxed::Box, vec::Vec};

/// Decomposition based on boundary detection
pub struct BoundaryBasedDecomposition<P: Float> {
    /// Boundary detectors to use
    boundary_detectors: Vec<Box<dyn BoundaryDetector<P>>>,
    /// Window extractor
    window_extractor: Box<dyn WindowExtractor<P>>,
    /// Minimum confidence threshold
    min_confidence: f64,
}

impl<P: Float> BoundaryBasedDecomposition<P> {
    /// Create a new boundary-based decomposition strategy
    pub fn new(
        boundary_detectors: Vec<Box<dyn BoundaryDetector<P>>>,
        window_extractor: Box<dyn WindowExtractor<P>>,
        min_confidence: f64,
    ) -> Self {
        Self {
            boundary_detectors,
            window_extractor,
            min_confidence,
        }
    }
}

impl<P: Float> DecompositionStrategy<P> for BoundaryBasedDecomposition<P> {
    fn name(&self) -> &str {
        "BoundaryBasedDecomposition"
    }
    
    fn decompose(
        &self,
        object: &dyn CoherentObject<P>,
        coc: &COC<P>,
    ) -> Result<Vec<Box<dyn CoherentObject<P>>>> {
        // TODO: Implement actual boundary-based decomposition
        Err(CocError::NotImplemented("Boundary-based decomposition".into()))
    }
    
    fn priority(&self) -> u32 {
        100 // High priority
    }
}