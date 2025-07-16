//! Overlapping window extractor

use crate::{
    boundary::Boundary,
    window::{Window, WindowExtractor, WindowAnalysis},
};
use ccm::{StandardCCM, CliffordElement};
use ccm_core::Float;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

/// Extracts overlapping windows
pub struct OverlappingExtractor {
    /// Window size
    window_size: usize,
    /// Step size (overlap = window_size - step_size)
    step_size: usize,
}

impl OverlappingExtractor {
    /// Create a new overlapping extractor
    pub fn new(window_size: usize, step_size: usize) -> Self {
        Self { window_size, step_size }
    }
}

impl<P: Float> WindowExtractor<P> for OverlappingExtractor {
    fn extract_windows(
        &self,
        sections: &[CliffordElement<P>],
        boundaries: &[Boundary],
        ccm: &StandardCCM<P>,
    ) -> Vec<Window<P>> {
        let mut windows = Vec::new();
        
        // TODO: Implement actual overlapping window extraction
        // For now, return empty
        windows
    }
    
    fn name(&self) -> &str {
        "OverlappingExtractor"
    }
}