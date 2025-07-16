//! Boundary detection system

use ccm::{StandardCCM, CliffordElement};
use ccm_core::Float;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{vec::Vec, string::String};
#[cfg(feature = "std")]
use std::{vec::Vec, string::String};

pub mod detectors;

/// Represents a boundary between composed objects
#[derive(Clone, Debug)]
pub struct Boundary {
    /// Position in the section array
    pub position: usize,
    /// Confidence score (0.0 to 1.0)
    pub confidence: f64,
    /// Type of boundary detected
    pub boundary_type: BoundaryType,
    /// Additional metadata
    pub metadata: BoundaryMetadata,
}

/// Types of boundaries that can be detected
#[derive(Clone, Debug)]
pub enum BoundaryType {
    /// Low coherence coupling between sections
    WeakCoupling,
    /// Symmetry break point
    SymmetryBreak,
    /// Conservation law boundary
    ConservationBoundary,
    /// Page-aligned boundary (256-period)
    PageAligned,
    /// Klein group transition
    KleinTransition,
    /// Combined indicators
    Multiple(Vec<BoundaryType>),
}

/// Additional metadata for boundaries
#[derive(Clone, Debug, Default)]
pub struct BoundaryMetadata {
    /// Coupling strength if applicable
    pub coupling_strength: Option<f64>,
    /// Symmetry group elements if applicable
    pub symmetry_info: Option<String>,
    /// Conservation quantity changes
    pub conservation_delta: Option<f64>,
    /// Page number if page-aligned
    pub page_number: Option<usize>,
    /// Klein group transition details
    pub klein_info: Option<String>,
}

/// Strategy for detecting boundaries
pub trait BoundaryDetector<P: Float>: Send + Sync {
    /// Detect boundaries in a sequence of sections
    fn detect_boundaries(
        &self,
        sections: &[CliffordElement<P>],
        ccm: &StandardCCM<P>,
    ) -> Vec<Boundary>;
    
    /// Get the name of this detector
    fn name(&self) -> &str;
}