//! Core types for CCM-Factor

use ccm_coherence::CliffordElement;
use ccm_core::BitWord;
use num_traits::Float;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Represents an alignment window in the channel sequence
#[derive(Debug, Clone)]
pub struct AlignmentWindow<P: Float> {
    /// Starting index in the channel sequence
    pub start: usize,

    /// Length of the window
    pub length: usize,

    /// Clifford sections in this window
    pub sections: Vec<CliffordElement<P>>,

    /// Factor hint derived from this window
    pub factor_hint: FactorHint<P>,
}

/// Hint about potential factors from an alignment window
#[derive(Debug, Clone)]
pub struct FactorHint<P: Float> {
    /// Confidence score for this hint (0.0 to 1.0)
    pub confidence: P,

    /// Orbit representatives from symmetry analysis
    pub orbit_representatives: Vec<BitWord>,

    /// Grade decomposition of window sections
    pub grade_decomposition: Vec<Vec<CliffordElement<P>>>,

    /// Resonance signature of the window
    pub resonance_signature: P,

    /// Detected symmetry type
    pub symmetry_type: SymmetryType,
}

/// Types of symmetry detected in alignment windows
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymmetryType {
    /// No special symmetry
    None,

    /// Klein group symmetry
    Klein,

    /// Page-aligned symmetry
    PageAligned,

    /// Full resonance conservation
    ResonanceConserving,

    /// Combined symmetries
    Combined,
}

/// Configuration for CCM factorization
#[derive(Debug, Clone)]
pub struct FactorConfig {
    /// Base channel size in bits
    pub channel_size: usize,

    /// Whether to use adaptive channel sizing
    pub adaptive_channels: bool,

    /// Maximum window size to consider
    pub max_window_size: usize,

    /// Minimum confidence threshold for factor hints
    pub min_confidence: f64,

    /// Enable parallel processing
    pub parallel: bool,

    /// Maximum attempts before giving up
    pub max_attempts: usize,

    /// Tolerance for resonance matching
    pub resonance_tolerance: f64,
}

impl Default for FactorConfig {
    fn default() -> Self {
        Self {
            channel_size: 8,
            adaptive_channels: true,
            max_window_size: 16,
            min_confidence: 0.7,
            parallel: cfg!(feature = "parallel"),
            max_attempts: 1000,
            resonance_tolerance: 1e-10,
        }
    }
}
