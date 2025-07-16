//! # CCM-COC: Coherent Object Composition Framework
//!
//! This crate provides a generic framework for composing and decomposing mathematical objects
//! using Coherence-Centric Mathematics (CCM). It bridges the gap between CCM's fundamental
//! operations and domain-specific applications.
//!
//! ## Overview
//!
//! COC provides:
//! - Generic composition/decomposition algorithms
//! - Boundary detection strategies
//! - Window extraction and analysis
//! - Conservation law verification
//! - Extensible framework for new domains
//!
//! ## Example
//!
//! ```rust,no_run
//! use ccm_coc::{COC, CoherentObject, Composable};
//! use ccm::{StandardCCM, CliffordElement};
//! 
//! // Define your domain object
//! #[derive(Clone)]
//! struct MyObject {
//!     // ... domain-specific fields
//! }
//!
//! impl<P: Float> CoherentObject<P> for MyObject {
//!     // ... implement required methods
//! }
//!
//! impl<P: Float> Composable<P> for MyObject {
//!     // ... implement composition/decomposition
//! }
//!
//! // Use COC for decomposition
//! let coc = COC::<f64>::new(8)?;
//! let object = MyObject { /* ... */ };
//! let parts = object.decompose(&coc)?;
//! # Ok::<(), ccm_coc::CocError>(())
//! ```

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]
#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![allow(clippy::module_name_repetitions)]

#[cfg(feature = "alloc")]
extern crate alloc;

// Core traits and types
mod coherent_object;
mod composable;
mod coc;
mod config;
mod error;

// Detection and extraction systems
mod boundary;
mod window;

// Conservation laws
mod conservation;

// Decomposition strategies
mod strategies;

// Public exports - Core traits
pub use coherent_object::{CoherentObject, ObjectMetadata};
pub use composable::Composable;
pub use coc::COC;
pub use config::CocConfig;
pub use error::{CocError, Result};

// Public exports - Boundary detection
pub use boundary::{
    Boundary, BoundaryDetector, BoundaryMetadata, BoundaryType,
    detectors::{
        ConservationBoundaryDetector, SymmetryBreakDetector, WeakCouplingDetector,
    },
};

// Public exports - Window extraction  
pub use window::{
    Window, WindowAnalysis, WindowExtractor,
    extractors::{
        FixedSizeExtractor, OverlappingExtractor, VariableSizeExtractor,
    },
};

// Public exports - Conservation laws
pub use conservation::{
    ConservationLaw, ConservationLawId, ConservationResult,
    laws::{
        CoherenceConservation, CoherenceMode, CycleConservation, ResonanceConservation,
    },
};

// Public exports - Decomposition strategies
pub use strategies::{
    DecompositionStrategy,
    boundary_based::BoundaryBasedDecomposition,
    exhaustive::ExhaustiveDecomposition,
    resonance_guided::ResonanceGuidedDecomposition,
    symmetry_based::SymmetryBasedDecomposition,
};

// Re-export commonly used types from dependencies
pub use ccm::{StandardCCM, CliffordElement};
pub use ccm_core::{BitWord, Float};
pub use ccm_symmetry::SymmetryType;

// Note: Individual modules handle their own imports

/// Prelude module for convenient imports
pub mod prelude {
    pub use crate::{
        CoherentObject, Composable, COC, CocConfig, CocError, Result,
        ConservationLaw, ConservationLawId,
        DecompositionStrategy,
        BoundaryDetector, WindowExtractor,
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_module_structure() {
        // Verify that all modules are accessible
        let _ = CocConfig::default();
    }
}