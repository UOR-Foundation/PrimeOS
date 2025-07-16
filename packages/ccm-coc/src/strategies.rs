//! Decomposition strategies

use crate::{COC, CoherentObject, CocError, Result};
use ccm_core::Float;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{boxed::Box, vec::Vec};
#[cfg(feature = "std")]
use std::{boxed::Box, vec::Vec};

pub mod boundary_based;
pub mod exhaustive;
pub mod resonance_guided;
pub mod symmetry_based;

/// Strategy for decomposing objects
pub trait DecompositionStrategy<P: Float>: Send + Sync {
    /// Name of the strategy
    fn name(&self) -> &str;
    
    /// Attempt decomposition using this strategy
    fn decompose(
        &self,
        object: &dyn CoherentObject<P>,
        coc: &COC<P>,
    ) -> Result<Vec<Box<dyn CoherentObject<P>>>>;
    
    /// Priority (higher = try first)
    fn priority(&self) -> u32;
}