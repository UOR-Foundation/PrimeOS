//! Composable trait for composition and decomposition

use crate::{COC, CoherentObject, CocError, Result};
use ccm_core::Float;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

/// Defines how objects can be composed and decomposed
pub trait Composable<P: Float>: CoherentObject<P> {
    /// Compose multiple objects into one
    fn compose(parts: &[Self], coc: &COC<P>) -> Result<Self>;
    
    /// Attempt to decompose into constituent parts
    fn decompose(&self, coc: &COC<P>) -> Result<Vec<Self>>;
    
    /// Check if a decomposition is valid
    fn is_valid_decomposition(&self, parts: &[Self], coc: &COC<P>) -> bool;
}