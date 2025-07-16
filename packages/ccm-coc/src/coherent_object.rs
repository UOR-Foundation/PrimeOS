//! Coherent object trait and metadata

use crate::{CocError, Result};
use ccm::{StandardCCM, CliffordElement};
use ccm_core::Float;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{string::String, vec::Vec};
#[cfg(feature = "std")]  
use std::{string::String, vec::Vec};

/// Metadata for coherent objects
#[derive(Clone, Debug, PartialEq)]
pub struct ObjectMetadata {
    /// Type identifier for the object
    pub type_id: String,
    /// Dimension of the object's representation
    pub dimension: usize,
    /// Conservation properties this object should satisfy
    pub conservation_laws: Vec<String>,
}

/// Represents any mathematical object that can be coherently composed
pub trait CoherentObject<P: Float>: Clone {
    /// Convert to CCM sections for analysis
    fn to_sections(&self, ccm: &StandardCCM<P>) -> Result<Vec<CliffordElement<P>>>;
    
    /// Reconstruct from CCM sections
    fn from_sections(sections: &[CliffordElement<P>], ccm: &StandardCCM<P>) -> Result<Self>
    where
        Self: Sized;
    
    /// Get the coherent norm of this object
    fn coherent_norm(&self, ccm: &StandardCCM<P>) -> P;
    
    /// Check if this object is atomic (cannot be decomposed further)
    fn is_atomic(&self) -> bool;
    
    /// Get metadata about this object
    fn metadata(&self) -> ObjectMetadata;
}