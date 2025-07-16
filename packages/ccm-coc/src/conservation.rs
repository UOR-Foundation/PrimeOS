//! Conservation laws framework

use crate::{COC, CoherentObject, CocError, Result};
use ccm_core::Float;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{boxed::Box, string::String, vec::Vec};
#[cfg(feature = "std")]
use std::{boxed::Box, string::String, vec::Vec};

pub mod laws;

/// Identifier for conservation laws
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConservationLawId(pub String);

/// Result of conservation law verification
#[derive(Clone, Debug)]
pub struct ConservationResult {
    /// Whether the law is satisfied
    pub satisfied: bool,
    /// Conserved quantity for the whole object
    pub whole_quantity: f64,
    /// Sum of conserved quantities for parts
    pub parts_sum: f64,
    /// Relative error
    pub relative_error: f64,
    /// Additional details
    pub details: String,
}

/// Represents a mathematical conservation principle
pub trait ConservationLaw<P: Float>: Send + Sync {
    /// Unique identifier for this law
    fn id(&self) -> ConservationLawId;
    
    /// Human-readable name
    fn name(&self) -> &str;
    
    /// Check if the law is satisfied
    fn verify(
        &self,
        whole: &dyn CoherentObject<P>,
        parts: &[Box<dyn CoherentObject<P>>],
        coc: &COC<P>,
    ) -> Result<ConservationResult>;
    
    /// Get the conserved quantity value
    fn compute_quantity(
        &self,
        object: &dyn CoherentObject<P>,
        coc: &COC<P>,
    ) -> Result<P>;
}