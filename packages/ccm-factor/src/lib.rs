//! # CCM-Factor: Integer Factorization using Coherence-Centric Mathematics
//!
//! This crate provides integer factorization algorithms based on CCM principles,
//! using coherence metrics, resonance algebra, and symmetry groups to find factors.
//!
//! ## Key Features
//!
//! - Arbitrary precision integer factorization
//! - Channel-based embedding with configurable sizes
//! - Coherence-based alignment detection
//! - Symmetry exploitation for optimization
//! - Conservation law verification
//!
//! ## Example
//!
//! ```rust,no_run
//! use ccm_factor::CCMFactor;
//! use num_bigint::BigUint;
//!
//! let factor = CCMFactor::<f64>::new(8)?;
//! let n = BigUint::from(15u32);
//! let factors = factor.factor(&n)?;
//! assert_eq!(factors, vec![BigUint::from(3u32), BigUint::from(5u32)]);
//! # Ok::<(), ccm_factor::FactorError>(())
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

mod alignment;
mod cache;
mod error;
mod factor;
mod recovery;
mod symmetry;
mod types;
mod verification;

pub use error::{FactorError, Result};
pub use factor::CCMFactor;
pub use types::{AlignmentWindow, FactorConfig, FactorHint};

// Symmetry analysis exports
pub use symmetry::{
    compute_orbit_stabilizer, detect_continuous_symmetries, ContinuousSymmetry, ConservedQuantity,
    Orbit, StabilizerSubgroup,
};

// Re-export commonly used types
pub use num_bigint::{BigInt, BigUint};

#[cfg(feature = "parallel")]
pub use factor::ParallelCCMFactor;

#[cfg(test)]
mod tests;
