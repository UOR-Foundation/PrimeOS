//! Polynomial invariant theory
//! 
//! This module implements polynomial rings, Gröbner basis computation,
//! and invariant detection for group actions.

mod monomial;
mod polynomial;
mod groebner;
mod reynolds;
mod invariant_ring;

pub use monomial::{Monomial, MonomialOrdering};
pub use polynomial::{Polynomial, PolynomialRing};
pub use groebner::{GroebnerBasis, buchberger_algorithm};
pub use reynolds::ReynoldsOperator;
pub use invariant_ring::{InvariantRing, PolynomialInvariant};

#[cfg(test)]
mod tests;