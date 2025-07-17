//! Multivariate polynomials over a field

use super::monomial::{Monomial, MonomialOrdering};
use ccm_core::Float;
use core::ops::{Add, Mul, Sub};

#[cfg(feature = "alloc")]
use alloc::{vec, vec::Vec};

#[cfg(feature = "std")]
use std::collections::BTreeMap;
#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::collections::BTreeMap;

/// A multivariate polynomial
#[derive(Debug, Clone, PartialEq)]
pub struct Polynomial<P: Float> {
    /// Terms stored as (monomial, coefficient) pairs
    pub terms: BTreeMap<Monomial, P>,
    /// Number of variables
    pub num_vars: usize,
}

impl<P: Float> Polynomial<P> {
    /// Create a new polynomial
    pub fn new(num_vars: usize) -> Self {
        Self {
            terms: BTreeMap::new(),
            num_vars,
        }
    }
    
    /// Create the zero polynomial
    pub fn zero(num_vars: usize) -> Self {
        Self::new(num_vars)
    }
    
    /// Create the constant polynomial
    pub fn constant(value: P, num_vars: usize) -> Self {
        let mut poly = Self::new(num_vars);
        if value != P::zero() {
            poly.terms.insert(Monomial::one(num_vars), value);
        }
        poly
    }
    
    /// Create a polynomial from a single variable
    pub fn variable(var_index: usize, num_vars: usize) -> Self {
        assert!(var_index < num_vars);
        let mut exponents = vec![0; num_vars];
        exponents[var_index] = 1;
        
        let mut poly = Self::new(num_vars);
        poly.terms.insert(Monomial::new(exponents), P::one());
        poly
    }
    
    /// Add a term to the polynomial
    pub fn add_term(&mut self, monomial: Monomial, coefficient: P) {
        assert_eq!(monomial.exponents.len(), self.num_vars);
        if coefficient != P::zero() {
            match self.terms.entry(monomial) {
                #[cfg(feature = "std")]
                std::collections::btree_map::Entry::Occupied(mut e) => {
                    let val = e.get_mut();
                    *val = *val + coefficient;
                    if *val == P::zero() {
                        e.remove();
                    }
                }
                #[cfg(feature = "std")]
                std::collections::btree_map::Entry::Vacant(e) => {
                    e.insert(coefficient);
                }
                #[cfg(all(feature = "alloc", not(feature = "std")))]
                alloc::collections::btree_map::Entry::Occupied(mut e) => {
                    let val = e.get_mut();
                    *val = *val + coefficient;
                    if *val == P::zero() {
                        e.remove();
                    }
                }
                #[cfg(all(feature = "alloc", not(feature = "std")))]
                alloc::collections::btree_map::Entry::Vacant(e) => {
                    e.insert(coefficient);
                }
            }
        }
    }
    
    /// Get the degree of the polynomial
    pub fn degree(&self) -> usize {
        self.terms
            .keys()
            .map(|m| m.degree())
            .max()
            .unwrap_or(0)
    }
    
    /// Get the leading monomial with respect to an ordering
    pub fn leading_monomial(&self, ordering: MonomialOrdering) -> Option<&Monomial> {
        self.terms
            .keys()
            .max_by(|a, b| ordering.compare(a, b))
    }
    
    /// Get the leading coefficient
    pub fn leading_coefficient(&self, ordering: MonomialOrdering) -> Option<P> {
        self.leading_monomial(ordering)
            .and_then(|m| self.terms.get(m).copied())
    }
    
    /// Get the leading term (monomial and coefficient)
    pub fn leading_term(&self, ordering: MonomialOrdering) -> Option<(Monomial, P)> {
        self.leading_monomial(ordering)
            .and_then(|m| self.terms.get(m).map(|c| (m.clone(), *c)))
    }
    
    /// Check if polynomial is zero
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }
    
    /// Evaluate the polynomial at a point
    pub fn evaluate(&self, point: &[P]) -> P {
        assert_eq!(point.len(), self.num_vars);
        self.terms
            .iter()
            .map(|(monomial, coeff)| *coeff * monomial.evaluate(point))
            .fold(P::zero(), |acc, val| acc + val)
    }
    
    /// Apply a variable permutation to the polynomial
    pub fn permute_variables(&self, permutation: &[usize]) -> Self {
        assert_eq!(permutation.len(), self.num_vars);
        
        let mut result = Self::new(self.num_vars);
        for (monomial, coeff) in &self.terms {
            let mut new_exponents = vec![0; self.num_vars];
            for (i, &j) in permutation.iter().enumerate() {
                new_exponents[j] = monomial.exponents[i];
            }
            result.add_term(Monomial::new(new_exponents), *coeff);
        }
        result
    }
    
    /// Multiply by a scalar
    pub fn scalar_multiply(&self, scalar: P) -> Self {
        let mut result = Self::new(self.num_vars);
        for (monomial, coeff) in &self.terms {
            result.add_term(monomial.clone(), *coeff * scalar);
        }
        result
    }
    
    /// Polynomial division (returns quotient and remainder)
    pub fn divide(&self, divisor: &Self, ordering: MonomialOrdering) -> (Self, Self) {
        if divisor.is_zero() {
            panic!("Division by zero polynomial");
        }
        
        let mut quotient = Self::new(self.num_vars);
        let mut remainder = self.clone();
        
        while !remainder.is_zero() {
            if let (Some((lt_rem_mon, lt_rem_coeff)), Some((lt_div_mon, lt_div_coeff))) = 
                (remainder.leading_term(ordering), divisor.leading_term(ordering)) {
                
                if let Some(mono_quot) = lt_rem_mon.divide(&lt_div_mon) {
                    let coeff_quot = lt_rem_coeff / lt_div_coeff;
                    quotient.add_term(mono_quot.clone(), coeff_quot);
                    
                    // Subtract lt_quot * divisor from remainder
                    for (div_mono, div_coeff) in &divisor.terms {
                        let prod_mono = mono_quot.multiply(div_mono);
                        let prod_coeff = coeff_quot * *div_coeff;
                        remainder.add_term(prod_mono, -prod_coeff);
                    }
                } else {
                    // Leading term of divisor doesn't divide leading term of remainder
                    break;
                }
            } else {
                break;
            }
        }
        
        (quotient, remainder)
    }
}

impl<P: Float> Add for Polynomial<P> {
    type Output = Self;
    
    fn add(mut self, other: Self) -> Self {
        assert_eq!(self.num_vars, other.num_vars);
        for (monomial, coeff) in other.terms {
            self.add_term(monomial, coeff);
        }
        self
    }
}

impl<P: Float> Sub for Polynomial<P> {
    type Output = Self;
    
    fn sub(mut self, other: Self) -> Self {
        assert_eq!(self.num_vars, other.num_vars);
        for (monomial, coeff) in other.terms {
            self.add_term(monomial, -coeff);
        }
        self
    }
}

impl<P: Float> Mul for Polynomial<P> {
    type Output = Self;
    
    fn mul(self, other: Self) -> Self {
        assert_eq!(self.num_vars, other.num_vars);
        let mut result = Self::new(self.num_vars);
        
        for (mono1, coeff1) in &self.terms {
            for (mono2, coeff2) in &other.terms {
                let prod_mono = mono1.multiply(mono2);
                let prod_coeff = *coeff1 * *coeff2;
                result.add_term(prod_mono, prod_coeff);
            }
        }
        
        result
    }
}

/// Polynomial ring structure
pub struct PolynomialRing<P: Float> {
    /// Number of variables
    pub num_vars: usize,
    /// Variable names (optional)
    pub var_names: Option<Vec<&'static str>>,
    /// Phantom data for type parameter
    _phantom: core::marker::PhantomData<P>,
}

impl<P: Float> PolynomialRing<P> {
    /// Create a new polynomial ring
    pub fn new(num_vars: usize) -> Self {
        Self {
            num_vars,
            var_names: None,
            _phantom: core::marker::PhantomData,
        }
    }
    
    /// Create with variable names
    pub fn with_names(num_vars: usize, names: Vec<&'static str>) -> Self {
        assert_eq!(names.len(), num_vars);
        Self {
            num_vars,
            var_names: Some(names),
            _phantom: core::marker::PhantomData,
        }
    }
    
    /// Get the i-th variable as a polynomial
    pub fn variable(&self, i: usize) -> Polynomial<P> {
        Polynomial::variable(i, self.num_vars)
    }
    
    /// Create the zero polynomial
    pub fn zero(&self) -> Polynomial<P> {
        Polynomial::zero(self.num_vars)
    }
    
    /// Create the one polynomial
    pub fn one(&self) -> Polynomial<P> {
        Polynomial::constant(P::one(), self.num_vars)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_polynomial_arithmetic() {
        // Create ring R[x,y]
        let ring = PolynomialRing::<f64>::new(2);
        
        // x + y
        let p1 = ring.variable(0) + ring.variable(1);
        
        // x - y
        let p2 = ring.variable(0) - ring.variable(1);
        
        // (x + y)(x - y) = x² - y²
        let product = p1 * p2;
        
        // Check result
        assert_eq!(product.evaluate(&[2.0, 1.0]), 3.0); // 2² - 1² = 3
        assert_eq!(product.evaluate(&[3.0, 2.0]), 5.0); // 3² - 2² = 5
    }
    
    #[test]
    fn test_polynomial_division() {
        let ring = PolynomialRing::<f64>::new(2);
        let ordering = MonomialOrdering::Lex;
        
        // Dividend: x² + 2xy + y²
        let mut dividend = ring.variable(0).clone();
        dividend = dividend * ring.variable(0); // x²
        let mut term2 = ring.variable(0) * ring.variable(1);
        term2 = term2.scalar_multiply(2.0); // 2xy
        let mut term3 = ring.variable(1).clone();
        term3 = term3 * ring.variable(1); // y²
        dividend = dividend + term2 + term3;
        
        // Divisor: x + y
        let divisor = ring.variable(0) + ring.variable(1);
        
        // Divide
        let (quotient, remainder) = dividend.divide(&divisor, ordering);
        
        // Should get quotient = x + y, remainder = 0
        assert!(remainder.is_zero());
        assert_eq!(quotient.evaluate(&[2.0, 3.0]), 5.0);
    }
}