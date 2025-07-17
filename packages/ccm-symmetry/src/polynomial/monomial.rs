//! Monomials and monomial orderings

use ccm_core::Float;
use core::cmp::Ordering;

#[cfg(feature = "alloc")]
use alloc::{vec, vec::Vec};

/// A monomial in multiple variables
/// 
/// Represents x₁^{a₁} × x₂^{a₂} × ... × xₙ^{aₙ}
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Monomial {
    /// Exponents for each variable
    pub exponents: Vec<usize>,
}

impl Monomial {
    /// Create a new monomial with given exponents
    pub fn new(exponents: Vec<usize>) -> Self {
        Self { exponents }
    }
    
    /// Create the constant monomial (all exponents zero)
    pub fn one(num_vars: usize) -> Self {
        Self {
            exponents: vec![0; num_vars],
        }
    }
    
    /// Total degree of the monomial
    pub fn degree(&self) -> usize {
        self.exponents.iter().sum()
    }
    
    /// Multiply two monomials
    pub fn multiply(&self, other: &Self) -> Self {
        assert_eq!(self.exponents.len(), other.exponents.len());
        let exponents = self.exponents
            .iter()
            .zip(&other.exponents)
            .map(|(a, b)| a + b)
            .collect();
        Self { exponents }
    }
    
    /// Check if this monomial divides another
    pub fn divides(&self, other: &Self) -> bool {
        assert_eq!(self.exponents.len(), other.exponents.len());
        self.exponents
            .iter()
            .zip(&other.exponents)
            .all(|(a, b)| a <= b)
    }
    
    /// Divide monomials (assumes divisibility)
    pub fn divide(&self, divisor: &Self) -> Option<Self> {
        if !divisor.divides(self) {
            return None;
        }
        let exponents = self.exponents
            .iter()
            .zip(&divisor.exponents)
            .map(|(a, b)| a - b)
            .collect();
        Some(Self { exponents })
    }
    
    /// Least common multiple of two monomials
    pub fn lcm(&self, other: &Self) -> Self {
        assert_eq!(self.exponents.len(), other.exponents.len());
        let exponents = self.exponents
            .iter()
            .zip(&other.exponents)
            .map(|(a, b)| *a.max(b))
            .collect();
        Self { exponents }
    }
    
    /// Evaluate the monomial at a point
    pub fn evaluate<P: Float>(&self, point: &[P]) -> P {
        assert_eq!(self.exponents.len(), point.len());
        self.exponents
            .iter()
            .zip(point)
            .map(|(exp, val)| val.powi(*exp as i32))
            .fold(P::one(), |acc, val| acc * val)
    }
}

/// Monomial ordering for Gröbner basis computation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MonomialOrdering {
    /// Lexicographic ordering
    Lex,
    /// Graded reverse lexicographic ordering
    GrRevLex,
    /// Graded lexicographic ordering
    GrLex,
}

impl MonomialOrdering {
    /// Compare two monomials according to this ordering
    pub fn compare(&self, a: &Monomial, b: &Monomial) -> Ordering {
        match self {
            MonomialOrdering::Lex => Self::lex_compare(a, b),
            MonomialOrdering::GrRevLex => Self::grrevlex_compare(a, b),
            MonomialOrdering::GrLex => Self::grlex_compare(a, b),
        }
    }
    
    /// Lexicographic ordering
    fn lex_compare(a: &Monomial, b: &Monomial) -> Ordering {
        for (exp_a, exp_b) in a.exponents.iter().zip(&b.exponents) {
            match exp_a.cmp(exp_b) {
                Ordering::Equal => continue,
                other => return other,
            }
        }
        Ordering::Equal
    }
    
    /// Graded reverse lexicographic ordering
    fn grrevlex_compare(a: &Monomial, b: &Monomial) -> Ordering {
        // First compare by total degree
        match a.degree().cmp(&b.degree()) {
            Ordering::Equal => {
                // Then reverse lexicographic from the last variable
                for (exp_a, exp_b) in a.exponents.iter().zip(&b.exponents).rev() {
                    match exp_b.cmp(exp_a) { // Note: reversed comparison
                        Ordering::Equal => continue,
                        other => return other,
                    }
                }
                Ordering::Equal
            }
            other => other,
        }
    }
    
    /// Graded lexicographic ordering
    fn grlex_compare(a: &Monomial, b: &Monomial) -> Ordering {
        // First compare by total degree
        match a.degree().cmp(&b.degree()) {
            Ordering::Equal => Self::lex_compare(a, b),
            other => other,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_monomial_operations() {
        // x²y
        let m1 = Monomial::new(vec![2, 1]);
        // xy²
        let m2 = Monomial::new(vec![1, 2]);
        
        // Test multiplication: x²y × xy² = x³y³
        let product = m1.multiply(&m2);
        assert_eq!(product.exponents, vec![3, 3]);
        
        // Test degree
        assert_eq!(m1.degree(), 3);
        assert_eq!(m2.degree(), 3);
        assert_eq!(product.degree(), 6);
        
        // Test division
        let quotient = product.divide(&m1).unwrap();
        assert_eq!(quotient.exponents, m2.exponents);
        
        // Test LCM
        let lcm = m1.lcm(&m2);
        assert_eq!(lcm.exponents, vec![2, 2]);
    }
    
    #[test]
    fn test_monomial_orderings() {
        let m1 = Monomial::new(vec![2, 1, 0]); // x²y
        let m2 = Monomial::new(vec![1, 2, 0]); // xy²
        let m3 = Monomial::new(vec![0, 0, 3]); // z³
        
        // Lexicographic: x²y > xy² > z³
        assert_eq!(MonomialOrdering::Lex.compare(&m1, &m2), Ordering::Greater);
        assert_eq!(MonomialOrdering::Lex.compare(&m2, &m3), Ordering::Greater);
        
        // Graded reverse lex: For same degree, compares reverse lexicographically
        // m3 = (0,0,3) vs m1 = (2,1,0): same degree 3
        // Reverse comparison: z exponent first: 3 > 0, so m3 < m1 in GrRevLex
        assert_eq!(MonomialOrdering::GrRevLex.compare(&m3, &m1), Ordering::Less);
        // m1 = (2,1,0) vs m2 = (1,2,0): same degree 3
        // Reverse comparison: z equal, y: 1 < 2 (reversed), so m1 > m2
        assert_eq!(MonomialOrdering::GrRevLex.compare(&m1, &m2), Ordering::Greater);
    }
}