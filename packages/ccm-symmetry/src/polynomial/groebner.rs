//! Gröbner basis computation using Buchberger's algorithm

use super::{Monomial, MonomialOrdering, Polynomial};
use ccm_core::Float;

#[cfg(feature = "alloc")]
use alloc::{vec, vec::Vec};

/// A Gröbner basis for a polynomial ideal
#[derive(Debug, Clone)]
pub struct GroebnerBasis<P: Float> {
    /// The basis polynomials
    pub basis: Vec<Polynomial<P>>,
    /// The monomial ordering used
    pub ordering: MonomialOrdering,
}

impl<P: Float> GroebnerBasis<P> {
    /// Create a new Gröbner basis
    pub fn new(basis: Vec<Polynomial<P>>, ordering: MonomialOrdering) -> Self {
        Self { basis, ordering }
    }
    
    /// Reduce a polynomial modulo the Gröbner basis
    pub fn reduce(&self, poly: &Polynomial<P>) -> Polynomial<P> {
        let mut result = poly.clone();
        let mut changed = true;
        
        while changed {
            changed = false;
            for basis_poly in &self.basis {
                if basis_poly.is_zero() {
                    continue;
                }
                
                // Try to reduce by this basis element
                if let (Some(result_lt), Some(basis_lt)) = 
                    (result.leading_monomial(self.ordering), basis_poly.leading_monomial(self.ordering)) {
                    
                    if basis_lt.divides(result_lt) {
                        let (_, remainder) = result.divide(basis_poly, self.ordering);
                        if remainder.terms.len() < result.terms.len() || 
                           remainder.degree() < result.degree() {
                            result = remainder;
                            changed = true;
                            break;
                        }
                    }
                }
            }
        }
        
        result
    }
    
    /// Check if a polynomial is in the ideal
    pub fn contains(&self, poly: &Polynomial<P>) -> bool {
        self.reduce(poly).is_zero()
    }
    
    /// Get the leading term ideal
    pub fn leading_term_ideal(&self) -> Vec<Monomial> {
        self.basis
            .iter()
            .filter_map(|p| p.leading_monomial(self.ordering).cloned())
            .collect()
    }
}

/// Compute the S-polynomial of two polynomials
fn s_polynomial<P: Float>(
    f: &Polynomial<P>,
    g: &Polynomial<P>,
    ordering: MonomialOrdering,
) -> Polynomial<P> {
    if f.is_zero() || g.is_zero() {
        return Polynomial::zero(f.num_vars);
    }
    
    let (f_lt_mono, f_lt_coeff) = f.leading_term(ordering).unwrap();
    let (g_lt_mono, g_lt_coeff) = g.leading_term(ordering).unwrap();
    
    let lcm = f_lt_mono.lcm(&g_lt_mono);
    let f_multiplier = lcm.divide(&f_lt_mono).unwrap();
    let g_multiplier = lcm.divide(&g_lt_mono).unwrap();
    
    // Multiply polynomials by appropriate monomials
    let mut f_scaled = Polynomial::new(f.num_vars);
    for (mono, coeff) in &f.terms {
        let new_mono = f_multiplier.multiply(mono);
        f_scaled.add_term(new_mono, *coeff / f_lt_coeff);
    }
    
    let mut g_scaled = Polynomial::new(g.num_vars);
    for (mono, coeff) in &g.terms {
        let new_mono = g_multiplier.multiply(mono);
        g_scaled.add_term(new_mono, *coeff / g_lt_coeff);
    }
    
    f_scaled - g_scaled
}

/// Buchberger's algorithm for computing Gröbner basis
pub fn buchberger_algorithm<P: Float>(
    generators: Vec<Polynomial<P>>,
    ordering: MonomialOrdering,
) -> GroebnerBasis<P> {
    if generators.is_empty() {
        return GroebnerBasis::new(vec![], ordering);
    }
    
    let mut basis = generators;
    let mut pairs: Vec<(usize, usize)> = vec![];
    
    // Initialize with all pairs
    for i in 0..basis.len() {
        for j in i + 1..basis.len() {
            pairs.push((i, j));
        }
    }
    
    while !pairs.is_empty() {
        let (i, j) = pairs.pop().unwrap();
        
        // Compute S-polynomial
        let s_poly = s_polynomial(&basis[i], &basis[j], ordering);
        
        // Reduce S-polynomial by current basis
        let mut remainder = s_poly;
        for k in 0..basis.len() {
            if k != i && k != j && !basis[k].is_zero() {
                let (_, rem) = remainder.divide(&basis[k], ordering);
                remainder = rem;
            }
        }
        
        // If remainder is non-zero, add to basis
        if !remainder.is_zero() {
            let new_index = basis.len();
            basis.push(remainder);
            
            // Add new pairs
            for k in 0..new_index {
                pairs.push((k, new_index));
            }
        }
    }
    
    // Remove redundant elements (optional optimization)
    minimize_basis(&mut basis, ordering);
    
    GroebnerBasis::new(basis, ordering)
}

/// Minimize a Gröbner basis by removing redundant elements
fn minimize_basis<P: Float>(basis: &mut Vec<Polynomial<P>>, ordering: MonomialOrdering) {
    let mut i = 0;
    while i < basis.len() {
        let mut redundant = false;
        
        // Check if basis[i] can be reduced by other elements
        for j in 0..basis.len() {
            if i != j && !basis[j].is_zero() {
                if let (Some(lt_i), Some(lt_j)) = 
                    (basis[i].leading_monomial(ordering), basis[j].leading_monomial(ordering)) {
                    if lt_j.divides(lt_i) && i != j {
                        redundant = true;
                        break;
                    }
                }
            }
        }
        
        if redundant {
            basis.remove(i);
        } else {
            i += 1;
        }
    }
}

/// Compute a reduced Gröbner basis
pub fn reduced_groebner_basis<P: Float>(
    generators: Vec<Polynomial<P>>,
    ordering: MonomialOrdering,
) -> GroebnerBasis<P> {
    let mut gb = buchberger_algorithm(generators, ordering);
    
    // Make leading coefficients 1
    for poly in &mut gb.basis {
        if let Some(lc) = poly.leading_coefficient(ordering) {
            *poly = poly.scalar_multiply(P::one() / lc);
        }
    }
    
    // Reduce each polynomial by the others
    let n = gb.basis.len();
    for i in 0..n {
        let mut reduced = gb.basis[i].clone();
        for j in 0..n {
            if i != j {
                let (_, rem) = reduced.divide(&gb.basis[j], ordering);
                reduced = rem;
            }
        }
        gb.basis[i] = reduced;
    }
    
    gb
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polynomial::PolynomialRing;
    
    #[test]
    fn test_s_polynomial() {
        let ring = PolynomialRing::<f64>::new(2);
        let ordering = MonomialOrdering::Lex;
        
        // f = x² - 1
        let mut f = ring.variable(0) * ring.variable(0);
        f = f - ring.one();
        
        // g = xy - 1
        let mut g = ring.variable(0) * ring.variable(1);
        g = g - ring.one();
        
        let s_poly = s_polynomial(&f, &g, ordering);
        
        // S(f,g) should be x - y (not y - x)
        // f = x² - 1, g = xy - 1
        // LCM(x², xy) = x²y
        // S(f,g) = (x²y/x²)f - (x²y/xy)g = y(x² - 1) - x(xy - 1) = x²y - y - x²y + x = x - y
        assert_eq!(s_poly.evaluate(&[2.0, 3.0]), -1.0); // 2 - 3 = -1
    }
    
    #[test]
    fn test_groebner_basis() {
        let ring = PolynomialRing::<f64>::new(2);
        let ordering = MonomialOrdering::Lex;
        
        // Ideal generated by x² + y² - 1 and xy
        let mut f1 = ring.variable(0) * ring.variable(0) + ring.variable(1) * ring.variable(1);
        f1 = f1 - ring.one(); // x² + y² - 1
        
        let f2 = ring.variable(0) * ring.variable(1); // xy
        let f2_copy = f2.clone();
        
        let gb = buchberger_algorithm(vec![f1, f2], ordering);
        
        // The Gröbner basis should contain polynomials that generate the same ideal
        assert!(gb.basis.len() >= 2);
        
        // Test that xy is in the ideal
        assert!(gb.contains(&f2_copy));
    }
}