//! Reynolds operator for computing invariant polynomials

use super::{Polynomial, Monomial};
use crate::group::{GroupElement, SymmetryGroup};
use ccm_core::Float;

#[cfg(feature = "alloc")]
use alloc::{vec, vec::Vec};

/// Reynolds operator for averaging over a group
pub struct ReynoldsOperator<P: Float> {
    /// The group to average over
    group: SymmetryGroup<P>,
}

impl<P: Float> ReynoldsOperator<P> {
    /// Create a new Reynolds operator for a group
    pub fn new(group: SymmetryGroup<P>) -> Self {
        Self { group }
    }
    
    /// Apply the Reynolds operator to a polynomial
    /// 
    /// For a finite group G, this computes:
    /// R(f) = (1/|G|) * Σ_{g∈G} g·f
    /// 
    /// The result is invariant under the group action.
    pub fn apply(&self, poly: &Polynomial<P>) -> Polynomial<P> {
        match self.group.order() {
            Some(order) => self.apply_finite(poly, order),
            None => panic!("Reynolds operator requires finite group"),
        }
    }
    
    /// Apply Reynolds operator for finite groups
    fn apply_finite(&self, poly: &Polynomial<P>, order: usize) -> Polynomial<P> {
        let mut result = Polynomial::zero(poly.num_vars);
        let scale = P::one() / P::from(order).unwrap();
        
        let elements = self.group.all_elements();
        
        // For each group element, apply it to the polynomial and accumulate
        for g in elements {
            let transformed = self.apply_group_element(poly, &g);
            result = result + transformed;
        }
        
        result.scalar_multiply(scale)
    }
    
    /// Apply a group element to a polynomial
    pub(crate) fn apply_group_element(&self, poly: &Polynomial<P>, g: &GroupElement<P>) -> Polynomial<P> {
        // Check if this is a permutation matrix
        if let Some(perm) = self.element_as_permutation(g) {
            // The permutation tells us where each variable goes
            // perm[i] = j means variable i maps to position j
            // But permute_variables expects the inverse: which variable goes to position i
            let mut inverse_perm = vec![0; perm.len()];
            for (i, &j) in perm.iter().enumerate() {
                inverse_perm[j] = i;
            }
            poly.permute_variables(&inverse_perm)
        } else {
            // For matrix groups, we need to transform the variables
            self.apply_linear_transformation(poly, g)
        }
    }
    
    /// Convert group element to permutation if possible
    fn element_as_permutation(&self, g: &GroupElement<P>) -> Option<Vec<usize>> {
        // Check if this is a permutation matrix
        let n = (self.group.dimension() as f64).sqrt() as usize;
        if n * n != self.group.dimension() {
            return None;
        }
        
        let mut perm = vec![0; n];
        for i in 0..n {
            let mut found = false;
            for j in 0..n {
                let idx = i * n + j;
                if idx < g.params.len() && (g.params[idx] - P::one()).abs() < P::epsilon() {
                    // Check that this is the only 1 in the row
                    let mut row_sum = P::zero();
                    for k in 0..n {
                        row_sum = row_sum + g.params[i * n + k].abs();
                    }
                    if (row_sum - P::one()).abs() < P::epsilon() {
                        perm[i] = j;
                        found = true;
                        break;
                    }
                }
            }
            if !found {
                return None;
            }
        }
        
        Some(perm)
    }
    
    /// Apply linear transformation to polynomial variables
    fn apply_linear_transformation(&self, poly: &Polynomial<P>, g: &GroupElement<P>) -> Polynomial<P> {
        // For a linear transformation x ↦ Ax, we substitute
        // x_i ↦ Σ_j A_{ij} x_j in the polynomial
        
        let n = poly.num_vars;
        let mat_n = (g.params.len() as f64).sqrt() as usize;
        
        if mat_n != n || mat_n * mat_n != g.params.len() {
            // Not a square matrix of the right size
            return poly.clone();
        }
        
        // Create substitution polynomials for each variable
        let mut substitutions = Vec::new();
        for i in 0..n {
            let mut sub_poly = Polynomial::zero(n);
            for j in 0..n {
                let coeff = g.params[i * n + j];
                if coeff != P::zero() {
                    sub_poly = sub_poly + Polynomial::variable(j, n).scalar_multiply(coeff);
                }
            }
            substitutions.push(sub_poly);
        }
        
        // Apply substitution to each term
        let mut result = Polynomial::zero(n);
        for (monomial, coeff) in &poly.terms {
            let mut term_result = Polynomial::constant(*coeff, n);
            
            // For each variable in the monomial
            for (var_idx, &power) in monomial.exponents.iter().enumerate() {
                if power > 0 {
                    let mut var_contrib = substitutions[var_idx].clone();
                    // Raise to the appropriate power
                    for _ in 1..power {
                        var_contrib = var_contrib.clone() * substitutions[var_idx].clone();
                    }
                    term_result = term_result * var_contrib;
                }
            }
            
            result = result + term_result;
        }
        
        result
    }
    
    /// Generate invariant polynomials up to given degree
    pub fn generate_invariants(&self, max_degree: usize, num_vars: usize) -> Vec<Polynomial<P>> {
        let mut invariants = Vec::new();
        
        // Generate all monomials up to max_degree
        let monomials = generate_monomials(num_vars, max_degree);
        
        // Apply Reynolds operator to each monomial
        for monomial in monomials {
            let mut poly = Polynomial::new(num_vars);
            poly.add_term(monomial, P::one());
            
            let invariant = self.apply(&poly);
            
            // Check if this gives a new invariant (not in span of existing ones)
            if !invariant.is_zero() && is_linearly_independent(&invariant, &invariants) {
                invariants.push(invariant);
            }
        }
        
        invariants
    }
}

/// Generate all monomials of degree <= max_degree
pub(super) fn generate_monomials(num_vars: usize, max_degree: usize) -> Vec<Monomial> {
    use super::Monomial;
    
    let mut monomials = Vec::new();
    let mut exponents = vec![0; num_vars];
    
    fn generate_recursive(
        exponents: &mut Vec<usize>,
        var_idx: usize,
        remaining_degree: usize,
        monomials: &mut Vec<Monomial>,
    ) {
        if var_idx == exponents.len() {
            monomials.push(Monomial::new(exponents.clone()));
            return;
        }
        
        for degree in 0..=remaining_degree {
            exponents[var_idx] = degree;
            generate_recursive(exponents, var_idx + 1, remaining_degree - degree, monomials);
        }
        exponents[var_idx] = 0;
    }
    
    for degree in 0..=max_degree {
        generate_recursive(&mut exponents, 0, degree, &mut monomials);
    }
    
    monomials
}

/// Check if a polynomial is linearly independent from a set
fn is_linearly_independent<P: Float>(
    poly: &Polynomial<P>,
    basis: &[Polynomial<P>],
) -> bool {
    use super::{GroebnerBasis, MonomialOrdering, buchberger_algorithm};
    
    if basis.is_empty() {
        return !poly.is_zero();
    }
    
    // To check linear independence, we solve the system:
    // c₁*basis[0] + c₂*basis[1] + ... + cₙ*basis[n-1] + c*poly = 0
    // If the only solution has c = 0, then poly is linearly independent
    
    // Create an extended polynomial ring with coefficient variables
    let num_polys = basis.len() + 1;
    let original_vars = poly.num_vars;
    let total_vars = original_vars + num_polys;
    
    // Build the linear combination polynomial
    let mut linear_comb = Polynomial::zero(total_vars);
    
    // Add c₁*basis[0] + c₂*basis[1] + ...
    for (i, basis_poly) in basis.iter().enumerate() {
        for (mono, coeff) in &basis_poly.terms {
            // Create monomial in extended space: cᵢ * original_monomial
            let mut extended_exp = vec![0; total_vars];
            // Copy original monomial exponents
            for (j, &exp) in mono.exponents.iter().enumerate() {
                extended_exp[j] = exp;
            }
            // Add coefficient variable cᵢ
            extended_exp[original_vars + i] = 1;
            
            linear_comb.add_term(Monomial::new(extended_exp), *coeff);
        }
    }
    
    // Add c*poly (where c is the last coefficient variable)
    for (mono, coeff) in &poly.terms {
        let mut extended_exp = vec![0; total_vars];
        for (j, &exp) in mono.exponents.iter().enumerate() {
            extended_exp[j] = exp;
        }
        extended_exp[original_vars + basis.len()] = 1;
        
        linear_comb.add_term(Monomial::new(extended_exp), *coeff);
    }
    
    // The polynomial should be zero for all values of original variables
    // This means all coefficients (when grouped by original monomials) must be zero
    
    // Group terms by original monomial
    #[cfg(feature = "std")]
    let mut coeff_equations = std::collections::HashMap::<Vec<usize>, Polynomial<P>>::new();
    #[cfg(all(feature = "alloc", not(feature = "std")))]
    let mut coeff_equations = alloc::collections::HashMap::<Vec<usize>, Polynomial<P>>::new();
    
    for (mono, coeff) in &linear_comb.terms {
        let original_mono_exp = mono.exponents[..original_vars].to_vec();
        let coeff_mono_exp = mono.exponents[original_vars..].to_vec();
        
        let entry = coeff_equations.entry(original_mono_exp).or_insert_with(|| {
            Polynomial::zero(num_polys)
        });
        
        entry.add_term(Monomial::new(coeff_mono_exp), *coeff);
    }
    
    // Check if the system has only the trivial solution
    // For linear independence, we need c (last variable) to be forced to be 0
    
    // Build ideal from coefficient equations
    let ideal_gens: Vec<_> = coeff_equations.into_values().collect();
    
    if ideal_gens.is_empty() {
        // No constraints, so dependent only if poly is zero
        return !poly.is_zero();
    }
    
    // Compute Gröbner basis
    let gb = buchberger_algorithm(ideal_gens, MonomialOrdering::Lex);
    
    // Check if we can derive that c = 0 (last variable must be zero)
    // Look for a polynomial that is just the last variable
    let mut c_var = Polynomial::zero(num_polys);
    let mut c_exp = vec![0; num_polys];
    c_exp[basis.len()] = 1;
    c_var.add_term(Monomial::new(c_exp), P::one());
    
    // Reduce c by the Gröbner basis
    let reduced = gb.reduce(&c_var);
    
    // If c reduces to 0, then c must be 0, so poly is linearly independent
    reduced.is_zero()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::group::SymmetryGroup;
    use crate::polynomial::PolynomialRing;
    
    #[test]
    fn test_reynolds_symmetric_group() {
        // Create S3 acting on 3 variables
        let s3 = SymmetryGroup::<f64>::symmetric_group(3).unwrap();
        
        // Debug: check generators
        let gens = s3.generators();
        assert_eq!(gens.len(), 2, "S3 should have 2 generators");
        
        // Verify S3 has 6 elements
        assert_eq!(s3.order(), Some(6));
        
        // Let's debug: check what elements we have
        let elements = s3.all_elements();
        assert_eq!(elements.len(), 6, "S3 should have 6 elements");
        
        let reynolds = ReynoldsOperator::new(s3);
        
        let ring = PolynomialRing::<f64>::new(3);
        
        // First test with S2 acting on 2 variables for simpler debugging
        let s2 = SymmetryGroup::<f64>::symmetric_group(2).unwrap();
        let reynolds2 = ReynoldsOperator::new(s2);
        let ring2 = PolynomialRing::<f64>::new(2);
        let x = ring2.variable(0);
        let inv2 = reynolds2.apply(&x);
        // Should get (x + y)/2
        assert_eq!(inv2.evaluate(&[1.0, 3.0]), 2.0); // (1+3)/2 = 2
        
        // Now test S3
        let x1 = ring.variable(0);
        let invariant = reynolds.apply(&x1);
        
        // Should get (x₁ + x₂ + x₃)/3, but S3 has 6 elements, so it's /6
        // The averaging should include all permutations of x₁
        // For S3: identity keeps x₁ as x₁, (12) swaps to x₂, (13) swaps to x₃, etc.
        // So we get 2x₁ + 2x₂ + 2x₃ / 6 = (x₁ + x₂ + x₃)/3
        let result = invariant.evaluate(&[1.0, 2.0, 3.0]);
        assert!((result - 2.0).abs() < 1e-10, "Expected 2.0, got {}", result); // (1+2+3)/3 = 2
        
        // Apply Reynolds to x₁²
        let x1_squared = x1.clone() * x1;
        let invariant2 = reynolds.apply(&x1_squared);
        
        // Should get (x₁² + x₂² + x₃²)/3
        let result2 = invariant2.evaluate(&[1.0, 2.0, 3.0]);
        let expected2 = 14.0/3.0; // (1+4+9)/3
        assert!((result2 - expected2).abs() < 1e-10, "Expected {}, got {}", expected2, result2);
    }
}