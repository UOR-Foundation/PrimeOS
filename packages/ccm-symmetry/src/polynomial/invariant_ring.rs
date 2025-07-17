//! Polynomial invariant rings and detection algorithms

use super::{GroebnerBasis, Monomial, MonomialOrdering, Polynomial, PolynomialRing, ReynoldsOperator, buchberger_algorithm};
use super::reynolds::generate_monomials;
use crate::group::SymmetryGroup;
use ccm_core::Float;

#[cfg(feature = "alloc")]
use alloc::{string::String, vec, vec::Vec};

/// A polynomial invariant under group action
#[derive(Debug, Clone)]
pub struct PolynomialInvariant<P: Float> {
    /// The invariant polynomial
    pub polynomial: Polynomial<P>,
    /// Description of the invariant
    pub description: String,
    /// Degree of the invariant
    pub degree: usize,
}

impl<P: Float> PolynomialInvariant<P> {
    /// Create a new polynomial invariant
    pub fn new(polynomial: Polynomial<P>, description: String) -> Self {
        let degree = polynomial.degree();
        Self {
            polynomial,
            description,
            degree,
        }
    }
    
    /// Evaluate the invariant at a point
    pub fn evaluate(&self, point: &[P]) -> P {
        self.polynomial.evaluate(point)
    }
    
    /// Check if this invariant is actually invariant under a group element
    pub fn verify_invariance(&self, group: &SymmetryGroup<P>, element: &crate::group::GroupElement<P>) -> bool {
        let reynolds = ReynoldsOperator::new(group.clone());
        let transformed = reynolds.apply_group_element(&self.polynomial, element);
        
        // Check if transformed equals original
        polynomial_equal(&transformed, &self.polynomial)
    }
}

/// The ring of polynomial invariants for a group
pub struct InvariantRing<P: Float> {
    /// The group acting on the polynomial ring
    pub group: SymmetryGroup<P>,
    /// Number of variables
    pub num_vars: usize,
    /// Generating invariants
    pub generators: Vec<PolynomialInvariant<P>>,
    /// Relations between generators (as a Gröbner basis)
    pub relations: Option<GroebnerBasis<P>>,
}

impl<P: Float> InvariantRing<P> {
    /// Create a new invariant ring
    pub fn new(group: SymmetryGroup<P>, num_vars: usize) -> Self {
        Self {
            group,
            num_vars,
            generators: Vec::new(),
            relations: None,
        }
    }
    
    /// Compute generators for the invariant ring up to given degree
    pub fn compute_generators(&mut self, max_degree: usize) {
        let reynolds = ReynoldsOperator::new(self.group.clone());
        
        // Generate primary invariants
        self.generators.clear();
        
        // For symmetric groups, we know the generators
        if let Some(n) = self.detect_symmetric_group() {
            self.add_symmetric_group_generators(n, max_degree);
            return;
        }
        
        // For other groups, use Reynolds operator
        let invariants = reynolds.generate_invariants(max_degree, self.num_vars);
        
        for (i, inv) in invariants.into_iter().enumerate() {
            let description = format!("Invariant_{}", i + 1);
            self.generators.push(PolynomialInvariant::new(inv, description));
        }
        
        // Compute relations if we have enough generators
        if self.generators.len() > 1 {
            self.compute_relations();
        }
    }
    
    /// Add known generators for symmetric group Sn
    fn add_symmetric_group_generators(&mut self, n: usize, max_degree: usize) {
        let ring = PolynomialRing::<P>::new(n);
        
        // Elementary symmetric polynomials
        for k in 1..=n.min(max_degree) {
            let mut poly = Polynomial::zero(n);
            
            // Generate all k-subsets of variables
            let subsets = generate_k_subsets(n, k);
            for subset in subsets {
                let mut term = Polynomial::constant(P::one(), n);
                for &var_idx in &subset {
                    term = term * ring.variable(var_idx);
                }
                poly = poly + term;
            }
            
            let description = format!("e_{} (elementary symmetric)", k);
            self.generators.push(PolynomialInvariant::new(poly, description));
        }
        
        // Power sum polynomials (if degree allows)
        for k in 1..=max_degree {
            let mut poly = Polynomial::zero(n);
            for i in 0..n {
                let mut var_power = ring.variable(i);
                for _ in 1..k {
                    var_power = var_power.clone() * ring.variable(i);
                }
                poly = poly + var_power;
            }
            
            if k <= n {  // Avoid redundancy with elementary symmetric
                let description = format!("p_{} (power sum)", k);
                self.generators.push(PolynomialInvariant::new(poly, description));
            }
        }
    }
    
    /// Detect if the group is a symmetric group
    fn detect_symmetric_group(&self) -> Option<usize> {
        // Simple heuristic: check if group order is n!
        if let Some(order) = self.group.order() {
            for n in 2..=10 {
                if order == factorial(n) && self.num_vars == n {
                    return Some(n);
                }
            }
        }
        None
    }
    
    /// Compute relations between generators
    fn compute_relations(&mut self) {
        if self.generators.len() < 2 {
            return; // No relations possible with fewer than 2 generators
        }
        
        // Create polynomials in auxiliary variables representing the generators
        let aux_ring = PolynomialRing::<P>::new(self.generators.len());
        let mut relation_polys = Vec::<Polynomial<P>>::new();
        
        // Compute syzygies: relations among generators
        // For each pair of generators, check if there's a polynomial relation
        
        // First, collect all monomials that appear in any generator
        #[cfg(feature = "std")]
        let mut all_monomials = std::collections::BTreeSet::new();
        #[cfg(all(feature = "alloc", not(feature = "std")))]
        let mut all_monomials = alloc::collections::BTreeSet::new();
        for gen in &self.generators {
            for (mono, _) in &gen.polynomial.terms {
                all_monomials.insert(mono.clone());
            }
        }
        
        // Build coefficient matrix: rows are monomials, columns are generators
        let monomials: Vec<_> = all_monomials.into_iter().collect();
        let num_monomials = monomials.len();
        let num_gens = self.generators.len();
        
        if num_monomials == 0 {
            return;
        }
        
        // Create matrix where entry (i,j) is coefficient of monomial i in generator j
        let mut matrix = vec![vec![P::zero(); num_gens]; num_monomials];
        
        for (j, gen) in self.generators.iter().enumerate() {
            for (i, mono) in monomials.iter().enumerate() {
                if let Some(&coeff) = gen.polynomial.terms.get(mono) {
                    matrix[i][j] = coeff;
                }
            }
        }
        
        // Find kernel of the matrix (null space)
        // These are the linear dependencies among generators
        let kernel_basis = compute_kernel(&matrix);
        
        // Convert kernel vectors to polynomial relations
        for kernel_vec in kernel_basis {
            let mut relation = Polynomial::zero(self.generators.len());
            for (i, &coeff) in kernel_vec.iter().enumerate() {
                if coeff != P::zero() {
                    let mut mono_exp = vec![0; self.generators.len()];
                    mono_exp[i] = 1;
                    relation.add_term(
                        Monomial::new(mono_exp),
                        coeff
                    );
                }
            }
            if !relation.is_zero() {
                relation_polys.push(relation);
            }
        }
        
        // Also check for algebraic relations (non-linear)
        // For small degree products of generators
        if self.generators.len() <= 4 {
            for max_deg in 2..=3 {
                self.find_algebraic_relations(&aux_ring, max_deg, &mut relation_polys);
            }
        }
        
        if !relation_polys.is_empty() {
            self.relations = Some(buchberger_algorithm(relation_polys, MonomialOrdering::GrRevLex));
        }
    }
    
    /// Find algebraic (non-linear) relations among generators
    fn find_algebraic_relations(
        &self,
        aux_ring: &PolynomialRing<P>,
        max_degree: usize,
        relations: &mut Vec<Polynomial<P>>
    ) {
        // Generate monomials in auxiliary variables up to max_degree
        let aux_monomials = generate_monomials(self.generators.len(), max_degree);
        
        // For each aux monomial, compute the corresponding polynomial in original vars
        let mut monomial_polys = Vec::new();
        
        for aux_mono in &aux_monomials {
            if aux_mono.degree() <= 1 {
                continue; // Skip linear terms
            }
            
            // Compute product of generators according to aux_mono
            let mut product = Polynomial::constant(P::one(), self.num_vars);
            
            for (i, &exp) in aux_mono.exponents.iter().enumerate() {
                for _ in 0..exp {
                    product = product * self.generators[i].polynomial.clone();
                }
            }
            
            monomial_polys.push((aux_mono.clone(), product));
        }
        
        // Check if any polynomial can be expressed as combination of others
        for (i, (aux_mono_i, poly_i)) in monomial_polys.iter().enumerate() {
            // Try to express poly_i as linear combination of other polys
            let mut target = poly_i.clone();
            let mut relation = Polynomial::zero(self.generators.len());
            relation.add_term(aux_mono_i.clone(), P::one());
            
            for (j, (aux_mono_j, poly_j)) in monomial_polys.iter().enumerate() {
                if i != j && poly_j.degree() <= poly_i.degree() {
                    // Check if poly_j appears in target
                    let leading_mono = poly_j.leading_monomial(MonomialOrdering::GrRevLex);
                    if let Some(lead_m) = leading_mono {
                        if let Some(lead_coeff) = poly_j.leading_coefficient(MonomialOrdering::GrRevLex) {
                            // Try to eliminate leading term of poly_j from target
                            if let Some(&target_coeff) = target.terms.get(lead_m) {
                                let scale = target_coeff / lead_coeff;
                                target = target - poly_j.scalar_multiply(scale);
                                let mut term = Polynomial::zero(self.generators.len());
                                term.add_term(aux_mono_j.clone(), scale);
                                relation = relation - term;
                            }
                        }
                    }
                }
            }
            
            // If target reduces to constant or zero, we found a relation
            if target.degree() == 0 {
                if let Some(&const_val) = target.terms.values().next() {
                    relation = relation - Polynomial::constant(const_val, self.generators.len());
                }
                if !relation.is_zero() {
                    relations.push(relation);
                }
            }
        }
    }
    
    /// Check if a polynomial is invariant
    pub fn is_invariant(&self, poly: &Polynomial<P>) -> bool {
        let reynolds = ReynoldsOperator::new(self.group.clone());
        let averaged = reynolds.apply(poly);
        polynomial_equal(&averaged, poly)
    }
    
    /// Express an invariant polynomial in terms of generators (if possible)
    pub fn express_in_generators(&self, poly: &Polynomial<P>) -> Option<Polynomial<P>> {
        if !self.is_invariant(poly) {
            return None;
        }
        
        // Create extended polynomial ring with original vars and generator vars
        let total_vars = self.num_vars + self.generators.len();
        let extended_ring = PolynomialRing::<P>::new(total_vars);
        
        // Create polynomials representing: generator_i - y_i = 0
        // where y_i are new variables representing the generators
        let mut ideal_generators = Vec::new();
        
        for (i, gen) in self.generators.iter().enumerate() {
            // Create polynomial: gen(x₁,...,xₙ) - yᵢ
            let mut gen_poly = Polynomial::zero(total_vars);
            
            // Add terms from generator polynomial (in original variables)
            for (mono, coeff) in &gen.polynomial.terms {
                let mut extended_exponents = vec![0; total_vars];
                for (j, &exp) in mono.exponents.iter().enumerate() {
                    extended_exponents[j] = exp;
                }
                gen_poly.add_term(Monomial::new(extended_exponents), *coeff);
            }
            
            // Subtract yᵢ (the new variable)
            let mut y_exponents = vec![0; total_vars];
            y_exponents[self.num_vars + i] = 1;
            gen_poly.add_term(Monomial::new(y_exponents), -P::one());
            
            ideal_generators.push(gen_poly);
        }
        
        // Extend the target polynomial to the larger ring
        let mut target = Polynomial::zero(total_vars);
        for (mono, coeff) in &poly.terms {
            let mut extended_exponents = vec![0; total_vars];
            for (j, &exp) in mono.exponents.iter().enumerate() {
                extended_exponents[j] = exp;
            }
            target.add_term(Monomial::new(extended_exponents), *coeff);
        }
        
        // Compute Gröbner basis with elimination ordering
        // We want to eliminate x variables and keep y variables
        let gb = buchberger_algorithm(ideal_generators, MonomialOrdering::Lex);
        
        // Reduce the target polynomial by the Gröbner basis
        let reduced = gb.reduce(&target);
        
        // Check if reduced polynomial only involves y variables
        let mut expression = Polynomial::zero(self.generators.len());
        let mut has_x_vars = false;
        
        for (mono, coeff) in &reduced.terms {
            // Check if monomial involves any x variables
            let x_vars_used = mono.exponents[..self.num_vars].iter().any(|&e| e > 0);
            
            if x_vars_used {
                has_x_vars = true;
                break;
            }
            
            // Extract y variable exponents
            let y_exponents = mono.exponents[self.num_vars..].to_vec();
            expression.add_term(Monomial::new(y_exponents), *coeff);
        }
        
        if has_x_vars {
            None // Could not eliminate all x variables
        } else {
            Some(expression)
        }
    }
    
    /// Get Hilbert series (generating function for dimensions)
    pub fn hilbert_series(&self, max_degree: usize) -> Vec<usize> {
        let mut dims = vec![0; max_degree + 1];
        
        // Count invariants of each degree
        for gen in &self.generators {
            if gen.degree <= max_degree {
                dims[gen.degree] += 1;
            }
        }
        
        // This is simplified - full computation would use Molien's formula
        dims
    }
}

/// Generate all k-element subsets of {0, 1, ..., n-1}
fn generate_k_subsets(n: usize, k: usize) -> Vec<Vec<usize>> {
    let mut result = Vec::new();
    let mut subset = vec![0; k];
    
    fn generate_recursive(
        subset: &mut Vec<usize>,
        n: usize,
        k: usize,
        start: usize,
        index: usize,
        result: &mut Vec<Vec<usize>>,
    ) {
        if index == k {
            result.push(subset.clone());
            return;
        }
        
        for i in start..=n - k + index {
            subset[index] = i;
            generate_recursive(subset, n, k, i + 1, index + 1, result);
        }
    }
    
    if k > 0 && k <= n {
        generate_recursive(&mut subset, n, k, 0, 0, &mut result);
    }
    
    result
}

/// Compute factorial
fn factorial(n: usize) -> usize {
    (1..=n).product()
}

/// Check if two polynomials are equal
fn polynomial_equal<P: Float>(p1: &Polynomial<P>, p2: &Polynomial<P>) -> bool {
    if p1.num_vars != p2.num_vars {
        return false;
    }
    
    // Check all terms
    if p1.terms.len() != p2.terms.len() {
        return false;
    }
    
    for (mono, coeff) in &p1.terms {
        match p2.terms.get(mono) {
            Some(coeff2) => {
                if (*coeff - *coeff2).abs() > P::epsilon() {
                    return false;
                }
            }
            None => return false,
        }
    }
    
    true
}

/// Compute kernel (null space) of a matrix
fn compute_kernel<P: Float>(matrix: &[Vec<P>]) -> Vec<Vec<P>> {
    if matrix.is_empty() || matrix[0].is_empty() {
        return vec![];
    }
    
    let m = matrix.len();
    let n = matrix[0].len();
    
    // Create augmented matrix for row reduction
    let mut aug = matrix.to_vec();
    
    // Perform Gaussian elimination with partial pivoting
    let mut pivot_cols = Vec::new();
    let mut col = 0;
    
    for row in 0..m {
        if col >= n {
            break;
        }
        
        // Find pivot
        let mut pivot_row = row;
        let mut max_val = P::zero();
        
        for i in row..m {
            let val = aug[i][col].abs();
            if val > max_val {
                max_val = val;
                pivot_row = i;
            }
        }
        
        if max_val < P::epsilon() {
            // No pivot in this column, move to next
            col += 1;
            continue;
        }
        
        // Swap rows
        aug.swap(row, pivot_row);
        pivot_cols.push(col);
        
        // Scale pivot row
        let pivot_val = aug[row][col];
        for j in 0..n {
            aug[row][j] = aug[row][j] / pivot_val;
        }
        
        // Eliminate column
        for i in 0..m {
            if i != row && aug[i][col].abs() > P::epsilon() {
                let factor = aug[i][col];
                for j in 0..n {
                    aug[i][j] = aug[i][j] - factor * aug[row][j];
                }
            }
        }
        
        col += 1;
    }
    
    // Find free variables
    let mut free_vars = Vec::new();
    for j in 0..n {
        if !pivot_cols.contains(&j) {
            free_vars.push(j);
        }
    }
    
    // Build kernel basis
    let mut kernel_basis = Vec::new();
    
    for &free_var in &free_vars {
        let mut kernel_vec = vec![P::zero(); n];
        kernel_vec[free_var] = P::one();
        
        // Back-substitute to find values of pivot variables
        for (i, &pivot_col) in pivot_cols.iter().enumerate().rev() {
            let mut sum = P::zero();
            for j in pivot_col + 1..n {
                sum = sum + aug[i][j] * kernel_vec[j];
            }
            kernel_vec[pivot_col] = -sum;
        }
        
        kernel_basis.push(kernel_vec);
    }
    
    kernel_basis
}

/// Standard invariant generators for common groups
impl<P: Float> InvariantRing<P> {
    /// Create invariant ring for orthogonal group SO(n)
    pub fn orthogonal_invariants(n: usize) -> Vec<PolynomialInvariant<P>> {
        let ring = PolynomialRing::<P>::new(n);
        let mut invariants = Vec::new();
        
        // For SO(n), the basic invariant is the quadratic form Σx_i²
        let mut quadratic = Polynomial::zero(n);
        for i in 0..n {
            let var = ring.variable(i);
            quadratic = quadratic + var.clone() * var;
        }
        
        invariants.push(PolynomialInvariant::new(
            quadratic,
            "Quadratic form".into(),
        ));
        
        invariants
    }
    
    /// Create invariant ring for special unitary group SU(n)
    pub fn unitary_invariants(n: usize) -> Vec<PolynomialInvariant<P>> {
        let ring = PolynomialRing::<P>::new(2 * n); // Complex variables
        let mut invariants = Vec::new();
        
        // For SU(n), basic invariants include |z_i|² = x_i² + y_i²
        for i in 0..n {
            let x = ring.variable(2 * i);
            let y = ring.variable(2 * i + 1);
            let norm_squared = x.clone() * x + y.clone() * y;
            
            invariants.push(PolynomialInvariant::new(
                norm_squared,
                format!("|z_{}|²", i + 1),
            ));
        }
        
        invariants
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_symmetric_group_invariants() {
        // Create invariant ring for S3
        let s3 = SymmetryGroup::<f64>::symmetric_group(3).unwrap();
        let mut inv_ring = InvariantRing::new(s3, 3);
        
        // Compute generators up to degree 3
        inv_ring.compute_generators(3);
        
        // Should have elementary symmetric polynomials
        assert!(inv_ring.generators.len() >= 3);
        
        // Check e_1 = x + y + z
        let e1 = &inv_ring.generators[0];
        assert_eq!(e1.evaluate(&[1.0, 2.0, 3.0]), 6.0);
        
        // Check e_2 = xy + xz + yz
        let e2 = &inv_ring.generators[1];
        assert_eq!(e2.evaluate(&[1.0, 2.0, 3.0]), 11.0); // 1*2 + 1*3 + 2*3
    }
    
    #[test]
    fn test_orthogonal_invariants() {
        let invariants = InvariantRing::<f64>::orthogonal_invariants(3);
        
        // Should have quadratic form
        assert_eq!(invariants.len(), 1);
        
        let quad = &invariants[0];
        assert_eq!(quad.evaluate(&[1.0, 2.0, 3.0]), 14.0); // 1² + 2² + 3²
    }
}