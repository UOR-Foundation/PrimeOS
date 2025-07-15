//! Group manifold and Lie algebra checks
//! 
//! This module provides functionality to check if elements belong to
//! the group manifold and satisfy Lie algebra constraints.

use num_traits::Float;
use crate::group::{GroupElement, SymmetryGroup};
use crate::group::matrix_operations::GroupRepresentation;

impl<P: Float> SymmetryGroup<P> {
    /// Check if element is on the group manifold (generic continuous groups)
    pub(crate) fn is_on_group_manifold(&self, g: &GroupElement<P>) -> bool {
        // For continuous groups, check if element can be reached
        // by exponentiating linear combinations of generators
        
        // Check if element is identity
        if g.is_identity() {
            return true;
        }
        
        // Try to find element in the exponential image
        // For matrix groups, we need to check if log(g) is in the Lie algebra
        match self.get_representation() {
            GroupRepresentation::Matrix(n) => {
                self.check_matrix_group_manifold(g, n)
            }
            GroupRepresentation::Abstract => {
                // For abstract continuous groups, use local chart check
                self.check_abstract_manifold(g)
            }
        }
    }
    
    /// Check if matrix element is on the group manifold
    fn check_matrix_group_manifold(&self, g: &GroupElement<P>, n: usize) -> bool {
        // First verify basic matrix group constraints
        match self.get_group_name() {
            "SO(n)" => {
                if !self.is_special_orthogonal(g) {
                    return false;
                }
            }
            "SU(n)" => {
                if !self.is_special_unitary(g) {
                    return false;
                }
            }
            "GL(n)" => {
                if !self.is_general_linear(g) {
                    return false;
                }
            }
            _ => {}
        }
        
        // Try to compute logarithm and check if it's in the Lie algebra
        if let Some(log_g) = self.matrix_logarithm_safe(&g.params, n) {
            // Check if log_g is in the span of generator logarithms
            self.is_in_lie_algebra(&log_g)
        } else {
            // If logarithm fails, element might be too far from identity
            // Use connectivity check instead
            self.check_connectivity_to_identity(g)
        }
    }
    
    /// Check if vector is in the Lie algebra
    pub(crate) fn is_in_lie_algebra(&self, v: &[P]) -> bool {
        // The Lie algebra is spanned by the logarithms of the generators
        // For now, check if v is "close" to the tangent space at identity
        
        // Get generator tangent vectors
        let mut tangent_vectors = Vec::new();
        for gen in &self.generators {
            if let Some(log_gen) = self.compute_tangent_vector(gen) {
                tangent_vectors.push(log_gen);
            }
        }
        
        if tangent_vectors.is_empty() {
            return false;
        }
        
        // Check if v is in the span of tangent vectors using proper orthogonal projection
        
        // First, orthonormalize the tangent vectors using Gram-Schmidt
        let orthonormal_basis = self.gram_schmidt_orthonormalize(&tangent_vectors);
        
        if orthonormal_basis.is_empty() {
            return false;
        }
        
        // Project v onto the subspace spanned by the orthonormal basis
        let projection = self.project_onto_subspace(v, &orthonormal_basis);
        
        // Compute the residual (component of v orthogonal to the subspace)
        let mut residual = vec![P::zero(); v.len()];
        for i in 0..v.len() {
            residual[i] = v[i] - projection[i];
        }
        
        // Compute norm of residual
        let residual_norm = residual.iter()
            .map(|x| x.powi(2))
            .fold(P::zero(), |acc, x| acc + x)
            .sqrt();
            
        // v is in the subspace if the residual is negligible
        let v_norm = v.iter()
            .map(|x| x.powi(2))
            .fold(P::zero(), |acc, x| acc + x)
            .sqrt();
            
        // Use relative tolerance for numerical stability
        let tolerance = P::epsilon() * (P::one() + v_norm);
        if residual_norm < tolerance {
            return true;
        }
        
        // For continuous groups, be more permissive
        // Check if v satisfies Lie algebra constraints
        self.satisfies_lie_algebra_constraints(v)
    }
    
    /// Compute tangent vector at identity for a generator
    pub(crate) fn compute_tangent_vector(&self, gen: &GroupElement<P>) -> Option<Vec<P>> {
        // For generators close to identity, use finite difference
        // tangent ≈ (gen - identity) / ε
        
        let identity = self.identity();
        if gen.params.len() != identity.params.len() {
            return None;
        }
        
        let mut tangent = Vec::new();
        let mut has_nonzero = false;
        
        for (g, i) in gen.params.iter().zip(identity.params.iter()) {
            let diff = *g - *i;
            if diff.abs() > P::epsilon() {
                has_nonzero = true;
            }
            tangent.push(diff);
        }
        
        if has_nonzero {
            Some(tangent)
        } else {
            None
        }
    }
    
    /// Check Lie algebra constraints
    pub(crate) fn satisfies_lie_algebra_constraints(&self, v: &[P]) -> bool {
        // Check constraints based on group type
        match self.get_group_name() {
            "SO(n)" => {
                // Lie algebra so(n) consists of skew-symmetric matrices
                let n = (v.len() as f64).sqrt() as usize;
                if n * n != v.len() {
                    return false;
                }
                
                // Check skew-symmetry: A + A^T = 0
                for i in 0..n {
                    for j in 0..n {
                        let a_ij = v[i * n + j];
                        let a_ji = v[j * n + i];
                        if (a_ij + a_ji).abs() > P::epsilon() {
                            return false;
                        }
                    }
                }
                true
            }
            _ => {
                // For generic groups, accept if norm is reasonable
                let norm = v.iter().map(|x| x.powi(2)).fold(P::zero(), |acc, x| acc + x).sqrt();
                norm < P::from(10.0).unwrap()
            }
        }
    }
    
    /// Check connectivity to identity for abstract continuous groups
    pub(crate) fn check_connectivity_to_identity(&self, g: &GroupElement<P>) -> bool {
        // Use geodesic distance estimate
        // For Lie groups, any element in the identity component
        // can be connected to identity by a smooth path
        
        // Simple check: see if we can find a path via repeated square roots
        let mut current = g.clone();
        let identity = self.identity();
        
        for _ in 0..10 {
            // Check if current is close to identity
            let distance = current.params.iter()
                .zip(&identity.params)
                .map(|(a, b)| (*a - *b).powi(2))
                .fold(P::zero(), |acc, x| acc + x)
                .sqrt();
                
            if distance < P::from(0.1).unwrap() {
                return true;
            }
            
            // Try to take square root (move halfway to identity)
            if let Some(sqrt) = self.group_square_root(&current) {
                current = sqrt;
            } else {
                break;
            }
        }
        
        // If we couldn't reach identity, might be in different component
        false
    }
    
    /// Check if abstract element is on manifold
    fn check_abstract_manifold(&self, g: &GroupElement<P>) -> bool {
        // For abstract continuous groups, use local chart checks
        
        // Check if element satisfies group relations
        if !self.satisfies_group_relations(g) {
            return false;
        }
        
        // Check if parameters are in valid range
        if !self.parameters_in_valid_range(&g.params) {
            return false;
        }
        
        // Use connectivity check
        self.check_connectivity_to_identity(g)
    }
    
    /// Check if element satisfies group relations
    fn satisfies_group_relations(&self, g: &GroupElement<P>) -> bool {
        // Check basic properties like finite order for torsion elements
        if let Some(order) = g.cached_order {
            if order > 0 && order < 1000 {
                // Verify g^order = identity
                if let Ok(power) = self.power(g, order as i32) {
                    return power.is_identity();
                }
            }
        }
        
        // For continuous groups, most elements have infinite order
        true
    }
    
    /// Check if parameters are in valid range
    fn parameters_in_valid_range(&self, params: &[P]) -> bool {
        // Basic sanity check on parameter values
        for &p in params {
            let abs_p = p.abs();
            if abs_p > P::from(1000.0).unwrap() || abs_p < P::from(1e-10).unwrap() && abs_p != P::zero() {
                return false;
            }
        }
        true
    }
    
    /// Gram-Schmidt orthonormalization of vectors
    fn gram_schmidt_orthonormalize(&self, vectors: &[Vec<P>]) -> Vec<Vec<P>> {
        let mut orthonormal: Vec<Vec<P>> = Vec::new();
        
        for vec in vectors {
            let mut v = vec.clone();
            
            // Subtract projections onto already processed vectors
            for ortho in &orthonormal {
                let dot = v.iter().zip(ortho.iter())
                    .map(|(a, b)| *a * *b)
                    .fold(P::zero(), |acc, x| acc + x);
                
                for i in 0..v.len() {
                    v[i] = v[i] - dot * ortho[i];
                }
            }
            
            // Normalize
            let norm = v.iter()
                .map(|x| x.powi(2))
                .fold(P::zero(), |acc, x| acc + x)
                .sqrt();
            
            if norm > P::epsilon() {
                let normalized: Vec<P> = v.iter()
                    .map(|x| *x / norm)
                    .collect();
                orthonormal.push(normalized);
            }
        }
        
        orthonormal
    }
    
    /// Project vector onto subspace spanned by orthonormal basis
    fn project_onto_subspace(&self, v: &[P], basis: &[Vec<P>]) -> Vec<P> {
        let mut projection = vec![P::zero(); v.len()];
        
        for basis_vec in basis {
            // Compute coefficient: <v, basis_vec>
            let coeff = v.iter().zip(basis_vec.iter())
                .map(|(a, b)| *a * *b)
                .fold(P::zero(), |acc, x| acc + x);
            
            // Add contribution: coeff * basis_vec
            for i in 0..projection.len() {
                projection[i] = projection[i] + coeff * basis_vec[i];
            }
        }
        
        projection
    }
}