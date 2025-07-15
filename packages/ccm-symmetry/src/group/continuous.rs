//! Continuous group implementations (Lie groups)
//! 
//! This module handles continuous groups such as:
//! - Special orthogonal group SO(n)
//! - Special unitary group SU(n)
//! - General linear group GL(n)
//! - Symplectic group Sp(n)

use num_traits::Float;
use crate::group::{GroupElement, SymmetryGroup, GroupType};
use crate::SymmetryError;
use ccm_core::CcmError;

/// Trait for continuous group operations
pub trait ContinuousGroup<P: Float> {
    /// Get the Lie algebra of the group
    fn lie_algebra_dimension(&self) -> usize;
    
    /// Exponential map from Lie algebra to group
    fn exponential_map(&self, algebra_element: &[P]) -> GroupElement<P>;
    
    /// Logarithm map from group to Lie algebra
    fn logarithm_map(&self, group_element: &GroupElement<P>) -> Option<Vec<P>>;
}

impl<P: Float> ContinuousGroup<P> for SymmetryGroup<P> {
    /// Get the Lie algebra of the group
    fn lie_algebra_dimension(&self) -> usize {
        match &self.group_type {
            GroupType::Continuous => {
                // For matrix groups, compute based on type
                let n = (self.dimension as f64).sqrt() as usize;
                if n * n == self.dimension {
                    // This is a matrix group
                    
                    // Detect the specific type of matrix group
                    if self.is_special_orthogonal_group(n) {
                        // SO(n) has dimension n(n-1)/2
                        n * (n - 1) / 2
                    } else if self.is_special_unitary_group(n) {
                        // SU(n) has dimension n²-1
                        n * n - 1
                    } else if self.is_general_linear_group(n) {
                        // GL(n) has dimension n²
                        n * n
                    } else if self.is_symplectic_group(n) {
                        // Sp(2n) has dimension n(2n+1)
                        // Note: n here is the matrix dimension, so for Sp(2n) we have n/2
                        if n % 2 == 0 {
                            let n_half = n / 2;
                            n_half * (n + 1)
                        } else {
                            // Not a valid symplectic group dimension
                            self.generators.len()
                        }
                    } else {
                        // Unknown matrix group type, use generator count
                        self.generators.len()
                    }
                } else {
                    // Non-matrix continuous group
                    self.generators.len()
                }
            }
            _ => 0,
        }
    }
    
    /// Exponential map from Lie algebra to group
    fn exponential_map(&self, algebra_element: &[P]) -> GroupElement<P> {
        // Use the exponential_map method from stabilizer module
        match self.exponential_map(algebra_element, P::one()) {
            Ok(element) => element,
            Err(_) => self.identity(),
        }
    }
    
    /// Logarithm map from group to Lie algebra
    fn logarithm_map(&self, group_element: &GroupElement<P>) -> Option<Vec<P>> {
        match &self.group_type {
            GroupType::Continuous => {
                // Detect if this is a matrix group
                let n_sq = (self.dimension as f64).sqrt() as usize;
                
                if n_sq * n_sq == self.dimension {
                    // This is a matrix group
                    match n_sq {
                        2 => {
                            // Use specialized 2x2 matrix logarithm
                            self.matrix_log_2x2(&group_element.params)
                        }
                        3 => {
                            // Use specialized 3x3 matrix logarithm
                            self.matrix_log_3x3(&group_element.params)
                        }
                        _ => {
                            // For larger matrices, use general algorithm
                            self.matrix_logarithm_general(&group_element.params, n_sq)
                        }
                    }
                } else {
                    // Non-matrix continuous group
                    // For elements close to identity, approximate log(I + X) ≈ X
                    let identity = self.identity();
                    let distance = group_element.params.iter()
                        .zip(identity.params.iter())
                        .map(|(a, b)| (*a - *b).powi(2))
                        .fold(P::zero(), |acc, x| acc + x)
                        .sqrt();
                        
                    if distance > P::one() {
                        // Too far from identity for simple approximation
                        return None;
                    }
                    
                    // Return X = g - I
                    let lie_element: Vec<P> = group_element.params.iter()
                        .zip(identity.params.iter())
                        .map(|(g, e)| *g - *e)
                        .collect();
                        
                    Some(lie_element)
                }
            }
            _ => None, // Not a continuous group
        }
    }
    
}

impl<P: Float> SymmetryGroup<P> {
    /// Check if this is a special orthogonal group SO(n)
    fn is_special_orthogonal_group(&self, n: usize) -> bool {
        if self.generators.is_empty() {
            return false;
        }
        
        // SO(n) generators are skew-symmetric matrices
        // Check if all generators satisfy A^T = -A
        for gen in &self.generators {
            if !self.is_skew_symmetric_matrix(&gen.params, n) {
                return false;
            }
        }
        
        // Check if we have the right number of generators
        let expected_dim = n * (n - 1) / 2;
        self.generators.len() == expected_dim
    }
    
    /// Check if this is a special unitary group SU(n)
    fn is_special_unitary_group(&self, n: usize) -> bool {
        if self.generators.is_empty() {
            return false;
        }
        
        // SU(n) generators are traceless anti-Hermitian matrices
        // For real representation, they appear as pairs (real, imaginary)
        if self.dimension != 2 * n * n {
            return false; // Need complex representation
        }
        
        // Check if we have the right number of generators
        let expected_dim = n * n - 1;
        self.generators.len() == expected_dim
    }
    
    /// Check if this is a general linear group GL(n)
    fn is_general_linear_group(&self, n: usize) -> bool {
        // GL(n) has dimension n² and includes all invertible matrices
        // Generators can be any linearly independent set of matrices
        self.generators.len() == n * n
    }
    
    /// Check if this is a symplectic group Sp(2n)
    fn is_symplectic_group(&self, n: usize) -> bool {
        if n % 2 != 0 {
            return false; // Symplectic groups have even dimension
        }
        
        // Sp(2n) preserves a symplectic form
        // Generators satisfy J^T Ω + Ω J = 0 where Ω is the symplectic form
        let n_half = n / 2;
        let expected_dim = n_half * (n + 1);
        self.generators.len() == expected_dim
    }
    
    /// Check if a matrix is skew-symmetric
    fn is_skew_symmetric_matrix(&self, matrix: &[P], n: usize) -> bool {
        if matrix.len() != n * n {
            return false;
        }
        
        let tolerance = P::epsilon() * P::from(10.0).unwrap();
        
        for i in 0..n {
            for j in 0..n {
                let a_ij = matrix[i * n + j];
                let a_ji = matrix[j * n + i];
                
                if i == j {
                    // Diagonal elements must be zero
                    if a_ij.abs() > tolerance {
                        return false;
                    }
                } else {
                    // Off-diagonal: A[i,j] = -A[j,i]
                    if (a_ij + a_ji).abs() > tolerance {
                        return false;
                    }
                }
            }
        }
        
        true
    }
    
    /// Generate the special orthogonal group SO(n)
    /// 
    /// SO(n) is the group of n×n orthogonal matrices with determinant 1.
    /// It represents rotations in n-dimensional space.
    pub fn so(n: usize) -> Result<Self, CcmError> {
        if n == 0 {
            return Err(SymmetryError::InvalidGroupOperation.into());
        }
        
        let mut group = Self::generate(n * n)?; // Matrix representation
        
        // Lie algebra dimension: n(n-1)/2
        let _lie_dim = n * (n - 1) / 2;
        
        // Generate standard basis for so(n) Lie algebra
        // These are skew-symmetric matrices
        let mut generators = Vec::new();
        let mut _gen_idx = 0;
        
        for i in 0..n {
            for j in (i + 1)..n {
                // E_ij - E_ji generator (skew-symmetric)
                let mut params = vec![P::zero(); n * n];
                params[i * n + j] = P::one();
                params[j * n + i] = -P::one();
                
                generators.push(GroupElement {
                    params,
                    cached_order: None, // Continuous group
                });
                _gen_idx += 1;
            }
        }
        
        group.generators = generators;
        group.group_type = GroupType::Continuous;
        group.cached_order = None; // Infinite
        
        Ok(group)
    }
    
    /// Generate the special unitary group SU(n)
    /// 
    /// SU(n) is the group of n×n unitary matrices with determinant 1.
    /// It represents symmetries that preserve complex inner products.
    pub fn su(n: usize) -> Result<Self, CcmError> {
        if n == 0 {
            return Err(SymmetryError::InvalidGroupOperation.into());
        }
        
        // For complex matrices, we need 2n² real parameters
        // (real and imaginary parts for each complex entry)
        let mut group = Self::generate(2 * n * n)?;
        
        // Lie algebra dimension: n² - 1
        // Generators are traceless Hermitian matrices
        
        let mut generators = Vec::new();
        
        match n {
            1 => {
                // SU(1) is trivial (just the identity)
                // No generators needed
            }
            2 => {
                // SU(2) - use Pauli matrices
                generators.extend(Self::pauli_matrices());
            }
            3 => {
                // SU(3) - use Gell-Mann matrices
                generators.extend(Self::gell_mann_matrices());
            }
            _ => {
                // General SU(n) - generalized Gell-Mann matrices
                generators.extend(Self::generalized_gell_mann_matrices(n));
            }
        }
        
        group.generators = generators;
        group.group_type = GroupType::Continuous;
        group.cached_order = None; // Infinite
        
        Ok(group)
    }
    
    /// Generate Pauli matrices for SU(2)
    /// 
    /// These are the standard generators:
    /// σ₁ = [[0, 1], [1, 0]]
    /// σ₂ = [[0, -i], [i, 0]]
    /// σ₃ = [[1, 0], [0, -1]]
    fn pauli_matrices() -> Vec<GroupElement<P>> {
        let mut generators = Vec::new();
        
        // σ₁ (sigma_x)
        // Real part: [[0, 1], [1, 0]]
        // Imaginary part: [[0, 0], [0, 0]]
        let mut params1 = vec![P::zero(); 8];
        params1[2] = P::one();  // Real[0,1] = 1
        params1[4] = P::one();  // Real[1,0] = 1
        generators.push(GroupElement {
            params: params1,
            cached_order: None,
        });
        
        // σ₂ (sigma_y)
        // Real part: [[0, 0], [0, 0]]
        // Imaginary part: [[0, -1], [1, 0]]
        let mut params2 = vec![P::zero(); 8];
        params2[3] = -P::one(); // Imag[0,1] = -1
        params2[5] = P::one();  // Imag[1,0] = 1
        generators.push(GroupElement {
            params: params2,
            cached_order: None,
        });
        
        // σ₃ (sigma_z)
        // Real part: [[1, 0], [0, -1]]
        // Imaginary part: [[0, 0], [0, 0]]
        let mut params3 = vec![P::zero(); 8];
        params3[0] = P::one();   // Real[0,0] = 1
        params3[6] = -P::one();  // Real[1,1] = -1
        generators.push(GroupElement {
            params: params3,
            cached_order: None,
        });
        
        generators
    }
    
    /// Generate Gell-Mann matrices for SU(3)
    /// 
    /// These are the 8 standard generators of SU(3),
    /// analogous to Pauli matrices for SU(2)
    fn gell_mann_matrices() -> Vec<GroupElement<P>> {
        let mut generators = Vec::new();
        
        // λ₁ - similar to Pauli σ₁
        let mut params1 = vec![P::zero(); 18]; // 2*3*3
        params1[2] = P::one();  // Real[0,1] = 1
        params1[6] = P::one();  // Real[1,0] = 1
        generators.push(GroupElement {
            params: params1,
            cached_order: None,
        });
        
        // λ₂ - similar to Pauli σ₂
        let mut params2 = vec![P::zero(); 18];
        params2[3] = -P::one(); // Imag[0,1] = -1
        params2[7] = P::one();  // Imag[1,0] = 1
        generators.push(GroupElement {
            params: params2,
            cached_order: None,
        });
        
        // λ₃ - similar to Pauli σ₃
        let mut params3 = vec![P::zero(); 18];
        params3[0] = P::one();   // Real[0,0] = 1
        params3[8] = -P::one();  // Real[1,1] = -1
        generators.push(GroupElement {
            params: params3,
            cached_order: None,
        });
        
        // λ₄
        let mut params4 = vec![P::zero(); 18];
        params4[4] = P::one();   // Real[0,2] = 1
        params4[12] = P::one();  // Real[2,0] = 1
        generators.push(GroupElement {
            params: params4,
            cached_order: None,
        });
        
        // λ₅
        let mut params5 = vec![P::zero(); 18];
        params5[5] = -P::one();  // Imag[0,2] = -1
        params5[13] = P::one();  // Imag[2,0] = 1
        generators.push(GroupElement {
            params: params5,
            cached_order: None,
        });
        
        // λ₆
        let mut params6 = vec![P::zero(); 18];
        params6[10] = P::one();  // Real[1,2] = 1
        params6[14] = P::one();  // Real[2,1] = 1
        generators.push(GroupElement {
            params: params6,
            cached_order: None,
        });
        
        // λ₇
        let mut params7 = vec![P::zero(); 18];
        params7[11] = -P::one(); // Imag[1,2] = -1
        params7[15] = P::one();  // Imag[2,1] = 1
        generators.push(GroupElement {
            params: params7,
            cached_order: None,
        });
        
        // λ₈ - diagonal, traceless
        let sqrt3 = P::from(3.0).unwrap().sqrt();
        let mut params8 = vec![P::zero(); 18];
        params8[0] = P::one() / sqrt3;      // Real[0,0] = 1/√3
        params8[8] = P::one() / sqrt3;      // Real[1,1] = 1/√3
        params8[16] = -P::from(2.0).unwrap() / sqrt3; // Real[2,2] = -2/√3
        generators.push(GroupElement {
            params: params8,
            cached_order: None,
        });
        
        generators
    }
    
    /// Generate generalized Gell-Mann matrices for SU(n)
    /// 
    /// For n > 3, we use a systematic construction:
    /// 1. Symmetric matrices: (E_ij + E_ji) for i < j
    /// 2. Antisymmetric matrices: i(E_ij - E_ji) for i < j
    /// 3. Diagonal matrices: generalized λ₈ pattern
    fn generalized_gell_mann_matrices(n: usize) -> Vec<GroupElement<P>> {
        let mut generators = Vec::new();
        let param_size = 2 * n * n; // Real and imaginary parts
        
        // Type 1: Symmetric generators (real off-diagonal)
        for i in 0..n {
            for j in (i + 1)..n {
                let mut params = vec![P::zero(); param_size];
                // Real part: E_ij + E_ji
                params[2 * (i * n + j)] = P::one();     // Real[i,j] = 1
                params[2 * (j * n + i)] = P::one();     // Real[j,i] = 1
                generators.push(GroupElement {
                    params,
                    cached_order: None,
                });
            }
        }
        
        // Type 2: Antisymmetric generators (imaginary off-diagonal)
        for i in 0..n {
            for j in (i + 1)..n {
                let mut params = vec![P::zero(); param_size];
                // Imaginary part: i(E_ij - E_ji)
                params[2 * (i * n + j) + 1] = -P::one(); // Imag[i,j] = -1
                params[2 * (j * n + i) + 1] = P::one();  // Imag[j,i] = 1
                generators.push(GroupElement {
                    params,
                    cached_order: None,
                });
            }
        }
        
        // Type 3: Diagonal generators (traceless)
        // We need n-1 diagonal generators
        for l in 1..n {
            let mut params = vec![P::zero(); param_size];
            
            // Normalization factor
            let norm = (P::from(2.0).unwrap() / (P::from(l).unwrap() * (P::from(l + 1).unwrap()))).sqrt();
            
            // First l entries get 1/sqrt(l(l+1))
            for k in 0..l {
                params[2 * (k * n + k)] = norm / P::from(2.0).unwrap().sqrt();
            }
            
            // The l-th entry gets -l/sqrt(l(l+1))
            params[2 * (l * n + l)] = -P::from(l).unwrap() * norm / P::from(2.0).unwrap().sqrt();
            
            generators.push(GroupElement {
                params,
                cached_order: None,
            });
        }
        
        generators
    }
}