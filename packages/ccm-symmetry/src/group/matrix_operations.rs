//! Matrix operations for group computations
//! 
//! This module provides matrix operations used by symmetry groups,
//! including determinant, multiplication, logarithm, and exponential.

use num_traits::Float;
use num_complex::Complex;
use crate::group::{GroupElement, SymmetryGroup};

impl<P: Float> SymmetryGroup<P> {
    /// Compute determinant of n×n matrix stored as flat array
    pub fn compute_determinant(&self, matrix: &[P], n: usize) -> Option<P> {
        if matrix.len() != n * n {
            return None;
        }
        
        if n == 0 {
            return Some(P::one());
        }
        
        if n == 1 {
            return Some(matrix[0]);
        }
        
        if n == 2 {
            // 2×2 determinant: ad - bc
            return Some(matrix[0] * matrix[3] - matrix[1] * matrix[2]);
        }
        
        if n == 3 {
            // 3×3 determinant using rule of Sarrus
            let a = matrix[0] * (matrix[4] * matrix[8] - matrix[5] * matrix[7]);
            let b = matrix[1] * (matrix[5] * matrix[6] - matrix[3] * matrix[8]);
            let c = matrix[2] * (matrix[3] * matrix[7] - matrix[4] * matrix[6]);
            return Some(a - b + c);
        }
        
        // For larger matrices, use LU decomposition
        // Copy matrix since we'll modify it
        let mut work_matrix = matrix.to_vec();
        let mut det = P::one();
        let mut pivot_sign = 1i32;
        
        // Gaussian elimination with partial pivoting
        for i in 0..n {
            // Find pivot
            let mut max_val = P::zero();
            let mut max_row = i;
            
            for k in i..n {
                let val = work_matrix[k * n + i].abs();
                if val > max_val {
                    max_val = val;
                    max_row = k;
                }
            }
            
            // Check for zero pivot (singular matrix)
            if max_val < P::epsilon() {
                return Some(P::zero());
            }
            
            // Swap rows if needed
            if max_row != i {
                for j in 0..n {
                    let idx1 = i * n + j;
                    let idx2 = max_row * n + j;
                    work_matrix.swap(idx1, idx2);
                }
                pivot_sign = -pivot_sign;
            }
            
            let pivot = work_matrix[i * n + i];
            det = det * pivot;
            
            // Eliminate column below pivot
            for k in (i + 1)..n {
                let factor = work_matrix[k * n + i] / pivot;
                for j in i..n {
                    let idx = k * n + j;
                    work_matrix[idx] = work_matrix[idx] - factor * work_matrix[i * n + j];
                }
            }
        }
        
        // Apply sign from row swaps
        if pivot_sign < 0 {
            det = -det;
        }
        
        Some(det)
    }
    
    /// Matrix multiplication helper
    pub(crate) fn matrix_multiply(&self, a: &[P], b: &[P], n: usize) -> Option<Vec<P>> {
        if a.len() != n * n || b.len() != n * n {
            return None;
        }
        
        let mut result = vec![P::zero(); n * n];
        
        for i in 0..n {
            for j in 0..n {
                let mut sum = P::zero();
                for k in 0..n {
                    sum = sum + a[i * n + k] * b[k * n + j];
                }
                result[i * n + j] = sum;
            }
        }
        
        Some(result)
    }
    
    /// Safe matrix logarithm that handles edge cases
    pub(crate) fn matrix_logarithm_safe(&self, matrix: &[P], n: usize) -> Option<Vec<P>> {
        if matrix.len() != n * n {
            return None;
        }
        
        // Check if matrix is close to identity
        let mut max_deviation = P::zero();
        for i in 0..n {
            for j in 0..n {
                let expected = if i == j { P::one() } else { P::zero() };
                let deviation = (matrix[i * n + j] - expected).abs();
                if deviation > max_deviation {
                    max_deviation = deviation;
                }
            }
        }
        
        // If close to identity, use power series
        if max_deviation < P::from(0.5).unwrap() {
            // log(I + A) = A - A²/2 + A³/3 - ...
            let mut log_matrix = vec![P::zero(); n * n];
            let mut a_power = vec![P::zero(); n * n];
            
            // A = M - I
            for i in 0..n {
                for j in 0..n {
                    let idx = i * n + j;
                    a_power[idx] = matrix[idx] - if i == j { P::one() } else { P::zero() };
                }
            }
            
            // Copy A as first term
            for i in 0..n * n {
                log_matrix[i] = a_power[i];
            }
            
            // Power series expansion
            let mut current_power = a_power.clone();
            for k in 2..10 {
                // Compute A^k = A^(k-1) * A
                let next_power = self.matrix_multiply(&current_power, &a_power, n)?;
                
                // Add (-1)^(k+1) * A^k / k
                let sign = if k % 2 == 0 { -P::one() } else { P::one() };
                let factor = sign / P::from(k).unwrap();
                
                for i in 0..n * n {
                    log_matrix[i] = log_matrix[i] + factor * next_power[i];
                }
                
                current_power = next_power;
                
                // Check convergence
                let norm = current_power.iter()
                    .map(|x| x.powi(2))
                    .fold(P::zero(), |acc, x| acc + x)
                    .sqrt();
                    
                if norm < P::epsilon() {
                    break;
                }
            }
            
            Some(log_matrix)
        } else {
            // Matrix too far from identity for power series
            // Try eigenvalue decomposition for specific cases
            if n == 2 {
                self.matrix_log_2x2(matrix)
            } else if n == 3 {
                self.matrix_log_3x3(matrix)
            } else {
                None
            }
        }
    }
    
    /// Matrix logarithm for 2x2 matrices
    pub(crate) fn matrix_log_2x2(&self, matrix: &[P]) -> Option<Vec<P>> {
        let a = matrix[0];
        let b = matrix[1];
        let c = matrix[2];
        let d = matrix[3];
        
        // For SO(2), matrix is [[cos θ, -sin θ], [sin θ, cos θ]]
        // Check if it's a rotation matrix
        let det = a * d - b * c;
        if (det - P::one()).abs() > P::epsilon() {
            return None;
        }
        
        // Check orthogonality
        if (a * a + c * c - P::one()).abs() > P::epsilon() ||
           (b * b + d * d - P::one()).abs() > P::epsilon() {
            return None;
        }
        
        // Extract angle
        let cos_theta = a;
        let sin_theta = c;
        let theta = sin_theta.atan2(cos_theta);
        
        // Log of rotation matrix is [[0, -θ], [θ, 0]]
        Some(vec![P::zero(), -theta, theta, P::zero()])
    }
    
    /// Matrix logarithm for 3x3 matrices
    pub(crate) fn matrix_log_3x3(&self, matrix: &[P]) -> Option<Vec<P>> {
        // For SO(3), use Rodrigues' formula in reverse
        // R = I + sin(θ)K + (1-cos(θ))K²
        // where K is the skew-symmetric matrix of the axis
        
        // First check if it's a valid rotation
        if !self.is_rotation_matrix_3x3(matrix) {
            return None;
        }
        
        // Compute trace to find angle
        let trace = matrix[0] + matrix[4] + matrix[8];
        let cos_theta = (trace - P::one()) / P::from(2.0).unwrap();
        
        // Handle special cases
        if (cos_theta - P::one()).abs() < P::epsilon() {
            // Identity rotation
            return Some(vec![P::zero(); 9]);
        }
        
        if (cos_theta + P::one()).abs() < P::epsilon() {
            // 180-degree rotation (θ = π)
            // For a 180-degree rotation, R = 2nn^T - I where n is the rotation axis
            // We need to find the axis by solving (R + I)n = 2nn^T n = 2n
            
            // R + I should have rank 1, and its non-zero column gives us the axis
            let r_plus_i = vec![
                matrix[0] + P::one(), matrix[1], matrix[2],
                matrix[3], matrix[4] + P::one(), matrix[5],
                matrix[6], matrix[7], matrix[8] + P::one()
            ];
            
            // Find the column with largest norm in R + I
            let mut max_norm = P::zero();
            let mut axis_idx = 0;
            
            for j in 0..3 {
                let col_norm = (r_plus_i[j].powi(2) + 
                               r_plus_i[3 + j].powi(2) + 
                               r_plus_i[6 + j].powi(2)).sqrt();
                if col_norm > max_norm {
                    max_norm = col_norm;
                    axis_idx = j;
                }
            }
            
            if max_norm < P::epsilon() {
                // This shouldn't happen for a valid 180-degree rotation
                return None;
            }
            
            // Extract and normalize the axis
            let mut axis = vec![
                r_plus_i[axis_idx],
                r_plus_i[3 + axis_idx], 
                r_plus_i[6 + axis_idx]
            ];
            
            // Normalize the axis
            let axis_norm = (axis[0].powi(2) + axis[1].powi(2) + axis[2].powi(2)).sqrt();
            axis[0] = axis[0] / axis_norm;
            axis[1] = axis[1] / axis_norm;
            axis[2] = axis[2] / axis_norm;
            
            // For 180-degree rotation, θ = π
            let theta = P::from(std::f64::consts::PI).unwrap();
            
            // Build the logarithm: log(R) = θ * K where K is skew-symmetric from axis
            let log_matrix = vec![
                P::zero(), -axis[2] * theta, axis[1] * theta,
                axis[2] * theta, P::zero(), -axis[0] * theta,
                -axis[1] * theta, axis[0] * theta, P::zero()
            ];
            
            return Some(log_matrix);
        }
        
        // General case: extract axis from skew-symmetric part
        let theta = cos_theta.acos();
        let sin_theta = theta.sin();
        
        if sin_theta.abs() < P::epsilon() {
            return None;
        }
        
        // Extract skew-symmetric part: K = (R - R^T) / (2 sin θ)
        let factor = P::one() / (P::from(2.0).unwrap() * sin_theta);
        
        let k01 = (matrix[1] - matrix[3]) * factor;
        let k02 = (matrix[2] - matrix[6]) * factor;
        let k12 = (matrix[5] - matrix[7]) * factor;
        
        // Scale by angle to get log
        let log_matrix = vec![
            P::zero(), -k01 * theta, k02 * theta,
            k01 * theta, P::zero(), -k12 * theta,
            -k02 * theta, k12 * theta, P::zero()
        ];
        
        Some(log_matrix)
    }
    
    /// Check if 3x3 matrix is a rotation
    pub fn is_rotation_matrix_3x3(&self, matrix: &[P]) -> bool {
        // Check orthogonality: R^T * R = I
        // This means checking dot products of rows with rows
        let tolerance = P::epsilon() * P::from(100.0).unwrap(); // More relaxed tolerance for numerical stability
        
        for i in 0..3 {
            for j in 0..3 {
                let mut sum = P::zero();
                for k in 0..3 {
                    // Row i dot row j
                    sum = sum + matrix[i * 3 + k] * matrix[j * 3 + k];
                }
                let expected = if i == j { P::one() } else { P::zero() };
                if (sum - expected).abs() > tolerance {
                    return false;
                }
            }
        }
        
        // Check determinant (should be exactly +1 for SO(3))
        self.compute_determinant(matrix, 3)
            .map(|det| {
                // Accept both +1 and values very close to +1
                let det_check = (det - P::one()).abs() < tolerance;
                det_check
            })
            .unwrap_or(false)
    }
    
    /// Matrix square root for small matrices
    pub(crate) fn matrix_square_root(&self, matrix: &[P], n: usize) -> Option<Vec<P>> {
        if matrix.len() != n * n {
            return None;
        }
        
        if n == 2 {
            // For 2x2 rotation matrices
            if let Some(log_m) = self.matrix_log_2x2(matrix) {
                // sqrt(M) = exp(log(M)/2)
                let half_log: Vec<P> = log_m.iter().map(|x| *x / P::from(2.0).unwrap()).collect();
                self.matrix_exp_2x2(&half_log)
            } else {
                None
            }
        } else if n == 3 {
            // For 3x3 matrices, use eigenvalue decomposition approach
            self.matrix_sqrt_3x3(matrix)
        } else {
            // For larger matrices, use general eigenvalue decomposition
            self.matrix_sqrt_general(matrix, n)
        }
    }
    
    /// Matrix square root for 3x3 matrices
    pub(crate) fn matrix_sqrt_3x3(&self, matrix: &[P]) -> Option<Vec<P>> {
        // For 3x3 symmetric positive definite matrices, we can use the spectral decomposition
        // For rotation matrices, we can use the matrix logarithm approach
        
        // First check if it's a rotation matrix
        if self.is_rotation_matrix_3x3(matrix) {
            // Use logarithm approach: sqrt(R) = exp(log(R)/2)
            if let Some(log_m) = self.matrix_log_3x3(matrix) {
                let half_log: Vec<P> = log_m.iter().map(|x| *x / P::from(2.0).unwrap()).collect();
                return self.matrix_exp_3x3(&half_log);
            }
        }
        
        // For general 3x3 matrices, use Denman-Beavers iteration
        self.matrix_sqrt_denman_beavers(matrix, 3)
    }
    
    /// Matrix square root for general n×n matrices
    pub(crate) fn matrix_sqrt_general(&self, matrix: &[P], n: usize) -> Option<Vec<P>> {
        // For general matrices, use iterative methods
        // We'll use the Denman-Beavers iteration which is quadratically convergent
        
        // First check if matrix is positive definite
        if !self.is_positive_definite(matrix, n) {
            return None;
        }
        
        self.matrix_sqrt_denman_beavers(matrix, n)
    }
    
    /// Denman-Beavers iteration for matrix square root
    /// Converges quadratically for matrices with positive eigenvalues
    pub(crate) fn matrix_sqrt_denman_beavers(&self, matrix: &[P], n: usize) -> Option<Vec<P>> {
        // Initialize Y₀ = A, Z₀ = I
        let mut y = matrix.to_vec();
        let mut z = vec![P::zero(); n * n];
        
        // Initialize Z to identity
        for i in 0..n {
            z[i * n + i] = P::one();
        }
        
        let max_iterations = 20;
        let tolerance = P::epsilon() * P::from(10.0).unwrap();
        
        for _iteration in 0..max_iterations {
            // Compute Y_{k+1} = (Y_k + Z_k^{-1}) / 2
            // Compute Z_{k+1} = (Z_k + Y_k^{-1}) / 2
            
            // Invert Y_k
            let y_inv = self.matrix_inverse(&y, n)?;
            
            // Invert Z_k
            let z_inv = self.matrix_inverse(&z, n)?;
            
            // New Y = (Y + Z^{-1}) / 2
            let mut new_y = vec![P::zero(); n * n];
            for i in 0..n * n {
                new_y[i] = (y[i] + z_inv[i]) / P::from(2.0).unwrap();
            }
            
            // New Z = (Z + Y^{-1}) / 2
            let mut new_z = vec![P::zero(); n * n];
            for i in 0..n * n {
                new_z[i] = (z[i] + y_inv[i]) / P::from(2.0).unwrap();
            }
            
            // Check convergence
            let mut max_change = P::zero();
            for i in 0..n * n {
                let change = (new_y[i] - y[i]).abs();
                if change > max_change {
                    max_change = change;
                }
            }
            
            y = new_y;
            z = new_z;
            
            if max_change < tolerance {
                // Verify: Y * Y ≈ A
                if let Some(y_squared) = self.matrix_multiply(&y, &y, n) {
                    let mut max_error = P::zero();
                    for i in 0..n * n {
                        let error = (y_squared[i] - matrix[i]).abs();
                        if error > max_error {
                            max_error = error;
                        }
                    }
                    
                    if max_error < tolerance * P::from(100.0).unwrap() {
                        return Some(y);
                    }
                }
            }
        }
        
        None
    }
    
    /// Check if matrix is positive definite
    pub(crate) fn is_positive_definite(&self, matrix: &[P], n: usize) -> bool {
        // For positive definiteness, all leading principal minors must be positive
        // We'll use Sylvester's criterion
        
        for k in 1..=n {
            // Extract k×k leading principal submatrix
            let mut submatrix = vec![P::zero(); k * k];
            for i in 0..k {
                for j in 0..k {
                    submatrix[i * k + j] = matrix[i * n + j];
                }
            }
            
            // Compute determinant of submatrix
            if let Some(det) = self.compute_determinant(&submatrix, k) {
                if det <= P::zero() {
                    return false;
                }
            } else {
                return false;
            }
        }
        
        true
    }
    
    /// Matrix inversion using Gauss-Jordan elimination
    pub(crate) fn matrix_inverse(&self, matrix: &[P], n: usize) -> Option<Vec<P>> {
        if matrix.len() != n * n {
            return None;
        }
        
        // Create augmented matrix [A | I]
        let mut augmented = vec![P::zero(); n * n * 2];
        
        // Copy matrix to left half
        for i in 0..n {
            for j in 0..n {
                augmented[i * 2 * n + j] = matrix[i * n + j];
            }
        }
        
        // Set right half to identity
        for i in 0..n {
            augmented[i * 2 * n + n + i] = P::one();
        }
        
        // Perform Gauss-Jordan elimination
        for i in 0..n {
            // Find pivot
            let mut max_val = P::zero();
            let mut max_row = i;
            
            for k in i..n {
                let val = augmented[k * 2 * n + i].abs();
                if val > max_val {
                    max_val = val;
                    max_row = k;
                }
            }
            
            if max_val < P::epsilon() {
                return None; // Singular matrix
            }
            
            // Swap rows
            if max_row != i {
                for j in 0..2 * n {
                    let idx1 = i * 2 * n + j;
                    let idx2 = max_row * 2 * n + j;
                    let temp = augmented[idx1];
                    augmented[idx1] = augmented[idx2];
                    augmented[idx2] = temp;
                }
            }
            
            // Scale pivot row
            let pivot = augmented[i * 2 * n + i];
            for j in 0..2 * n {
                augmented[i * 2 * n + j] = augmented[i * 2 * n + j] / pivot;
            }
            
            // Eliminate column
            for k in 0..n {
                if k != i {
                    let factor = augmented[k * 2 * n + i];
                    for j in 0..2 * n {
                        augmented[k * 2 * n + j] = augmented[k * 2 * n + j] - factor * augmented[i * 2 * n + j];
                    }
                }
            }
        }
        
        // Extract inverse from right half
        let mut inverse = vec![P::zero(); n * n];
        for i in 0..n {
            for j in 0..n {
                inverse[i * n + j] = augmented[i * 2 * n + n + j];
            }
        }
        
        Some(inverse)
    }
    
    /// Matrix exponential for 3x3 skew-symmetric matrices  
    pub(crate) fn matrix_exp_3x3(&self, log_matrix: &[P]) -> Option<Vec<P>> {
        if log_matrix.len() != 9 {
            return None;
        }
        
        // For skew-symmetric matrices, use Rodrigues' formula
        // exp(K) = I + sin(θ)K + (1-cos(θ))K²
        // where K is the skew-symmetric matrix and θ = ||k|| where k is the axial vector
        
        // Extract axial vector from skew-symmetric matrix
        let k1 = log_matrix[5];  // (2,1) element
        let k2 = -log_matrix[2]; // -(0,2) element  
        let k3 = log_matrix[1];  // (0,1) element
        
        let theta = (k1 * k1 + k2 * k2 + k3 * k3).sqrt();
        
        if theta < P::epsilon() {
            // Close to identity
            let mut result = vec![P::zero(); 9];
            for i in 0..3 {
                result[i * 3 + i] = P::one();
            }
            return Some(result);
        }
        
        // Normalize k
        let k1 = k1 / theta;
        let k2 = k2 / theta;
        let k3 = k3 / theta;
        
        // Build K matrix (normalized)
        let k_matrix = vec![
            P::zero(), -k3, k2,
            k3, P::zero(), -k1,
            -k2, k1, P::zero()
        ];
        
        // Compute K²
        let k_squared = self.matrix_multiply(&k_matrix, &k_matrix, 3)?;
        
        // Apply Rodrigues' formula
        let sin_theta = theta.sin();
        let one_minus_cos = P::one() - theta.cos();
        
        let mut result = vec![P::zero(); 9];
        
        // I + sin(θ)K + (1-cos(θ))K²
        for i in 0..9 {
            result[i] = sin_theta * k_matrix[i] + one_minus_cos * k_squared[i];
        }
        
        // Add identity
        for i in 0..3 {
            result[i * 3 + i] = result[i * 3 + i] + P::one();
        }
        
        Some(result)
    }
    
    /// Matrix exponential for 2x2 skew-symmetric matrices
    pub(crate) fn matrix_exp_2x2(&self, log_matrix: &[P]) -> Option<Vec<P>> {
        if log_matrix.len() != 4 {
            return None;
        }
        
        // For skew-symmetric [[0, -θ], [θ, 0]]
        let theta = log_matrix[2];
        let cos_theta = theta.cos();
        let sin_theta = theta.sin();
        
        Some(vec![cos_theta, -sin_theta, sin_theta, cos_theta])
    }
    
    /// Compute square root of group element if possible
    pub(crate) fn group_square_root(&self, g: &GroupElement<P>) -> Option<GroupElement<P>> {
        // For matrix groups, compute matrix square root
        // For abstract groups, use parametrization
        
        match self.get_representation() {
            GroupRepresentation::Matrix(n) => {
                // Now we can handle matrices of any size
                self.matrix_square_root(&g.params, n)
                    .map(|params| GroupElement { params, cached_order: None })
            }
            GroupRepresentation::Abstract => {
                // For abstract groups, try parameter interpolation
                let identity = self.identity();
                let mut sqrt_params = Vec::new();
                
                for (g_param, id_param) in g.params.iter().zip(&identity.params) {
                    // Interpolate halfway between g and identity
                    sqrt_params.push((*g_param + *id_param) / P::from(2.0).unwrap());
                }
                
                Some(GroupElement {
                    params: sqrt_params,
                    cached_order: None
                })
            }
        }
    }
}

/// Group representation type
#[derive(Debug, Clone, Copy)]
pub(crate) enum GroupRepresentation {
    /// Matrix group of dimension n
    Matrix(usize),
    /// Abstract group
    Abstract,
}

impl<P: Float> SymmetryGroup<P> {
    /// Get group representation type
    pub(crate) fn get_representation(&self) -> GroupRepresentation {
        // Determine representation based on dimension and generators
        let n_sq = (self.dimension as f64).sqrt() as usize;
        
        if n_sq * n_sq == self.dimension {
            // Dimension is a perfect square, likely a matrix group
            GroupRepresentation::Matrix(n_sq)
        } else {
            GroupRepresentation::Abstract
        }
    }
    
    /// General matrix logarithm for n×n matrices
    pub(crate) fn matrix_logarithm_general(&self, matrix: &[P], n: usize) -> Option<Vec<P>> {
        if matrix.len() != n * n {
            return None;
        }
        
        // Try the safe logarithm first (for matrices close to identity)
        if let Some(result) = self.matrix_logarithm_safe(matrix, n) {
            return Some(result);
        }
        
        // For matrices far from identity, use advanced methods
        self.matrix_logarithm_advanced(matrix, n)
    }
    
    /// Convert real parameters to complex matrix
    /// params[2k] + i*params[2k+1] forms the (k/n, k%n)-th element
    pub(crate) fn params_to_complex_matrix(&self, params: &[P], n: usize) -> Vec<Complex<P>> {
        let mut complex_matrix = vec![Complex::new(P::zero(), P::zero()); n * n];
        
        for i in 0..n {
            for j in 0..n {
                let idx = i * n + j;
                let real_idx = 2 * idx;
                let imag_idx = real_idx + 1;
                
                if real_idx < params.len() && imag_idx < params.len() {
                    complex_matrix[idx] = Complex::new(params[real_idx], params[imag_idx]);
                }
            }
        }
        
        complex_matrix
    }
    
    /// Check if a complex matrix is unitary (M† M = I)
    pub(crate) fn is_unitary_matrix(&self, matrix: &[Complex<P>], n: usize) -> bool {
        if matrix.len() != n * n {
            return false;
        }
        
        // Compute M† M
        for i in 0..n {
            for j in 0..n {
                let mut sum = Complex::new(P::zero(), P::zero());
                
                // (M† M)_{ij} = Σ_k M†_{ik} M_{kj} = Σ_k conj(M_{ki}) M_{kj}
                for k in 0..n {
                    let m_ki = matrix[k * n + i];
                    let m_kj = matrix[k * n + j];
                    sum = sum + m_ki.conj() * m_kj;
                }
                
                // Check if equals identity
                let expected = if i == j {
                    Complex::new(P::one(), P::zero())
                } else {
                    Complex::new(P::zero(), P::zero())
                };
                
                if (sum - expected).norm() > P::epsilon() {
                    return false;
                }
            }
        }
        
        true
    }
    
    /// Compute determinant of complex matrix
    pub(crate) fn compute_complex_determinant(&self, matrix: &[Complex<P>], n: usize) -> Option<Complex<P>> {
        if matrix.len() != n * n {
            return None;
        }
        
        if n == 0 {
            return Some(Complex::new(P::one(), P::zero()));
        }
        
        if n == 1 {
            return Some(matrix[0]);
        }
        
        if n == 2 {
            // 2×2 determinant: ad - bc
            return Some(matrix[0] * matrix[3] - matrix[1] * matrix[2]);
        }
        
        if n == 3 {
            // 3×3 determinant using rule of Sarrus
            let a = matrix[0] * (matrix[4] * matrix[8] - matrix[5] * matrix[7]);
            let b = matrix[1] * (matrix[5] * matrix[6] - matrix[3] * matrix[8]);
            let c = matrix[2] * (matrix[3] * matrix[7] - matrix[4] * matrix[6]);
            return Some(a - b + c);
        }
        
        // For larger matrices, use LU decomposition with complex arithmetic
        let mut work_matrix = matrix.to_vec();
        let mut det = Complex::new(P::one(), P::zero());
        let mut pivot_sign = 1i32;
        
        // Gaussian elimination with partial pivoting
        for i in 0..n {
            // Find pivot
            let mut max_val = P::zero();
            let mut max_row = i;
            
            for k in i..n {
                let val = work_matrix[k * n + i].norm();
                if val > max_val {
                    max_val = val;
                    max_row = k;
                }
            }
            
            if max_val < P::epsilon() {
                // Matrix is singular
                return Some(Complex::new(P::zero(), P::zero()));
            }
            
            // Swap rows if needed
            if max_row != i {
                for j in 0..n {
                    let idx1 = i * n + j;
                    let idx2 = max_row * n + j;
                    work_matrix.swap(idx1, idx2);
                }
                pivot_sign = -pivot_sign;
            }
            
            let pivot = work_matrix[i * n + i];
            det = det * pivot;
            
            // Eliminate column
            for k in (i + 1)..n {
                let factor = work_matrix[k * n + i] / pivot;
                for j in (i + 1)..n {
                    let idx = k * n + j;
                    work_matrix[idx] = work_matrix[idx] - factor * work_matrix[i * n + j];
                }
            }
        }
        
        if pivot_sign < 0 {
            det = -det;
        }
        
        Some(det)
    }
    
    /// Check if a complex matrix is hermitian (M† = M)
    pub(crate) fn is_hermitian_matrix(&self, matrix: &[Complex<P>], n: usize) -> bool {
        if matrix.len() != n * n {
            return false;
        }
        
        for i in 0..n {
            for j in 0..n {
                let m_ij = matrix[i * n + j];
                let m_ji = matrix[j * n + i];
                
                if (m_ij - m_ji.conj()).norm() > P::epsilon() {
                    return false;
                }
            }
        }
        
        true
    }
    
    /// Compute the conjugate transpose (Hermitian conjugate) of a complex matrix
    pub(crate) fn conjugate_transpose(&self, matrix: &[Complex<P>], n: usize) -> Vec<Complex<P>> {
        let mut result = vec![Complex::new(P::zero(), P::zero()); n * n];
        
        for i in 0..n {
            for j in 0..n {
                result[j * n + i] = matrix[i * n + j].conj();
            }
        }
        
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::group::{SymmetryGroup, GroupElement};
    
    #[test]
    fn test_180_degree_rotation_logarithm() {
        let group = SymmetryGroup::<f64>::generate(9).unwrap();
        
        // Test 180-degree rotation around x-axis
        let rotation_x = vec![
            1.0,  0.0,  0.0,
            0.0, -1.0,  0.0,
            0.0,  0.0, -1.0
        ];
        
        let log_result = group.matrix_log_3x3(&rotation_x);
        assert!(log_result.is_some());
        
        let log_matrix = log_result.unwrap();
        
        // Check that it's skew-symmetric
        for i in 0..3 {
            for j in 0..3 {
                let log_ij = log_matrix[i * 3 + j];
                let log_ji = log_matrix[j * 3 + i];
                assert!((log_ij + log_ji).abs() < 1e-10);
            }
        }
        
        // Verify we can recover the rotation by exponentiating
        let exp_result = group.matrix_exp_3x3(&log_matrix);
        assert!(exp_result.is_some());
        let recovered = exp_result.unwrap();
        
        for i in 0..9 {
            assert!((recovered[i] - rotation_x[i]).abs() < 1e-10);
        }
    }
    
    #[test]
    fn test_180_degree_rotation_all_axes() {
        let group = SymmetryGroup::<f64>::generate(9).unwrap();
        
        // Test rotations around all three coordinate axes
        let test_cases = vec![
            // X-axis
            vec![1.0, 0.0, 0.0, 0.0, -1.0, 0.0, 0.0, 0.0, -1.0],
            // Y-axis  
            vec![-1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, -1.0],
            // Z-axis
            vec![-1.0, 0.0, 0.0, 0.0, -1.0, 0.0, 0.0, 0.0, 1.0],
        ];
        
        for rotation in test_cases {
            let log_result = group.matrix_log_3x3(&rotation);
            assert!(log_result.is_some(), "Failed to compute logarithm");
            
            let log_matrix = log_result.unwrap();
            
            // Verify skew-symmetry
            for i in 0..3 {
                assert!(log_matrix[i * 3 + i].abs() < 1e-10, "Diagonal should be zero");
            }
            
            // Verify exp(log(R)) = R
            let exp_result = group.matrix_exp_3x3(&log_matrix);
            assert!(exp_result.is_some());
            let recovered = exp_result.unwrap();
            
            for i in 0..9 {
                assert!((recovered[i] - rotation[i]).abs() < 1e-10,
                    "Failed to recover rotation at index {}", i);
            }
        }
    }
    
    #[test]
    fn test_180_degree_arbitrary_axis() {
        let group = SymmetryGroup::<f64>::generate(9).unwrap();
        
        // Test a 180-degree rotation around the z-axis
        // This has trace = -1 and is handled by the special case
        let rotation = vec![
            -1.0,  0.0,  0.0,
             0.0, -1.0,  0.0,
             0.0,  0.0,  1.0
        ];
        
        // First verify it's a valid rotation matrix
        let is_rotation = group.is_rotation_matrix_3x3(&rotation);
        if !is_rotation {
            println!("Warning: Matrix is not a valid rotation matrix");
            println!("Matrix:");
            for i in 0..3 {
                println!("[{:8.5}, {:8.5}, {:8.5}]", 
                    rotation[i*3], rotation[i*3+1], rotation[i*3+2]);
            }
            // Let's check what's wrong
            let det = group.compute_determinant(&rotation, 3).unwrap();
            println!("Actual determinant: {}", det);
            
            // Debug: compute determinant manually
            let a = rotation[0] * (rotation[4] * rotation[8] - rotation[5] * rotation[7]);
            let b = rotation[1] * (rotation[5] * rotation[6] - rotation[3] * rotation[8]);
            let c = rotation[2] * (rotation[3] * rotation[7] - rotation[4] * rotation[6]);
            println!("Manual det calculation: {} - {} + {} = {}", a, b, c, a - b + c);
            
            // Check orthogonality
            for i in 0..3 {
                for j in 0..3 {
                    let mut sum = 0.0;
                    for k in 0..3 {
                        sum += rotation[k * 3 + i] * rotation[k * 3 + j];
                    }
                    let expected = if i == j { 1.0 } else { 0.0 };
                    println!("R^T R[{},{}] = {} (expected {})", i, j, sum, expected);
                }
            }
        }
        
        let log_result = group.matrix_log_3x3(&rotation);
        assert!(log_result.is_some(), "Failed to compute logarithm of 180-degree rotation");
        
        let log_matrix = log_result.unwrap();
        
        println!("\nLogarithm of rotation:");
        for i in 0..3 {
            println!("[{:8.5}, {:8.5}, {:8.5}]", 
                log_matrix[i*3], log_matrix[i*3+1], log_matrix[i*3+2]);
        }
        
        // Verify it's skew-symmetric
        println!("\nChecking skew-symmetry of logarithm:");
        for i in 0..3 {
            for j in 0..3 {
                let log_ij = log_matrix[i * 3 + j];
                let log_ji = log_matrix[j * 3 + i];
                if (log_ij + log_ji).abs() > 1e-10 {
                    println!("Not skew-symmetric at ({}, {}): {} + {} = {}", 
                        i, j, log_ij, log_ji, log_ij + log_ji);
                }
            }
        }
        
        let exp_result = group.matrix_exp_3x3(&log_matrix);
        assert!(exp_result.is_some());
        
        let recovered = exp_result.unwrap();
        
        println!("\nVerifying exp(log(R)) = R:");
        println!("Original rotation:");
        for i in 0..3 {
            println!("[{:8.5}, {:8.5}, {:8.5}]", 
                rotation[i*3], rotation[i*3+1], rotation[i*3+2]);
        }
        println!("\nRecovered rotation:");
        for i in 0..3 {
            println!("[{:8.5}, {:8.5}, {:8.5}]", 
                recovered[i*3], recovered[i*3+1], recovered[i*3+2]);
        }
        
        let mut max_diff = 0.0;
        for i in 0..9 {
            let diff = (recovered[i] - rotation[i]).abs();
            if diff > max_diff {
                max_diff = diff;
            }
        }
        println!("\nMaximum difference: {}", max_diff);
        
        assert!(max_diff < 1e-9, "exp(log(R)) != R, max difference: {}", max_diff);
    }
    
    #[test]
    fn test_complex_matrix_operations() {
        use num_complex::Complex;
        let group = SymmetryGroup::<f64>::generate(8).unwrap(); // 8 real params = 2x2 complex
        
        // Test params to complex matrix conversion
        let params = vec![1.0, 0.0, 0.0, 1.0, 0.0, 0.0, 1.0, 0.0]; // 2x2 identity
        let complex_matrix = group.params_to_complex_matrix(&params, 2);
        
        assert_eq!(complex_matrix[0], Complex::new(1.0, 0.0));
        assert_eq!(complex_matrix[1], Complex::new(0.0, 1.0));
        assert_eq!(complex_matrix[2], Complex::new(0.0, 0.0));
        assert_eq!(complex_matrix[3], Complex::new(1.0, 0.0));
    }
    
    #[test]
    fn test_unitary_matrix_check() {
        use num_complex::Complex;
        let group = SymmetryGroup::<f64>::generate(8).unwrap();
        
        // Test with 2x2 identity (is unitary)
        let identity = vec![
            Complex::new(1.0, 0.0), Complex::new(0.0, 0.0),
            Complex::new(0.0, 0.0), Complex::new(1.0, 0.0)
        ];
        assert!(group.is_unitary_matrix(&identity, 2));
        
        // Test with Pauli X matrix (is unitary)
        let pauli_x = vec![
            Complex::new(0.0, 0.0), Complex::new(1.0, 0.0),
            Complex::new(1.0, 0.0), Complex::new(0.0, 0.0)
        ];
        assert!(group.is_unitary_matrix(&pauli_x, 2));
        
        // Test with Pauli Y matrix (is unitary)
        let pauli_y = vec![
            Complex::new(0.0, 0.0), Complex::new(0.0, -1.0),
            Complex::new(0.0, 1.0), Complex::new(0.0, 0.0)
        ];
        assert!(group.is_unitary_matrix(&pauli_y, 2));
        
        // Test with non-unitary matrix
        let non_unitary = vec![
            Complex::new(2.0, 0.0), Complex::new(0.0, 0.0),
            Complex::new(0.0, 0.0), Complex::new(1.0, 0.0)
        ];
        assert!(!group.is_unitary_matrix(&non_unitary, 2));
    }
    
    #[test]
    fn test_complex_determinant() {
        use num_complex::Complex;
        let group = SymmetryGroup::<f64>::generate(8).unwrap();
        
        // Test 2x2 identity
        let identity = vec![
            Complex::new(1.0, 0.0), Complex::new(0.0, 0.0),
            Complex::new(0.0, 0.0), Complex::new(1.0, 0.0)
        ];
        let det = group.compute_complex_determinant(&identity, 2).unwrap();
        assert!((det - Complex::new(1.0, 0.0)).norm() < 1e-10);
        
        // Test 2x2 with known determinant
        // [[1+i, 2], [3, 4-i]] -> det = (1+i)(4-i) - 2*3 = 4-i+4i+1 - 6 = 5+3i - 6 = -1+3i
        let matrix = vec![
            Complex::new(1.0, 1.0), Complex::new(2.0, 0.0),
            Complex::new(3.0, 0.0), Complex::new(4.0, -1.0)
        ];
        let det = group.compute_complex_determinant(&matrix, 2).unwrap();
        let expected = Complex::new(-1.0, 3.0);
        assert!((det - expected).norm() < 1e-10);
        
        // Test singular matrix
        let singular = vec![
            Complex::new(1.0, 0.0), Complex::new(2.0, 0.0),
            Complex::new(2.0, 0.0), Complex::new(4.0, 0.0)
        ];
        let det = group.compute_complex_determinant(&singular, 2).unwrap();
        assert!(det.norm() < 1e-10);
    }
    
    #[test]
    fn test_hermitian_check() {
        use num_complex::Complex;
        let group = SymmetryGroup::<f64>::generate(8).unwrap();
        
        // Test Hermitian matrix
        let hermitian = vec![
            Complex::new(1.0, 0.0), Complex::new(2.0, 3.0),
            Complex::new(2.0, -3.0), Complex::new(4.0, 0.0)
        ];
        assert!(group.is_hermitian_matrix(&hermitian, 2));
        
        // Test non-Hermitian matrix
        let non_hermitian = vec![
            Complex::new(1.0, 0.0), Complex::new(2.0, 3.0),
            Complex::new(2.0, 3.0), Complex::new(4.0, 0.0)
        ];
        assert!(!group.is_hermitian_matrix(&non_hermitian, 2));
    }
    
    #[test]
    fn test_conjugate_transpose() {
        use num_complex::Complex;
        let group = SymmetryGroup::<f64>::generate(8).unwrap();
        
        let matrix = vec![
            Complex::new(1.0, 2.0), Complex::new(3.0, 4.0),
            Complex::new(5.0, 6.0), Complex::new(7.0, 8.0)
        ];
        
        let conj_transpose = group.conjugate_transpose(&matrix, 2);
        
        assert_eq!(conj_transpose[0], Complex::new(1.0, -2.0));
        assert_eq!(conj_transpose[1], Complex::new(5.0, -6.0));
        assert_eq!(conj_transpose[2], Complex::new(3.0, -4.0));
        assert_eq!(conj_transpose[3], Complex::new(7.0, -8.0));
    }
}