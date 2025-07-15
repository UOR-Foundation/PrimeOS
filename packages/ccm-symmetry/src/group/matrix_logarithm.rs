//! Advanced matrix logarithm implementations
//! 
//! This module provides matrix logarithm computation for matrices
//! that are far from the identity, using eigenvalue decomposition
//! and other advanced techniques.

use num_traits::Float;
use crate::group::SymmetryGroup;

impl<P: Float> SymmetryGroup<P> {
    /// Compute matrix logarithm for matrices far from identity
    /// 
    /// This is called when the simple power series would not converge.
    /// Uses eigenvalue decomposition, Schur decomposition, or inverse
    /// scaling and squaring methods.
    pub(crate) fn matrix_logarithm_advanced(&self, matrix: &[P], n: usize) -> Option<Vec<P>> {
        // First try specialized methods for small matrices
        match n {
            2 => self.matrix_log_2x2_general(matrix),
            3 => self.matrix_log_3x3_general(matrix),
            _ => {
                // For larger matrices, check matrix properties
                if self.is_symmetric_matrix(matrix, n) {
                    self.matrix_log_symmetric(matrix, n)
                } else if self.is_orthogonal_matrix(matrix, n) {
                    self.matrix_log_orthogonal(matrix, n)
                } else {
                    // General case: use inverse scaling and squaring
                    self.matrix_log_inverse_scaling_squaring(matrix, n)
                }
            }
        }
    }
    
    /// Compute logarithm of general 2x2 matrix using eigenvalues
    fn matrix_log_2x2_general(&self, matrix: &[P]) -> Option<Vec<P>> {
        let a = matrix[0];
        let b = matrix[1];
        let c = matrix[2];
        let d = matrix[3];
        
        let det = a * d - b * c;
        if det <= P::zero() {
            return None; // Need positive determinant
        }
        
        let trace = a + d;
        let discriminant_sq = trace * trace - P::from(4.0).unwrap() * det;
        
        if discriminant_sq < P::zero() {
            // Complex eigenvalues - handle rotation matrices
            return self.matrix_log_2x2_complex_eigenvalues(matrix);
        }
        
        let discriminant = discriminant_sq.sqrt();
        let lambda1 = (trace + discriminant) / P::from(2.0).unwrap();
        let lambda2 = (trace - discriminant) / P::from(2.0).unwrap();
        
        if lambda1 <= P::zero() || lambda2 <= P::zero() {
            return None; // Need positive eigenvalues for real logarithm
        }
        
        // Case 1: Repeated eigenvalues
        if (lambda1 - lambda2).abs() < P::epsilon() {
            let log_lambda = lambda1.ln();
            
            // Check if matrix is diagonal
            if b.abs() < P::epsilon() && c.abs() < P::epsilon() {
                return Some(vec![log_lambda, P::zero(), P::zero(), log_lambda]);
            }
            
            // Jordan form case: log(λI + N) = log(λ)I + N/λ - N²/(2λ²) + ...
            let n11 = (a - lambda1) / lambda1;
            let n12 = b / lambda1;
            let n21 = c / lambda1;
            let n22 = (d - lambda1) / lambda1;
            
            // Compute log using Padé approximation for log(I + N/λ)
            return Some(vec![
                log_lambda + n11,
                n12,
                n21,
                log_lambda + n22
            ]);
        }
        
        // Case 2: Distinct eigenvalues - use Putzer's algorithm
        let log_lambda1 = lambda1.ln();
        let log_lambda2 = lambda2.ln();
        
        // Coefficients for matrix function
        let c0 = (lambda2 * log_lambda1 - lambda1 * log_lambda2) / (lambda2 - lambda1);
        let c1 = (log_lambda2 - log_lambda1) / (lambda2 - lambda1);
        
        Some(vec![
            c0 + c1 * a,
            c1 * b,
            c1 * c,
            c0 + c1 * d
        ])
    }
    
    /// Handle 2x2 matrices with complex eigenvalues (rotations)
    fn matrix_log_2x2_complex_eigenvalues(&self, matrix: &[P]) -> Option<Vec<P>> {
        let a = matrix[0];
        let b = matrix[1];
        let c = matrix[2];
        let d = matrix[3];
        
        // For rotation matrix, we have a = d = cos(θ), b = -sin(θ), c = sin(θ)
        let cos_theta = (a + d) / P::from(2.0).unwrap();
        let sin_theta = (c - b) / P::from(2.0).unwrap();
        
        // Ensure it's actually a rotation
        let norm_check = cos_theta * cos_theta + sin_theta * sin_theta;
        if (norm_check - P::one()).abs() > P::epsilon() * P::from(10.0).unwrap() {
            return None;
        }
        
        let theta = sin_theta.atan2(cos_theta);
        
        // Log of rotation matrix is skew-symmetric
        Some(vec![
            P::zero(), -theta,
            theta, P::zero()
        ])
    }
    
    /// Compute logarithm of general 3x3 matrix
    fn matrix_log_3x3_general(&self, matrix: &[P]) -> Option<Vec<P>> {
        // First check if it's a rotation matrix
        if self.is_rotation_matrix_3x3(matrix) {
            return self.matrix_log_3x3(matrix);
        }
        
        // For general 3x3 matrices, use inverse scaling and squaring
        self.matrix_log_inverse_scaling_squaring(matrix, 3)
    }
    
    /// Check if matrix is symmetric
    fn is_symmetric_matrix(&self, matrix: &[P], n: usize) -> bool {
        for i in 0..n {
            for j in i+1..n {
                let diff = (matrix[i * n + j] - matrix[j * n + i]).abs();
                if diff > P::epsilon() * P::from(10.0).unwrap() {
                    return false;
                }
            }
        }
        true
    }
    
    /// Check if matrix is orthogonal
    fn is_orthogonal_matrix(&self, matrix: &[P], n: usize) -> bool {
        // Check if M^T M = I
        for i in 0..n {
            for j in 0..n {
                let mut sum = P::zero();
                for k in 0..n {
                    sum = sum + matrix[k * n + i] * matrix[k * n + j];
                }
                let expected = if i == j { P::one() } else { P::zero() };
                if (sum - expected).abs() > P::epsilon() * P::from(100.0).unwrap() {
                    return false;
                }
            }
        }
        true
    }
    
    /// Compute logarithm of symmetric positive definite matrix
    fn matrix_log_symmetric(&self, matrix: &[P], n: usize) -> Option<Vec<P>> {
        // Check positive definiteness using Cholesky decomposition attempt
        if !self.is_positive_definite_cholesky(matrix, n) {
            return None;
        }
        
        // Use spectral decomposition for symmetric matrices
        // For now, use inverse scaling and squaring which works well
        // for positive definite matrices
        self.matrix_log_inverse_scaling_squaring(matrix, n)
    }
    
    /// Compute logarithm of orthogonal matrix
    fn matrix_log_orthogonal(&self, matrix: &[P], n: usize) -> Option<Vec<P>> {
        // Check determinant to distinguish SO(n) from O(n)
        let det = self.compute_determinant(matrix, n)?;
        
        if (det - P::one()).abs() > P::epsilon() {
            // Determinant -1: has a reflection component
            // Log doesn't exist in SO(n)
            return None;
        }
        
        // For SO(n), use specialized methods
        match n {
            2 => self.matrix_log_2x2(matrix),
            3 => self.matrix_log_3x3(matrix),
            _ => self.matrix_log_inverse_scaling_squaring(matrix, n)
        }
    }
    
    /// Check positive definiteness using Cholesky decomposition
    fn is_positive_definite_cholesky(&self, matrix: &[P], n: usize) -> bool {
        // Attempt Cholesky decomposition
        let mut l = vec![P::zero(); n * n];
        
        for i in 0..n {
            for j in 0..=i {
                let mut sum = P::zero();
                
                if i == j {
                    // Diagonal elements
                    for k in 0..j {
                        sum = sum + l[i * n + k] * l[i * n + k];
                    }
                    let diag = matrix[i * n + i] - sum;
                    if diag <= P::zero() {
                        return false; // Not positive definite
                    }
                    l[i * n + j] = diag.sqrt();
                } else {
                    // Off-diagonal elements
                    for k in 0..j {
                        sum = sum + l[i * n + k] * l[j * n + k];
                    }
                    l[i * n + j] = (matrix[i * n + j] - sum) / l[j * n + j];
                }
            }
        }
        
        true
    }
    
    /// Compute matrix logarithm using inverse scaling and squaring
    /// 
    /// Algorithm:
    /// 1. Compute s such that ||M^(1/2^s) - I|| < 0.5
    /// 2. Compute log(M^(1/2^s)) using Padé approximation
    /// 3. log(M) = 2^s * log(M^(1/2^s))
    pub(crate) fn matrix_log_inverse_scaling_squaring(&self, matrix: &[P], n: usize) -> Option<Vec<P>> {
        let mut m = matrix.to_vec();
        let mut s = 0;
        let identity = self.identity_matrix(n);
        
        // Step 1: Square root scaling
        let max_sqrts = 20;
        while s < max_sqrts {
            let norm = self.matrix_norm_minus_identity(&m, &identity, n);
            if norm < P::from(0.25).unwrap() {
                break;
            }
            
            // Take matrix square root
            m = self.matrix_square_root_denman_beavers(&m, n)?;
            s += 1;
        }
        
        if s == max_sqrts {
            // Failed to get close enough to identity
            return None;
        }
        
        // Step 2: Compute log using Padé approximation
        let log_m = self.matrix_log_pade(&m, n)?;
        
        // Step 3: Scale back
        let scale = P::from(1 << s).unwrap();
        let mut result = vec![P::zero(); n * n];
        for i in 0..n * n {
            result[i] = log_m[i] * scale;
        }
        
        Some(result)
    }
    
    /// Identity matrix
    fn identity_matrix(&self, n: usize) -> Vec<P> {
        let mut id = vec![P::zero(); n * n];
        for i in 0..n {
            id[i * n + i] = P::one();
        }
        id
    }
    
    /// Compute ||M - I||_∞
    fn matrix_norm_minus_identity(&self, matrix: &[P], identity: &[P], n: usize) -> P {
        let mut max_diff = P::zero();
        for i in 0..n * n {
            let diff = (matrix[i] - identity[i]).abs();
            if diff > max_diff {
                max_diff = diff;
            }
        }
        max_diff
    }
    
    /// Matrix square root using Denman-Beavers iteration
    fn matrix_square_root_denman_beavers(&self, matrix: &[P], n: usize) -> Option<Vec<P>> {
        let mut y = matrix.to_vec();
        let mut z = self.identity_matrix(n);
        
        let max_iter = 20;
        let tolerance = P::epsilon() * P::from(100.0).unwrap();
        
        for _ in 0..max_iter {
            // Compute Y_inv and Z_inv
            let y_inv = self.matrix_inverse(&y, n)?;
            let z_inv = self.matrix_inverse(&z, n)?;
            
            // Y_{k+1} = (Y_k + Z_k^{-1}) / 2
            // Z_{k+1} = (Z_k + Y_k^{-1}) / 2
            let mut y_new = vec![P::zero(); n * n];
            let mut z_new = vec![P::zero(); n * n];
            
            for i in 0..n * n {
                y_new[i] = (y[i] + z_inv[i]) / P::from(2.0).unwrap();
                z_new[i] = (z[i] + y_inv[i]) / P::from(2.0).unwrap();
            }
            
            // Check convergence
            let mut max_change = P::zero();
            for i in 0..n * n {
                let change_y = (y_new[i] - y[i]).abs();
                let change_z = (z_new[i] - z[i]).abs();
                max_change = max_change.max(change_y).max(change_z);
            }
            
            y = y_new;
            z = z_new;
            
            if max_change < tolerance {
                return Some(y);
            }
        }
        
        // Check if we have a good approximation
        let y_squared = self.matrix_multiply(&y, &y, n)?;
        let mut error = P::zero();
        for i in 0..n * n {
            error = error.max((y_squared[i] - matrix[i]).abs());
        }
        
        if error < tolerance * P::from(10.0).unwrap() {
            Some(y)
        } else {
            None
        }
    }
    
    /// Compute matrix logarithm using Padé approximation
    /// 
    /// For matrices close to identity, use rational approximation
    fn matrix_log_pade(&self, matrix: &[P], n: usize) -> Option<Vec<P>> {
        let identity = self.identity_matrix(n);
        let mut a = vec![P::zero(); n * n];
        
        // A = M - I
        for i in 0..n * n {
            a[i] = matrix[i] - identity[i];
        }
        
        // Check if A is small enough for Padé
        let a_norm = a.iter().map(|&x| x.abs()).fold(P::zero(), |acc, x| acc.max(x));
        if a_norm > P::from(0.5).unwrap() {
            // Fall back to power series with more terms
            return self.matrix_log_power_series_extended(&matrix, n);
        }
        
        // Use Padé approximant of order [3/3]
        // log(I+A) ≈ A * (I + A/2 + A²/12)^{-1} * (I - A/2 + A²/12)
        
        let mut a_squared = self.matrix_multiply(&a, &a, n)?;
        
        // Scale A²/12
        for i in 0..n * n {
            a_squared[i] = a_squared[i] / P::from(12.0).unwrap();
        }
        
        // Compute numerator: A
        let numerator = a.clone();
        
        // Compute P = I + A/2 + A²/12
        let mut p = identity.clone();
        for i in 0..n * n {
            p[i] = p[i] + a[i] / P::from(2.0).unwrap() + a_squared[i];
        }
        
        // Compute Q = I - A/2 + A²/12
        let mut q = identity;
        for i in 0..n * n {
            q[i] = q[i] - a[i] / P::from(2.0).unwrap() + a_squared[i];
        }
        
        // Compute P^{-1} * Q
        let p_inv = self.matrix_inverse(&p, n)?;
        let p_inv_q = self.matrix_multiply(&p_inv, &q, n)?;
        
        // Result = numerator * P^{-1} * Q
        self.matrix_multiply(&numerator, &p_inv_q, n)
    }
    
    /// Extended power series for larger norm matrices
    fn matrix_log_power_series_extended(&self, matrix: &[P], n: usize) -> Option<Vec<P>> {
        let identity = self.identity_matrix(n);
        let mut a = vec![P::zero(); n * n];
        
        // A = M - I
        for i in 0..n * n {
            a[i] = matrix[i] - identity[i];
        }
        
        // log(I + A) = Σ((-1)^{k+1} * A^k / k) for k=1 to ∞
        let mut result = a.clone();
        let mut a_power = a.clone();
        let max_terms = 50; // More terms for better convergence
        
        for k in 2..=max_terms {
            // a_power = a_power * a
            a_power = self.matrix_multiply(&a_power, &a, n)?;
            
            // Add term: (-1)^{k+1} * a_power / k
            let sign = if k % 2 == 0 { -P::one() } else { P::one() };
            let coeff = sign / P::from(k).unwrap();
            
            for i in 0..n * n {
                result[i] = result[i] + coeff * a_power[i];
            }
            
            // Check convergence
            let term_norm = a_power.iter()
                .map(|&x| x.abs())
                .fold(P::zero(), |acc, x| acc.max(x));
            
            if term_norm * coeff.abs() < P::epsilon() {
                break;
            }
        }
        
        Some(result)
    }
}