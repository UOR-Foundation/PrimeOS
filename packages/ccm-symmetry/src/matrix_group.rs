//! Matrix group implementation

use crate::{group::GroupElement, SymmetryError};
use ccm_core::{CcmError, Float};

#[cfg(feature = "alloc")]
use alloc::vec;

/// Matrix group operations
pub struct MatrixGroup<P: Float> {
    /// Dimension of the matrices
    dimension: usize,
    _phantom: core::marker::PhantomData<P>,
}

impl<P: Float> MatrixGroup<P> {
    /// Create a new matrix group
    pub fn new(dimension: usize) -> Self {
        Self {
            dimension,
            _phantom: core::marker::PhantomData,
        }
    }

    /// Multiply two matrices represented as group elements
    pub fn multiply(
        &self,
        g: &GroupElement<P>,
        h: &GroupElement<P>,
    ) -> Result<GroupElement<P>, CcmError> {
        let n = self.dimension;

        // Verify dimensions
        if g.params.len() != n * n || h.params.len() != n * n {
            return Err(SymmetryError::InvalidGroupOperation.into());
        }

        let mut result = vec![P::zero(); n * n];

        // Matrix multiplication: C[i,j] = Σ_k A[i,k] * B[k,j]
        for i in 0..n {
            for j in 0..n {
                let mut sum = P::zero();
                for k in 0..n {
                    sum = sum + g.params[i * n + k] * h.params[k * n + j];
                }
                result[i * n + j] = sum;
            }
        }

        Ok(GroupElement { params: result, cached_order: None })
    }

    /// Compute matrix inverse
    pub fn inverse(&self, g: &GroupElement<P>) -> Result<GroupElement<P>, CcmError> {
        let n = self.dimension;

        if g.params.len() != n * n {
            return Err(SymmetryError::InvalidGroupOperation.into());
        }

        // For simplicity, implement for 2x2 and 3x3 matrices
        match n {
            1 => {
                // 1x1 matrix
                let det = g.params[0];
                if det.abs() < P::epsilon() {
                    return Err(SymmetryError::InvalidGroupOperation.into());
                }
                Ok(GroupElement {
                    params: vec![P::one() / det],
                    cached_order: None,
                })
            }
            2 => {
                // 2x2 matrix inverse
                let a = g.params[0];
                let b = g.params[1];
                let c = g.params[2];
                let d = g.params[3];

                let det = a * d - b * c;
                if det.abs() < P::epsilon() {
                    return Err(SymmetryError::InvalidGroupOperation.into());
                }

                let inv_det = P::one() / det;
                Ok(GroupElement {
                    params: vec![d * inv_det, -b * inv_det, -c * inv_det, a * inv_det],
                    cached_order: None,
                })
            }
            3 => {
                // 3x3 matrix inverse using cofactor method
                let m = &g.params;

                // Calculate determinant
                let det = m[0] * (m[4] * m[8] - m[5] * m[7]) - m[1] * (m[3] * m[8] - m[5] * m[6])
                    + m[2] * (m[3] * m[7] - m[4] * m[6]);

                if det.abs() < P::epsilon() {
                    return Err(SymmetryError::InvalidGroupOperation.into());
                }

                let inv_det = P::one() / det;

                // Calculate cofactor matrix and transpose
                Ok(GroupElement {
                    cached_order: None,
                    params: vec![
                        (m[4] * m[8] - m[5] * m[7]) * inv_det,
                        (m[2] * m[7] - m[1] * m[8]) * inv_det,
                        (m[1] * m[5] - m[2] * m[4]) * inv_det,
                        (m[5] * m[6] - m[3] * m[8]) * inv_det,
                        (m[0] * m[8] - m[2] * m[6]) * inv_det,
                        (m[2] * m[3] - m[0] * m[5]) * inv_det,
                        (m[3] * m[7] - m[4] * m[6]) * inv_det,
                        (m[1] * m[6] - m[0] * m[7]) * inv_det,
                        (m[0] * m[4] - m[1] * m[3]) * inv_det,
                    ],
                })
            }
            _ => {
                // For larger matrices, use LU decomposition with partial pivoting
                self.inverse_lu_decomposition(g)
            }
        }
    }

    /// Compute matrix inverse using LU decomposition with partial pivoting
    fn inverse_lu_decomposition(&self, g: &GroupElement<P>) -> Result<GroupElement<P>, CcmError> {
        let n = self.dimension;
        
        // Create working copies
        let mut a = g.params.clone();
        let mut pivot = vec![0usize; n];
        
        // Perform LU decomposition with partial pivoting
        for k in 0..n {
            // Find pivot
            let mut max_val = P::zero();
            let mut max_row = k;
            
            for i in k..n {
                let val = a[i * n + k].abs();
                if val > max_val {
                    max_val = val;
                    max_row = i;
                }
            }
            
            // Check for singular matrix with better tolerance
            // Use a scaled epsilon based on matrix norm
            let tol = P::epsilon() * P::from(n).unwrap_or(P::one()) * P::from(100.0).unwrap_or(P::one());
            if max_val < tol {
                return Err(CcmError::Custom("Matrix is singular or nearly singular"));
            }
            
            // Swap rows if needed
            if max_row != k {
                for j in 0..n {
                    let tmp = a[k * n + j];
                    a[k * n + j] = a[max_row * n + j];
                    a[max_row * n + j] = tmp;
                }
            }
            pivot[k] = max_row;
            
            // Compute multipliers and eliminate column
            let pivot_val = a[k * n + k];
            for i in (k + 1)..n {
                a[i * n + k] = a[i * n + k] / pivot_val;
                for j in (k + 1)..n {
                    a[i * n + j] = a[i * n + j] - a[i * n + k] * a[k * n + j];
                }
            }
        }
        
        // Now solve for inverse by solving AX = I
        let mut inv = vec![P::zero(); n * n];
        
        // Process each column of the identity matrix
        for col in 0..n {
            // Create unit vector for this column
            let mut b = vec![P::zero(); n];
            b[col] = P::one();
            
            // Apply row permutations from pivoting
            for k in 0..n {
                if pivot[k] != k {
                    let tmp = b[k];
                    b[k] = b[pivot[k]];
                    b[pivot[k]] = tmp;
                }
            }
            
            // Forward substitution (solve Ly = b)
            let mut y = vec![P::zero(); n];
            for i in 0..n {
                let mut sum = b[i];
                for j in 0..i {
                    sum = sum - a[i * n + j] * y[j];
                }
                y[i] = sum;
            }
            
            // Back substitution (solve Ux = y)
            for i in (0..n).rev() {
                let mut sum = y[i];
                for j in (i + 1)..n {
                    sum = sum - a[i * n + j] * inv[j * n + col];
                }
                inv[i * n + col] = sum / a[i * n + i];
            }
        }
        
        Ok(GroupElement {
            params: inv,
            cached_order: None,
        })
    }

    /// Check if a matrix is orthogonal (for SO(n) group)
    pub fn is_orthogonal(&self, g: &GroupElement<P>) -> bool {
        let n = self.dimension;
        if g.params.len() != n * n {
            return false;
        }

        // Check if G^T G = I
        let transpose = self.transpose(g);
        if let Ok(product) = self.multiply(&transpose, g) {
            // Check if product is identity
            for i in 0..n {
                for j in 0..n {
                    let expected = if i == j { P::one() } else { P::zero() };
                    let actual = product.params[i * n + j];
                    if (actual - expected).abs() > P::epsilon() {
                        return false;
                    }
                }
            }
            true
        } else {
            false
        }
    }

    /// Compute condition number estimate using 1-norm
    /// Returns None if matrix is singular
    pub fn condition_number(&self, g: &GroupElement<P>) -> Option<P> {
        let n = self.dimension;
        if g.params.len() != n * n {
            return None;
        }
        
        // Compute 1-norm of matrix: max column sum
        let mut norm_a = P::zero();
        for j in 0..n {
            let mut col_sum = P::zero();
            for i in 0..n {
                col_sum = col_sum + g.params[i * n + j].abs();
            }
            if col_sum > norm_a {
                norm_a = col_sum;
            }
        }
        
        // Try to compute inverse
        match self.inverse(g) {
            Ok(inv) => {
                // Compute 1-norm of inverse
                let mut norm_inv = P::zero();
                for j in 0..n {
                    let mut col_sum = P::zero();
                    for i in 0..n {
                        col_sum = col_sum + inv.params[i * n + j].abs();
                    }
                    if col_sum > norm_inv {
                        norm_inv = col_sum;
                    }
                }
                
                Some(norm_a * norm_inv)
            }
            Err(_) => None, // Matrix is singular
        }
    }
    
    /// Check if matrix is numerically stable for inversion
    /// Returns true if condition number is reasonable
    pub fn is_numerically_stable(&self, g: &GroupElement<P>) -> bool {
        match self.condition_number(g) {
            Some(cond) => {
                // Check if condition number is not too large
                // For f64, we want cond < 1e12 to have at least 4 digits of accuracy
                let max_cond = P::from(1e12).unwrap_or(P::from(1000000.0).unwrap());
                cond < max_cond
            }
            None => false, // Singular matrix
        }
    }

    /// Transpose a matrix
    pub fn transpose(&self, g: &GroupElement<P>) -> GroupElement<P> {
        let n = self.dimension;
        let mut result = vec![P::zero(); n * n];

        for i in 0..n {
            for j in 0..n {
                result[j * n + i] = g.params[i * n + j];
            }
        }

        GroupElement { params: result, cached_order: None }
    }

    /// Create identity matrix
    pub fn identity(&self) -> GroupElement<P> {
        let n = self.dimension;
        let mut params = vec![P::zero(); n * n];

        for i in 0..n {
            params[i * n + i] = P::one();
        }

        GroupElement { params, cached_order: Some(1) }
    }
}

/// Special orthogonal group SO(n)
pub struct SpecialOrthogonalGroup<P: Float> {
    matrix_group: MatrixGroup<P>,
}

impl<P: Float> SpecialOrthogonalGroup<P> {
    /// Create SO(n)
    pub fn new(n: usize) -> Self {
        Self {
            matrix_group: MatrixGroup::new(n),
        }
    }

    /// Generate a rotation in the (i,j) plane
    pub fn rotation_generator(
        &self,
        i: usize,
        j: usize,
        angle: P,
    ) -> Result<GroupElement<P>, CcmError> {
        let n = self.matrix_group.dimension;

        if i >= n || j >= n || i == j {
            return Err(SymmetryError::InvalidGroupOperation.into());
        }

        let mut rotation = self.matrix_group.identity();
        let c = angle.cos();
        let s = angle.sin();

        // Set rotation elements
        rotation.params[i * n + i] = c;
        rotation.params[j * n + j] = c;
        rotation.params[i * n + j] = -s;
        rotation.params[j * n + i] = s;

        Ok(rotation)
    }

    /// Verify element is in SO(n)
    pub fn verify_member(&self, g: &GroupElement<P>) -> bool {
        // Must be orthogonal
        if !self.matrix_group.is_orthogonal(g) {
            return false;
        }

        // Must have determinant +1
        if let Ok(det) = self.determinant(g) {
            (det - P::one()).abs() < P::epsilon()
        } else {
            false
        }
    }

    /// Calculate determinant (for small matrices)
    fn determinant(&self, g: &GroupElement<P>) -> Result<P, CcmError> {
        let n = self.matrix_group.dimension;
        let m = &g.params;

        match n {
            1 => Ok(m[0]),
            2 => Ok(m[0] * m[3] - m[1] * m[2]),
            3 => Ok(
                m[0] * (m[4] * m[8] - m[5] * m[7]) - m[1] * (m[3] * m[8] - m[5] * m[6])
                    + m[2] * (m[3] * m[7] - m[4] * m[6]),
            ),
            _ => Err(CcmError::Custom(
                "Determinant not implemented for dimension > 3",
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_matrix_multiplication() {
        let group = MatrixGroup::<f64>::new(2);

        // Test 2x2 matrix multiplication
        let a = GroupElement {
            params: vec![1.0, 2.0, 3.0, 4.0],
            cached_order: None,
        };
        let b = GroupElement {
            params: vec![5.0, 6.0, 7.0, 8.0],
            cached_order: None,
        };

        let c = group.multiply(&a, &b).unwrap();

        // [1 2] [5 6] = [19 22]
        // [3 4] [7 8]   [43 50]
        assert_eq!(c.params, vec![19.0, 22.0, 43.0, 50.0]);
    }

    #[test]
    fn test_matrix_inverse() {
        let group = MatrixGroup::<f64>::new(2);

        // Test 2x2 matrix inverse
        let a = GroupElement {
            params: vec![4.0, 7.0, 2.0, 6.0],
            cached_order: None,
        };
        let a_inv = group.inverse(&a).unwrap();

        // Check A * A^(-1) = I
        let product = group.multiply(&a, &a_inv).unwrap();
        let identity = group.identity();

        for i in 0..4 {
            assert!((product.params[i] - identity.params[i]).abs() < 1e-10);
        }
    }

    #[test]
    fn test_so2_rotation() {
        let so2 = SpecialOrthogonalGroup::<f64>::new(2);
        let angle = std::f64::consts::PI / 4.0; // 45 degrees

        let rotation = so2.rotation_generator(0, 1, angle).unwrap();

        assert!(so2.verify_member(&rotation));
        assert!(so2.matrix_group.is_orthogonal(&rotation));
    }
    
    #[test]
    fn test_lu_decomposition_4x4() {
        let group = MatrixGroup::<f64>::new(4);
        
        // Test with a well-conditioned 4x4 matrix
        let a = GroupElement {
            params: vec![
                 4.0,  2.0, -1.0,  3.0,
                 2.0,  5.0,  2.0, -1.0,
                -1.0,  2.0,  6.0,  2.0,
                 3.0, -1.0,  2.0,  4.0,
            ],
            cached_order: None,
        };
        
        let a_inv = group.inverse(&a).unwrap();
        
        // Check A * A^(-1) = I
        let product = group.multiply(&a, &a_inv).unwrap();
        let identity = group.identity();
        
        for i in 0..16 {
            assert!((product.params[i] - identity.params[i]).abs() < 1e-10,
                    "Product differs from identity at position {}: {} vs {}", 
                    i, product.params[i], identity.params[i]);
        }
        
        // Also check A^(-1) * A = I
        let product2 = group.multiply(&a_inv, &a).unwrap();
        for i in 0..16 {
            assert!((product2.params[i] - identity.params[i]).abs() < 1e-10);
        }
    }
    
    #[test]
    fn test_lu_decomposition_5x5() {
        let group = MatrixGroup::<f64>::new(5);
        
        // Test with a 5x5 Hilbert-like matrix (well-known test case)
        let mut params = vec![0.0; 25];
        for i in 0..5 {
            for j in 0..5 {
                params[i * 5 + j] = 1.0 / (i + j + 1) as f64;
            }
        }
        
        let hilbert = GroupElement { params, cached_order: None };
        
        // Hilbert matrices are notoriously ill-conditioned but still invertible
        let hilbert_inv = group.inverse(&hilbert).unwrap();
        
        // Check that inverse exists and multiplication gives approximately identity
        let product = group.multiply(&hilbert, &hilbert_inv).unwrap();
        let identity = group.identity();
        
        // Due to ill-conditioning, we need a larger tolerance
        for i in 0..5 {
            for j in 0..5 {
                let idx = i * 5 + j;
                let expected = if i == j { 1.0 } else { 0.0 };
                assert!((product.params[idx] - expected).abs() < 1e-8,
                        "Product[{},{}] = {}, expected {}", 
                        i, j, product.params[idx], expected);
            }
        }
    }
    
    #[test]
    fn test_singular_matrix_detection() {
        let group = MatrixGroup::<f64>::new(4);
        
        // Create a singular matrix (rank deficient)
        let singular = GroupElement {
            params: vec![
                1.0, 2.0, 3.0, 4.0,
                2.0, 4.0, 6.0, 8.0,    // Row 2 = 2 * Row 1
                1.0, 1.0, 1.0, 1.0,
                0.0, 0.0, 0.0, 0.0,    // Zero row
            ],
            cached_order: None,
        };
        
        // Should return error for singular matrix
        assert!(group.inverse(&singular).is_err());
    }
    
    #[test]
    fn test_nearly_singular_matrix() {
        let group = MatrixGroup::<f64>::new(3);
        
        // Create a nearly singular matrix
        let eps = 1e-15;
        let nearly_singular = GroupElement {
            params: vec![
                1.0, 0.0, 0.0,
                0.0, eps, 0.0,    // Very small diagonal element
                0.0, 0.0, 1.0,
            ],
            cached_order: None,
        };
        
        // Should handle or reject based on tolerance
        match group.inverse(&nearly_singular) {
            Ok(_) => {
                // If it succeeds, check that it's not numerically stable
                assert!(!group.is_numerically_stable(&nearly_singular));
            }
            Err(_) => {
                // Expected for very ill-conditioned matrices
            }
        }
    }
    
    #[test]
    fn test_condition_number() {
        let group = MatrixGroup::<f64>::new(3);
        
        // Well-conditioned matrix
        let good = GroupElement {
            params: vec![
                2.0, 1.0, 0.0,
                1.0, 3.0, 1.0,
                0.0, 1.0, 2.0,
            ],
            cached_order: None,
        };
        
        let cond = group.condition_number(&good).unwrap();
        assert!(cond < 10.0, "Condition number {} should be small", cond);
        assert!(group.is_numerically_stable(&good));
        
        // Ill-conditioned matrix
        let bad = GroupElement {
            params: vec![
                1.0,     1.0,      1.0,
                1.0,     1.0001,   1.0,
                1.0,     1.0,      1.0001,
            ],
            cached_order: None,
        };
        
        if let Some(cond_bad) = group.condition_number(&bad) {
            assert!(cond_bad > 1000.0, "Condition number {} should be large", cond_bad);
        }
    }
    
    #[test]
    fn test_large_matrix_inverse() {
        // Test with an 8x8 matrix
        let n = 8;
        let group = MatrixGroup::<f64>::new(n);
        
        // Create a diagonally dominant matrix (well-conditioned)
        let mut params = vec![0.0; n * n];
        for i in 0..n {
            for j in 0..n {
                if i == j {
                    params[i * n + j] = 10.0 + i as f64;
                } else {
                    params[i * n + j] = (1.0 / (i + j + 2) as f64).sin();
                }
            }
        }
        
        let matrix = GroupElement { params, cached_order: None };
        let inverse = group.inverse(&matrix).unwrap();
        
        // Verify A * A^(-1) = I
        let product = group.multiply(&matrix, &inverse).unwrap();
        
        for i in 0..n {
            for j in 0..n {
                let idx = i * n + j;
                let expected = if i == j { 1.0 } else { 0.0 };
                assert!((product.params[idx] - expected).abs() < 1e-10,
                        "Product[{},{}] = {}, expected {}", 
                        i, j, product.params[idx], expected);
            }
        }
    }
}
