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

        Ok(GroupElement { params: result })
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
                // For larger matrices, would need LU decomposition or similar
                Err(CcmError::Custom(
                    "Matrix inverse not implemented for dimension > 3",
                ))
            }
        }
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

    /// Transpose a matrix
    pub fn transpose(&self, g: &GroupElement<P>) -> GroupElement<P> {
        let n = self.dimension;
        let mut result = vec![P::zero(); n * n];

        for i in 0..n {
            for j in 0..n {
                result[j * n + i] = g.params[i * n + j];
            }
        }

        GroupElement { params: result }
    }

    /// Create identity matrix
    pub fn identity(&self) -> GroupElement<P> {
        let n = self.dimension;
        let mut params = vec![P::zero(); n * n];

        for i in 0..n {
            params[i * n + i] = P::one();
        }

        GroupElement { params }
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
        };
        let b = GroupElement {
            params: vec![5.0, 6.0, 7.0, 8.0],
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
}
