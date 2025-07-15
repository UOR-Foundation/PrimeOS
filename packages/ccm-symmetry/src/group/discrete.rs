//! Discrete group implementations
//! 
//! This module handles discrete groups that don't fit neatly
//! into finite or infinite categories, such as:
//! - Crystallographic groups
//! - Wallpaper groups
//! - Space groups

use num_traits::Float;
use crate::group::{GroupElement, SymmetryGroup};
use crate::actions::{GroupAction, VectorSpaceAction};
use ccm_core::CcmError;
use crate::SymmetryError;


impl<P: Float> SymmetryGroup<P> {
    /// Check if transformation is a point transformation (no translation)
    fn is_point_transformation(&self, element: &GroupElement<P>) -> bool {
        // A point transformation fixes the origin: T(0) = 0
        // This means it's a linear transformation (no affine part)
        
        // Detect the representation type and check accordingly
        let n = element.params.len();
        
        // Case 1: Matrix representation (n = d²)
        let d = (n as f64).sqrt() as usize;
        if d * d == n {
            // It's a d×d matrix - check if it preserves origin
            // For orthogonal/rotation matrices: det = ±1 and M^T M = I
            return self.is_orthogonal_matrix_discrete(&element.params, d);
        }
        
        // Case 2: Affine representation (rotation + translation)
        // Usually stored as (rotation_params, translation_params)
        if n > 3 {
            // Try to split into rotation and translation parts
            // Common patterns:
            // - SO(2): (cos θ, sin θ, tx, ty) - 4 params
            // - SO(3): (9 rotation params, 3 translation) - 12 params
            // - Quaternion + translation: (4 quat, 3 trans) - 7 params
            
            if n == 4 {
                // 2D affine: check if last 2 params (translation) are zero
                return element.params[2].abs() < P::epsilon() && 
                       element.params[3].abs() < P::epsilon();
            } else if n == 7 {
                // Quaternion + translation: check if last 3 are zero
                return element.params[4].abs() < P::epsilon() && 
                       element.params[5].abs() < P::epsilon() && 
                       element.params[6].abs() < P::epsilon();
            } else if n == 12 {
                // 3D affine (3×3 rotation + 3 translation)
                return element.params[9].abs() < P::epsilon() && 
                       element.params[10].abs() < P::epsilon() && 
                       element.params[11].abs() < P::epsilon();
            }
        }
        
        // Case 3: Check if applying to origin gives origin
        // Create a zero vector and apply the transformation
        let origin = vec![P::zero(); self.ambient_dimension()];
        if let Ok(transformed) = self.apply_to_vector(element, &origin) {
            // Check if transformed origin is still at origin
            return transformed.iter().all(|&x| x.abs() < P::epsilon());
        }
        
        // Default: assume it's a point transformation if all params are bounded
        element.params.iter().all(|&p| p.abs() <= P::one() + P::epsilon())
    }
    
    /// Check if matrix is orthogonal (preserves distances and angles)
    fn is_orthogonal_matrix_discrete(&self, matrix: &[P], d: usize) -> bool {
        // Check if M^T M = I and det(M) = ±1
        
        // First check determinant
        if let Some(det) = self.compute_determinant(matrix, d) {
            if (det.abs() - P::one()).abs() > P::epsilon() {
                return false;
            }
        } else {
            return false;
        }
        
        // Check orthogonality: M^T M = I
        for i in 0..d {
            for j in 0..d {
                let mut dot = P::zero();
                for k in 0..d {
                    // Dot product of columns i and j
                    dot = dot + matrix[k * d + i] * matrix[k * d + j];
                }
                
                let expected = if i == j { P::one() } else { P::zero() };
                if (dot - expected).abs() > P::epsilon() * P::from(10.0).unwrap() {
                    return false;
                }
            }
        }
        
        true
    }
    
    /// Get the ambient dimension for point transformations
    fn ambient_dimension(&self) -> usize {
        // Infer from group dimension
        let n = self.dimension;
        
        // Common cases:
        // SO(2): dimension 1 → ambient 2
        // SO(3): dimension 3 → ambient 3
        // SE(2): dimension 3 → ambient 2
        // SE(3): dimension 6 → ambient 3
        
        match n {
            1 => 2,  // SO(2)
            3 => 3,  // SO(3) or SE(2) 
            6 => 3,  // SE(3)
            _ => {
                // Try to infer from square root
                let d = (n as f64).sqrt() as usize;
                if d * d == n {
                    d  // Matrix group
                } else {
                    // Default assumption
                    3
                }
            }
        }
    }
    
    /// Apply transformation to a vector
    fn apply_to_vector(&self, element: &GroupElement<P>, vector: &[P]) -> Result<Vec<P>, CcmError> {
        let n = element.params.len();
        let d = vector.len();
        
        // Case 1: Matrix representation
        let matrix_d = (n as f64).sqrt() as usize;
        if matrix_d * matrix_d == n && matrix_d == d {
            // Apply matrix multiplication
            let mut result = vec![P::zero(); d];
            for i in 0..d {
                for j in 0..d {
                    result[i] = result[i] + element.params[i * d + j] * vector[j];
                }
            }
            return Ok(result);
        }
        
        // Case 2: Specialized representations
        if n == 4 && d == 2 {
            // 2D affine: [cos θ, sin θ, tx, ty]
            let cos_theta = element.params[0];
            let sin_theta = element.params[1];
            let tx = element.params[2];
            let ty = element.params[3];
            
            let x = vector[0];
            let y = vector[1];
            
            return Ok(vec![
                cos_theta * x - sin_theta * y + tx,
                sin_theta * x + cos_theta * y + ty
            ]);
        }
        
        // Default: return error
        Err(SymmetryError::InvalidGroupOperation.into())
    }
    
    /// Check if transformation is a pure translation
    fn is_pure_translation(&self, element: &GroupElement<P>) -> bool {
        // A pure translation has the form x → x + v
        // In different representations:
        // 1. Affine: (I, v) where I is identity rotation and v is translation
        // 2. Homogeneous matrix: [[I, v], [0, 1]]
        // 3. Direct sum: rotation ⊕ translation components
        
        let n = element.params.len();
        let _identity = self.identity();
        
        // First, try to detect the representation type
        
        // Check for homogeneous matrix representation
        let matrix_dim = ((n + 1) as f64).sqrt() as usize;
        if matrix_dim * matrix_dim == n + 1 {
            // Might be homogeneous coordinates missing the last row
            // For n×n homogeneous matrix stored as (n-1)×n, check structure
            return self.is_homogeneous_translation(element, matrix_dim);
        }
        
        // Check for affine representation (rotation + translation)
        // Common patterns: SO(2) × R² (4 params), SO(3) × R³ (12 params)
        if n == 4 || n == 12 {
            return self.is_affine_translation(element, n);
        }
        
        // Check for block matrix representation
        let block_dim = (n as f64).sqrt() as usize;
        if block_dim * block_dim == n && block_dim > 1 {
            return self.is_block_matrix_translation(element, block_dim);
        }
        
        // Fallback: check if element acts as pure translation
        // by examining its effect on standard basis vectors
        self.check_translation_action(element)
    }
    
    /// Check if element is translation in homogeneous coordinates
    fn is_homogeneous_translation(&self, element: &GroupElement<P>, dim: usize) -> bool {
        // For homogeneous matrix [[R, t], [0, 1]], check R = I
        // Since we're missing the last row, just check the rotation part
        
        let rot_size = (dim - 1) * (dim - 1);
        let _identity = self.identity();
        
        // Check rotation part is identity
        for i in 0..rot_size {
            let row = i / (dim - 1);
            let col = i % (dim - 1);
            let expected = if row == col { P::one() } else { P::zero() };
            
            if (element.params[i] - expected).abs() > P::epsilon() {
                return false;
            }
        }
        
        // Check translation part is non-zero
        let trans_start = rot_size;
        let mut has_translation = false;
        
        for i in trans_start..element.params.len().min(trans_start + dim - 1) {
            if element.params[i].abs() > P::epsilon() {
                has_translation = true;
                break;
            }
        }
        
        has_translation
    }
    
    /// Check if element is translation in affine representation
    fn is_affine_translation(&self, element: &GroupElement<P>, n: usize) -> bool {
        match n {
            4 => {
                // SO(2) × R²: params are [cos θ, sin θ, tx, ty]
                // Pure translation has θ = 0, so cos θ = 1, sin θ = 0
                let cos_theta = element.params[0];
                let sin_theta = element.params[1];
                let tx = element.params[2];
                let ty = element.params[3];
                
                (cos_theta - P::one()).abs() < P::epsilon() &&
                sin_theta.abs() < P::epsilon() &&
                (tx.abs() > P::epsilon() || ty.abs() > P::epsilon())
            }
            12 => {
                // SO(3) × R³: 9 rotation params + 3 translation params
                // Check if rotation part is identity
                for i in 0..9 {
                    let row = i / 3;
                    let col = i % 3;
                    let expected = if row == col { P::one() } else { P::zero() };
                    
                    if (element.params[i] - expected).abs() > P::epsilon() {
                        return false;
                    }
                }
                
                // Check translation part is non-zero
                element.params[9].abs() > P::epsilon() ||
                element.params[10].abs() > P::epsilon() ||
                element.params[11].abs() > P::epsilon()
            }
            _ => false
        }
    }
    
    /// Check if element is translation in block matrix form
    fn is_block_matrix_translation(&self, element: &GroupElement<P>, dim: usize) -> bool {
        // For block matrix [[I, 0], [v, I]], check upper-left and lower-right are identity
        
        // Check upper-left block (should be identity)
        for i in 0..dim {
            for j in 0..dim {
                let idx = i * dim + j;
                let expected = if i == j { P::one() } else { P::zero() };
                
                if (element.params[idx] - expected).abs() > P::epsilon() {
                    return false;
                }
            }
        }
        
        // Lower-left block contains translation, lower-right should be identity
        let half = dim * dim / 2;
        
        // Check lower-right block
        for i in 0..dim/2 {
            for j in 0..dim/2 {
                let idx = half + i * (dim/2) + j;
                if idx < element.params.len() {
                    let expected = if i == j { P::one() } else { P::zero() };
                    if (element.params[idx] - expected).abs() > P::epsilon() {
                        return false;
                    }
                }
            }
        }
        
        // Check if there's non-zero translation in lower-left block
        let mut has_translation = false;
        for i in dim..half {
            if element.params[i].abs() > P::epsilon() {
                has_translation = true;
                break;
            }
        }
        
        has_translation
    }
    
    /// Check translation by examining action on basis vectors
    fn check_translation_action(&self, element: &GroupElement<P>) -> bool {
        // A pure translation satisfies: g(x) - g(y) = x - y for all x, y
        // We can verify this by checking the Jacobian is identity
        
        // Create a vector space action to test
        let action = VectorSpaceAction::new(self.dimension);
        
        // Test points: origin and basis vectors
        let origin = vec![P::zero(); self.dimension];
        let mut basis_vectors = Vec::new();
        
        for i in 0..self.dimension {
            let mut ei = vec![P::zero(); self.dimension];
            ei[i] = P::one();
            basis_vectors.push(ei);
        }
        
        // Apply transformation to origin
        if let Ok(transformed_origin) = action.apply(element, &origin) {
            // For pure translation, g(0) = v (the translation vector)
            let translation = transformed_origin;
            
            // Check that g(ei) = ei + v for all basis vectors
            for (_i, ei) in basis_vectors.iter().enumerate() {
                if let Ok(transformed_ei) = action.apply(element, ei) {
                    // Check if g(ei) - ei equals the translation vector
                    for j in 0..self.dimension {
                        let diff = transformed_ei[j] - ei[j];
                        if (diff - translation[j]).abs() > P::epsilon() {
                            return false;
                        }
                    }
                } else {
                    return false;
                }
            }
            
            // Check that translation is non-zero
            let is_non_zero = translation.iter()
                .any(|&x| x.abs() > P::epsilon());
            
            is_non_zero
        } else {
            false
        }
    }
}