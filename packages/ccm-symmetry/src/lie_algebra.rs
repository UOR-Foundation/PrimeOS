//! Lie algebra structure and continuous symmetries

use crate::SymmetryError;
use ccm_core::{CcmError, Float};
use num_traits::{One, Zero};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Element of a Lie algebra
#[derive(Debug, Clone)]
pub struct LieAlgebraElement<P: Float> {
    /// Coefficients in the basis expansion
    pub coefficients: Vec<P>,
    /// Dimension of the Lie algebra
    pub dimension: usize,
}

impl<P: Float> LieAlgebraElement<P> {
    /// Create zero element
    pub fn zero(dimension: usize) -> Self {
        Self {
            coefficients: vec![P::zero(); dimension],
            dimension,
        }
    }
    
    /// Create from coefficients
    pub fn from_coefficients(coeffs: Vec<P>) -> Self {
        let dimension = coeffs.len();
        Self {
            coefficients: coeffs,
            dimension,
        }
    }
    
    /// Scale by a constant
    pub fn scale(&self, c: P) -> Self {
        Self {
            coefficients: self.coefficients.iter().map(|&x| x * c).collect(),
            dimension: self.dimension,
        }
    }
    
    /// Add two elements
    pub fn add(&self, other: &Self) -> Result<Self, CcmError> {
        if self.dimension != other.dimension {
            return Err(SymmetryError::LieAlgebraError.into());
        }
        
        let coeffs: Vec<P> = self.coefficients.iter()
            .zip(&other.coefficients)
            .map(|(&a, &b)| a + b)
            .collect();
            
        Ok(Self::from_coefficients(coeffs))
    }
}

/// Lie algebra with bracket operation
pub struct LieAlgebra<P: Float> {
    /// Dimension of the algebra
    pub dimension: usize,
    /// Basis elements
    pub basis: Vec<LieAlgebraElement<P>>,
    /// Structure constants C^k_ij where [e_i, e_j] = C^k_ij e_k
    pub structure_constants: Vec<Vec<Vec<P>>>,
}

impl<P: Float> LieAlgebra<P> {
    /// Create a new Lie algebra from structure constants
    pub fn from_structure_constants(structure_constants: Vec<Vec<Vec<P>>>) -> Result<Self, CcmError> {
        let dimension = structure_constants.len();
        
        // Verify antisymmetry: C^k_ij = -C^k_ji
        for i in 0..dimension {
            for j in 0..dimension {
                for k in 0..dimension {
                    let c_ijk = structure_constants[i][j][k];
                    let c_jik = structure_constants[j][i][k];
                    if (c_ijk + c_jik).abs() > P::epsilon() {
                        return Err(SymmetryError::LieAlgebraError.into());
                    }
                }
            }
        }
        
        // Create basis
        let mut basis = Vec::new();
        for i in 0..dimension {
            let mut coeffs = vec![P::zero(); dimension];
            coeffs[i] = P::one();
            basis.push(LieAlgebraElement::from_coefficients(coeffs));
        }
        
        Ok(Self {
            dimension,
            basis,
            structure_constants,
        })
    }
    
    /// Compute Lie bracket [X, Y]
    pub fn bracket(&self, x: &LieAlgebraElement<P>, y: &LieAlgebraElement<P>) -> Result<LieAlgebraElement<P>, CcmError> {
        if x.dimension != self.dimension || y.dimension != self.dimension {
            return Err(SymmetryError::LieAlgebraError.into());
        }
        
        let mut result = LieAlgebraElement::zero(self.dimension);
        
        // [X, Y] = X^i Y^j [e_i, e_j] = X^i Y^j C^k_ij e_k
        for i in 0..self.dimension {
            for j in 0..self.dimension {
                for k in 0..self.dimension {
                    result.coefficients[k] = result.coefficients[k] + 
                        x.coefficients[i] * y.coefficients[j] * self.structure_constants[i][j][k];
                }
            }
        }
        
        Ok(result)
    }
    
    /// Check Jacobi identity for basis elements
    pub fn verify_jacobi_identity(&self) -> bool {
        // [[X,Y],Z] + [[Y,Z],X] + [[Z,X],Y] = 0
        for i in 0..self.dimension {
            for j in 0..self.dimension {
                for k in 0..self.dimension {
                    let mut sum = P::zero();
                    
                    // [[e_i, e_j], e_k]
                    for l in 0..self.dimension {
                        for m in 0..self.dimension {
                            sum = sum + self.structure_constants[i][j][l] * self.structure_constants[l][k][m];
                        }
                    }
                    
                    // [[e_j, e_k], e_i]
                    for l in 0..self.dimension {
                        for m in 0..self.dimension {
                            sum = sum + self.structure_constants[j][k][l] * self.structure_constants[l][i][m];
                        }
                    }
                    
                    // [[e_k, e_i], e_j]
                    for l in 0..self.dimension {
                        for m in 0..self.dimension {
                            sum = sum + self.structure_constants[k][i][l] * self.structure_constants[l][j][m];
                        }
                    }
                    
                    if sum.abs() > P::epsilon() {
                        return false;
                    }
                }
            }
        }
        
        true
    }
}

/// Exponential map from Lie algebra to group
pub fn exponential_map<P: Float>(
    x: &LieAlgebraElement<P>,
    t: P,
    max_terms: usize,
) -> Result<Vec<P>, CcmError> {
    // exp(tX) = I + tX + (tX)²/2! + (tX)³/3! + ...
    // This returns coefficients in matrix representation
    
    let dim = x.dimension;
    let mut result = vec![P::zero(); dim * dim]; // Matrix representation
    let mut tx_power = vec![P::zero(); dim * dim]; // (tX)^n
    let mut temp = vec![P::zero(); dim * dim]; // Temporary for multiplication
    
    // Identity matrix
    for i in 0..dim {
        result[i * dim + i] = P::one();
        tx_power[i * dim + i] = P::one(); // Start with I for multiplication
    }
    
    // Convert Lie algebra element to matrix representation
    // For so(n), skew-symmetric matrices
    let mut tx_matrix = vec![P::zero(); dim * dim];
    
    // Build skew-symmetric matrix from coefficients
    // For so(3): X = a*L_x + b*L_y + c*L_z where L_i are generators
    if dim == 3 {
        // so(3) generators
        tx_matrix[1] = -t * x.coefficients[2]; // -c at position [0,1]
        tx_matrix[2] = t * x.coefficients[1];  // b at position [0,2]
        tx_matrix[3] = t * x.coefficients[2];  // c at position [1,0]
        tx_matrix[5] = -t * x.coefficients[0]; // -a at position [1,2]
        tx_matrix[6] = -t * x.coefficients[1]; // -b at position [2,0]
        tx_matrix[7] = t * x.coefficients[0];  // a at position [2,1]
    } else {
        // General case: use structure constants
        // This would require the full Lie algebra structure
        return Err(CcmError::Custom("Exponential map only implemented for so(3)"));
    }
    
    let mut factorial = P::one();
    
    // Power series expansion
    for n in 1..=max_terms {
        // Multiply tx_power by tx_matrix
        for i in 0..dim {
            for j in 0..dim {
                let mut sum = P::zero();
                for k in 0..dim {
                    sum = sum + tx_power[i * dim + k] * tx_matrix[k * dim + j];
                }
                temp[i * dim + j] = sum;
            }
        }
        
        // Copy temp to tx_power
        tx_power.copy_from_slice(&temp);
        
        // Update factorial
        factorial = factorial * P::from(n).unwrap();
        
        // Add term to result
        let inv_factorial = P::one() / factorial;
        for i in 0..dim * dim {
            result[i] = result[i] + tx_power[i] * inv_factorial;
        }
        
        // Check convergence
        let norm = tx_power.iter().map(|&x| x * x).fold(P::zero(), |a, b| a + b).sqrt();
        if norm * inv_factorial < P::epsilon() {
            break;
        }
    }
    
    Ok(result)
}

/// Specialized exponential map for so(3) using Rodrigues' formula
pub fn exponential_map_so3<P: Float>(
    axis: &[P; 3],
    angle: P,
) -> Result<Vec<P>, CcmError> {
    // Rodrigues' formula: exp(θK) = I + sin(θ)K + (1-cos(θ))K²
    // where K is the skew-symmetric matrix for axis
    
    let mut result = vec![P::zero(); 9];
    
    // Normalize axis
    let norm = (axis[0] * axis[0] + axis[1] * axis[1] + axis[2] * axis[2]).sqrt();
    if norm < P::epsilon() {
        // Zero rotation - return identity
        result[0] = P::one();
        result[4] = P::one();
        result[8] = P::one();
        return Ok(result);
    }
    
    let k = [axis[0] / norm, axis[1] / norm, axis[2] / norm];
    let c = angle.cos();
    let s = angle.sin();
    let one_minus_c = P::one() - c;
    
    // Rodrigues formula components
    result[0] = c + k[0] * k[0] * one_minus_c;
    result[1] = -k[2] * s + k[0] * k[1] * one_minus_c;
    result[2] = k[1] * s + k[0] * k[2] * one_minus_c;
    
    result[3] = k[2] * s + k[1] * k[0] * one_minus_c;
    result[4] = c + k[1] * k[1] * one_minus_c;
    result[5] = -k[0] * s + k[1] * k[2] * one_minus_c;
    
    result[6] = -k[1] * s + k[2] * k[0] * one_minus_c;
    result[7] = k[0] * s + k[2] * k[1] * one_minus_c;
    result[8] = c + k[2] * k[2] * one_minus_c;
    
    Ok(result)
}

/// Lie derivative D_X acting on functions
pub struct LieDerivative<P: Float> {
    /// The vector field X
    pub vector_field: LieAlgebraElement<P>,
}

impl<P: Float> LieDerivative<P> {
    /// Create a new Lie derivative operator
    pub fn new(x: LieAlgebraElement<P>) -> Self {
        Self { vector_field: x }
    }
    
    /// Apply to a scalar function on the manifold
    pub fn apply_scalar<F>(&self, f: F, point: &[P]) -> Result<P, CcmError>
    where
        F: Fn(&[P]) -> P,
    {
        // D_X f = X^i ∂f/∂x^i (directional derivative)
        let dim = self.vector_field.dimension;
        if point.len() != dim {
            return Err(CcmError::InvalidInput);
        }
        
        let mut result = P::zero();
        let h = P::from(1e-8).unwrap_or(P::epsilon()); // Small step for numerical derivative
        
        // Compute directional derivative
        for i in 0..dim {
            if self.vector_field.coefficients[i].abs() > P::epsilon() {
                // Compute partial derivative ∂f/∂x^i
                let mut point_plus = point.to_vec();
                let mut point_minus = point.to_vec();
                
                point_plus[i] = point_plus[i] + h;
                point_minus[i] = point_minus[i] - h;
                
                let df_dxi = (f(&point_plus) - f(&point_minus)) / (h + h);
                result = result + self.vector_field.coefficients[i] * df_dxi;
            }
        }
        
        Ok(result)
    }
    
    /// Apply to a vector field
    pub fn apply_vector(&self, y: &LieAlgebraElement<P>, algebra: &LieAlgebra<P>) -> Result<LieAlgebraElement<P>, CcmError> {
        // [X, Y] = Lie bracket
        algebra.bracket(&self.vector_field, y)
    }
    
    /// Apply to a differential form (simplified for 1-forms)
    pub fn apply_form(&self, omega: &[P], point: &[P]) -> Result<Vec<P>, CcmError> {
        // L_X ω = d(i_X ω) + i_X(dω) (Cartan's formula)
        // For 1-forms: (L_X ω)_i = X^j ∂ω_i/∂x^j + ω_j ∂X^j/∂x^i
        
        let dim = self.vector_field.dimension;
        if omega.len() != dim || point.len() != dim {
            return Err(CcmError::InvalidInput);
        }
        
        let mut result = vec![P::zero(); dim];
        let h = P::from(1e-8).unwrap_or(P::epsilon());
        
        for i in 0..dim {
            // First term: X^j ∂ω_i/∂x^j
            for j in 0..dim {
                if self.vector_field.coefficients[j].abs() > P::epsilon() {
                    let mut point_plus = point.to_vec();
                    let mut point_minus = point.to_vec();
                    
                    point_plus[j] = point_plus[j] + h;
                    point_minus[j] = point_minus[j] - h;
                    
                    // Assuming omega depends on position (would need function for omega(x))
                    // For now, assume constant form
                    let domega_dxj = P::zero();
                    result[i] = result[i] + self.vector_field.coefficients[j] * domega_dxj;
                }
            }
            
            // Second term: ω_j ∂X^j/∂x^i
            // This requires knowing how X varies with position
            // For constant vector field, this term is zero
        }
        
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_lie_algebra_element() {
        let x = LieAlgebraElement::<f64>::from_coefficients(vec![1.0, 2.0, 3.0]);
        let y = LieAlgebraElement::from_coefficients(vec![4.0, 5.0, 6.0]);
        
        let sum = x.add(&y).unwrap();
        assert_eq!(sum.coefficients, vec![5.0, 7.0, 9.0]);
        
        let scaled = x.scale(2.0);
        assert_eq!(scaled.coefficients, vec![2.0, 4.0, 6.0]);
    }
    
    #[test]
    fn test_lie_algebra_antisymmetry() {
        // sl(2) structure constants
        let mut structure = vec![vec![vec![0.0; 3]; 3]; 3];
        
        // [e_0, e_1] = e_2
        structure[0][1][2] = 1.0;
        structure[1][0][2] = -1.0;
        
        // [e_1, e_2] = e_0  
        structure[1][2][0] = 1.0;
        structure[2][1][0] = -1.0;
        
        // [e_2, e_0] = e_1
        structure[2][0][1] = 1.0;
        structure[0][2][1] = -1.0;
        
        let algebra = LieAlgebra::<f64>::from_structure_constants(structure).unwrap();
        assert_eq!(algebra.dimension, 3);
    }
}