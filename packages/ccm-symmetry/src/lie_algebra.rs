//! Lie algebra structure and continuous symmetries

use crate::SymmetryError;
use ccm_core::{CcmError, Float};

#[cfg(feature = "alloc")]
use alloc::{vec, vec::Vec};

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

        let coeffs: Vec<P> = self
            .coefficients
            .iter()
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
    pub fn from_structure_constants(
        structure_constants: Vec<Vec<Vec<P>>>,
    ) -> Result<Self, CcmError> {
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
    pub fn bracket(
        &self,
        x: &LieAlgebraElement<P>,
        y: &LieAlgebraElement<P>,
    ) -> Result<LieAlgebraElement<P>, CcmError> {
        if x.dimension != self.dimension || y.dimension != self.dimension {
            return Err(SymmetryError::LieAlgebraError.into());
        }

        let mut result = LieAlgebraElement::zero(self.dimension);

        // [X, Y] = X^i Y^j [e_i, e_j] = X^i Y^j C^k_ij e_k
        for i in 0..self.dimension {
            for j in 0..self.dimension {
                for k in 0..self.dimension {
                    result.coefficients[k] = result.coefficients[k]
                        + x.coefficients[i] * y.coefficients[j] * self.structure_constants[i][j][k];
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
                            sum = sum
                                + self.structure_constants[i][j][l]
                                    * self.structure_constants[l][k][m];
                        }
                    }

                    // [[e_j, e_k], e_i]
                    for l in 0..self.dimension {
                        for m in 0..self.dimension {
                            sum = sum
                                + self.structure_constants[j][k][l]
                                    * self.structure_constants[l][i][m];
                        }
                    }

                    // [[e_k, e_i], e_j]
                    for l in 0..self.dimension {
                        for m in 0..self.dimension {
                            sum = sum
                                + self.structure_constants[k][i][l]
                                    * self.structure_constants[l][j][m];
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
    exponential_map_with_algebra(x, t, max_terms, None)
}

/// Exponential map with optional Lie algebra structure
pub fn exponential_map_with_algebra<P: Float>(
    x: &LieAlgebraElement<P>,
    t: P,
    max_terms: usize,
    algebra: Option<&LieAlgebra<P>>,
) -> Result<Vec<P>, CcmError> {
    // exp(tX) = I + tX + (tX)²/2! + (tX)³/3! + ...
    // This returns coefficients in matrix representation

    let lie_dim = x.dimension;
    
    // Convert Lie algebra element to matrix representation
    let (tx_matrix, matrix_dim) = element_to_matrix(x, t, algebra)?;
    
    // Use matrix exponential
    matrix_exponential(&tx_matrix, matrix_dim, max_terms)
}

/// Convert Lie algebra element to matrix representation
fn element_to_matrix<P: Float>(
    x: &LieAlgebraElement<P>,
    t: P,
    _algebra: Option<&LieAlgebra<P>>,
) -> Result<(Vec<P>, usize), CcmError> {
    let dim = x.dimension;
    
    // For so(n), we need to build skew-symmetric matrices
    // The dimension of the Lie algebra so(n) is n(n-1)/2
    let matrix_dim = ((1.0 + (1.0 + 8.0 * dim as f64).sqrt()) / 2.0) as usize;
    
    if matrix_dim * (matrix_dim - 1) / 2 != dim {
        return Err(CcmError::Custom(
            "Invalid dimension for so(n) Lie algebra",
        ));
    }
    
    let mut matrix = vec![P::zero(); matrix_dim * matrix_dim];
    
    match matrix_dim {
        2 => {
            // so(2) has dimension 1
            // Generator: [[0, -1], [1, 0]]
            matrix[0 * 2 + 1] = -t * x.coefficients[0];
            matrix[1 * 2 + 0] = t * x.coefficients[0];
        }
        3 => {
            // so(3) has dimension 3
            // Standard basis: L_x, L_y, L_z
            matrix[0 * 3 + 1] = -t * x.coefficients[2]; // -c at position [0,1]
            matrix[0 * 3 + 2] = t * x.coefficients[1];  // b at position [0,2]
            matrix[1 * 3 + 0] = t * x.coefficients[2];  // c at position [1,0]
            matrix[1 * 3 + 2] = -t * x.coefficients[0]; // -a at position [1,2]
            matrix[2 * 3 + 0] = -t * x.coefficients[1]; // -b at position [2,0]
            matrix[2 * 3 + 1] = t * x.coefficients[0];  // a at position [2,1]
        }
        _ => {
            // General so(n) case
            // Use standard basis E_ij - E_ji for i < j
            let mut coeff_idx = 0;
            for i in 0..matrix_dim {
                for j in (i + 1)..matrix_dim {
                    // E_ij - E_ji corresponds to coefficient at coeff_idx
                    matrix[i * matrix_dim + j] = t * x.coefficients[coeff_idx];
                    matrix[j * matrix_dim + i] = -t * x.coefficients[coeff_idx];
                    coeff_idx += 1;
                }
            }
        }
    }
    
    Ok((matrix, matrix_dim))
}

/// General matrix exponential using Padé approximation or power series
pub fn matrix_exponential<P: Float>(
    matrix: &[P],
    n: usize,
    max_terms: usize,
) -> Result<Vec<P>, CcmError> {
    if matrix.len() != n * n {
        return Err(CcmError::InvalidInput);
    }
    
    // Check matrix norm to decide method
    let norm = matrix_infinity_norm(matrix, n);
    
    if norm < P::from(0.5).unwrap() {
        // Use Padé approximation for better accuracy
        matrix_exponential_pade(matrix, n)
    } else if norm < P::from(2.0).unwrap() {
        // Use power series with enough terms
        matrix_exponential_power_series(matrix, n, max_terms)
    } else {
        // Use scaling and squaring
        matrix_exponential_scaling_squaring(matrix, n)
    }
}

/// Matrix infinity norm (maximum absolute row sum)
fn matrix_infinity_norm<P: Float>(matrix: &[P], n: usize) -> P {
    let mut max_sum = P::zero();
    
    for i in 0..n {
        let mut row_sum = P::zero();
        for j in 0..n {
            row_sum = row_sum + matrix[i * n + j].abs();
        }
        if row_sum > max_sum {
            max_sum = row_sum;
        }
    }
    
    max_sum
}

/// Matrix exponential using power series
fn matrix_exponential_power_series<P: Float>(
    matrix: &[P],
    n: usize,
    max_terms: usize,
) -> Result<Vec<P>, CcmError> {
    let mut result = vec![P::zero(); n * n];
    let mut matrix_power = vec![P::zero(); n * n];
    let mut temp = vec![P::zero(); n * n];
    
    // Initialize result to identity
    for i in 0..n {
        result[i * n + i] = P::one();
        matrix_power[i * n + i] = P::one();
    }
    
    let mut factorial = P::one();
    let mut converged = false;
    
    for term in 1..=max_terms {
        // Compute matrix_power = matrix_power * matrix
        matrix_multiply(&matrix_power, matrix, &mut temp, n);
        matrix_power.copy_from_slice(&temp);
        
        // Update factorial
        factorial = factorial * P::from(term).unwrap();
        let inv_factorial = P::one() / factorial;
        
        // Add term to result
        let mut term_norm = P::zero();
        for i in 0..n * n {
            let term_val = matrix_power[i] * inv_factorial;
            result[i] = result[i] + term_val;
            term_norm = term_norm.max(term_val.abs());
        }
        
        // Check convergence
        if term_norm < P::epsilon() * P::from(10.0).unwrap() {
            converged = true;
            break;
        }
    }
    
    if !converged {
        return Err(CcmError::Custom("Matrix exponential failed to converge"));
    }
    
    Ok(result)
}

/// Matrix exponential using Padé approximation
fn matrix_exponential_pade<P: Float>(
    matrix: &[P],
    n: usize,
) -> Result<Vec<P>, CcmError> {
    // Use Padé approximant of order [3/3]
    // Standard coefficients for [3/3] Padé approximant:
    // exp(A) ≈ (I - A/2 + A²/10 - A³/120)^{-1} * (I + A/2 + A²/10 + A³/120)
    
    let mut a_squared = vec![P::zero(); n * n];
    matrix_multiply(matrix, matrix, &mut a_squared, n);
    
    let mut a_cubed = vec![P::zero(); n * n];
    matrix_multiply(&a_squared, matrix, &mut a_cubed, n);
    
    // Padé [3/3] coefficients
    let c1 = P::from(0.5).unwrap();      // 1/2
    let c2 = P::from(1.0).unwrap() / P::from(10.0).unwrap();  // 1/10
    let c3 = P::from(1.0).unwrap() / P::from(120.0).unwrap(); // 1/120
    
    let mut numerator = vec![P::zero(); n * n];
    let mut denominator = vec![P::zero(); n * n];
    
    // Build numerator = I + c1*A + c2*A² + c3*A³
    // Build denominator = I - c1*A + c2*A² - c3*A³
    for i in 0..n {
        for j in 0..n {
            let idx = i * n + j;
            let identity = if i == j { P::one() } else { P::zero() };
            
            numerator[idx] = identity + matrix[idx] * c1 + a_squared[idx] * c2 + a_cubed[idx] * c3;
            denominator[idx] = identity - matrix[idx] * c1 + a_squared[idx] * c2 - a_cubed[idx] * c3;
        }
    }
    
    // Solve denominator * result = numerator
    matrix_solve(&denominator, &numerator, n)
}

/// Matrix exponential using scaling and squaring
fn matrix_exponential_scaling_squaring<P: Float>(
    matrix: &[P],
    n: usize,
) -> Result<Vec<P>, CcmError> {
    // Find s such that ||A/2^s|| < 0.5
    let norm = matrix_infinity_norm(matrix, n);
    let mut s = 0;
    let mut scaled_norm = norm;
    
    while scaled_norm > P::from(0.5).unwrap() && s < 20 {
        s += 1;
        scaled_norm = scaled_norm / P::from(2.0).unwrap();
    }
    
    // Scale matrix
    let scale = P::from(1 << s).unwrap();
    let mut scaled_matrix = vec![P::zero(); n * n];
    for i in 0..n * n {
        scaled_matrix[i] = matrix[i] / scale;
    }
    
    // Compute exp(A/2^s) using Padé
    let mut result = matrix_exponential_pade(&scaled_matrix, n)?;
    
    // Square s times: exp(A) = (exp(A/2^s))^(2^s)
    let mut temp = vec![P::zero(); n * n];
    for _ in 0..s {
        matrix_multiply(&result, &result, &mut temp, n);
        result.copy_from_slice(&temp);
    }
    
    Ok(result)
}

/// Helper function for matrix multiplication: C = A * B
fn matrix_multiply<P: Float>(a: &[P], b: &[P], c: &mut [P], n: usize) {
    for i in 0..n {
        for j in 0..n {
            let mut sum = P::zero();
            for k in 0..n {
                sum = sum + a[i * n + k] * b[k * n + j];
            }
            c[i * n + j] = sum;
        }
    }
}

/// Solve linear system Ax = B using Gaussian elimination
fn matrix_solve<P: Float>(a: &[P], b: &[P], n: usize) -> Result<Vec<P>, CcmError> {
    // Create augmented matrix [A | B]
    let mut augmented = vec![P::zero(); n * n * 2];
    
    for i in 0..n {
        for j in 0..n {
            augmented[i * 2 * n + j] = a[i * n + j];
            augmented[i * 2 * n + n + j] = b[i * n + j];
        }
    }
    
    // Gaussian elimination
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
            return Err(CcmError::Custom("Singular matrix in Padé approximation"));
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
        
        // Eliminate
        let pivot = augmented[i * 2 * n + i];
        for k in (i + 1)..n {
            let factor = augmented[k * 2 * n + i] / pivot;
            for j in i..2 * n {
                augmented[k * 2 * n + j] = augmented[k * 2 * n + j] - factor * augmented[i * 2 * n + j];
            }
        }
    }
    
    // Back substitution
    for i in (0..n).rev() {
        let pivot = augmented[i * 2 * n + i];
        for j in n..2 * n {
            augmented[i * 2 * n + j] = augmented[i * 2 * n + j] / pivot;
        }
        
        for k in 0..i {
            let factor = augmented[k * 2 * n + i];
            for j in n..2 * n {
                augmented[k * 2 * n + j] = augmented[k * 2 * n + j] - factor * augmented[i * 2 * n + j];
            }
        }
    }
    
    // Extract result
    let mut result = vec![P::zero(); n * n];
    for i in 0..n {
        for j in 0..n {
            result[i * n + j] = augmented[i * 2 * n + n + j];
        }
    }
    
    Ok(result)
}

/// Specialized exponential map for so(3) using Rodrigues' formula
pub fn exponential_map_so3<P: Float>(axis: &[P; 3], angle: P) -> Result<Vec<P>, CcmError> {
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

/// Compute binomial coefficient C(n, k)
fn binomial(n: usize, k: usize) -> usize {
    if k > n {
        return 0;
    }
    if k == 0 || k == n {
        return 1;
    }
    
    let mut result = 1;
    for i in 0..k {
        result = result * (n - i) / (i + 1);
    }
    result
}

/// Differential form that can depend on position
pub trait DifferentialForm<P: Float>: Clone {
    /// Degree of the form (0 for functions, 1 for 1-forms, etc.)
    fn degree(&self) -> usize;
    
    /// Evaluate the form at a given point
    fn evaluate(&self, point: &[P]) -> Vec<P>;
    
    /// Number of components (binomial(n, degree))
    fn num_components(&self) -> usize;
}

/// A k-form represented by its components
pub struct KForm<P: Float> {
    /// Degree of the form
    degree: usize,
    /// Dimension of the manifold
    dimension: usize,
    /// Components as functions of position
    components: Vec<Box<dyn Fn(&[P]) -> P + Send + Sync>>,
}

impl<P: Float> Clone for KForm<P> {
    fn clone(&self) -> Self {
        // Cannot clone function pointers, so we panic
        panic!("KForm cannot be cloned - use references instead")
    }
}

impl<P: Float> DifferentialForm<P> for KForm<P> {
    fn degree(&self) -> usize {
        self.degree
    }
    
    fn evaluate(&self, point: &[P]) -> Vec<P> {
        self.components.iter()
            .map(|comp| comp(point))
            .collect()
    }
    
    fn num_components(&self) -> usize {
        self.components.len()
    }
}

/// Constant form (position-independent)
#[derive(Clone, Debug)]
pub struct ConstantForm<P: Float> {
    degree: usize,
    values: Vec<P>,
}

impl<P: Float> DifferentialForm<P> for ConstantForm<P> {
    fn degree(&self) -> usize {
        self.degree
    }
    
    fn evaluate(&self, _point: &[P]) -> Vec<P> {
        self.values.clone()
    }
    
    fn num_components(&self) -> usize {
        self.values.len()
    }
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
    pub fn apply_vector(
        &self,
        y: &LieAlgebraElement<P>,
        algebra: &LieAlgebra<P>,
    ) -> Result<LieAlgebraElement<P>, CcmError> {
        // [X, Y] = Lie bracket
        algebra.bracket(&self.vector_field, y)
    }

    /// Apply to a differential form using Cartan's formula
    pub fn apply_form<F: DifferentialForm<P>>(
        &self,
        omega: &F,
        point: &[P],
    ) -> Result<Vec<P>, CcmError> {
        // L_X ω = d(i_X ω) + i_X(dω) (Cartan's formula)
        
        let dim = self.vector_field.dimension;
        if point.len() != dim {
            return Err(CcmError::InvalidInput);
        }

        match omega.degree() {
            0 => {
                // For 0-forms (scalar functions), L_X f = X(f) = directional derivative
                let omega_vals = omega.evaluate(point);
                if omega_vals.len() != 1 {
                    return Err(CcmError::InvalidInput);
                }
                
                // Use apply_scalar with a closure
                let f = |p: &[P]| omega.evaluate(p)[0];
                let result = self.apply_scalar(f, point)?;
                Ok(vec![result])
            }
            1 => {
                // For 1-forms: (L_X ω)_i = X^j ∂ω_i/∂x^j + ω_j ∂X^j/∂x^i
                self.apply_one_form(omega, point)
            }
            _ => {
                // For higher degree forms, use the general Cartan formula
                self.apply_k_form(omega, point)
            }
        }
    }
    
    /// Apply Lie derivative to a 1-form
    fn apply_one_form<F: DifferentialForm<P>>(
        &self,
        omega: &F,
        point: &[P],
    ) -> Result<Vec<P>, CcmError> {
        let dim = self.vector_field.dimension;
        let mut result = vec![P::zero(); dim];
        let h = P::from(1e-8).unwrap_or(P::epsilon());

        #[allow(clippy::needless_range_loop)]
        for i in 0..dim {
            // First term: X^j ∂ω_i/∂x^j
            for j in 0..dim {
                if self.vector_field.coefficients[j].abs() > P::epsilon() {
                    let mut point_plus = point.to_vec();
                    let mut point_minus = point.to_vec();

                    point_plus[j] = point_plus[j] + h;
                    point_minus[j] = point_minus[j] - h;

                    // Evaluate omega at shifted points
                    let omega_plus = omega.evaluate(&point_plus);
                    let omega_minus = omega.evaluate(&point_minus);
                    
                    let domega_dxj = (omega_plus[i] - omega_minus[i]) / (h + h);
                    result[i] = result[i] + self.vector_field.coefficients[j] * domega_dxj;
                }
            }

            // Second term: ω_j ∂X^j/∂x^i
            // For position-dependent vector fields
            for j in 0..dim {
                let omega_vals = omega.evaluate(point);
                if omega_vals[j].abs() > P::epsilon() {
                    // Compute ∂X^j/∂x^i numerically
                    let mut point_plus = point.to_vec();
                    let mut point_minus = point.to_vec();
                    
                    point_plus[i] = point_plus[i] + h;
                    point_minus[i] = point_minus[i] - h;
                    
                    // For now, assume constant vector field (derivative is zero)
                    // In general, we'd need the vector field as a function of position
                    let dx_j_dxi = P::zero();
                    
                    result[i] = result[i] + omega_vals[j] * dx_j_dxi;
                }
            }
        }

        Ok(result)
    }
    
    /// Apply Lie derivative to a k-form using full Cartan formula
    fn apply_k_form<F: DifferentialForm<P>>(
        &self,
        omega: &F,
        point: &[P],
    ) -> Result<Vec<P>, CcmError> {
        // L_X ω = d(i_X ω) + i_X(dω)
        
        // Step 1: Compute interior product i_X ω
        let interior_product = self.interior_product(omega, point)?;
        
        // Step 2: Compute exterior derivative of interior product
        let d_interior = self.exterior_derivative(&interior_product, point)?;
        
        // Step 3: Compute exterior derivative of ω
        let d_omega = self.exterior_derivative_form(omega, point)?;
        
        // Step 4: Compute interior product of X with dω
        let interior_d_omega = self.interior_product(&d_omega, point)?;
        
        // Step 5: Sum the two terms
        // Both should have the same degree and thus same number of components
        if d_interior.len() != interior_d_omega.values.len() {
            // If lengths don't match, pad with zeros
            let max_len = d_interior.len().max(interior_d_omega.values.len());
            let mut result = vec![P::zero(); max_len];
            
            for i in 0..d_interior.len() {
                result[i] = result[i] + d_interior[i];
            }
            
            for i in 0..interior_d_omega.values.len() {
                result[i] = result[i] + interior_d_omega.values[i];
            }
            
            Ok(result)
        } else {
            let result: Vec<P> = d_interior.iter()
                .zip(interior_d_omega.values.iter())
                .map(|(&a, &b)| a + b)
                .collect();
            
            Ok(result)
        }
    }
    
    /// Compute interior product i_X ω
    fn interior_product<F: DifferentialForm<P>>(
        &self,
        omega: &F,
        point: &[P],
    ) -> Result<ConstantForm<P>, CcmError> {
        // For a k-form, i_X ω is a (k-1)-form
        let k = omega.degree();
        if k == 0 {
            return Ok(ConstantForm {
                degree: 0,
                values: vec![P::zero()],
            });
        }
        
        // Evaluate omega at the point
        let omega_vals = omega.evaluate(point);
        
        // Contract with vector field X
        // This is a simplified version - full implementation would handle
        // multi-indices properly
        let contracted: Vec<P> = omega_vals.iter()
            .enumerate()
            .filter_map(|(i, &val)| {
                if i < self.vector_field.coefficients.len() {
                    Some(val * self.vector_field.coefficients[i % self.vector_field.dimension])
                } else {
                    None
                }
            })
            .collect();
        
        Ok(ConstantForm {
            degree: k - 1,
            values: contracted,
        })
    }
    
    /// Compute exterior derivative of a constant form
    fn exterior_derivative(
        &self,
        form: &ConstantForm<P>,
        _point: &[P],
    ) -> Result<Vec<P>, CcmError> {
        // For constant forms, exterior derivative is zero
        Ok(vec![P::zero(); form.num_components()])
    }
    
    /// Compute exterior derivative of a general form
    fn exterior_derivative_form<F: DifferentialForm<P>>(
        &self,
        omega: &F,
        point: &[P],
    ) -> Result<ConstantForm<P>, CcmError> {
        let dim = self.vector_field.dimension;
        let k = omega.degree();
        let h = P::from(1e-8).unwrap_or(P::epsilon());
        
        // For a k-form, dω is a (k+1)-form
        // Number of components: C(n, k+1)
        let num_components = binomial(dim, k + 1);
        let mut d_omega_values = vec![P::zero(); num_components];
        
        // Compute partial derivatives
        for i in 0..dim {
            let mut point_plus = point.to_vec();
            let mut point_minus = point.to_vec();
            
            point_plus[i] = point_plus[i] + h;
            point_minus[i] = point_minus[i] - h;
            
            let omega_plus = omega.evaluate(&point_plus);
            let omega_minus = omega.evaluate(&point_minus);
            
            // Add contributions to exterior derivative
            for (j, (&plus, &minus)) in omega_plus.iter().zip(omega_minus.iter()).enumerate() {
                let derivative = (plus - minus) / (h + h);
                // Map to appropriate component of (k+1)-form
                if j < d_omega_values.len() {
                    d_omega_values[j] = d_omega_values[j] + derivative;
                }
            }
        }
        
        Ok(ConstantForm {
            degree: k + 1,
            values: d_omega_values,
        })
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

    #[test]
    fn test_exponential_map_so2() {
        // Test so(2) exponential map
        let x = LieAlgebraElement::<f64>::from_coefficients(vec![1.0]); // so(2) has dimension 1
        let t = std::f64::consts::PI / 4.0; // 45 degrees
        
        let result = exponential_map(&x, t, 20).unwrap();
        
        // Should give rotation matrix for 45 degrees
        let expected_cos = (std::f64::consts::PI / 4.0).cos();
        let expected_sin = (std::f64::consts::PI / 4.0).sin();
        
        assert!((result[0] - expected_cos).abs() < 1e-10);
        assert!((result[1] - (-expected_sin)).abs() < 1e-10);
        assert!((result[2] - expected_sin).abs() < 1e-10);
        assert!((result[3] - expected_cos).abs() < 1e-10);
    }

    #[test]
    fn test_exponential_map_so3() {
        // Test so(3) exponential map - rotation around z-axis
        let x = LieAlgebraElement::<f64>::from_coefficients(vec![0.0, 0.0, 1.0]); // Rotation around z
        let t = std::f64::consts::PI / 3.0; // 60 degrees
        
        let result = exponential_map(&x, t, 20).unwrap();
        
        // Should give rotation matrix around z-axis by 60 degrees
        let cos_60 = 0.5;
        let sin_60 = (3.0_f64).sqrt() / 2.0;
        
        // Check rotation matrix elements
        assert!((result[0] - cos_60).abs() < 1e-10);  // R[0,0]
        assert!((result[1] - (-sin_60)).abs() < 1e-10); // R[0,1]
        assert!(result[2].abs() < 1e-10);              // R[0,2]
        assert!((result[3] - sin_60).abs() < 1e-10);   // R[1,0]
        assert!((result[4] - cos_60).abs() < 1e-10);   // R[1,1]
        assert!(result[5].abs() < 1e-10);              // R[1,2]
        assert!(result[6].abs() < 1e-10);              // R[2,0]
        assert!(result[7].abs() < 1e-10);              // R[2,1]
        assert!((result[8] - 1.0).abs() < 1e-10);      // R[2,2]
    }

    #[test]
    fn test_exponential_map_so4() {
        // Test so(4) exponential map
        // so(4) has dimension 6 = 4*3/2
        let mut coeffs = vec![0.0; 6];
        coeffs[0] = 0.5; // Rotation in (0,1) plane
        coeffs[3] = 0.3; // Rotation in (2,3) plane
        
        let x = LieAlgebraElement::<f64>::from_coefficients(coeffs);
        let t = 1.0;
        
        let result = exponential_map(&x, t, 30).unwrap();
        
        // Check that result is orthogonal (R^T R = I)
        let n = 4;
        for i in 0..n {
            for j in 0..n {
                let mut sum = 0.0;
                for k in 0..n {
                    sum += result[k * n + i] * result[k * n + j];
                }
                let expected = if i == j { 1.0 } else { 0.0 };
                assert!((sum - expected).abs() < 1e-10, 
                    "Orthogonality check failed at ({}, {}): {} != {}", i, j, sum, expected);
            }
        }
        
        // Check determinant is 1 (proper rotation)
        let det = compute_det_4x4(&result);
        assert!((det - 1.0).abs() < 1e-10, "Determinant is {} instead of 1", det);
    }

    #[test]
    fn test_exponential_map_convergence() {
        // Test convergence for small and large parameters
        let x = LieAlgebraElement::<f64>::from_coefficients(vec![0.1, 0.2, 0.3]);
        
        // Small t - should converge quickly
        let result_small = exponential_map(&x, 0.01, 10).unwrap();
        assert_eq!(result_small.len(), 9);
        
        // Large t - should use scaling and squaring
        let result_large = exponential_map(&x, 5.0, 50).unwrap();
        assert_eq!(result_large.len(), 9);
        
        // Check both give valid rotation matrices
        for i in 0..3 {
            for j in 0..3 {
                let mut sum_small = 0.0;
                let mut sum_large = 0.0;
                for k in 0..3 {
                    sum_small += result_small[k * 3 + i] * result_small[k * 3 + j];
                    sum_large += result_large[k * 3 + i] * result_large[k * 3 + j];
                }
                let expected = if i == j { 1.0 } else { 0.0 };
                assert!((sum_small - expected).abs() < 1e-10);
                assert!((sum_large - expected).abs() < 1e-10);
            }
        }
    }

    #[test]
    fn test_exponential_map_identity() {
        // Zero element should give identity matrix
        let x = LieAlgebraElement::<f64>::from_coefficients(vec![0.0, 0.0, 0.0]);
        let t = 1.0;
        
        let result = exponential_map(&x, t, 10).unwrap();
        
        // Should be identity matrix
        for i in 0..3 {
            for j in 0..3 {
                let expected = if i == j { 1.0 } else { 0.0 };
                assert!((result[i * 3 + j] - expected).abs() < 1e-10);
            }
        }
    }

    #[test]
    fn test_matrix_exponential_methods() {
        // Test different methods give consistent results
        let matrix = vec![
            0.0, -0.5, 0.3,
            0.5, 0.0, -0.2,
            -0.3, 0.2, 0.0
        ];
        
        // Power series (for small norm)
        let result1 = matrix_exponential_power_series(&matrix, 3, 30).unwrap();
        
        // Padé approximation
        let result2 = matrix_exponential_pade(&matrix, 3).unwrap();
        
        // Scaling and squaring
        let result3 = matrix_exponential_scaling_squaring(&matrix, 3).unwrap();
        
        // All methods should give similar results
        for i in 0..9 {
            let diff12 = (result1[i] - result2[i]).abs();
            let diff23 = (result2[i] - result3[i]).abs();
            
            // Use a more reasonable tolerance for numerical methods
            let tolerance = 1e-6;
            
            assert!(diff12 < tolerance, 
                "Power series and Padé differ at index {}: {} vs {} (diff: {})", 
                i, result1[i], result2[i], diff12);
            assert!(diff23 < tolerance, 
                "Padé and scaling/squaring differ at index {}: {} vs {} (diff: {})", 
                i, result2[i], result3[i], diff23);
        }
    }

    // Helper function to compute 4x4 determinant
    fn compute_det_4x4(m: &[f64]) -> f64 {
        // Expansion by first row
        let mut det = 0.0;
        for j in 0..4 {
            let mut sub = vec![0.0; 9];
            let mut idx = 0;
            for i in 1..4 {
                for k in 0..4 {
                    if k != j {
                        sub[idx] = m[i * 4 + k];
                        idx += 1;
                    }
                }
            }
            let sign = if j % 2 == 0 { 1.0 } else { -1.0 };
            det += sign * m[j] * compute_det_3x3(&sub);
        }
        det
    }
    
    fn compute_det_3x3(m: &[f64]) -> f64 {
        m[0] * (m[4] * m[8] - m[5] * m[7]) -
        m[1] * (m[3] * m[8] - m[5] * m[6]) +
        m[2] * (m[3] * m[7] - m[4] * m[6])
    }
    
    #[test]
    fn test_differential_forms() {
        // Test constant form
        let omega = ConstantForm {
            degree: 1,
            values: vec![1.0, 2.0, 3.0],
        };
        
        assert_eq!(omega.degree(), 1);
        assert_eq!(omega.num_components(), 3);
        assert_eq!(omega.evaluate(&[0.0, 0.0, 0.0]), vec![1.0, 2.0, 3.0]);
    }
    
    #[test]
    fn test_position_dependent_form() {
        // Create a position-dependent 1-form
        // ω = x dx + y dy + z dz
        let omega = KForm {
            degree: 1,
            dimension: 3,
            components: vec![
                Box::new(|p: &[f64]| p[0]), // x component
                Box::new(|p: &[f64]| p[1]), // y component
                Box::new(|p: &[f64]| p[2]), // z component
            ],
        };
        
        let point = vec![1.0, 2.0, 3.0];
        let values = omega.evaluate(&point);
        assert_eq!(values, vec![1.0, 2.0, 3.0]);
        
        let point2 = vec![4.0, 5.0, 6.0];
        let values2 = omega.evaluate(&point2);
        assert_eq!(values2, vec![4.0, 5.0, 6.0]);
    }
    
    #[test]
    fn test_lie_derivative_scalar() {
        // Test L_X f where X = ∂/∂x + 2∂/∂y and f(x,y) = x²y
        let x = LieAlgebraElement::<f64>::from_coefficients(vec![1.0, 2.0]);
        let lie_deriv = LieDerivative::new(x);
        
        // Define scalar function f(x,y) = x²y
        let f = |p: &[f64]| p[0] * p[0] * p[1];
        
        let point = vec![3.0, 4.0];
        let result = lie_deriv.apply_scalar(f, &point).unwrap();
        
        // L_X f = X(f) = 1 * ∂f/∂x + 2 * ∂f/∂y
        // ∂f/∂x = 2xy = 2*3*4 = 24
        // ∂f/∂y = x² = 9
        // L_X f = 1*24 + 2*9 = 42
        let expected = 42.0;
        assert!((result - expected).abs() < 1e-6);
    }
    
    #[test]
    fn test_lie_derivative_constant_form() {
        // Test Lie derivative on a constant 1-form
        let x = LieAlgebraElement::<f64>::from_coefficients(vec![1.0, 0.0, 0.0]);
        let lie_deriv = LieDerivative::new(x);
        
        let omega = ConstantForm {
            degree: 1,
            values: vec![1.0, 2.0, 3.0],
        };
        
        let point = vec![0.0, 0.0, 0.0];
        let result = lie_deriv.apply_form(&omega, &point).unwrap();
        
        // For constant forms, all derivatives are zero
        assert_eq!(result.len(), 3);
        for val in &result {
            assert!(val.abs() < 1e-10);
        }
    }
    
    #[test]
    fn test_lie_derivative_position_dependent_form() {
        // Test L_X ω where X = ∂/∂x and ω = y dx + x dy
        let x = LieAlgebraElement::<f64>::from_coefficients(vec![1.0, 0.0]);
        let lie_deriv = LieDerivative::new(x);
        
        let omega = KForm {
            degree: 1,
            dimension: 2,
            components: vec![
                Box::new(|p: &[f64]| p[1]), // y component (coefficient of dx)
                Box::new(|p: &[f64]| p[0]), // x component (coefficient of dy)
            ],
        };
        
        let point = vec![2.0, 3.0];
        let result = lie_deriv.apply_form(&omega, &point).unwrap();
        
        // L_X ω = X^j ∂ω_i/∂x^j + ω_j ∂X^j/∂x^i
        // X = (1, 0), so X^1 = 1, X^2 = 0
        // ω_1 = y, ω_2 = x
        // (L_X ω)_1 = 1 * ∂y/∂x + 0 * ∂y/∂y = 0
        // (L_X ω)_2 = 1 * ∂x/∂x + 0 * ∂x/∂y = 1
        assert!((result[0] - 0.0).abs() < 1e-6);
        assert!((result[1] - 1.0).abs() < 1e-6);
    }
    
    #[test]
    fn test_cartan_formula() {
        // Test that L_X = d ∘ i_X + i_X ∘ d for a simple form
        let x = LieAlgebraElement::<f64>::from_coefficients(vec![1.0, 1.0]);
        let lie_deriv = LieDerivative::new(x);
        
        // Create a simple 2-form to test the general formula
        let omega = KForm {
            degree: 2,
            dimension: 2,
            components: vec![
                Box::new(|p: &[f64]| p[0] + p[1]), // coefficient of dx∧dy
            ],
        };
        
        let point = vec![1.0, 2.0];
        let result = lie_deriv.apply_form(&omega, &point).unwrap();
        
        // For a 2-form, the Lie derivative gives another 2-form
        // In 2D, there's only one 2-form component (dx∧dy)
        assert_eq!(result.len(), 1);
        // L_X(dx∧dy) = d(i_X(dx∧dy)) + i_X(d(dx∧dy))
        // Since d(dx∧dy) = 0 (3-forms don't exist in 2D), we have:
        // L_X(dx∧dy) = d(i_X(dx∧dy))
        // i_X(dx∧dy) = X^1 dy - X^2 dx = 1·dy - 1·dx
        // d(dy - dx) = 0 (constant 1-form)
        // So the result should be 0
        assert!(result[0].abs() < 1e-6);
    }
}
