//! Group constraint validation
//! 
//! This module provides functions to validate elements against specific
//! group constraints (SO(n), SU(n), GL(n), etc.).

use num_traits::Float;
use crate::group::{GroupElement, SymmetryGroup, GroupType};
use ccm_core::CcmError;
use crate::SymmetryError;

impl<P: Float> SymmetryGroup<P> {
    /// Check if element belongs to the group
    pub fn contains(&self, g: &GroupElement<P>) -> bool {
        if g.dimension() != self.dimension {
            return false;
        }
        
        match &self.group_type {
            GroupType::Finite { elements } => {
                // For finite groups, check if element is in the list
                elements.iter().any(|e| {
                    e.params.iter().zip(&g.params)
                        .all(|(a, b)| (*a - *b).abs() < P::epsilon())
                })
            }
            GroupType::DiscreteInfinite => {
                // For discrete infinite groups (like Z), check if element can be
                // expressed as integer combination of generators
                self.can_express_as_word(g)
            }
            GroupType::Continuous => {
                // For continuous groups, check if element satisfies group constraints
                self.satisfies_group_constraints(g)
            }
        }
    }
    
    /// Add a generator to the group
    pub fn add_generator(&mut self, g: GroupElement<P>) -> Result<(), CcmError> {
        if g.dimension() != self.dimension {
            return Err(SymmetryError::InvalidGroupOperation.into());
        }
        
        self.generators.push(g);
        self.cached_order = None; // Reset cached order
        Ok(())
    }
    
    /// Check if element satisfies constraints for continuous groups
    pub(crate) fn satisfies_group_constraints(&self, g: &GroupElement<P>) -> bool {
        // For matrix groups, check specific constraints
        match self.get_group_name() {
            "SO(n)" => self.is_special_orthogonal(g),
            "SU(n)" => self.is_special_unitary(g),
            "GL(n)" => self.is_general_linear(g),
            _ => {
                // For generic continuous groups, check if element preserves
                // the group structure by verifying it's close to the group manifold
                self.is_on_group_manifold(g)
            }
        }
    }
    
    /// Get group name based on generators and properties
    pub(crate) fn get_group_name(&self) -> &'static str {
        if self.dimension == 0 {
            return "Trivial";
        }
        
        // Detect based on generator structure
        if self.generators.is_empty() {
            return "Unknown";
        }
        
        // Check for orthogonal group pattern
        let n = (self.dimension as f64).sqrt();
        if n.floor() == n && n > 0.0 {
            let n = n as usize;
            if self.generators.len() == n * (n - 1) / 2 {
                return "SO(n)";
            }
        }
        
        // Check for unitary group pattern (complex dimension)
        let n_complex = ((self.dimension / 2) as f64).sqrt();
        if n_complex.floor() == n_complex && n_complex > 0.0 {
            let n = n_complex as usize;
            if self.generators.len() == n * n - 1 {
                return "SU(n)";
            } else if self.generators.len() == n * n {
                return "U(n)";
            }
        }
        
        "Generic"
    }
    
    /// Check if element is a special orthogonal matrix
    pub(crate) fn is_special_orthogonal(&self, g: &GroupElement<P>) -> bool {
        let n = (self.dimension as f64).sqrt() as usize;
        if n * n != self.dimension {
            return false;
        }
        
        // Check orthogonality: M^T M = I
        for i in 0..n {
            for j in 0..n {
                let mut sum = P::zero();
                for k in 0..n {
                    sum = sum + g.params[k * n + i] * g.params[k * n + j];
                }
                
                let expected = if i == j { P::one() } else { P::zero() };
                if (sum - expected).abs() > P::epsilon() {
                    return false;
                }
            }
        }
        
        // Check determinant = 1
        self.compute_determinant(&g.params, n)
            .map(|det| (det - P::one()).abs() < P::epsilon())
            .unwrap_or(false)
    }
    
    /// Check if element is a special unitary matrix
    pub(crate) fn is_special_unitary(&self, g: &GroupElement<P>) -> bool {
        use num_complex::Complex;
        
        // For SU(n), we need 2n² real parameters (real and imaginary parts)
        // The matrix dimension n is sqrt(self.dimension / 2)
        let n_squared = self.dimension / 2;
        let n = (n_squared as f64).sqrt() as usize;
        if n * n * 2 != self.dimension {
            return false;
        }
        
        // Interpret params as complex matrix: params[2k] + i*params[2k+1]
        let complex_matrix = self.params_to_complex_matrix(&g.params, n);
        
        // Check unitarity: M† M = I
        if !self.is_unitary_matrix(&complex_matrix, n) {
            return false;
        }
        
        // Check determinant = 1 (special unitary)
        self.compute_complex_determinant(&complex_matrix, n)
            .map(|det| {
                let one = Complex::new(P::one(), P::zero());
                (det - one).norm() < P::epsilon()
            })
            .unwrap_or(false)
    }
    
    /// Check if element is invertible (general linear group)
    pub(crate) fn is_general_linear(&self, g: &GroupElement<P>) -> bool {
        // Check if matrix is invertible (non-zero determinant)
        let n = (self.dimension as f64).sqrt() as usize;
        if n * n != self.dimension {
            return false;
        }
        
        // Compute determinant and check if non-zero
        self.compute_determinant(&g.params, n)
            .map(|det| det.abs() > P::epsilon())
            .unwrap_or(false)
    }
    
    /// Check if element is a unitary matrix (U(n))
    pub(crate) fn is_unitary(&self, g: &GroupElement<P>) -> bool {
        use num_complex::Complex;
        
        // For U(n), we need 2n² real parameters
        let n_squared = self.dimension / 2;
        let n = (n_squared as f64).sqrt() as usize;
        if n * n * 2 != self.dimension {
            return false;
        }
        
        // Convert to complex matrix and check unitarity
        let complex_matrix = self.params_to_complex_matrix(&g.params, n);
        self.is_unitary_matrix(&complex_matrix, n)
    }
    
    /// Check if element is a general linear complex matrix (GL(n,C))
    pub(crate) fn is_general_linear_complex(&self, g: &GroupElement<P>) -> bool {
        use num_complex::Complex;
        
        // For GL(n,C), we need 2n² real parameters
        let n_squared = self.dimension / 2;
        let n = (n_squared as f64).sqrt() as usize;
        if n * n * 2 != self.dimension {
            return false;
        }
        
        // Convert to complex matrix and check if invertible
        let complex_matrix = self.params_to_complex_matrix(&g.params, n);
        self.compute_complex_determinant(&complex_matrix, n)
            .map(|det| det.norm() > P::epsilon())
            .unwrap_or(false)
    }
    
    /// Check if element is in the special linear complex group (SL(n,C))
    pub(crate) fn is_special_linear_complex(&self, g: &GroupElement<P>) -> bool {
        use num_complex::Complex;
        
        // For SL(n,C), we need 2n² real parameters
        let n_squared = self.dimension / 2;
        let n = (n_squared as f64).sqrt() as usize;
        if n * n * 2 != self.dimension {
            return false;
        }
        
        // Convert to complex matrix and check determinant = 1
        let complex_matrix = self.params_to_complex_matrix(&g.params, n);
        self.compute_complex_determinant(&complex_matrix, n)
            .map(|det| {
                let one = Complex::new(P::one(), P::zero());
                (det - one).norm() < P::epsilon()
            })
            .unwrap_or(false)
    }
    
    /// Check if element satisfies constraints with numerical stability
    pub(crate) fn satisfies_constraints_stable(&self, g: &GroupElement<P>) -> bool {
        // Use scaled epsilon for numerical stability
        let tolerance = P::epsilon() * P::from(10.0).unwrap_or(P::one());
        
        match self.get_group_name() {
            "SO(n)" => self.is_special_orthogonal_stable(g, tolerance),
            "SU(n)" => self.is_special_unitary_stable(g, tolerance),
            "U(n)" => self.is_unitary_stable(g, tolerance),
            _ => self.satisfies_group_constraints(g)
        }
    }
    
    /// Check special orthogonal with custom tolerance
    fn is_special_orthogonal_stable(&self, g: &GroupElement<P>, tolerance: P) -> bool {
        let n = (self.dimension as f64).sqrt() as usize;
        if n * n != self.dimension {
            return false;
        }
        
        // Check orthogonality with tolerance
        for i in 0..n {
            for j in 0..n {
                let mut sum = P::zero();
                for k in 0..n {
                    sum = sum + g.params[k * n + i] * g.params[k * n + j];
                }
                
                let expected = if i == j { P::one() } else { P::zero() };
                if (sum - expected).abs() > tolerance {
                    return false;
                }
            }
        }
        
        // Check determinant with tolerance
        self.compute_determinant(&g.params, n)
            .map(|det| (det - P::one()).abs() < tolerance)
            .unwrap_or(false)
    }
    
    /// Check special unitary with custom tolerance
    fn is_special_unitary_stable(&self, g: &GroupElement<P>, tolerance: P) -> bool {
        use num_complex::Complex;
        
        let n_squared = self.dimension / 2;
        let n = (n_squared as f64).sqrt() as usize;
        if n * n * 2 != self.dimension {
            return false;
        }
        
        let complex_matrix = self.params_to_complex_matrix(&g.params, n);
        
        // Check unitarity with tolerance
        for i in 0..n {
            for j in 0..n {
                let mut sum = Complex::new(P::zero(), P::zero());
                
                for k in 0..n {
                    let m_ki = complex_matrix[k * n + i];
                    let m_kj = complex_matrix[k * n + j];
                    sum = sum + m_ki.conj() * m_kj;
                }
                
                let expected = if i == j {
                    Complex::new(P::one(), P::zero())
                } else {
                    Complex::new(P::zero(), P::zero())
                };
                
                if (sum - expected).norm() > tolerance {
                    return false;
                }
            }
        }
        
        // Check determinant with tolerance
        self.compute_complex_determinant(&complex_matrix, n)
            .map(|det| {
                let one = Complex::new(P::one(), P::zero());
                (det - one).norm() < tolerance
            })
            .unwrap_or(false)
    }
    
    /// Check unitary with custom tolerance
    fn is_unitary_stable(&self, g: &GroupElement<P>, tolerance: P) -> bool {
        use num_complex::Complex;
        
        let n_squared = self.dimension / 2;
        let n = (n_squared as f64).sqrt() as usize;
        if n * n * 2 != self.dimension {
            return false;
        }
        
        let complex_matrix = self.params_to_complex_matrix(&g.params, n);
        
        // Check unitarity with tolerance
        for i in 0..n {
            for j in 0..n {
                let mut sum = Complex::new(P::zero(), P::zero());
                
                for k in 0..n {
                    let m_ki = complex_matrix[k * n + i];
                    let m_kj = complex_matrix[k * n + j];
                    sum = sum + m_ki.conj() * m_kj;
                }
                
                let expected = if i == j {
                    Complex::new(P::one(), P::zero())
                } else {
                    Complex::new(P::zero(), P::zero())
                };
                
                if (sum - expected).norm() > tolerance {
                    return false;
                }
            }
        }
        
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::group::{SymmetryGroup, GroupElement};
    
    #[test]
    fn test_su2_validation() {
        // SU(2) has dimension 8 (2x2 complex = 8 real params)
        let group = SymmetryGroup::<f64>::generate(8).unwrap();
        
        // Test identity element (is in SU(2))
        let identity = GroupElement::from_params(vec![
            1.0, 0.0,  // (0,0): 1+0i
            0.0, 0.0,  // (0,1): 0+0i
            0.0, 0.0,  // (1,0): 0+0i
            1.0, 0.0   // (1,1): 1+0i
        ]);
        assert!(group.is_special_unitary(&identity));
        
        // Test Pauli Z matrix (is in U(2) but NOT in SU(2) - det = -1)
        let pauli_z = GroupElement::from_params(vec![
            1.0, 0.0,   // (0,0): 1+0i
            0.0, 0.0,   // (0,1): 0+0i
            0.0, 0.0,   // (1,0): 0+0i
            -1.0, 0.0   // (1,1): -1+0i
        ]);
        assert!(group.is_unitary(&pauli_z));
        assert!(!group.is_special_unitary(&pauli_z)); // det = -1, not 1
        
        // Test a rotation matrix in SU(2)
        // exp(i*theta/2 * sigma_x) for theta = pi/2
        let angle = std::f64::consts::PI / 4.0;
        let c = angle.cos();
        let s = angle.sin();
        let rotation = GroupElement::from_params(vec![
            c, 0.0,     // (0,0): cos(pi/4)
            0.0, s,     // (0,1): i*sin(pi/4)
            0.0, s,     // (1,0): i*sin(pi/4)
            c, 0.0      // (1,1): cos(pi/4)
        ]);
        assert!(group.is_special_unitary(&rotation));
        
        // Test non-unitary matrix (not in SU(2))
        let non_unitary = GroupElement::from_params(vec![
            2.0, 0.0,   // (0,0): 2+0i
            0.0, 0.0,   // (0,1): 0+0i
            0.0, 0.0,   // (1,0): 0+0i
            1.0, 0.0    // (1,1): 1+0i
        ]);
        assert!(!group.is_special_unitary(&non_unitary));
    }
    
    #[test]
    fn test_u2_validation() {
        let group = SymmetryGroup::<f64>::generate(8).unwrap();
        
        // Test phase matrix (is in U(2) but not SU(2))
        let phase = GroupElement::from_params(vec![
            0.0, 1.0,   // (0,0): i
            0.0, 0.0,   // (0,1): 0
            0.0, 0.0,   // (1,0): 0
            0.0, 1.0    // (1,1): i
        ]);
        assert!(group.is_unitary(&phase));
        assert!(!group.is_special_unitary(&phase)); // det = i*i = -1
    }
    
    #[test]
    fn test_complex_determinant_validation() {
        let group = SymmetryGroup::<f64>::generate(8).unwrap();
        
        // Test GL(2,C) element
        let gl_element = GroupElement::from_params(vec![
            1.0, 1.0,   // (0,0): 1+i
            2.0, 0.0,   // (0,1): 2
            0.0, 0.0,   // (1,0): 0
            1.0, -1.0   // (1,1): 1-i
        ]);
        assert!(group.is_general_linear_complex(&gl_element));
        
        // Test singular matrix (not in GL(2,C))
        let singular = GroupElement::from_params(vec![
            1.0, 0.0,   // (0,0): 1
            2.0, 0.0,   // (0,1): 2
            2.0, 0.0,   // (1,0): 2
            4.0, 0.0    // (1,1): 4
        ]);
        assert!(!group.is_general_linear_complex(&singular));
    }
    
    #[test]
    fn test_sl2c_validation() {
        let group = SymmetryGroup::<f64>::generate(8).unwrap();
        
        // Test SL(2,C) element with det = 1
        // Matrix [[2, 1], [3, 2]] has det = 4-3 = 1
        let sl_element = GroupElement::from_params(vec![
            2.0, 0.0,   // (0,0): 2
            1.0, 0.0,   // (0,1): 1
            3.0, 0.0,   // (1,0): 3
            2.0, 0.0    // (1,1): 2
        ]);
        assert!(group.is_special_linear_complex(&sl_element));
        
        // Test element with det != 1
        let non_sl = GroupElement::from_params(vec![
            2.0, 0.0,   // (0,0): 2
            0.0, 0.0,   // (0,1): 0
            0.0, 0.0,   // (1,0): 0
            2.0, 0.0    // (1,1): 2
        ]);
        assert!(!group.is_special_linear_complex(&non_sl)); // det = 4
    }
    
    #[test]
    fn test_numerical_stability() {
        let group = SymmetryGroup::<f64>::generate(8).unwrap();
        
        // Test nearly unitary matrix (within tolerance)
        let epsilon = 1e-10;
        let nearly_unitary = GroupElement::from_params(vec![
            1.0 + epsilon, 0.0,
            0.0, 0.0,
            0.0, 0.0,
            1.0, 0.0
        ]);
        
        // Should pass with stable check
        assert!(group.satisfies_constraints_stable(&nearly_unitary));
    }
    
    #[test]
    fn test_group_name_detection() {
        // Test SO(3) detection
        let so3_group = SymmetryGroup::<f64>::generate(9).unwrap();
        assert_eq!(so3_group.get_group_name(), "Unknown"); // No generators yet
        
        // Test SU(2) detection  
        let mut su2_group = SymmetryGroup::<f64>::generate(8).unwrap();
        // Add 3 generators for su(2) Lie algebra (n²-1 for SU(n))
        for i in 0..3 {
            let mut params = vec![0.0; 8];
            params[i] = 1.0;
            su2_group.add_generator(GroupElement::from_params(params)).unwrap();
        }
        assert_eq!(su2_group.get_group_name(), "SU(n)");
        
        // Test U(2) detection
        let mut u2_group = SymmetryGroup::<f64>::generate(8).unwrap();
        // Add 4 generators for u(2) Lie algebra
        for i in 0..4 {
            let mut params = vec![0.0; 8];
            params[i] = 1.0;
            u2_group.add_generator(GroupElement::from_params(params)).unwrap();
        }
        assert_eq!(u2_group.get_group_name(), "U(n)");
    }
}