//! Clifford algebra structure and basis generation

use crate::element::CliffordElement;
use ccm_core::{CcmError, Float};
use num_complex::Complex;
use num_traits::One;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Clifford algebra Cl(n) for n-dimensional vector space
#[derive(Debug, Clone)]
pub struct CliffordAlgebra<P: Float> {
    /// Dimension of the underlying vector space
    dimension: usize,
    /// Metric signature (p, q, r) where p + q + r = n
    /// p: positive signature, q: negative signature, r: zero signature
    signature: (usize, usize, usize),
    _phantom: core::marker::PhantomData<P>,
}

impl<P: Float> CliffordAlgebra<P> {
    /// Generate Euclidean Clifford algebra Cl(n) with positive definite metric
    ///
    /// # Note
    /// Default limit is 12 dimensions for safety. Use `generate_with_limit` for larger dimensions.
    pub fn generate(n: usize) -> Result<Self, CcmError> {
        Self::generate_with_limit(n, 12)
    }

    /// Generate Euclidean Clifford algebra with custom dimension limit
    ///
    /// # Safety
    /// Large dimensions require exponential memory: 2^n basis elements.
    /// Ensure sufficient memory before using large dimensions.
    pub fn generate_with_limit(n: usize, max_dimension: usize) -> Result<Self, CcmError> {
        if n > max_dimension {
            return Err(CcmError::InvalidInput);
        }

        // Prevent overflow in 2^n calculation
        if n >= core::mem::size_of::<usize>() * 8 {
            return Err(CcmError::InvalidInput);
        }

        Ok(Self {
            dimension: n,
            signature: (n, 0, 0), // Euclidean signature
            _phantom: core::marker::PhantomData,
        })
    }

    /// Generate Clifford algebra with specified metric signature
    ///
    /// # Note
    /// Default limit is 12 dimensions for safety. Use `with_signature_limit` for larger dimensions.
    pub fn with_signature(p: usize, q: usize, r: usize) -> Result<Self, CcmError> {
        Self::with_signature_limit(p, q, r, 12)
    }

    /// Generate Clifford algebra with specified metric signature and custom limit
    pub fn with_signature_limit(
        p: usize,
        q: usize,
        r: usize,
        max_dimension: usize,
    ) -> Result<Self, CcmError> {
        let n = p + q + r;
        if n > max_dimension {
            return Err(CcmError::InvalidInput);
        }

        // Prevent overflow
        if n >= core::mem::size_of::<usize>() * 8 {
            return Err(CcmError::InvalidInput);
        }

        Ok(Self {
            dimension: n,
            signature: (p, q, r),
            _phantom: core::marker::PhantomData,
        })
    }

    /// Get the dimension of the underlying vector space
    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// Get the metric signature
    pub fn signature(&self) -> (usize, usize, usize) {
        self.signature
    }

    /// Get the total number of basis elements (2^n)
    pub fn num_basis_elements(&self) -> usize {
        1usize << self.dimension
    }

    /// Generate all basis elements
    #[cfg(feature = "alloc")]
    pub fn basis_elements(&self) -> Vec<CliffordElement<P>> {
        let mut elements = Vec::with_capacity(self.num_basis_elements());

        // Generate all 2^n basis elements
        for i in 0..self.num_basis_elements() {
            let mut elem = CliffordElement::zero(self.dimension);
            elem.components[i] = Complex::one();
            elements.push(elem);
        }

        elements
    }

    /// Get a specific basis element by its bit pattern
    pub fn basis_element(&self, index: usize) -> Result<CliffordElement<P>, CcmError> {
        if index >= self.num_basis_elements() {
            return Err(CcmError::InvalidInput);
        }

        let mut elem = CliffordElement::zero(self.dimension);
        elem.components[index] = Complex::one();
        Ok(elem)
    }

    /// Get basis element from a list of vector indices
    /// For example, [0, 2] gives e_0 ∧ e_2
    pub fn basis_blade(&self, indices: &[usize]) -> Result<CliffordElement<P>, CcmError> {
        CliffordElement::basis_blade(indices, self.dimension)
    }

    /// Convert bit pattern to list of indices
    /// For example, 5 (binary 101) -> [0, 2]
    pub fn bit_pattern_to_indices(pattern: usize) -> Vec<usize> {
        let mut indices = Vec::new();
        let mut p = pattern;
        let mut i = 0;

        while p > 0 {
            if p & 1 == 1 {
                indices.push(i);
            }
            p >>= 1;
            i += 1;
        }

        indices
    }

    /// Convert list of indices to bit pattern
    /// For example, [0, 2] -> 5 (binary 101)
    pub fn indices_to_bit_pattern(indices: &[usize]) -> usize {
        let mut pattern = 0;
        for &i in indices {
            pattern |= 1 << i;
        }
        pattern
    }

    /// Get the metric value for basis vector i
    /// Returns +1, -1, or 0 based on signature
    pub fn metric_value(&self, i: usize) -> P {
        let (p, q, _r) = self.signature;

        if i < p {
            P::one()
        } else if i < p + q {
            -P::one()
        } else {
            P::zero()
        }
    }

    /// Compute the sign when multiplying basis elements
    /// This implements the anticommutation relations
    pub fn multiplication_sign(&self, indices1: &[usize], indices2: &[usize]) -> P {
        let mut sign = P::one();

        // Count inversions needed to merge the two lists
        for &idx1 in indices1.iter() {
            for &idx2 in indices2 {
                if idx1 > idx2 {
                    sign = -sign;
                }
                if idx1 == idx2 {
                    // e_i * e_i = metric(i)
                    sign = sign * self.metric_value(idx1);
                    // This basis element will cancel out
                }
            }
        }

        // Additional inversions from moving indices2 past indices1
        let inversions = indices1.len() * indices2.len()
            - indices1
                .iter()
                .filter(|&&i1| indices2.contains(&i1))
                .count();

        if inversions % 2 == 1 {
            sign = -sign;
        }

        sign
    }

    /// Get the basis name for display (e.g., "e₁e₂")
    pub fn basis_name(indices: &[usize]) -> String {
        if indices.is_empty() {
            return "1".to_string();
        }

        let subscripts = ['₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉'];
        let mut name = String::new();

        for &i in indices {
            name.push('e');
            if i < 10 {
                name.push(subscripts[i]);
            } else {
                name.push_str(&format!("_{i}"));
            }
        }

        name
    }

    /// Compute the geometric product of two Clifford elements
    pub fn geometric_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        if a.dimension != self.dimension || b.dimension != self.dimension {
            return Err(CcmError::InvalidInput);
        }

        let mut result = CliffordElement::zero(self.dimension);

        // For each component of a and b
        for i in 0..a.components.len() {
            if a.components[i].norm_sqr() < P::epsilon() {
                continue;
            }

            let indices_i = Self::bit_pattern_to_indices(i);

            for j in 0..b.components.len() {
                if b.components[j].norm_sqr() < P::epsilon() {
                    continue;
                }

                let indices_j = Self::bit_pattern_to_indices(j);

                // Compute the product of basis elements
                let (result_pattern, sign) = self.multiply_basis_elements(&indices_i, &indices_j);

                // Add contribution to result
                let coeff = a.components[i] * b.components[j] * Complex::new(sign, P::zero());
                result.components[result_pattern] = result.components[result_pattern] + coeff;
            }
        }

        Ok(result)
    }

    /// Multiply two basis elements and return the result pattern and sign
    fn multiply_basis_elements(&self, indices1: &[usize], indices2: &[usize]) -> (usize, P) {
        let mut result_indices = Vec::new();
        let mut sign = P::one();

        // Track which indices appear in the result
        let mut i = 0;
        let mut j = 0;

        while i < indices1.len() || j < indices2.len() {
            if i < indices1.len() && (j >= indices2.len() || indices1[i] < indices2[j]) {
                // Add index from first list
                result_indices.push(indices1[i]);
                // Count inversions: how many indices from indices2 come before this
                sign = sign * (-P::one()).powi(j as i32);
                i += 1;
            } else if j < indices2.len() && (i >= indices1.len() || indices2[j] < indices1[i]) {
                // Add index from second list
                result_indices.push(indices2[j]);
                j += 1;
            } else {
                // indices1[i] == indices2[j]
                // e_i * e_i = metric(i)
                sign = sign * self.metric_value(indices1[i]);
                i += 1;
                j += 1;
            }
        }

        let pattern = Self::indices_to_bit_pattern(&result_indices);
        (pattern, sign)
    }

    /// Compute the wedge product (exterior product) a ∧ b
    /// Result contains only the grade(a) + grade(b) component
    pub fn wedge_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        let ab = self.geometric_product(a, b)?;

        // Extract only components where grade = grade(a) + grade(b)
        let mut result = CliffordElement::zero(self.dimension);

        for i in 0..ab.components.len() {
            let grade_i = CliffordElement::<P>::grade_of_index(i);

            // Check if this component could come from wedge product
            let mut possible = false;
            for j in 0..a.components.len() {
                if a.components[j].norm_sqr() < P::epsilon() {
                    continue;
                }
                let grade_a = CliffordElement::<P>::grade_of_index(j);

                for k in 0..b.components.len() {
                    if b.components[k].norm_sqr() < P::epsilon() {
                        continue;
                    }
                    let grade_b = CliffordElement::<P>::grade_of_index(k);

                    if grade_i == grade_a + grade_b {
                        possible = true;
                        break;
                    }
                }
                if possible {
                    break;
                }
            }

            if possible {
                result.components[i] = ab.components[i];
            }
        }

        Ok(result)
    }

    /// Compute the inner product (contraction) a · b
    /// Result contains only the |grade(a) - grade(b)| component
    pub fn inner_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<CliffordElement<P>, CcmError> {
        let ab = self.geometric_product(a, b)?;

        // Extract only components where grade = |grade(a) - grade(b)|
        let mut result = CliffordElement::zero(self.dimension);

        for i in 0..ab.components.len() {
            let grade_i = CliffordElement::<P>::grade_of_index(i);

            // Check if this component could come from inner product
            let mut possible = false;
            for j in 0..a.components.len() {
                if a.components[j].norm_sqr() < P::epsilon() {
                    continue;
                }
                let grade_a = CliffordElement::<P>::grade_of_index(j);

                for k in 0..b.components.len() {
                    if b.components[k].norm_sqr() < P::epsilon() {
                        continue;
                    }
                    let grade_b = CliffordElement::<P>::grade_of_index(k);

                    let grade_diff = grade_a.abs_diff(grade_b);

                    if grade_i == grade_diff {
                        possible = true;
                        break;
                    }
                }
                if possible {
                    break;
                }
            }

            if possible {
                result.components[i] = ab.components[i];
            }
        }

        Ok(result)
    }

    /// Compute the scalar product ⟨a, b⟩ (grade 0 part of ab)
    pub fn scalar_product(
        &self,
        a: &CliffordElement<P>,
        b: &CliffordElement<P>,
    ) -> Result<Complex<P>, CcmError> {
        let ab = self.geometric_product(a, b)?;
        Ok(ab.components[0]) // Grade 0 component
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clifford_generation() {
        let cl3 = CliffordAlgebra::<f64>::generate(3).unwrap();
        assert_eq!(cl3.dimension(), 3);
        assert_eq!(cl3.num_basis_elements(), 8);
        assert_eq!(cl3.signature(), (3, 0, 0));
    }

    #[test]
    fn test_basis_element_generation() {
        let cl3 = CliffordAlgebra::<f64>::generate(3).unwrap();

        // Test scalar basis element
        let e0 = cl3.basis_element(0).unwrap();
        assert_eq!(e0.component(0), Some(Complex::one()));

        // Test vector basis elements
        let e1 = cl3.basis_element(1).unwrap(); // e₀
        assert_eq!(e1.component(1), Some(Complex::one()));
    }

    #[test]
    fn test_bit_pattern_conversions() {
        // 5 = binary 101 = e₀ ∧ e₂
        let indices = CliffordAlgebra::<f64>::bit_pattern_to_indices(5);
        assert_eq!(indices, vec![0, 2]);

        let pattern = CliffordAlgebra::<f64>::indices_to_bit_pattern(&[0, 2]);
        assert_eq!(pattern, 5);
    }

    #[test]
    fn test_metric_values() {
        // Minkowski signature (1, 3, 0)
        let cl_minkowski = CliffordAlgebra::<f64>::with_signature(1, 3, 0).unwrap();
        assert_eq!(cl_minkowski.metric_value(0), 1.0); // timelike
        assert_eq!(cl_minkowski.metric_value(1), -1.0); // spacelike
        assert_eq!(cl_minkowski.metric_value(2), -1.0); // spacelike
        assert_eq!(cl_minkowski.metric_value(3), -1.0); // spacelike
    }

    #[test]
    fn test_basis_names() {
        assert_eq!(CliffordAlgebra::<f64>::basis_name(&[]), "1");
        assert_eq!(CliffordAlgebra::<f64>::basis_name(&[0]), "e₀");
        assert_eq!(CliffordAlgebra::<f64>::basis_name(&[0, 1]), "e₀e₁");
        assert_eq!(CliffordAlgebra::<f64>::basis_name(&[0, 1, 2]), "e₀e₁e₂");
    }

    #[test]
    fn test_dimension_limit() {
        // Should fail for dimension > 12
        assert!(CliffordAlgebra::<f64>::generate(13).is_err());
        assert!(CliffordAlgebra::<f64>::generate(12).is_ok());
    }

    #[test]
    fn test_geometric_product() {
        let cl3 = CliffordAlgebra::<f64>::generate(3).unwrap();

        // Test e₀ * e₀ = 1
        let e0 = cl3.basis_element(1).unwrap();
        let e0_squared = cl3.geometric_product(&e0, &e0).unwrap();
        assert_eq!(e0_squared.component(0), Some(Complex::one()));

        // Test e₀ * e₁ = e₀e₁
        let e1 = cl3.basis_element(2).unwrap();
        let e01 = cl3.geometric_product(&e0, &e1).unwrap();
        assert_eq!(e01.component(3), Some(Complex::one())); // binary 011 = 3

        // Test e₁ * e₀ = -e₀e₁ (anticommutation)
        let e10 = cl3.geometric_product(&e1, &e0).unwrap();
        assert_eq!(e10.component(3), Some(Complex::new(-1.0, 0.0)));
    }

    #[test]
    fn test_wedge_product() {
        let cl3 = CliffordAlgebra::<f64>::generate(3).unwrap();

        let e0 = cl3.basis_element(1).unwrap();
        let e1 = cl3.basis_element(2).unwrap();

        // e₀ ∧ e₁ should give e₀e₁
        let wedge = cl3.wedge_product(&e0, &e1).unwrap();
        assert_eq!(wedge.component(3), Some(Complex::one()));

        // e₀ ∧ e₀ should be zero (wedge of same vector)
        let wedge_same = cl3.wedge_product(&e0, &e0).unwrap();
        assert!(wedge_same.component(0).unwrap().norm() < 1e-10);
    }

    #[test]
    fn test_inner_product() {
        let cl3 = CliffordAlgebra::<f64>::generate(3).unwrap();

        let e0 = cl3.basis_element(1).unwrap();
        let e01 = cl3.basis_element(3).unwrap(); // e₀e₁

        // e₀ · (e₀e₁) should give e₁
        let inner = cl3.inner_product(&e0, &e01).unwrap();
        assert_eq!(inner.component(2), Some(Complex::one())); // e₁
    }
}
