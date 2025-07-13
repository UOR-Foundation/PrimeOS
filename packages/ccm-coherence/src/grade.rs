//! Grade decomposition and projection operations

use crate::element::CliffordElement;
use ccm_core::Float;
use num_complex::Complex;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

impl<P: Float> CliffordElement<P> {
    /// Get the grade-k component of this element
    pub fn grade(&self, k: usize) -> Self {
        let mut result = Self::zero(self.dimension);

        // Copy only components of grade k
        for i in 0..self.components.len() {
            if Self::grade_of_index(i) == k {
                result.components[i] = self.components[i];
            }
        }

        result
    }

    /// Get all grade components (returns array indexed by grade)
    #[cfg(feature = "alloc")]
    pub fn grade_decomposition(&self) -> Vec<Self> {
        let max_grade = self.dimension;
        let mut grades = Vec::with_capacity(max_grade + 1);

        for k in 0..=max_grade {
            grades.push(self.grade(k));
        }

        grades
    }

    /// Get the maximum grade present in this element
    pub fn max_grade(&self) -> usize {
        // Find the highest index with non-zero component
        for i in (0..self.components.len()).rev() {
            if self.components[i].norm_sqr() > P::epsilon() {
                return Self::grade_of_index(i);
            }
        }
        0
    }

    /// Get the minimum grade present in this element
    pub fn min_grade(&self) -> usize {
        // Find the lowest index with non-zero component
        for i in 0..self.components.len() {
            if self.components[i].norm_sqr() > P::epsilon() {
                return Self::grade_of_index(i);
            }
        }
        0
    }

    /// Check if this is a k-vector (pure grade k)
    pub fn is_k_vector(&self, k: usize) -> bool {
        for i in 0..self.components.len() {
            let grade = Self::grade_of_index(i);
            if grade != k && self.components[i].norm_sqr() > P::epsilon() {
                return false;
            }
        }
        true
    }

    /// Check if this is a scalar (grade 0)
    pub fn is_scalar(&self) -> bool {
        self.is_k_vector(0)
    }

    /// Check if this is a vector (grade 1)
    pub fn is_vector(&self) -> bool {
        self.is_k_vector(1)
    }

    /// Check if this is a bivector (grade 2)
    pub fn is_bivector(&self) -> bool {
        self.is_k_vector(2)
    }

    /// Get the scalar part (grade 0)
    pub fn scalar_part(&self) -> Complex<P> {
        self.components[0]
    }

    /// Get the pseudoscalar part (grade n)
    pub fn pseudoscalar_part(&self) -> Complex<P> {
        let ps_index = self.components.len() - 1;
        self.components[ps_index]
    }

    /// Project onto even grades (0, 2, 4, ...)
    pub fn even_part(&self) -> Self {
        let mut result = Self::zero(self.dimension);

        for i in 0..self.components.len() {
            let grade = Self::grade_of_index(i);
            if grade % 2 == 0 {
                result.components[i] = self.components[i];
            }
        }

        result
    }

    /// Project onto odd grades (1, 3, 5, ...)
    pub fn odd_part(&self) -> Self {
        let mut result = Self::zero(self.dimension);

        for i in 0..self.components.len() {
            let grade = Self::grade_of_index(i);
            if grade % 2 == 1 {
                result.components[i] = self.components[i];
            }
        }

        result
    }

    /// Grade involution: α(x) changes sign of odd grades
    pub fn grade_involution(&self) -> Self {
        let mut result = self.clone();

        for i in 0..self.components.len() {
            let grade = Self::grade_of_index(i);
            if grade % 2 == 1 {
                result.components[i] = -result.components[i];
            }
        }

        result
    }

    /// Grade reversal (reversion): reverses order of basis vectors
    pub fn reversion(&self) -> Self {
        let mut result = self.clone();

        for i in 0..self.components.len() {
            let grade = Self::grade_of_index(i);
            // Sign is (-1)^(k(k-1)/2)
            let sign_exp = if grade > 0 {
                (grade * (grade - 1)) / 2
            } else {
                0
            };
            if sign_exp % 2 == 1 {
                result.components[i] = -result.components[i];
            }
        }

        result
    }

    /// Clifford conjugation: combination of grade involution and reversion
    pub fn clifford_conjugation(&self) -> Self {
        let mut result = self.clone();

        for i in 0..self.components.len() {
            let grade = Self::grade_of_index(i);
            // Sign is (-1)^(k(k+1)/2)
            let sign_exp = (grade * (grade + 1)) / 2;
            if sign_exp % 2 == 1 {
                result.components[i] = -result.components[i];
            }
        }

        result
    }

    /// Complex conjugation of all coefficients
    pub fn complex_conjugate(&self) -> Self {
        let mut result = self.clone();

        for i in 0..self.components.len() {
            result.components[i] = self.components[i].conj();
        }

        result
    }
}

/// Trait for types that support grade decomposition
pub trait Graded<P: Float> {
    /// Get the grade-k component
    fn grade(&self, k: usize) -> Self;

    /// Get all grade components
    #[cfg(feature = "alloc")]
    fn grade_decomposition(&self) -> Vec<Self>
    where
        Self: Sized;

    /// Maximum grade in the element
    fn max_grade(&self) -> usize;

    /// Get the L2 norm squared of the grade-k component
    fn grade_norm_sq(&self, k: usize) -> P;
}

impl<P: Float> Graded<P> for CliffordElement<P> {
    fn grade(&self, k: usize) -> Self {
        self.grade(k)
    }

    #[cfg(feature = "alloc")]
    fn grade_decomposition(&self) -> Vec<Self> {
        self.grade_decomposition()
    }

    fn max_grade(&self) -> usize {
        self.max_grade()
    }

    fn grade_norm_sq(&self, k: usize) -> P {
        let mut sum = P::zero();

        // Sum the squared norms of all components of grade k
        for i in 0..self.components.len() {
            if Self::grade_of_index(i) == k {
                sum = sum + self.components[i].norm_sqr();
            }
        }

        sum
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_complex::Complex;
    use num_traits::Zero;

    #[test]
    fn test_grade_operations() {
        // Create a test element in 3D with mixed grades
        let mut elem = CliffordElement::<f64>::zero(3);
        elem.set_component(0, Complex::new(1.0, 0.0)).unwrap(); // scalar
        elem.set_component(1, Complex::new(2.0, 0.0)).unwrap(); // e₀
        elem.set_component(3, Complex::new(3.0, 0.0)).unwrap(); // e₀e₁
        elem.set_component(7, Complex::new(4.0, 0.0)).unwrap(); // e₀e₁e₂

        // Test grade extraction
        let grade0 = elem.grade(0);
        assert_eq!(grade0.component(0), Some(Complex::new(1.0, 0.0)));
        assert_eq!(grade0.component(1), Some(Complex::zero()));

        let grade1 = elem.grade(1);
        assert_eq!(grade1.component(0), Some(Complex::zero()));
        assert_eq!(grade1.component(1), Some(Complex::new(2.0, 0.0)));

        let grade2 = elem.grade(2);
        assert_eq!(grade2.component(3), Some(Complex::new(3.0, 0.0)));

        let grade3 = elem.grade(3);
        assert_eq!(grade3.component(7), Some(Complex::new(4.0, 0.0)));
    }

    #[test]
    fn test_even_odd_parts() {
        let mut elem = CliffordElement::<f64>::zero(3);
        elem.set_component(0, Complex::new(1.0, 0.0)).unwrap(); // grade 0 (even)
        elem.set_component(1, Complex::new(2.0, 0.0)).unwrap(); // grade 1 (odd)
        elem.set_component(3, Complex::new(3.0, 0.0)).unwrap(); // grade 2 (even)
        elem.set_component(7, Complex::new(4.0, 0.0)).unwrap(); // grade 3 (odd)

        let even = elem.even_part();
        assert_eq!(even.component(0), Some(Complex::new(1.0, 0.0)));
        assert_eq!(even.component(1), Some(Complex::zero()));
        assert_eq!(even.component(3), Some(Complex::new(3.0, 0.0)));
        assert_eq!(even.component(7), Some(Complex::zero()));

        let odd = elem.odd_part();
        assert_eq!(odd.component(0), Some(Complex::zero()));
        assert_eq!(odd.component(1), Some(Complex::new(2.0, 0.0)));
        assert_eq!(odd.component(3), Some(Complex::zero()));
        assert_eq!(odd.component(7), Some(Complex::new(4.0, 0.0)));
    }

    #[test]
    fn test_involutions() {
        let mut elem = CliffordElement::<f64>::zero(3);
        elem.set_component(0, Complex::new(1.0, 0.0)).unwrap(); // grade 0
        elem.set_component(1, Complex::new(2.0, 0.0)).unwrap(); // grade 1
        elem.set_component(3, Complex::new(3.0, 0.0)).unwrap(); // grade 2
        elem.set_component(7, Complex::new(4.0, 0.0)).unwrap(); // grade 3

        // Grade involution: changes sign of odd grades
        let alpha = elem.grade_involution();
        assert_eq!(alpha.component(0), Some(Complex::new(1.0, 0.0))); // unchanged
        assert_eq!(alpha.component(1), Some(Complex::new(-2.0, 0.0))); // sign changed
        assert_eq!(alpha.component(3), Some(Complex::new(3.0, 0.0))); // unchanged
        assert_eq!(alpha.component(7), Some(Complex::new(-4.0, 0.0))); // sign changed

        // Reversion: (-1)^(k(k-1)/2)
        let rev = elem.reversion();
        assert_eq!(rev.component(0), Some(Complex::new(1.0, 0.0))); // grade 0: 0*(-1)/2 = 0 (even)
        assert_eq!(rev.component(1), Some(Complex::new(2.0, 0.0))); // grade 1: 1*0/2 = 0 (even)
        assert_eq!(rev.component(3), Some(Complex::new(-3.0, 0.0))); // grade 2: 2*1/2 = 1 (odd)
        assert_eq!(rev.component(7), Some(Complex::new(-4.0, 0.0))); // grade 3: 3*2/2 = 3 (odd)
    }

    #[test]
    fn test_k_vector_check() {
        let elem = CliffordElement::<f64>::scalar(2.0, 3);
        assert!(elem.is_scalar());
        assert!(elem.is_k_vector(0));
        assert!(!elem.is_vector());

        let e1 = CliffordElement::<f64>::basis_vector(0, 3).unwrap();
        assert!(!e1.is_scalar());
        assert!(e1.is_vector());
        assert!(e1.is_k_vector(1));
    }
}
