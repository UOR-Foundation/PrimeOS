//! Coherence norm implementation

use ccm_core::Float;
use crate::grade::Graded;

/// Trait for types that have a coherence norm
pub trait Coherence<P: Float> {
    /// Compute the squared coherence norm ‖·‖²_c
    fn coherence_norm_sq(&self) -> P;

    /// Compute the coherence norm ‖·‖_c
    fn coherence_norm(&self) -> P {
        self.coherence_norm_sq().sqrt()
    }
}

/// Blanket implementation for types with grade decomposition
impl<T, P> Coherence<P> for T
where
    T: Graded<P> + Clone,
    P: Float,
{
    fn coherence_norm_sq(&self) -> P {
        let mut sum = P::zero();

        // According to spec section 2.4:
        // ‖x‖²_c = Σ_k ‖x_k‖²_ℓ²
        for k in 0..=self.max_grade() {
            let grade_k_norm_sq = self.grade_norm_sq(k);
            sum = sum + grade_k_norm_sq;
        }

        sum
    }
}

/// Example multivector type for testing
#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone)]
    struct SimpleMultivector {
        components: Vec<f64>,
        grades: Vec<usize>,
    }

    impl crate::grade::Graded<f64> for SimpleMultivector {
        fn grade(&self, k: usize) -> Self {
            let mut filtered_components = Vec::new();
            let mut filtered_grades = Vec::new();

            for (i, &grade) in self.grades.iter().enumerate() {
                if grade == k {
                    filtered_components.push(self.components[i]);
                    filtered_grades.push(grade);
                }
            }

            SimpleMultivector {
                components: filtered_components,
                grades: filtered_grades,
            }
        }

        #[cfg(feature = "alloc")]
        fn grade_decomposition(&self) -> Vec<Self> {
            let max_g = self.max_grade();
            (0..=max_g).map(|k| self.grade(k)).collect()
        }

        fn max_grade(&self) -> usize {
            *self.grades.iter().max().unwrap_or(&0)
        }

        fn grade_norm_sq(&self, k: usize) -> f64 {
            let mut sum = 0.0;
            for (i, &grade) in self.grades.iter().enumerate() {
                if grade == k {
                    sum += self.components[i] * self.components[i];
                }
            }
            sum
        }
    }

    #[test]
    fn test_coherence_norm() {
        let mv = SimpleMultivector {
            components: vec![1.0, 2.0, 3.0],
            grades: vec![0, 1, 2],
        };

        // This will use the blanket implementation
        let norm_sq: f64 = mv.coherence_norm_sq();
        // Each component contributes its square: 1² + 2² + 3² = 1 + 4 + 9 = 14
        assert_eq!(norm_sq, 14.0);

        let norm = mv.coherence_norm();
        assert!((norm - 14.0_f64.sqrt()).abs() < 1e-10);
    }

    #[test]
    fn test_grade_orthogonality() {
        // Test that different grades contribute independently to coherence norm
        let mv = SimpleMultivector {
            components: vec![3.0, 4.0, 0.0, 0.0],
            grades: vec![0, 0, 1, 1],
        };

        // Grade 0: 3² + 4² = 9 + 16 = 25
        // Grade 1: 0² + 0² = 0
        let norm_sq: f64 = mv.coherence_norm_sq();
        assert_eq!(norm_sq, 25.0);
    }
}
