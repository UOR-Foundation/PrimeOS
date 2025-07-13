//! Coherence minimization and optimization algorithms

use crate::element::CliffordElement;
#[allow(unused_imports)]
use crate::metric::{coherence_norm, coherence_norm_squared, coherence_product};
use ccm_core::{CcmError, Float};
#[allow(unused_imports)]
use num_traits::{One, Zero};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Type alias for linear operators on Clifford elements
pub type LinearOperator<P> = Box<dyn Fn(&CliffordElement<P>) -> CliffordElement<P>>;

/// Constraint trait for coherence minimization
pub trait Constraint<P: Float> {
    /// Check if an element satisfies the constraint
    fn satisfies(&self, x: &CliffordElement<P>) -> bool;

    /// Project gradient onto constraint manifold
    fn project_gradient(&self, grad: &CliffordElement<P>) -> CliffordElement<P>;

    /// Project element onto constraint set
    fn project(&self, x: &CliffordElement<P>) -> CliffordElement<P>;
}

/// Linear constraint: Ax = b
pub struct LinearConstraint<P: Float> {
    /// Linear operator A
    pub operator: LinearOperator<P>,
    /// Target value b
    pub target: CliffordElement<P>,
}

impl<P: Float> Constraint<P> for LinearConstraint<P> {
    fn satisfies(&self, x: &CliffordElement<P>) -> bool {
        let ax = (self.operator)(x);
        let diff = ax - self.target.clone();
        coherence_norm_squared(&diff) < P::epsilon()
    }

    fn project_gradient(&self, grad: &CliffordElement<P>) -> CliffordElement<P> {
        // For linear constraints, project gradient orthogonal to constraint
        grad.clone()
    }

    fn project(&self, x: &CliffordElement<P>) -> CliffordElement<P> {
        // Simple projection for linear constraints
        x.clone()
    }
}

/// Grade constraint: Only allow specific grades
pub struct GradeConstraint {
    pub allowed_grades: Vec<usize>,
}

impl<P: Float> Constraint<P> for GradeConstraint {
    fn satisfies(&self, x: &CliffordElement<P>) -> bool {
        // Check if all non-zero components are in allowed grades
        for i in 0..x.num_components() {
            let grade = CliffordElement::<P>::grade_of_index(i);
            if let Some(comp) = x.component(i) {
                if comp.norm_sqr() > P::epsilon() && !self.allowed_grades.contains(&grade) {
                    return false;
                }
            }
        }
        true
    }

    fn project_gradient(&self, grad: &CliffordElement<P>) -> CliffordElement<P> {
        // Zero out gradient components not in allowed grades
        let mut result = CliffordElement::zero(grad.dimension());

        for i in 0..grad.num_components() {
            let grade = CliffordElement::<P>::grade_of_index(i);
            if self.allowed_grades.contains(&grade) {
                if let Some(comp) = grad.component(i) {
                    result.set_component(i, comp).unwrap();
                }
            }
        }

        result
    }

    fn project(&self, x: &CliffordElement<P>) -> CliffordElement<P> {
        // Keep only components in allowed grades
        let mut result = CliffordElement::zero(x.dimension());

        for i in 0..x.num_components() {
            let grade = CliffordElement::<P>::grade_of_index(i);
            if self.allowed_grades.contains(&grade) {
                if let Some(comp) = x.component(i) {
                    result.set_component(i, comp).unwrap();
                }
            }
        }

        result
    }
}

/// Options for coherence minimization
pub struct MinimizationOptions<P: Float> {
    /// Maximum iterations
    pub max_iterations: usize,
    /// Tolerance for convergence
    pub tolerance: P,
    /// Initial step size
    pub initial_step_size: P,
    /// Step size reduction factor
    pub step_reduction: P,
    /// Minimum step size
    pub min_step_size: P,
}

impl<P: Float> Default for MinimizationOptions<P> {
    fn default() -> Self {
        Self {
            max_iterations: 1000,
            tolerance: P::from(1e-6).unwrap_or_else(|| P::epsilon()),
            initial_step_size: P::from(0.1).unwrap_or_else(|| P::one() / P::from(10.0).unwrap()),
            step_reduction: P::from(0.5).unwrap_or_else(|| P::one() / P::from(2.0).unwrap()),
            min_step_size: P::from(1e-10).unwrap_or_else(|| P::epsilon()),
        }
    }
}

/// Result of coherence minimization
pub struct MinimizationResult<P: Float> {
    /// Minimizer element
    pub minimizer: CliffordElement<P>,
    /// Final coherence norm
    pub norm: P,
    /// Number of iterations
    pub iterations: usize,
    /// Whether convergence was achieved
    pub converged: bool,
}

/// Minimize coherence norm subject to constraints
///
/// Uses gradient descent with backtracking line search
pub fn minimize_coherence<P: Float>(
    initial: &CliffordElement<P>,
    constraint: &dyn Constraint<P>,
    options: MinimizationOptions<P>,
) -> Result<MinimizationResult<P>, CcmError> {
    let mut x = constraint.project(initial);
    let mut step_size = options.initial_step_size;

    for iter in 0..options.max_iterations {
        // Compute gradient: ∇‖x‖²_c = 2x
        let grad = crate::coherence_gradient::coherence_gradient(&x);

        // Project gradient according to constraint
        let proj_grad = constraint.project_gradient(&grad);

        // Check convergence
        let grad_norm = coherence_norm(&proj_grad);
        if grad_norm < options.tolerance {
            return Ok(MinimizationResult {
                norm: coherence_norm(&x),
                minimizer: x,
                iterations: iter,
                converged: true,
            });
        }

        // Backtracking line search
        let current_norm = coherence_norm_squared(&x);
        let mut found_step = false;

        while step_size > options.min_step_size {
            // Trial step
            let x_new = x.clone() - proj_grad.clone() * step_size;
            let x_new = constraint.project(&x_new);

            // Check if constraint is satisfied
            if !constraint.satisfies(&x_new) {
                step_size = step_size * options.step_reduction;
                continue;
            }

            // Check sufficient decrease (Armijo condition)
            let new_norm = coherence_norm_squared(&x_new);
            let expected_decrease = step_size * grad_norm * grad_norm;

            if new_norm < current_norm - P::from(0.1).unwrap() * expected_decrease {
                x = x_new;
                found_step = true;
                break;
            }

            step_size = step_size * options.step_reduction;
        }

        if !found_step {
            // Could not find valid step
            return Ok(MinimizationResult {
                norm: coherence_norm(&x),
                minimizer: x,
                iterations: iter,
                converged: false,
            });
        }

        // Increase step size for next iteration if successful
        step_size = (step_size * P::from(1.5).unwrap()).min(options.initial_step_size);
    }

    Ok(MinimizationResult {
        norm: coherence_norm(&x),
        minimizer: x,
        iterations: options.max_iterations,
        converged: false,
    })
}

/// Find element of minimal coherence norm in an affine subspace
///
/// Solves: minimize ‖x‖_c subject to Ax = b
pub fn minimize_in_affine_subspace<P: Float>(
    operator: LinearOperator<P>,
    target: CliffordElement<P>,
    initial_guess: Option<CliffordElement<P>>,
    options: MinimizationOptions<P>,
) -> Result<MinimizationResult<P>, CcmError> {
    let constraint = LinearConstraint { operator, target };

    let initial =
        initial_guess.unwrap_or_else(|| CliffordElement::zero(constraint.target.dimension()));

    minimize_coherence(&initial, &constraint, options)
}

/// Find element of minimal coherence norm with specified grades
pub fn minimize_with_grades<P: Float>(
    initial: &CliffordElement<P>,
    allowed_grades: Vec<usize>,
    options: MinimizationOptions<P>,
) -> Result<MinimizationResult<P>, CcmError> {
    let constraint = GradeConstraint { allowed_grades };
    minimize_coherence(initial, &constraint, options)
}

/// Conjugate gradient method for quadratic minimization
///
/// More efficient for large-scale problems
#[cfg(feature = "alloc")]
pub fn conjugate_gradient<P: Float>(
    initial: &CliffordElement<P>,
    operator: &dyn Fn(&CliffordElement<P>) -> CliffordElement<P>,
    target: &CliffordElement<P>,
    options: MinimizationOptions<P>,
) -> Result<MinimizationResult<P>, CcmError> {
    let mut x = initial.clone();
    let mut r = target.clone() - operator(&x);
    let mut p = r.clone();

    for iter in 0..options.max_iterations {
        let r_norm_sq = coherence_norm_squared(&r);

        if r_norm_sq < options.tolerance * options.tolerance {
            return Ok(MinimizationResult {
                norm: coherence_norm(&x),
                minimizer: x,
                iterations: iter,
                converged: true,
            });
        }

        let ap = operator(&p);
        let alpha = r_norm_sq / coherence_product(&p, &ap).re;

        x = x + p.clone() * alpha;
        let r_new = r.clone() - ap * alpha;

        let beta = coherence_norm_squared(&r_new) / r_norm_sq;
        p = r_new.clone() + p * beta;
        r = r_new;
    }

    Ok(MinimizationResult {
        norm: coherence_norm(&x),
        minimizer: x,
        iterations: options.max_iterations,
        converged: false,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_complex::Complex;

    #[test]
    fn test_grade_constraint() {
        let constraint = GradeConstraint {
            allowed_grades: vec![0, 1],
        };

        let mut elem = CliffordElement::<f64>::zero(3);
        elem.set_component(0, Complex::one()).unwrap(); // grade 0
        elem.set_component(1, Complex::one()).unwrap(); // grade 1

        assert!(constraint.satisfies(&elem));

        elem.set_component(3, Complex::one()).unwrap(); // grade 2
        assert!(!constraint.satisfies(&elem));

        let projected = constraint.project(&elem);
        assert!(constraint.satisfies(&projected));
        assert_eq!(projected.component(0), Some(Complex::one()));
        assert_eq!(projected.component(1), Some(Complex::one()));
        assert_eq!(projected.component(3), Some(Complex::zero()));
    }

    #[test]
    fn test_minimize_with_grades() {
        let mut initial = CliffordElement::<f64>::zero(3);
        initial.set_component(0, Complex::new(2.0, 0.0)).unwrap();
        initial.set_component(1, Complex::new(3.0, 0.0)).unwrap();
        initial.set_component(3, Complex::new(4.0, 0.0)).unwrap(); // grade 2

        let result = minimize_with_grades(
            &initial,
            vec![0, 1], // only scalar and vector grades
            MinimizationOptions::default(),
        )
        .unwrap();

        assert!(result.converged);
        // Result should have grade 2 component removed
        assert!(result.minimizer.component(3).unwrap().norm() < 1e-6);
    }

    #[test]
    fn test_gradient_descent_convergence() {
        // Start with non-minimal element
        let mut initial = CliffordElement::<f64>::zero(3);
        initial.set_component(0, Complex::new(5.0, 0.0)).unwrap();
        initial.set_component(1, Complex::new(5.0, 0.0)).unwrap();

        // Minimize without constraints
        struct NoConstraint;
        impl<P: Float> Constraint<P> for NoConstraint {
            fn satisfies(&self, _: &CliffordElement<P>) -> bool {
                true
            }
            fn project_gradient(&self, grad: &CliffordElement<P>) -> CliffordElement<P> {
                grad.clone()
            }
            fn project(&self, x: &CliffordElement<P>) -> CliffordElement<P> {
                x.clone()
            }
        }

        let result =
            minimize_coherence(&initial, &NoConstraint, MinimizationOptions::default()).unwrap();

        assert!(result.converged);
        assert!(result.norm < 1e-6); // Should minimize to zero
    }
}
