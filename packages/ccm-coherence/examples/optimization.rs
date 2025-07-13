//! Examples of coherence minimization and optimization

use ccm_coherence::{
    coherence_norm,
    optimization::{
        minimize_coherence, minimize_with_grades, GradeConstraint, MinimizationOptions,
    },
    CliffordElement,
};
use num_complex::Complex;

fn main() {
    println!("=== Coherence Optimization Examples ===\n");

    // Example 1: Minimize coherence with grade constraints
    println!("1. Minimizing coherence with grade constraints");

    // Start with a mixed-grade element
    let mut initial = CliffordElement::<f64>::zero(3);
    initial.set_component(0, Complex::new(3.0, 0.0)).unwrap(); // scalar
    initial.set_component(1, Complex::new(4.0, 0.0)).unwrap(); // e₁
    initial.set_component(3, Complex::new(2.0, 0.0)).unwrap(); // e₁e₂
    initial.set_component(7, Complex::new(1.0, 0.0)).unwrap(); // e₁e₂e₃

    println!("   Initial element has grades 0, 1, 2, 3");
    println!("   Initial coherence norm: {:.3}", coherence_norm(&initial));

    // Minimize keeping only even grades (0 and 2)
    let result =
        minimize_with_grades(&initial, vec![0, 2], MinimizationOptions::default()).unwrap();

    println!("   After constraining to even grades:");
    println!("   Final coherence norm: {:.3}", result.norm);
    println!("   Converged: {}", result.converged);
    println!("   Iterations: {}", result.iterations);

    // Example 2: Custom constraint
    println!("\n2. Minimization with custom constraint");

    // Create a constraint that keeps the scalar part fixed
    struct ScalarConstraint {
        target_scalar: Complex<f64>,
    }

    impl ccm_coherence::optimization::Constraint<f64> for ScalarConstraint {
        fn satisfies(&self, x: &CliffordElement<f64>) -> bool {
            if let Some(scalar) = x.component(0) {
                (scalar - self.target_scalar).norm() < 1e-6
            } else {
                false
            }
        }

        fn project_gradient(&self, grad: &CliffordElement<f64>) -> CliffordElement<f64> {
            // Zero out the scalar component of gradient
            let mut proj = grad.clone();
            proj.set_component(0, Complex::new(0.0, 0.0)).unwrap();
            proj
        }

        fn project(&self, x: &CliffordElement<f64>) -> CliffordElement<f64> {
            // Ensure scalar part equals target
            let mut proj = x.clone();
            proj.set_component(0, self.target_scalar).unwrap();
            proj
        }
    }

    let constraint = ScalarConstraint {
        target_scalar: Complex::new(1.0, 0.0),
    };

    let result2 =
        minimize_coherence(&initial, &constraint, MinimizationOptions::default()).unwrap();

    println!("   Minimizing with scalar = 1 constraint:");
    println!("   Final norm: {:.3}", result2.norm);
    println!(
        "   Scalar component: {:.3}",
        result2.minimizer.component(0).unwrap().re
    );

    // Example 3: Minimization options
    println!("\n3. Custom minimization options");

    let mut options = MinimizationOptions::default();
    options.max_iterations = 100;
    options.tolerance = 1e-8;
    options.initial_step_size = 0.01;

    let grade_constraint = GradeConstraint {
        allowed_grades: vec![1], // Only vectors
    };

    let result3 = minimize_coherence(&initial, &grade_constraint, options).unwrap();

    println!("   Minimizing to vector subspace:");
    println!("   Final norm: {:.3}", result3.norm);
    println!("   Result has only grade 1 components");

    // Print non-zero components
    print!("   Non-zero components: ");
    for i in 0..8 {
        if let Some(comp) = result3.minimizer.component(i) {
            if comp.norm() > 1e-6 {
                print!("e{} ", format_index(i));
            }
        }
    }
    println!();
}

fn format_index(i: usize) -> String {
    match i {
        0 => "1".to_string(),
        1 => "₁".to_string(),
        2 => "₂".to_string(),
        3 => "₁₂".to_string(),
        4 => "₃".to_string(),
        5 => "₁₃".to_string(),
        6 => "₂₃".to_string(),
        7 => "₁₂₃".to_string(),
        _ => format!("{}", i),
    }
}
