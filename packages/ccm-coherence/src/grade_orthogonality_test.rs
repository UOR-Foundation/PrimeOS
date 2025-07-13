//! Test to verify grade orthogonality in coherence inner product

#[cfg(test)]
mod tests {
    use crate::{coherence_product, CliffordElement};
    use num_complex::Complex;

    #[test]
    fn test_grade_orthogonality() {
        // Create elements of different grades
        let mut grade0 = CliffordElement::<f64>::zero(3);
        grade0.set_component(0, Complex::new(2.0, 0.0)).unwrap(); // scalar

        let mut grade1 = CliffordElement::<f64>::zero(3);
        grade1.set_component(1, Complex::new(3.0, 0.0)).unwrap(); // e₀
        grade1.set_component(2, Complex::new(4.0, 0.0)).unwrap(); // e₁

        let mut grade2 = CliffordElement::<f64>::zero(3);
        grade2.set_component(3, Complex::new(5.0, 0.0)).unwrap(); // e₀e₁
        grade2.set_component(5, Complex::new(6.0, 0.0)).unwrap(); // e₀e₂

        let mut grade3 = CliffordElement::<f64>::zero(3);
        grade3.set_component(7, Complex::new(7.0, 0.0)).unwrap(); // e₀e₁e₂

        // Test orthogonality between different grades
        let prod_01 = coherence_product(&grade0, &grade1);
        assert!(prod_01.norm() < 1e-10, "Grade 0 and 1 should be orthogonal");

        let prod_02 = coherence_product(&grade0, &grade2);
        assert!(prod_02.norm() < 1e-10, "Grade 0 and 2 should be orthogonal");

        let prod_03 = coherence_product(&grade0, &grade3);
        assert!(prod_03.norm() < 1e-10, "Grade 0 and 3 should be orthogonal");

        let prod_12 = coherence_product(&grade1, &grade2);
        assert!(prod_12.norm() < 1e-10, "Grade 1 and 2 should be orthogonal");

        let prod_13 = coherence_product(&grade1, &grade3);
        assert!(prod_13.norm() < 1e-10, "Grade 1 and 3 should be orthogonal");

        let prod_23 = coherence_product(&grade2, &grade3);
        assert!(prod_23.norm() < 1e-10, "Grade 2 and 3 should be orthogonal");

        // Test non-orthogonality within same grade
        let prod_00 = coherence_product(&grade0, &grade0);
        assert!(
            (prod_00.re - 4.0).abs() < 1e-10,
            "Grade 0 self-product should be 4"
        );

        let prod_11 = coherence_product(&grade1, &grade1);
        assert!(
            (prod_11.re - 25.0).abs() < 1e-10,
            "Grade 1 self-product should be 25 (3²+4²)"
        );

        let prod_22 = coherence_product(&grade2, &grade2);
        assert!(
            (prod_22.re - 61.0).abs() < 1e-10,
            "Grade 2 self-product should be 61 (5²+6²)"
        );

        let prod_33 = coherence_product(&grade3, &grade3);
        assert!(
            (prod_33.re - 49.0).abs() < 1e-10,
            "Grade 3 self-product should be 49 (7²)"
        );
    }

    #[test]
    fn test_mixed_grade_orthogonality() {
        // Create an element with mixed grades
        let mut mixed = CliffordElement::<f64>::zero(3);
        mixed.set_component(0, Complex::new(1.0, 0.0)).unwrap(); // grade 0
        mixed.set_component(1, Complex::new(2.0, 0.0)).unwrap(); // grade 1
        mixed.set_component(3, Complex::new(3.0, 0.0)).unwrap(); // grade 2
        mixed.set_component(7, Complex::new(4.0, 0.0)).unwrap(); // grade 3

        // Extract individual grades
        let g0 = mixed.grade(0);
        let g1 = mixed.grade(1);
        let g2 = mixed.grade(2);
        let g3 = mixed.grade(3);

        // Verify orthogonality
        assert!(coherence_product(&g0, &g1).norm() < 1e-10);
        assert!(coherence_product(&g0, &g2).norm() < 1e-10);
        assert!(coherence_product(&g0, &g3).norm() < 1e-10);
        assert!(coherence_product(&g1, &g2).norm() < 1e-10);
        assert!(coherence_product(&g1, &g3).norm() < 1e-10);
        assert!(coherence_product(&g2, &g3).norm() < 1e-10);

        // Verify coherence norm decomposition
        use crate::metric::coherence_norm_squared;
        let total_norm_sq = coherence_norm_squared(&mixed);
        let sum_of_grade_norms = coherence_norm_squared(&g0)
            + coherence_norm_squared(&g1)
            + coherence_norm_squared(&g2)
            + coherence_norm_squared(&g3);

        assert!(
            (total_norm_sq - sum_of_grade_norms).abs() < 1e-10,
            "Total norm squared should equal sum of grade norm squares"
        );
    }
}
