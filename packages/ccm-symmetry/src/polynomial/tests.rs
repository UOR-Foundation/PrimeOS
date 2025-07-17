//! Tests for polynomial invariant theory

#[cfg(test)]
mod tests {
    use crate::polynomial::*;
    use crate::group::SymmetryGroup;
    
    #[test]
    fn test_monomial_lcm_and_gcd() {
        // Test LCM of x²y and xy²
        let m1 = Monomial::new(vec![2, 1, 0]);
        let m2 = Monomial::new(vec![1, 2, 0]);
        let lcm = m1.lcm(&m2);
        assert_eq!(lcm.exponents, vec![2, 2, 0]);
    }
    
    #[test]
    fn test_polynomial_substitution() {
        let ring = PolynomialRing::<f64>::new(2);
        
        // Create polynomial x² + y²
        let x = ring.variable(0);
        let y = ring.variable(1);
        let poly = x.clone() * x.clone() + y.clone() * y;
        
        // Evaluate at (3, 4)
        assert_eq!(poly.evaluate(&[3.0, 4.0]), 25.0);
    }
    
    #[test]
    fn test_groebner_basis_circle_line() {
        let ring = PolynomialRing::<f64>::new(2);
        let ordering = MonomialOrdering::Lex;
        
        // Ideal: circle x² + y² - 1 = 0 and line x - y = 0 (simpler case)
        let x = ring.variable(0);
        let y = ring.variable(1);
        
        let circle = x.clone() * x.clone() + y.clone() * y.clone() - ring.one();
        let line = x.clone() - y.clone();
        
        let gb = buchberger_algorithm(vec![circle.clone(), line.clone()], ordering);
        
        // The Gröbner basis should solve the system
        assert!(gb.basis.len() >= 1);
        
        // Solutions are x = y = ±√(1/2)
        let sqrt_half = (0.5_f64).sqrt();
        let test_point1 = vec![sqrt_half, sqrt_half];
        let test_point2 = vec![-sqrt_half, -sqrt_half];
        
        // Check that the original polynomials vanish at the solutions
        assert!((circle.evaluate(&test_point1)).abs() < 1e-10);
        assert!((line.evaluate(&test_point1)).abs() < 1e-10);
        assert!((circle.evaluate(&test_point2)).abs() < 1e-10);
        assert!((line.evaluate(&test_point2)).abs() < 1e-10);
        
        // The Gröbner basis should contain polynomials that also vanish
        for poly in &gb.basis {
            let value1 = poly.evaluate(&test_point1);
            let value2 = poly.evaluate(&test_point2);
            assert!(value1.abs() < 1e-6, "Poly failed at point1: {}", value1);
            assert!(value2.abs() < 1e-6, "Poly failed at point2: {}", value2);
        }
    }
    
    #[test]
    fn test_symmetric_polynomial_invariants() {
        // Test that elementary symmetric polynomials are invariant under S3
        let s3 = SymmetryGroup::<f64>::symmetric_group(3).unwrap();
        let mut inv_ring = InvariantRing::new(s3, 3);
        inv_ring.compute_generators(3);
        
        // Verify we have the expected number of generators
        assert!(inv_ring.generators.len() >= 3);
        
        // Test specific values
        let point = vec![2.0, 3.0, 5.0];
        
        // e1 = x + y + z = 10
        assert_eq!(inv_ring.generators[0].evaluate(&point), 10.0);
        
        // e2 = xy + xz + yz = 6 + 10 + 15 = 31
        assert_eq!(inv_ring.generators[1].evaluate(&point), 31.0);
        
        // e3 = xyz = 30
        assert_eq!(inv_ring.generators[2].evaluate(&point), 30.0);
    }
    
    #[test]
    fn test_reynolds_operator_averaging() {
        // Test Reynolds operator on symmetric group S2
        let s2 = SymmetryGroup::<f64>::symmetric_group(2).unwrap();
        let reynolds = ReynoldsOperator::new(s2);
        let ring = PolynomialRing::<f64>::new(2);
        
        // Test averaging x over S2
        let x = ring.variable(0);
        let averaged = reynolds.apply(&x);
        
        // Should get (x + y)/2
        assert_eq!(averaged.evaluate(&[2.0, 4.0]), 3.0); // (2 + 4)/2 = 3
        assert_eq!(averaged.evaluate(&[1.0, 5.0]), 3.0); // (1 + 5)/2 = 3
        
        // Test that x + y is already invariant
        let y = ring.variable(1);
        let invariant_poly = x.clone() + y.clone();
        
        let averaged2 = reynolds.apply(&invariant_poly);
        
        // Should be unchanged
        assert_eq!(
            invariant_poly.evaluate(&[1.0, 2.0]),
            averaged2.evaluate(&[1.0, 2.0])
        );
    }
    
    #[test]
    fn test_invariant_ring_verification() {
        let s2 = SymmetryGroup::<f64>::symmetric_group(2).unwrap();
        let inv_ring = InvariantRing::new(s2, 2);
        
        let ring = PolynomialRing::<f64>::new(2);
        let x = ring.variable(0);
        let y = ring.variable(1);
        
        // x + y is invariant under S2
        let sym_poly = x.clone() + y.clone();
        assert!(inv_ring.is_invariant(&sym_poly));
        
        // x - y is not invariant under S2
        let antisym_poly = x - y;
        assert!(!inv_ring.is_invariant(&antisym_poly));
    }
    
    #[test]
    fn test_power_sum_polynomials() {
        let ring = PolynomialRing::<f64>::new(3);
        
        // Create p_2 = x² + y² + z²
        let mut p2 = Polynomial::zero(3);
        for i in 0..3 {
            let var = ring.variable(i);
            p2 = p2 + var.clone() * var;
        }
        
        assert_eq!(p2.evaluate(&[1.0, 2.0, 3.0]), 14.0);
        assert_eq!(p2.degree(), 2);
    }
    
    #[test] 
    fn test_monomial_ordering_comparison() {
        // Test different orderings give different results
        let m1 = Monomial::new(vec![3, 1, 0]); // x³y
        let m2 = Monomial::new(vec![2, 2, 0]); // x²y²
        let m3 = Monomial::new(vec![1, 1, 2]); // xyz²
        
        use core::cmp::Ordering;
        
        // Lex: x³y > x²y² > xyz²
        assert_eq!(MonomialOrdering::Lex.compare(&m1, &m2), Ordering::Greater);
        assert_eq!(MonomialOrdering::Lex.compare(&m2, &m3), Ordering::Greater);
        
        // GrRevLex: xyz² > x³y = x²y² (same degree 4)
        assert_eq!(MonomialOrdering::GrRevLex.compare(&m3, &m1), Ordering::Less); // degree 4 vs 4
        assert_eq!(MonomialOrdering::GrRevLex.compare(&m1, &m2), Ordering::Greater); // x³y > x²y² in grevlex
    }
    
    #[test]
    fn test_orthogonal_group_invariants() {
        let invariants = InvariantRing::<f64>::orthogonal_invariants(4);
        
        // Should have quadratic form x² + y² + z² + w²
        assert_eq!(invariants.len(), 1);
        let quad = &invariants[0];
        
        // Test invariance under rotation
        let point1 = vec![1.0, 0.0, 0.0, 0.0];
        let point2 = vec![0.0, 1.0, 0.0, 0.0];
        assert_eq!(quad.evaluate(&point1), quad.evaluate(&point2));
    }
    
    #[test]
    fn test_unitary_group_invariants() {
        let invariants = InvariantRing::<f64>::unitary_invariants(2);
        
        // Should have |z₁|² and |z₂|²
        assert_eq!(invariants.len(), 2);
        
        // Test |z₁|² = x₁² + y₁²
        let z1_norm = &invariants[0];
        assert_eq!(z1_norm.evaluate(&[3.0, 4.0, 0.0, 0.0]), 25.0);
        
        // Test |z₂|² = x₂² + y₂²
        let z2_norm = &invariants[1];
        assert_eq!(z2_norm.evaluate(&[0.0, 0.0, 5.0, 12.0]), 169.0);
    }
}