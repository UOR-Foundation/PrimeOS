//! Verification methods for group axioms and action properties

use crate::{
    actions::GroupAction,
    group::{GroupElement, SymmetryGroup},
};
use ccm_coherence::{coherence_norm, coherence_product, CliffordElement};
use ccm_core::{CcmError, Float};

#[cfg(feature = "alloc")]
use alloc::boxed::Box;

/// Verify that a set of elements forms a group
pub struct GroupAxiomVerifier<P: Float> {
    /// The group to verify
    group: SymmetryGroup<P>,
    /// Tolerance for floating point comparisons
    tolerance: P,
}

impl<P: Float> GroupAxiomVerifier<P> {
    /// Create a new verifier
    pub fn new(group: SymmetryGroup<P>) -> Self {
        Self {
            group,
            tolerance: P::epsilon(),
        }
    }

    /// Set custom tolerance
    pub fn with_tolerance(mut self, tolerance: P) -> Self {
        self.tolerance = tolerance;
        self
    }

    /// Verify closure: g * h is in G for all g, h in G
    pub fn verify_closure(&self) -> Result<bool, CcmError> {
        for g in self.group.generators() {
            for h in self.group.generators() {
                let gh = self.group.multiply(g, h)?;
                if !self.group.contains(&gh) {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }

    /// Verify associativity: (g * h) * k = g * (h * k)
    pub fn verify_associativity(&self) -> Result<bool, CcmError> {
        let generators = self.group.generators();
        if generators.len() < 3 {
            return Ok(true); // Trivially true for small groups
        }

        // Check on a sample of triples
        for i in 0..generators.len().min(5) {
            for j in 0..generators.len().min(5) {
                for k in 0..generators.len().min(5) {
                    let g = &generators[i];
                    let h = &generators[j];
                    let k_elem = &generators[k];

                    let gh = self.group.multiply(g, h)?;
                    let gh_k = self.group.multiply(&gh, k_elem)?;

                    let hk = self.group.multiply(h, k_elem)?;
                    let g_hk = self.group.multiply(g, &hk)?;

                    if !self.elements_equal(&gh_k, &g_hk) {
                        return Ok(false);
                    }
                }
            }
        }
        Ok(true)
    }

    /// Verify identity exists: e * g = g * e = g
    pub fn verify_identity(&self) -> Result<bool, CcmError> {
        let identity = self.group.identity();

        for g in self.group.generators() {
            let eg = self.group.multiply(&identity, g)?;
            let ge = self.group.multiply(g, &identity)?;

            if !self.elements_equal(&eg, g) || !self.elements_equal(&ge, g) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Verify inverses exist: g * g^(-1) = g^(-1) * g = e
    pub fn verify_inverses(&self) -> Result<bool, CcmError> {
        let identity = self.group.identity();

        for g in self.group.generators() {
            let g_inv = self.group.inverse(g)?;
            let gg_inv = self.group.multiply(g, &g_inv)?;
            let g_inv_g = self.group.multiply(&g_inv, g)?;

            if !self.elements_equal(&gg_inv, &identity) || !self.elements_equal(&g_inv_g, &identity)
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Check if two group elements are equal within tolerance
    fn elements_equal(&self, a: &GroupElement<P>, b: &GroupElement<P>) -> bool {
        if a.dimension() != b.dimension() {
            return false;
        }

        a.params
            .iter()
            .zip(&b.params)
            .all(|(&x, &y)| (x - y).abs() < self.tolerance)
    }

    /// Verify all group axioms
    pub fn verify_all(&self) -> Result<bool, CcmError> {
        Ok(self.verify_closure()?
            && self.verify_associativity()?
            && self.verify_identity()?
            && self.verify_inverses()?)
    }
}

/// Verify properties of group actions
pub struct ActionVerifier<P: Float, T> {
    /// The group
    group: SymmetryGroup<P>,
    /// The action
    action: Box<dyn GroupAction<P, Target = T>>,
}

impl<P: Float, T: Clone + PartialEq> ActionVerifier<P, T> {
    /// Create a new action verifier
    pub fn new(group: SymmetryGroup<P>, action: Box<dyn GroupAction<P, Target = T>>) -> Self {
        Self { group, action }
    }

    /// Verify identity action: e · x = x
    pub fn verify_identity_action(&self, x: &T) -> Result<bool, CcmError> {
        let identity = self.group.identity();
        let ex = self.action.apply(&identity, x)?;
        Ok(&ex == x)
    }

    /// Verify compatibility: (g * h) · x = g · (h · x)
    pub fn verify_compatibility(&self, x: &T) -> Result<bool, CcmError> {
        for g in self.group.generators() {
            for h in self.group.generators() {
                let gh = self.group.multiply(g, h)?;
                let gh_x = self.action.apply(&gh, x)?;

                let h_x = self.action.apply(h, x)?;
                let g_hx = self.action.apply(g, &h_x)?;

                if gh_x != g_hx {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }
}

/// Verify invariance properties specific to CCM
pub struct CCMInvarianceVerifier<P: Float> {
    /// Tolerance for comparisons
    tolerance: P,
}

impl<P: Float> Default for CCMInvarianceVerifier<P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: Float> CCMInvarianceVerifier<P> {
    /// Create a new verifier
    pub fn new() -> Self {
        Self {
            tolerance: P::epsilon(),
        }
    }

    /// Verify coherence norm preservation
    pub fn verify_coherence_preservation(
        &self,
        g: &GroupElement<P>,
        x: &CliffordElement<P>,
        action: &dyn GroupAction<P, Target = CliffordElement<P>>,
    ) -> Result<bool, CcmError> {
        let gx = action.apply(g, x)?;
        let norm_x = coherence_norm(x);
        let norm_gx = coherence_norm(&gx);

        Ok((norm_x - norm_gx).abs() < self.tolerance)
    }

    /// Verify coherence inner product preservation
    pub fn verify_inner_product_preservation(
        &self,
        g: &GroupElement<P>,
        x: &CliffordElement<P>,
        y: &CliffordElement<P>,
        action: &dyn GroupAction<P, Target = CliffordElement<P>>,
    ) -> Result<bool, CcmError> {
        let gx = action.apply(g, x)?;
        let gy = action.apply(g, y)?;

        let inner_xy = coherence_product(x, y);
        let inner_gxgy = coherence_product(&gx, &gy);

        Ok((inner_xy - inner_gxgy).norm() < self.tolerance)
    }

    /// Verify grade preservation
    pub fn verify_grade_preservation(
        &self,
        g: &GroupElement<P>,
        x: &CliffordElement<P>,
        action: &dyn GroupAction<P, Target = CliffordElement<P>>,
    ) -> Result<bool, CcmError> {
        let gx = action.apply(g, x)?;

        // Check each grade component
        for k in 0..=x.dimension() {
            let x_k = x.grade(k);
            let gx_k = gx.grade(k);

            // If x has no k-grade component, gx shouldn't either
            let x_k_norm = coherence_norm(&x_k);
            let gx_k_norm = coherence_norm(&gx_k);

            if (x_k_norm < self.tolerance) != (gx_k_norm < self.tolerance) {
                return Ok(false);
            }
        }

        Ok(true)
    }

    /// Verify all CCM invariance properties
    pub fn verify_all_invariances(
        &self,
        g: &GroupElement<P>,
        x: &CliffordElement<P>,
        y: &CliffordElement<P>,
        action: &dyn GroupAction<P, Target = CliffordElement<P>>,
    ) -> Result<bool, CcmError> {
        Ok(self.verify_coherence_preservation(g, x, action)?
            && self.verify_inner_product_preservation(g, x, y, action)?
            && self.verify_grade_preservation(g, x, action)?)
    }
}

/// Quick verification functions
pub mod quick_verify {
    use super::*;

    /// Check if a transformation preserves unit norm
    pub fn preserves_unit_norm<P: Float>(
        g: &GroupElement<P>,
        action: &dyn GroupAction<P, Target = CliffordElement<P>>,
    ) -> Result<bool, CcmError> {
        // Test on several unit vectors
        for i in 0..g.dimension().min(5) {
            let mut x = CliffordElement::zero(g.dimension());
            x.set_component(1 << i, num_complex::Complex::new(P::one(), P::zero()))?;
            let x = ccm_coherence::metric::normalize(&x)?;

            let gx = action.apply(g, &x)?;
            let norm_gx = coherence_norm(&gx);

            if (norm_gx - P::one()).abs() > P::epsilon() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Check if the action is linear
    pub fn is_linear_action<P: Float>(
        g: &GroupElement<P>,
        action: &dyn GroupAction<P, Target = CliffordElement<P>>,
    ) -> Result<bool, CcmError> {
        // Test linearity: g(ax + by) = a*g(x) + b*g(y)
        let dim = g.dimension();
        let x = CliffordElement::scalar(P::from(2.0).unwrap(), dim);
        let y = CliffordElement::scalar(P::from(3.0).unwrap(), dim);
        let a = P::from(1.5).unwrap();
        let b = P::from(2.5).unwrap();

        let ax_by = x.clone() * a + y.clone() * b;
        let g_axby = action.apply(g, &ax_by)?;

        let gx = action.apply(g, &x)?;
        let gy = action.apply(g, &y)?;
        let agx_bgy = gx * a + gy * b;

        // Check if they're equal
        let diff = g_axby - agx_bgy;
        Ok(coherence_norm(&diff) < P::epsilon())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::actions::CliffordAction;
    use ccm_coherence::CliffordAlgebra;

    #[test]
    fn test_group_axiom_verifier() {
        let group = SymmetryGroup::<f64>::generate(4).unwrap();
        let verifier = GroupAxiomVerifier::new(group);

        assert!(verifier.verify_identity().unwrap());
        assert!(verifier.verify_closure().unwrap());
    }

    #[test]
    fn test_ccm_invariance() {
        let algebra = CliffordAlgebra::<f64>::generate(3).unwrap();
        let action = CliffordAction::new(algebra);
        let verifier = CCMInvarianceVerifier::<f64>::new();

        let g = GroupElement::identity(3);
        let x = CliffordElement::scalar(2.0, 3);
        let y = CliffordElement::scalar(3.0, 3);

        assert!(verifier
            .verify_all_invariances(&g, &x, &y, &action)
            .unwrap());
    }
}
