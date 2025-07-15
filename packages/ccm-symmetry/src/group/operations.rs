//! Core group operations
//! 
//! This module provides the fundamental group operations:
//! - Multiplication (binary operation)
//! - Inverse (unary operation)
//! - Identity element
//! - Power operations
//! - Commutator calculations

use num_traits::Float;
use crate::group::{GroupElement, SymmetryGroup};
use crate::{SymmetryError, GroupAction};
use ccm_core::CcmError;

/// Group representation type
enum GroupRepresentation {
    /// Matrix group of dimension n
    Matrix(usize),
    /// Abstract group
    Abstract,
}

/// Trait for basic group operations
pub trait GroupOperations<P: Float> {
    /// Multiply two group elements
    fn multiply(&self, a: &GroupElement<P>, b: &GroupElement<P>) -> Result<GroupElement<P>, CcmError>;
    
    /// Compute inverse of a group element
    fn inverse(&self, element: &GroupElement<P>) -> Result<GroupElement<P>, CcmError>;
    
    /// Get the identity element
    fn identity(&self) -> GroupElement<P>;
    
    /// Compute element raised to integer power
    fn power(&self, element: &GroupElement<P>, n: i32) -> Result<GroupElement<P>, CcmError>;
    
    /// Compute commutator [a,b] = a*b*a^(-1)*b^(-1)
    fn commutator(&self, a: &GroupElement<P>, b: &GroupElement<P>) -> Result<GroupElement<P>, CcmError>;
}

impl<P: Float> SymmetryGroup<P> {
    /// Compute group product g * h
    pub fn multiply(
        &self,
        g: &GroupElement<P>,
        h: &GroupElement<P>,
    ) -> Result<GroupElement<P>, CcmError> {
        if g.dimension() != self.dimension || h.dimension() != self.dimension {
            return Err(SymmetryError::InvalidGroupOperation.into());
        }

        // Special handling for Klein group (bit flips compose via XOR)
        if self.cached_order == Some(4) && self.dimension >= 2 {
            // Check if these are bit flip elements
            let g_is_bitflip = g.params.iter().all(|&p| p == P::one() || p == -P::one());
            let h_is_bitflip = h.params.iter().all(|&p| p == P::one() || p == -P::one());
            
            if g_is_bitflip && h_is_bitflip {
                // Multiply bit flips: -1 * -1 = 1, -1 * 1 = -1, etc.
                let params: Vec<P> = g.params.iter()
                    .zip(&h.params)
                    .map(|(&a, &b)| a * b)
                    .collect();
                    
                // Determine order of result
                let is_identity = params.iter().all(|&p| p == P::one());
                let cached_order = if is_identity { Some(1) } else { Some(2) };
                
                return Ok(GroupElement { params, cached_order });
            }
        }

        // Delegate to appropriate representation
        match self.get_representation() {
            GroupRepresentation::Matrix(n) => {
                let matrix_group = crate::matrix_group::MatrixGroup::<P>::new(n);
                matrix_group.multiply(g, h)
            }
            GroupRepresentation::Abstract => {
                // Handle abstract groups based on their structure
                self.multiply_abstract(g, h)
            }
        }
    }

    /// Compute inverse of group element
    pub fn inverse(&self, g: &GroupElement<P>) -> Result<GroupElement<P>, CcmError> {
        if g.dimension() != self.dimension {
            return Err(SymmetryError::InvalidGroupOperation.into());
        }

        // Delegate to appropriate representation
        match self.get_representation() {
            GroupRepresentation::Matrix(n) => {
                let matrix_group = crate::matrix_group::MatrixGroup::<P>::new(n);
                matrix_group.inverse(g)
            }
            GroupRepresentation::Abstract => {
                // Handle abstract groups based on their structure
                self.inverse_abstract(g)
            }
        }
    }

    /// Get the group representation type
    fn get_representation(&self) -> GroupRepresentation {
        // Heuristic: if dimension is a perfect square, assume matrix group
        let sqrt = (self.dimension as f64).sqrt();
        if sqrt.floor() == sqrt && sqrt > 0.0 {
            GroupRepresentation::Matrix(sqrt as usize)
        } else {
            GroupRepresentation::Abstract
        }
    }
    
    /// Compute the order of a group element
    /// 
    /// Returns the smallest positive integer n such that g^n = e
    pub fn element_order(&self, g: &GroupElement<P>) -> Option<usize> {
        if let Some(order) = g.cached_order {
            return Some(order);
        }
        
        // For finite groups, compute by repeated multiplication
        if self.order().is_some() {
            let identity = self.identity();
            let mut current = g.clone();
            let mut order = 1;
            
            // Maximum possible order is the group order
            let max_order = self.order().unwrap_or(100);
            
            while order <= max_order {
                if current.params.iter()
                    .zip(identity.params.iter())
                    .all(|(a, b)| (*a - *b).abs() < P::epsilon()) {
                    return Some(order);
                }
                
                current = self.multiply(&current, g).ok()?;
                order += 1;
            }
        }
        
        None
    }
    
    /// Apply group element to a target via the specified action
    pub fn apply<T>(
        &self,
        g: &GroupElement<P>,
        target: &T,
        action: &dyn GroupAction<P, Target = T>,
    ) -> Result<T, CcmError> {
        action.apply(g, target)
    }
    
    /// Multiply elements in abstract groups
    /// 
    /// This handles various abstract group representations including:
    /// - Permutation groups (symmetric group representations)
    /// - Cyclic groups (addition modulo n)
    /// - Direct products
    /// - Free groups and finitely presented groups
    fn multiply_abstract(
        &self,
        g: &GroupElement<P>,
        h: &GroupElement<P>,
    ) -> Result<GroupElement<P>, CcmError> {
        // Detect the type of abstract group based on generators and relations
        
        // Check if this is a cyclic group (single generator)
        if self.generators.len() == 1 && self.is_cyclic_group() {
            return self.multiply_cyclic(g, h);
        }
        
        // Check if this is a permutation representation
        if self.is_permutation_representation() {
            return self.multiply_permutation(g, h);
        }
        
        // Check if this is a direct product
        if self.is_direct_product() {
            return self.multiply_direct_product(g, h);
        }
        
        // For general abstract groups, use the presentation if available
        if self.has_presentation() {
            return self.multiply_with_relations(g, h);
        }
        
        // Fallback: For abelian groups, use addition of exponents
        if self.is_abelian() {
            return self.multiply_abelian(g, h);
        }
        
        // Last resort: Use free group multiplication
        self.multiply_free(g, h)
    }
    
    /// Compute inverse in abstract groups
    fn inverse_abstract(&self, g: &GroupElement<P>) -> Result<GroupElement<P>, CcmError> {
        // Detect the type of abstract group
        
        // Cyclic groups
        if self.generators.len() == 1 && self.is_cyclic_group() {
            return self.inverse_cyclic(g);
        }
        
        // Permutation groups
        if self.is_permutation_representation() {
            return self.inverse_permutation(g);
        }
        
        // Direct products
        if self.is_direct_product() {
            return self.inverse_direct_product(g);
        }
        
        // Groups with presentations
        if self.has_presentation() {
            return self.inverse_with_relations(g);
        }
        
        // Abelian groups
        if self.is_abelian() {
            return self.inverse_abelian(g);
        }
        
        // Free groups
        self.inverse_free(g)
    }
    
    /// Check if group is cyclic
    fn is_cyclic_group(&self) -> bool {
        // A group is cyclic if it has a single generator with finite or infinite order
        self.generators.len() == 1
    }
    
    /// Check if this is a permutation representation
    fn is_permutation_representation(&self) -> bool {
        // Check if parameters encode permutations
        // For n elements, we need n parameters each in [0, n)
        if self.dimension == 0 {
            return false;
        }
        
        // Check if all generator parameters are valid permutation indices
        self.generators.iter().all(|gen| {
            gen.params.iter().all(|&p| {
                let val = p.to_f64().unwrap_or(-1.0);
                val >= 0.0 && val < self.dimension as f64 && val.fract() == 0.0
            })
        })
    }
    
    /// Check if this is a direct product
    fn is_direct_product(&self) -> bool {
        // Direct products have generators that act on disjoint components
        // This is a heuristic check
        if self.generators.len() < 2 {
            return false;
        }
        
        // Check if generators have disjoint support
        let mut supports = Vec::new();
        for gen in &self.generators {
            let support: Vec<usize> = gen.params.iter().enumerate()
                .filter(|(_, &p)| (p - P::one()).abs() > P::epsilon())
                .map(|(i, _)| i)
                .collect();
            supports.push(support);
        }
        
        // Check if supports are disjoint
        for i in 0..supports.len() {
            for j in i+1..supports.len() {
                if supports[i].iter().any(|&x| supports[j].contains(&x)) {
                    return false;
                }
            }
        }
        
        true
    }
    
    /// Check if group has a presentation
    fn has_presentation(&self) -> bool {
        // For now, we don't store explicit presentations
        // This would be enhanced with a proper presentation structure
        false
    }
    
    /// Check if group is abelian
    fn is_abelian(&self) -> bool {
        // Check commutativity of generators
        // For small generator sets, we can check directly
        if self.generators.len() <= 1 {
            return true;
        }
        
        // For finite groups, check order
        if let Some(order) = self.cached_order {
            // Groups of prime order are cyclic hence abelian
            if is_prime(order) {
                return true;
            }
        }
        
        // Conservative: assume non-abelian unless we can prove otherwise
        false
    }
    
    /// Multiply in cyclic groups
    fn multiply_cyclic(
        &self,
        g: &GroupElement<P>,
        h: &GroupElement<P>,
    ) -> Result<GroupElement<P>, CcmError> {
        // In cyclic groups, multiplication is addition of exponents
        let gen = &self.generators[0];
        
        // Find exponents: g = gen^a, h = gen^b
        let a = self.find_cyclic_exponent(g, gen)?;
        let b = self.find_cyclic_exponent(h, gen)?;
        
        // Result is gen^(a+b)
        let c = a + b;
        
        // If finite cyclic group, reduce modulo order
        if let Some(order) = self.cached_order {
            let c_mod = c.to_f64().unwrap_or(0.0) % order as f64;
            self.power_of_generator(gen, P::from(c_mod).unwrap())
        } else {
            self.power_of_generator(gen, c)
        }
    }
    
    /// Find exponent in cyclic group
    fn find_cyclic_exponent(
        &self,
        elem: &GroupElement<P>,
        gen: &GroupElement<P>,
    ) -> Result<P, CcmError> {
        // For cyclic groups, find n such that elem = gen^n
        // This assumes elem.params = n * gen.params (approximately)
        
        for i in 0..gen.params.len() {
            if gen.params[i].abs() > P::epsilon() {
                return Ok(elem.params[i] / gen.params[i]);
            }
        }
        
        Err(SymmetryError::InvalidGroupOperation.into())
    }
    
    /// Compute power of generator
    fn power_of_generator(&self, gen: &GroupElement<P>, n: P) -> Result<GroupElement<P>, CcmError> {
        let params = gen.params.iter()
            .map(|&p| p * n)
            .collect();
            
        Ok(GroupElement {
            params,
            cached_order: None,
        })
    }
    
    /// Multiply permutations
    fn multiply_permutation(
        &self,
        g: &GroupElement<P>,
        h: &GroupElement<P>,
    ) -> Result<GroupElement<P>, CcmError> {
        // Permutation composition: (g ∘ h)(i) = g(h(i))
        let n = self.dimension;
        let mut result = vec![P::zero(); n];
        
        for i in 0..n {
            let h_i = h.params[i].to_f64().unwrap_or(0.0) as usize;
            if h_i >= n {
                return Err(SymmetryError::InvalidGroupOperation.into());
            }
            
            let g_h_i = g.params[h_i].to_f64().unwrap_or(0.0) as usize;
            if g_h_i >= n {
                return Err(SymmetryError::InvalidGroupOperation.into());
            }
            
            result[i] = P::from(g_h_i).unwrap();
        }
        
        Ok(GroupElement {
            params: result,
            cached_order: None,
        })
    }
    
    /// Multiply in direct product
    fn multiply_direct_product(
        &self,
        g: &GroupElement<P>,
        h: &GroupElement<P>,
    ) -> Result<GroupElement<P>, CcmError> {
        // Direct product: multiply component-wise according to component groups
        // This is a simplified version - full implementation would track
        // component boundaries and use appropriate multiplication for each
        
        let params = g.params.iter().zip(&h.params)
            .map(|(&a, &b)| a + b)  // Assuming additive notation for components
            .collect();
            
        Ok(GroupElement {
            params,
            cached_order: None,
        })
    }
    
    /// Multiply using group presentation relations
    fn multiply_with_relations(
        &self,
        _g: &GroupElement<P>,
        _h: &GroupElement<P>,
    ) -> Result<GroupElement<P>, CcmError> {
        // Would use Todd-Coxeter or similar algorithm
        // For now, not implemented
        Err(SymmetryError::InvalidGroupOperation.into())
    }
    
    /// Multiply in abelian groups
    fn multiply_abelian(
        &self,
        g: &GroupElement<P>,
        h: &GroupElement<P>,
    ) -> Result<GroupElement<P>, CcmError> {
        // In abelian groups, we can use additive notation
        let params = g.params.iter().zip(&h.params)
            .map(|(&a, &b)| a + b)
            .collect();
            
        Ok(GroupElement {
            params,
            cached_order: None,
        })
    }
    
    /// Multiply in free groups
    fn multiply_free(
        &self,
        g: &GroupElement<P>,
        h: &GroupElement<P>,
    ) -> Result<GroupElement<P>, CcmError> {
        // Free group multiplication: concatenate and reduce
        // This is a simplified version - full implementation would
        // properly handle word reduction
        
        // For now, just concatenate parameters
        let mut params = g.params.clone();
        params.extend(&h.params);
        
        // Reduce if possible (remove inverse pairs)
        // Simplified: just return concatenation
        Ok(GroupElement {
            params,
            cached_order: None,
        })
    }
    
    /// Inverse in cyclic groups
    fn inverse_cyclic(&self, g: &GroupElement<P>) -> Result<GroupElement<P>, CcmError> {
        let gen = &self.generators[0];
        let a = self.find_cyclic_exponent(g, gen)?;
        
        if let Some(order) = self.cached_order {
            // Finite cyclic: inverse is gen^(order - a)
            let inv_exp = P::from(order).unwrap() - a;
            self.power_of_generator(gen, inv_exp)
        } else {
            // Infinite cyclic: inverse is gen^(-a)
            self.power_of_generator(gen, -a)
        }
    }
    
    /// Inverse of permutation
    fn inverse_permutation(&self, g: &GroupElement<P>) -> Result<GroupElement<P>, CcmError> {
        // Inverse permutation: if g(i) = j, then g^(-1)(j) = i
        let n = self.dimension;
        let mut result = vec![P::zero(); n];
        
        for i in 0..n {
            let j = g.params[i].to_f64().unwrap_or(0.0) as usize;
            if j >= n {
                return Err(SymmetryError::InvalidGroupOperation.into());
            }
            result[j] = P::from(i).unwrap();
        }
        
        Ok(GroupElement {
            params: result,
            cached_order: g.cached_order, // Same order as original
        })
    }
    
    /// Inverse in direct product
    fn inverse_direct_product(&self, g: &GroupElement<P>) -> Result<GroupElement<P>, CcmError> {
        // Inverse component-wise
        let params = g.params.iter()
            .map(|&p| -p)  // Assuming additive notation
            .collect();
            
        Ok(GroupElement {
            params,
            cached_order: g.cached_order,
        })
    }
    
    /// Inverse using relations
    fn inverse_with_relations(&self, _g: &GroupElement<P>) -> Result<GroupElement<P>, CcmError> {
        // Would use presentation relations
        Err(SymmetryError::InvalidGroupOperation.into())
    }
    
    /// Inverse in abelian groups
    fn inverse_abelian(&self, g: &GroupElement<P>) -> Result<GroupElement<P>, CcmError> {
        // In abelian groups with additive notation, inverse is negation
        let params = g.params.iter()
            .map(|&p| -p)
            .collect();
            
        Ok(GroupElement {
            params,
            cached_order: g.cached_order,
        })
    }
    
    /// Inverse in free groups
    fn inverse_free(&self, g: &GroupElement<P>) -> Result<GroupElement<P>, CcmError> {
        // In free groups, reverse the word and invert each letter
        let params = g.params.iter().rev()
            .map(|&p| -p)  // Negative indicates inverse
            .collect();
            
        Ok(GroupElement {
            params,
            cached_order: g.cached_order,
        })
    }
}

/// Check if a number is prime
fn is_prime(n: usize) -> bool {
    if n < 2 {
        return false;
    }
    if n == 2 {
        return true;
    }
    if n % 2 == 0 {
        return false;
    }
    
    let sqrt_n = (n as f64).sqrt() as usize;
    for i in (3..=sqrt_n).step_by(2) {
        if n % i == 0 {
            return false;
        }
    }
    
    true
}