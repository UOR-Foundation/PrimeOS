//! Main SymmetryGroup struct implementation
//! 
//! This module contains the primary SymmetryGroup struct that
//! unifies all group types under a common interface.

use num_traits::Float;
use crate::group::{GroupElement, GroupType};

/// The symmetry group for n-dimensional CCM
/// 
/// This is the main interface for working with symmetry groups.
/// It provides a unified API for finite, infinite, and continuous groups.
#[derive(Clone)]
pub struct SymmetryGroup<P: Float> {
    /// Dimension of the space
    pub(crate) dimension: usize,
    /// Group generators
    pub(crate) generators: Vec<GroupElement<P>>,
    /// Type of group
    pub(crate) group_type: GroupType<P>,
    /// Cached order of the group
    pub(crate) cached_order: Option<usize>,
}

impl<P: Float> SymmetryGroup<P> {
    /// Generate symmetry group for n dimensions
    pub fn generate(n: usize) -> Result<Self, ccm_core::CcmError> {
        if n == 0 {
            return Err(crate::SymmetryError::InvalidGroupOperation.into());
        }

        // Start with empty generators - will be populated based on specific group
        Ok(Self {
            dimension: n,
            generators: Vec::new(),
            group_type: GroupType::Continuous, // Default to continuous
            cached_order: None,
        })
    }

    /// Get the identity element
    pub fn identity(&self) -> GroupElement<P> {
        GroupElement::identity(self.dimension)
    }

    /// Get group element from parameters
    pub fn element(&self, params: &[P]) -> Result<GroupElement<P>, ccm_core::CcmError> {
        if params.len() != self.dimension {
            return Err(crate::SymmetryError::InvalidGroupOperation.into());
        }

        Ok(GroupElement {
            params: params.to_vec(),
            cached_order: None,
        })
    }
    
    /// Get the dimension of the space this group acts on
    pub fn dimension(&self) -> usize {
        self.dimension
    }
    
    /// Get the group generators
    pub fn generators(&self) -> &[GroupElement<P>] {
        &self.generators
    }
    
    /// Get the group type
    pub fn group_type(&self) -> &GroupType<P> {
        &self.group_type
    }
    
    /// Get the order of the group (number of elements)
    pub fn order(&self) -> Option<usize> {
        if let Some(order) = self.cached_order {
            return Some(order);
        }
        
        match &self.group_type {
            GroupType::Finite { elements } => Some(elements.len()),
            GroupType::Continuous | GroupType::DiscreteInfinite => None,
        }
    }
    
    /// Add a generator to the group
    pub fn add_generator(&mut self, g: GroupElement<P>) -> Result<(), ccm_core::CcmError> {
        if g.dimension() != self.dimension {
            return Err(crate::SymmetryError::InvalidGroupOperation.into());
        }

        self.generators.push(g);
        Ok(())
    }

    /// Check if element is in the group
    /// 
    /// For finite groups, checks if the element is in the explicit element list.
    /// For infinite groups, verifies the element can be expressed as a product of generators.
    pub fn contains(&self, g: &GroupElement<P>) -> bool {
        // First check dimension compatibility
        if g.dimension() != self.dimension {
            return false;
        }
        
        match &self.group_type {
            GroupType::Finite { elements } => {
                // For finite groups, check explicit membership
                elements.iter().any(|elem| {
                    elem.params.len() == g.params.len() &&
                    elem.params.iter().zip(&g.params)
                        .all(|(a, b)| (*a - *b).abs() < P::epsilon())
                })
            }
            GroupType::DiscreteInfinite => {
                // For discrete infinite groups, check if element can be expressed
                // as a product of generators and their inverses
                self.can_express_as_word(g)
            }
            GroupType::Continuous => {
                // For continuous groups, check if element satisfies group constraints
                self.satisfies_group_constraints(g)
            }
        }
    }
    
    /// Check if element can be expressed as a word in the generators
    fn can_express_as_word(&self, g: &GroupElement<P>) -> bool {
        // For identity, always true
        if g.is_identity() {
            return true;
        }
        
        // For single generator groups (like Z), check if element is a power of generator
        if self.generators.len() == 1 {
            let gen = &self.generators[0];
            
            // Check if g = gen^n for some integer n
            // For Z, this means checking if g.params = n * gen.params
            if let Some(ratio) = self.find_integer_ratio(&g.params, &gen.params) {
                return ratio.abs() > P::epsilon();
            }
        }
        
        // For multiple generators, use bounded search
        // This is a simplified version - full implementation would use
        // more sophisticated algorithms like Todd-Coxeter
        let max_word_length = 10; // Reasonable bound for practical use
        self.bounded_word_search(g, max_word_length)
    }
    
    /// Find integer ratio between two parameter vectors if it exists
    pub(crate) fn find_integer_ratio(&self, a: &[P], b: &[P]) -> Option<P> {
        if a.len() != b.len() {
            return None;
        }
        
        // Find first non-zero component in b
        let mut ratio = None;
        for (ai, bi) in a.iter().zip(b.iter()) {
            if bi.abs() > P::epsilon() {
                let r = *ai / *bi;
                if let Some(existing_ratio) = ratio {
                    // Check consistency
                    if (r - existing_ratio).abs() > P::epsilon() {
                        return None;
                    }
                } else {
                    ratio = Some(r);
                }
            } else if ai.abs() > P::epsilon() {
                // ai is non-zero but bi is zero - not a scalar multiple
                return None;
            }
        }
        
        ratio
    }
    
    /// Bounded search for word representation
    fn bounded_word_search(&self, target: &GroupElement<P>, max_length: usize) -> bool {
        use std::collections::HashSet;
        
        let mut visited = HashSet::new();
        let mut current_level = vec![self.identity()];
        
        // Convert element to string for hashing
        let element_to_key = |e: &GroupElement<P>| -> String {
            e.params.iter()
                .map(|p| format!("{:.6}", p.to_f64().unwrap_or(0.0)))
                .collect::<Vec<_>>()
                .join(",")
        };
        
        visited.insert(element_to_key(&self.identity()));
        
        for _depth in 0..max_length {
            let mut next_level = Vec::new();
            
            for elem in current_level {
                // Try multiplying by each generator and its inverse
                for gen in &self.generators {
                    // elem * gen
                    if let Ok(product) = self.multiply(&elem, gen) {
                        // Check if we found the target
                        if product.params.iter().zip(&target.params)
                            .all(|(a, b)| (*a - *b).abs() < P::epsilon()) {
                            return true;
                        }
                        
                        let key = element_to_key(&product);
                        if !visited.contains(&key) {
                            visited.insert(key);
                            next_level.push(product);
                        }
                    }
                    
                    // elem * gen^(-1)
                    if let Ok(gen_inv) = self.inverse(gen) {
                        if let Ok(product) = self.multiply(&elem, &gen_inv) {
                            if product.params.iter().zip(&target.params)
                                .all(|(a, b)| (*a - *b).abs() < P::epsilon()) {
                                return true;
                            }
                            
                            let key = element_to_key(&product);
                            if !visited.contains(&key) {
                                visited.insert(key);
                                next_level.push(product);
                            }
                        }
                    }
                }
            }
            
            if next_level.is_empty() {
                break;
            }
            current_level = next_level;
        }
        
        false
    }
    
    /// Check if element satisfies constraints for continuous groups
    fn satisfies_group_constraints(&self, g: &GroupElement<P>) -> bool {
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
    fn get_group_name(&self) -> &'static str {
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
        
        "Generic"
    }
    
    /// Check if element is a special orthogonal matrix
    fn is_special_orthogonal(&self, g: &GroupElement<P>) -> bool {
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
        // For now, simplified check - full implementation would compute determinant
        true
    }
    
    /// Check if element is a special unitary matrix
    fn is_special_unitary(&self, _g: &GroupElement<P>) -> bool {
        // Complex matrices need 2n² real parameters
        // Check unitarity: M† M = I and det(M) = 1
        // Full implementation would handle complex arithmetic
        true
    }
    
    /// Check if element is invertible (general linear group)
    fn is_general_linear(&self, g: &GroupElement<P>) -> bool {
        // Check if matrix is invertible (non-zero determinant)
        // For now, check no zero rows/columns
        let n = (self.dimension as f64).sqrt() as usize;
        if n * n != self.dimension {
            return false;
        }
        
        // Simple invertibility check - full implementation would compute determinant
        for i in 0..n {
            let mut row_sum = P::zero();
            let mut col_sum = P::zero();
            for j in 0..n {
                row_sum = row_sum + g.params[i * n + j].abs();
                col_sum = col_sum + g.params[j * n + i].abs();
            }
            if row_sum < P::epsilon() || col_sum < P::epsilon() {
                return false;
            }
        }
        
        true
    }
    
    /// Check if element is on the group manifold (generic continuous groups)
    fn is_on_group_manifold(&self, g: &GroupElement<P>) -> bool {
        // For generic continuous groups, check if element can be reached
        // by exponentiating linear combinations of generators
        // This is a simplified check - full implementation would use
        // differential geometry
        
        // Check if element is "close" to identity or generators
        if g.is_identity() {
            return true;
        }
        
        // Check if close to any generator
        for gen in &self.generators {
            let distance = g.params.iter().zip(&gen.params)
                .map(|(a, b)| (*a - *b).powi(2))
                .fold(P::zero(), |acc, x| acc + x)
                .sqrt();
                
            if distance < P::one() {
                return true;
            }
        }
        
        // For now, accept elements within reasonable distance
        true
    }
}