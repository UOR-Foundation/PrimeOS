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
use crate::group::matrix_operations::GroupRepresentation;
use std::collections::VecDeque;
// StrongGeneratingSet is in schreier_sims module

/// Information about components in a direct product group
#[derive(Debug, Clone)]
struct DirectProductInfo {
    /// Number of components
    num_components: usize,
    /// Boundaries between components (indices where each component starts)
    component_boundaries: Vec<usize>,
    /// Whether each component uses additive notation
    component_is_additive: Vec<bool>,
    /// Order of each component (None for infinite)
    component_orders: Vec<Option<usize>>,
}

// Schreier-Sims data structures are now in schreier_sims module


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
    /// Check if two group elements are equal within tolerance
    pub fn elements_equal(&self, a: &GroupElement<P>, b: &GroupElement<P>) -> bool {
        if a.params.len() != b.params.len() {
            return false;
        }
        
        a.params.iter()
            .zip(&b.params)
            .all(|(a_i, b_i)| (*a_i - *b_i).abs() < P::epsilon() * P::from(10.0).unwrap())
    }
    
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
    
    /// Analyze direct product structure
    fn analyze_direct_product(&self) -> Option<DirectProductInfo> {
        if !self.is_direct_product() {
            return None;
        }
        
        // Find component boundaries from generator supports
        let mut component_map = vec![None; self.dimension];
        let mut components: Vec<(Vec<usize>, Vec<usize>)> = Vec::new();
        
        for (gen_idx, gen) in self.generators.iter().enumerate() {
            let support: Vec<usize> = gen.params.iter().enumerate()
                .filter(|(_, &p)| (p - P::one()).abs() > P::epsilon())
                .map(|(i, _)| i)
                .collect();
                
            if !support.is_empty() {
                // Check if this is a new component
                let mut found_component = false;
                let mut existing_comp_idx = 0;
                
                for &idx in &support {
                    if let Some(comp_idx) = component_map[idx] {
                        existing_comp_idx = comp_idx;
                        found_component = true;
                        break;
                    }
                }
                
                if found_component {
                    // Add all indices to existing component
                    for &i in &support {
                        component_map[i] = Some(existing_comp_idx);
                    }
                    if existing_comp_idx < components.len() {
                        components[existing_comp_idx].1.push(gen_idx);
                    }
                } else {
                    // New component
                    let comp_idx = components.len();
                    for &i in &support {
                        component_map[i] = Some(comp_idx);
                    }
                    components.push((support, vec![gen_idx]));
                }
            }
        }
        
        // Sort components by first index
        components.sort_by_key(|(support, _)| support[0]);
        
        // Build component boundaries
        let mut boundaries = vec![0];
        let mut current_pos = 0;
        let mut component_is_additive = Vec::new();
        let mut component_orders = Vec::new();
        
        for (support, gen_indices) in &components {
            current_pos += support.len();
            boundaries.push(current_pos);
            
            // Detect if component uses additive notation
            // Check if identity element of component is zero
            let is_additive = self.detect_additive_notation(&gen_indices);
            component_is_additive.push(is_additive);
            
            // Try to determine component order
            let order = self.detect_component_order(&gen_indices);
            component_orders.push(order);
        }
        
        Some(DirectProductInfo {
            num_components: components.len(),
            component_boundaries: boundaries,
            component_is_additive,
            component_orders,
        })
    }
    
    /// Detect if a component uses additive notation
    fn detect_additive_notation(&self, gen_indices: &[usize]) -> bool {
        // For additive groups, the identity is the zero element
        // For multiplicative groups, the identity has ones
        
        // Check if generators look like they're from an additive group
        // In additive groups, generators typically have mostly zeros with some non-zero entries
        for &idx in gen_indices {
            let gen = &self.generators[idx];
            let non_zero_count = gen.params.iter()
                .filter(|&&p| p.abs() > P::epsilon())
                .count();
                
            // If most entries are zero, likely additive
            if non_zero_count < gen.params.len() / 2 {
                return true;
            }
        }
        
        false
    }
    
    /// Try to detect the order of a component
    fn detect_component_order(&self, gen_indices: &[usize]) -> Option<usize> {
        // For finite cyclic components, compute generator orders
        if gen_indices.len() == 1 {
            let gen = &self.generators[gen_indices[0]];
            return self.element_order(gen);
        }
        
        // For multiple generators, generate the subgroup
        let selected_generators: Vec<GroupElement<P>> = gen_indices.iter()
            .map(|&i| self.generators[i].clone())
            .collect();
        
        // Use the robust subgroup generation method
        let max_elements = 10000; // Safety limit for finite groups
        let subgroup_elements = self.generate_subgroup(&selected_generators, max_elements);
        
        // If we hit the limit, the group is likely infinite
        if subgroup_elements.len() >= max_elements {
            return None;
        }
        
        Some(subgroup_elements.len())
    }
    
    /// Check if group has a presentation
    fn has_presentation(&self) -> bool {
        self.presentation.is_some()
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
        
        // Analyze the direct product structure
        let info = self.analyze_direct_product()
            .ok_or(SymmetryError::InvalidGroupOperation)?;
            
        let mut result_params = vec![P::zero(); self.dimension];
        
        // Process each component separately
        for comp_idx in 0..info.num_components {
            let start = info.component_boundaries[comp_idx];
            let end = info.component_boundaries[comp_idx + 1];
            let is_additive = info.component_is_additive[comp_idx];
            
            // Extract component elements
            let g_component = &g.params[start..end];
            let h_component = &h.params[start..end];
            
            if is_additive {
                // Additive notation: a + b
                for i in 0..g_component.len() {
                    result_params[start + i] = g_component[i] + h_component[i];
                    
                    // Handle modular arithmetic for finite cyclic components
                    if let Some(order) = info.component_orders[comp_idx] {
                        let order_p = P::from(order).unwrap();
                        result_params[start + i] = result_params[start + i] % order_p;
                        if result_params[start + i] < P::zero() {
                            result_params[start + i] = result_params[start + i] + order_p;
                        }
                    }
                }
            } else {
                // Multiplicative notation: a * b
                // Handle different types of multiplicative groups
                
                // Check if this is a matrix component
                let comp_size = end - start;
                let matrix_dim = (comp_size as f64).sqrt() as usize;
                
                if matrix_dim * matrix_dim == comp_size {
                    // This is likely a matrix group component
                    // Perform matrix multiplication
                    for i in 0..matrix_dim {
                        for j in 0..matrix_dim {
                            let mut sum = P::zero();
                            for k in 0..matrix_dim {
                                let g_idx = start + i * matrix_dim + k;
                                let h_idx = start + k * matrix_dim + j;
                                sum = sum + g.params[g_idx] * h.params[h_idx];
                            }
                            result_params[start + i * matrix_dim + j] = sum;
                        }
                    }
                } else {
                    // Not a square matrix, use component-wise multiplication
                    // This handles diagonal groups and other special cases
                    for i in 0..g_component.len() {
                        result_params[start + i] = g_component[i] * h_component[i];
                    }
                }
            }
        }
        
        // Compute cached order if possible
        let cached_order = self.compute_direct_product_order(&result_params, &info);
        
        Ok(GroupElement {
            params: result_params,
            cached_order,
        })
    }
    
    /// Compute order of element in direct product
    fn compute_direct_product_order(&self, params: &[P], info: &DirectProductInfo) -> Option<usize> {
        // Order is LCM of component orders
        let mut orders = Vec::new();
        
        for comp_idx in 0..info.num_components {
            let start = info.component_boundaries[comp_idx];
            let end = info.component_boundaries[comp_idx + 1];
            let component = &params[start..end];
            
            // Check if component is identity
            let is_identity = if info.component_is_additive[comp_idx] {
                component.iter().all(|&x| x.abs() < P::epsilon())
            } else {
                component.iter().all(|&x| (x - P::one()).abs() < P::epsilon())
            };
            
            if is_identity {
                orders.push(1);
            } else if let Some(comp_order) = info.component_orders[comp_idx] {
                // For finite components, compute actual order of the element
                let comp_element = GroupElement {
                    params: component.to_vec(),
                    cached_order: None,
                };
                
                // Compute order by repeated multiplication
                let mut power = comp_element.clone();
                let mut order = 1;
                let max_order = comp_order;
                
                while order <= max_order {
                    let is_comp_identity = if info.component_is_additive[comp_idx] {
                        power.params.iter().all(|&x| x.abs() < P::epsilon())
                    } else {
                        power.params.iter().all(|&x| (x - P::one()).abs() < P::epsilon())
                    };
                    
                    if is_comp_identity {
                        orders.push(order);
                        break;
                    }
                    
                    // Multiply by original element
                    if info.component_is_additive[comp_idx] {
                        for i in 0..power.params.len() {
                            power.params[i] = power.params[i] + component[i];
                            if let Some(ord) = info.component_orders[comp_idx] {
                                let ord_p = P::from(ord).unwrap();
                                power.params[i] = power.params[i] % ord_p;
                                if power.params[i] < P::zero() {
                                    power.params[i] = power.params[i] + ord_p;
                                }
                            }
                        }
                    } else {
                        for i in 0..power.params.len() {
                            power.params[i] = power.params[i] * component[i];
                        }
                    }
                    
                    order += 1;
                }
                
                if order > max_order {
                    return None; // Shouldn't happen for finite component
                }
            } else {
                // Infinite component with non-identity element
                return None;
            }
        }
        
        // Compute LCM of all orders
        Some(orders.into_iter().fold(1, |acc, x| self.lcm(acc, x)))
    }
    
    /// Compute least common multiple
    fn lcm(&self, a: usize, b: usize) -> usize {
        if a == 0 || b == 0 {
            0
        } else {
            (a * b) / self.gcd(a, b)
        }
    }
    
    /// Compute greatest common divisor
    fn gcd(&self, mut a: usize, mut b: usize) -> usize {
        while b != 0 {
            let temp = b;
            b = a % b;
            a = temp;
        }
        a
    }
    
    /// Multiply using group presentation relations
    fn multiply_with_relations(
        &self,
        g: &GroupElement<P>,
        h: &GroupElement<P>,
    ) -> Result<GroupElement<P>, CcmError> {
        // Convert elements to words in generators
        let word_g = self.element_to_word(g)?;
        let word_h = self.element_to_word(h)?;
        
        // Concatenate words
        let mut product_word = word_g;
        product_word.extend(word_h);
        
        // Reduce the word using relations
        let reduced_word = self.reduce_word(product_word)?;
        
        // Convert back to group element
        self.word_to_element(&reduced_word)
    }
    
    /// Convert a group element to a word in generators
    fn element_to_word(&self, elem: &GroupElement<P>) -> Result<Vec<(usize, i32)>, CcmError> {
        // Check if element is a generator
        for (i, gen) in self.generators.iter().enumerate() {
            if self.elements_equal(elem, gen) {
                return Ok(vec![(i, 1)]);
            }
        }
        
        // Check if element is inverse of a generator
        for (i, gen) in self.generators.iter().enumerate() {
            if let Ok(gen_inv) = self.inverse(gen) {
                if self.elements_equal(elem, &gen_inv) {
                    return Ok(vec![(i, -1)]);
                }
            }
        }
        
        // Use Schreier-Sims algorithm for factorization
        match self.element_to_word_schreier_sims(elem) {
            Ok(word) => return Ok(word),
            Err(_) => {
                // If Schreier-Sims fails (e.g., for non-permutation groups),
                // fall back to search with larger depth
                if let Some(factorization) = self.search_factorization(elem, 10) {
                    return Ok(factorization);
                }
            }
        }
        
        Err(SymmetryError::InvalidGroupOperation.into())
    }
    
    /// Search for a factorization of an element as a word in generators
    fn search_factorization(&self, target: &GroupElement<P>, max_length: usize) -> Option<Vec<(usize, i32)>> {
        // Breadth-first search for a word representing the target element
        use std::collections::{VecDeque, HashSet};
        
        let identity = self.identity();
        
        // Queue of (current_element, word_to_reach_it)
        let mut queue = VecDeque::new();
        queue.push_back((identity.clone(), Vec::new()));
        
        // Keep track of visited elements (using structural hash)
        let mut visited = HashSet::new();
        visited.insert(self.structural_hash(&identity));
        
        while let Some((current, word)) = queue.pop_front() {
            // Check if we've reached the target
            if self.elements_equal(&current, target) {
                return Some(word);
            }
            
            // Don't search beyond max length
            if word.len() >= max_length {
                continue;
            }
            
            // Try multiplying by each generator and its inverse
            for (i, gen) in self.generators.iter().enumerate() {
                // Try generator
                if let Ok(next) = self.multiply(&current, gen) {
                    let next_hash = self.structural_hash(&next);
                    if !visited.contains(&next_hash) {
                        visited.insert(next_hash);
                        let mut new_word = word.clone();
                        new_word.push((i, 1));
                        queue.push_back((next, new_word));
                    }
                }
                
                // Try inverse of generator
                if let Ok(gen_inv) = self.inverse(gen) {
                    if let Ok(next) = self.multiply(&current, &gen_inv) {
                        let next_hash = self.structural_hash(&next);
                        if !visited.contains(&next_hash) {
                            visited.insert(next_hash);
                            let mut new_word = word.clone();
                            new_word.push((i, -1));
                            queue.push_back((next, new_word));
                        }
                    }
                }
            }
        }
        
        None
    }
    
    /// Reduce a word using the group's relations
    fn reduce_word(&self, mut word: Vec<(usize, i32)>) -> Result<Vec<(usize, i32)>, CcmError> {
        let presentation = self.presentation.as_ref()
            .ok_or(SymmetryError::InvalidGroupOperation)?;
        
        let mut changed = true;
        while changed {
            changed = false;
            
            // Apply cancellation: g * g^(-1) = e
            let mut i = 0;
            while i + 1 < word.len() {
                if word[i].0 == word[i + 1].0 && word[i].1 == -word[i + 1].1 {
                    word.drain(i..i+2);
                    changed = true;
                    if i > 0 {
                        i -= 1;
                    }
                } else {
                    i += 1;
                }
            }
            
            // Apply relations from presentation
            for relation in &presentation.relations {
                if let Some(pos) = self.find_subword(&word, &relation.word) {
                    // Remove the subword (it equals identity)
                    word.drain(pos..pos + relation.word.len());
                    changed = true;
                }
            }
            
            // Combine adjacent powers of same generator
            let mut i = 0;
            while i + 1 < word.len() {
                if word[i].0 == word[i + 1].0 {
                    let combined_power = word[i].1 + word[i + 1].1;
                    if combined_power == 0 {
                        word.drain(i..i+2);
                        if i > 0 {
                            i -= 1;
                        }
                    } else {
                        word[i].1 = combined_power;
                        word.remove(i + 1);
                    }
                    changed = true;
                } else {
                    i += 1;
                }
            }
        }
        
        Ok(word)
    }
    
    /// Find a subword in a word
    fn find_subword(&self, word: &[(usize, i32)], subword: &[(usize, i32)]) -> Option<usize> {
        if subword.is_empty() {
            return Some(0);
        }
        
        for i in 0..=word.len().saturating_sub(subword.len()) {
            if word[i..i + subword.len()] == *subword {
                return Some(i);
            }
        }
        
        None
    }
    
    /// Convert a word back to a group element
    fn word_to_element(&self, word: &[(usize, i32)]) -> Result<GroupElement<P>, CcmError> {
        if word.is_empty() {
            return Ok(self.identity());
        }
        
        let mut result = self.identity();
        
        for &(gen_idx, power) in word {
            if gen_idx >= self.generators.len() {
                return Err(SymmetryError::InvalidGroupOperation.into());
            }
            
            let gen = &self.generators[gen_idx];
            let gen_power = self.power(gen, power)?;
            result = self.multiply(&result, &gen_power)?;
        }
        
        Ok(result)
    }
    
    /// Compute a structural hash of a group element for comparison
    fn structural_hash(&self, elem: &GroupElement<P>) -> u64 {
        use std::hash::{Hash, Hasher};
        use std::collections::hash_map::DefaultHasher;
        
        let mut hasher = DefaultHasher::new();
        
        // Hash the dimension
        elem.dimension().hash(&mut hasher);
        
        // Hash discretized parameter values
        for &param in &elem.params {
            let discretized = (param * P::from(1e6).unwrap()).round().to_i64().unwrap_or(0);
            discretized.hash(&mut hasher);
        }
        
        hasher.finish()
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
        // Each parameter represents a generator (positive) or its inverse (negative)
        
        // Start with g's parameters
        let mut result = g.params.clone();
        
        // Process h's parameters one by one, reducing as we go
        for &h_param in &h.params {
            if result.is_empty() {
                result.push(h_param);
            } else {
                let last = result.last().unwrap();
                
                // Check if we have an inverse pair
                // Two elements cancel if they sum to zero (g * g^-1 = e)
                if (*last + h_param).abs() < P::epsilon() {
                    // Cancel the pair
                    result.pop();
                } else {
                    // No cancellation, add the element
                    result.push(h_param);
                }
            }
        }
        
        // Determine cached order
        let cached_order = if result.is_empty() {
            Some(1) // Identity has order 1
        } else if result.len() == 1 {
            // Single generator or its inverse
            if result[0].abs() > P::epsilon() {
                None // Infinite order
            } else {
                Some(1) // Zero element is identity
            }
        } else {
            // Check for periodic words (like aba^-1b^-1 which might have finite order)
            self.compute_free_group_element_order(&result)
        };
        
        Ok(GroupElement {
            params: result,
            cached_order,
        })
    }
    
    /// Compute the order of an element in a free group
    fn compute_free_group_element_order(&self, word: &[P]) -> Option<usize> {
        // In a free group, only the identity has finite order
        // Check if this word represents the identity
        if word.is_empty() {
            return Some(1);
        }
        
        // Check if the word is a proper power of a smaller word
        // For example, (ab)^n would be ababab...
        let len = word.len();
        
        // Try all possible period lengths
        for period in 1..=len/2 {
            if len % period == 0 {
                let mut is_periodic = true;
                
                // Check if word = pattern^k for some pattern of length 'period'
                for i in period..len {
                    if (word[i] - word[i % period]).abs() > P::epsilon() {
                        is_periodic = false;
                        break;
                    }
                }
                
                if is_periodic {
                    // The word is w^k for some primitive word w
                    // In a free group, w^k = e only if w = e
                    // Check if the primitive word is trivial
                    let primitive_word = &word[0..period];
                    if self.is_trivial_in_free_group(primitive_word) {
                        return Some(1);
                    }
                }
            }
        }
        
        // No finite order in free groups except for identity
        None
    }
    
    /// Check if a word is trivial in the free group
    fn is_trivial_in_free_group(&self, word: &[P]) -> bool {
        // A word is trivial if it reduces to the empty word
        // This requires full reduction, which we handle in multiply_free
        
        // For a primitive word to be trivial, it must be reducible to empty
        // Since we already have a reduced word, it's trivial only if empty
        word.is_empty()
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
    
    /// Compute element raised to integer power
    pub fn power(&self, element: &GroupElement<P>, n: i32) -> Result<GroupElement<P>, CcmError> {
        if n == 0 {
            return Ok(self.identity());
        }
        
        if n == 1 {
            return Ok(element.clone());
        }
        
        if n == -1 {
            return self.inverse(element);
        }
        
        // Use binary exponentiation
        let mut result = self.identity();
        let mut base = element.clone();
        let mut exp = n.abs() as u32;
        
        while exp > 0 {
            if exp & 1 == 1 {
                result = self.multiply(&result, &base)?;
            }
            base = self.multiply(&base, &base)?;
            exp >>= 1;
        }
        
        // If negative exponent, take inverse
        if n < 0 {
            result = self.inverse(&result)?;
        }
        
        Ok(result)
    }
    
    /// Generate a subgroup from given generators up to a maximum size
    /// Returns the set of all group elements that can be generated
    fn generate_subgroup(&self, generators: &[GroupElement<P>], max_size: usize) -> Vec<GroupElement<P>> {
        let mut elements = Vec::new();
        let mut queue = VecDeque::new();
        
        // Add identity
        let identity = self.identity();
        elements.push(identity.clone());
        queue.push_back(identity);
        
        // Add generators and their inverses
        for gen in generators {
            if !self.element_in_list(&elements, gen) {
                elements.push(gen.clone());
                queue.push_back(gen.clone());
            }
            
            if let Ok(gen_inv) = self.inverse(gen) {
                if !self.element_in_list(&elements, &gen_inv) {
                    elements.push(gen_inv.clone());
                    queue.push_back(gen_inv);
                }
            }
        }
        
        // BFS to generate all elements
        while let Some(elem) = queue.pop_front() {
            if elements.len() >= max_size {
                break;
            }
            
            // Multiply by each generator and its inverse
            for gen in generators {
                // Try g * elem
                if let Ok(product) = self.multiply(gen, &elem) {
                    if !self.element_in_list(&elements, &product) {
                        elements.push(product.clone());
                        queue.push_back(product);
                    }
                }
                
                // Try elem * g
                if let Ok(product) = self.multiply(&elem, gen) {
                    if !self.element_in_list(&elements, &product) {
                        elements.push(product.clone());
                        queue.push_back(product);
                    }
                }
                
                // Try with inverse
                if let Ok(gen_inv) = self.inverse(gen) {
                    // Try g^-1 * elem
                    if let Ok(product) = self.multiply(&gen_inv, &elem) {
                        if !self.element_in_list(&elements, &product) {
                            elements.push(product.clone());
                            queue.push_back(product);
                        }
                    }
                    
                    // Try elem * g^-1
                    if let Ok(product) = self.multiply(&elem, &gen_inv) {
                        if !self.element_in_list(&elements, &product) {
                            elements.push(product.clone());
                            queue.push_back(product);
                        }
                    }
                }
            }
        }
        
        elements
    }
    
    /// Check if an element is in a list of elements
    fn element_in_list(&self, list: &[GroupElement<P>], element: &GroupElement<P>) -> bool {
        list.iter().any(|e| self.elements_equal(e, element))
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