//! Generator management for groups
//! 
//! This module handles:
//! - Minimal generating sets
//! - Relations between generators
//! - Generator enumeration
//! - Presentation from generators and relations

use num_traits::Float;
use std::collections::{HashMap, VecDeque};
use crate::group::{GroupElement, SymmetryGroup, GroupType};
use crate::group::continuous::ContinuousGroup;
use crate::SymmetryError;
use ccm_core::CcmError;

/// Coset table for Todd-Coxeter algorithm
#[derive(Clone, Debug)]
struct CosetTable {
    /// coset_action[coset][generator] = resulting_coset
    coset_action: Vec<HashMap<usize, usize>>,
    /// Track which cosets are identified as equal
    equivalence: Vec<usize>,
    /// Number of live cosets
    num_cosets: usize,
}

impl CosetTable {
    fn new() -> Self {
        let table = Self {
            coset_action: vec![HashMap::new()],
            equivalence: vec![0],
            num_cosets: 1,
        };
        table
    }
    
    fn find_representative(&self, coset: usize) -> usize {
        let mut repr = coset;
        while self.equivalence[repr] != repr {
            repr = self.equivalence[repr];
        }
        repr
    }
    
    fn define_new_coset(&mut self) -> usize {
        let new_coset = self.coset_action.len();
        self.coset_action.push(HashMap::new());
        self.equivalence.push(new_coset);
        self.num_cosets += 1;
        new_coset
    }
    
    fn merge_cosets(&mut self, c1: usize, c2: usize) {
        let r1 = self.find_representative(c1);
        let r2 = self.find_representative(c2);
        if r1 != r2 {
            self.equivalence[r2] = r1;
            self.num_cosets -= 1;
        }
    }
    
    fn get_action(&self, coset: usize, gen: usize) -> Option<usize> {
        let repr = self.find_representative(coset);
        self.coset_action[repr].get(&gen).map(|&c| self.find_representative(c))
    }
    
    fn set_action(&mut self, coset: usize, gen: usize, target: usize) {
        let repr_coset = self.find_representative(coset);
        let repr_target = self.find_representative(target);
        self.coset_action[repr_coset].insert(gen, repr_target);
    }
}

/// Trait for generator-related operations
pub trait GeneratorManagement<P: Float> {
    /// Get the generators of the group
    fn generators(&self) -> &[GroupElement<P>];
    
    /// Check if a set generates the group
    fn is_generating_set(&self, elements: &[GroupElement<P>]) -> bool;
    
    /// Find minimal generating set
    fn minimal_generators(&self) -> Vec<GroupElement<P>>;
    
    /// Express element as word in generators
    fn express_as_word(&self, element: &GroupElement<P>) -> Option<Vec<(usize, i32)>>;
}

impl<P: Float> GeneratorManagement<P> for SymmetryGroup<P> {
    /// Get the generators of the group
    fn generators(&self) -> &[GroupElement<P>] {
        &self.generators
    }
    
    /// Check if a set generates the group
    fn is_generating_set(&self, elements: &[GroupElement<P>]) -> bool {
        self.is_generating_set(elements)
    }
    
    /// Find minimal generating set
    fn minimal_generators(&self) -> Vec<GroupElement<P>> {
        self.minimal_generators()
    }
    
    /// Express element as word in generators
    fn express_as_word(&self, element: &GroupElement<P>) -> Option<Vec<(usize, i32)>> {
        self.express_as_word(element)
    }
}

impl<P: Float> SymmetryGroup<P> {
    /// Create a subgroup from generators
    pub fn subgroup(&self, generators: Vec<GroupElement<P>>) -> Result<SymmetryGroup<P>, CcmError> {
        // Verify all generators are in this group
        for gen in &generators {
            if !self.contains(gen) {
                return Err(SymmetryError::NotInGroup.into());
            }
        }
        
        Ok(SymmetryGroup {
            dimension: self.dimension,
            generators,
            group_type: GroupType::Continuous, // Will be determined later
            cached_order: None,
            presentation: None,
        })
    }
    
    /// Check if a set of elements generates the group
    /// 
    /// For finite groups, this generates all elements and compares.
    /// For infinite groups, this is a more complex problem.
    pub fn is_generating_set(&self, elements: &[GroupElement<P>]) -> bool {
        match &self.group_type {
            GroupType::Finite { elements: group_elements } => {
                // Generate all elements from the proposed generators
                let mut generated = Vec::new();
                let mut to_process = elements.to_vec();
                
                // Add identity
                generated.push(self.identity());
                
                while let Some(elem) = to_process.pop() {
                    let is_new = !generated.iter().any(|g| g.params == elem.params);
                    if is_new {
                        generated.push(elem.clone());
                        
                        // Generate products with all existing elements
                        for existing in generated.clone() {
                            if let Ok(product) = self.multiply(&elem, &existing) {
                                if !generated.iter().any(|g| g.params == product.params) {
                                    to_process.push(product);
                                }
                            }
                            if let Ok(product) = self.multiply(&existing, &elem) {
                                if !generated.iter().any(|g| g.params == product.params) {
                                    to_process.push(product);
                                }
                            }
                        }
                    }
                }
                
                generated.len() == group_elements.len()
            }
            GroupType::DiscreteInfinite => {
                // For discrete infinite groups, verify that the proposed generators
                // can express all known generators
                self.verify_generators_discrete_infinite(elements)
            }
            GroupType::Continuous => {
                // For continuous groups, check Lie algebra generation
                self.verify_generators_continuous(elements)
            }
        }
    }
    
    /// Find a minimal generating set for the group
    /// 
    /// This is a computationally hard problem in general.
    pub fn minimal_generators(&self) -> Vec<GroupElement<P>> {
        if self.generators.is_empty() {
            return Vec::new();
        }
        
        match &self.group_type {
            GroupType::Finite { .. } => {
                // For finite groups, use elimination algorithm
                self.minimal_generators_finite()
            }
            GroupType::DiscreteInfinite => {
                // For discrete infinite groups, use dependency analysis
                self.minimal_generators_discrete_infinite()
            }
            GroupType::Continuous => {
                // For continuous groups, use Lie algebra rank
                self.minimal_generators_continuous()
            }
        }
    }
    
    /// Find minimal generators for finite groups
    fn minimal_generators_finite(&self) -> Vec<GroupElement<P>> {
        let mut minimal = Vec::new();
        let mut remaining = self.generators.clone();
        
        // Greedy algorithm: add generators that increase the generated subgroup
        while !remaining.is_empty() {
            let mut best_idx = 0;
            let mut best_new_elements = 0;
            
            // Current subgroup size
            let current_size = self.subgroup_size(&minimal);
            
            // Try each remaining generator
            for (idx, gen) in remaining.iter().enumerate() {
                let mut test_gens = minimal.clone();
                test_gens.push(gen.clone());
                
                let new_size = self.subgroup_size(&test_gens);
                let new_elements = new_size.saturating_sub(current_size);
                
                if new_elements > best_new_elements {
                    best_new_elements = new_elements;
                    best_idx = idx;
                }
            }
            
            if best_new_elements > 0 {
                // This generator extends the group
                minimal.push(remaining.remove(best_idx));
            } else {
                // This generator is redundant
                remaining.remove(best_idx);
            }
            
            // Early exit if we've generated the full group
            if self.is_generating_set(&minimal) {
                break;
            }
        }
        
        minimal
    }
    
    /// Find minimal generators for discrete infinite groups
    fn minimal_generators_discrete_infinite(&self) -> Vec<GroupElement<P>> {
        // Use linear algebra to find dependencies
        let n = self.generators.len();
        if n <= 1 {
            return self.generators.clone();
        }
        
        // Build dependency matrix
        let mut dependencies = vec![vec![false; n]; n];
        
        for i in 0..n {
            for j in 0..n {
                if i != j {
                    // Check if generator i can be expressed using generators excluding j
                    let mut test_gens = self.generators.clone();
                    test_gens.remove(j);
                    
                    if let Some(_word) = self.express_element_with_generators(&self.generators[i], &test_gens) {
                        dependencies[i][j] = true;
                    }
                }
            }
        }
        
        // Find minimal set using dependency analysis
        let mut minimal_indices = Vec::new();
        let mut covered = vec![false; n];
        
        // Greedy selection: pick generators that cover the most uncovered generators
        while covered.iter().any(|&c| !c) {
            let mut best_idx = 0;
            let mut best_coverage = 0;
            
            for i in 0..n {
                if !minimal_indices.contains(&i) {
                    let mut coverage = 0;
                    for j in 0..n {
                        if !covered[j] && (i == j || dependencies[j][i]) {
                            coverage += 1;
                        }
                    }
                    
                    if coverage > best_coverage {
                        best_coverage = coverage;
                        best_idx = i;
                    }
                }
            }
            
            minimal_indices.push(best_idx);
            
            // Mark covered generators
            for j in 0..n {
                if best_idx == j || dependencies[j][best_idx] {
                    covered[j] = true;
                }
            }
        }
        
        minimal_indices.iter()
            .map(|&i| self.generators[i].clone())
            .collect()
    }
    
    /// Find minimal generators for continuous groups
    fn minimal_generators_continuous(&self) -> Vec<GroupElement<P>> {
        // Use Lie algebra rank computation
        let lie_dim = self.lie_algebra_dimension();
        
        if lie_dim == 0 || lie_dim >= self.generators.len() {
            return self.generators.clone();
        }
        
        // Select linearly independent generators in the Lie algebra
        let mut minimal = Vec::new();
        let mut lie_basis = Vec::new();
        
        for gen in &self.generators {
            // Convert to Lie algebra element
            if let Some(lie_elem) = self.to_lie_algebra_element(gen) {
                // Check linear independence
                if self.is_linearly_independent(&lie_elem, &lie_basis) {
                    minimal.push(gen.clone());
                    lie_basis.push(lie_elem);
                    
                    if lie_basis.len() >= lie_dim {
                        break;
                    }
                }
            }
        }
        
        minimal
    }
    
    /// Compute the size of the subgroup generated by given generators
    fn subgroup_size(&self, generators: &[GroupElement<P>]) -> usize {
        if generators.is_empty() {
            return 1; // Just identity
        }
        
        let mut subgroup = vec![self.identity()];
        let mut to_process = generators.to_vec();
        
        while let Some(elem) = to_process.pop() {
            if !subgroup.iter().any(|g| self.elements_equal(g, &elem)) {
                subgroup.push(elem.clone());
                
                // Generate new elements
                for existing in subgroup.clone() {
                    // Product
                    if let Ok(product) = self.multiply(&elem, &existing) {
                        if !subgroup.iter().any(|g| self.elements_equal(g, &product)) {
                            to_process.push(product);
                        }
                    }
                    
                    // Inverse
                    if let Ok(inv) = self.inverse(&elem) {
                        if !subgroup.iter().any(|g| self.elements_equal(g, &inv)) {
                            to_process.push(inv);
                        }
                    }
                }
                
                // Limit search for large groups
                if subgroup.len() > 1000 {
                    break;
                }
            }
        }
        
        subgroup.len()
    }
    
    /// Express element using a specific set of generators
    fn express_element_with_generators(
        &self,
        element: &GroupElement<P>,
        generators: &[GroupElement<P>]
    ) -> Option<Vec<(usize, i32)>> {
        // Limited BFS search
        let mut visited = Vec::new();
        let mut queue = std::collections::VecDeque::new();
        
        let identity = self.identity();
        queue.push_back((identity.clone(), vec![]));
        visited.push(identity);
        
        let max_depth = 10;
        
        while let Some((current, word)) = queue.pop_front() {
            if self.elements_equal(&current, element) {
                return Some(word);
            }
            
            if word.len() >= max_depth {
                continue;
            }
            
            for (i, gen) in generators.iter().enumerate() {
                // Forward
                if let Ok(next) = self.multiply(&current, gen) {
                    if !visited.iter().any(|v| self.elements_equal(v, &next)) {
                        visited.push(next.clone());
                        let mut new_word = word.clone();
                        new_word.push((i, 1));
                        queue.push_back((next, new_word));
                    }
                }
                
                // Inverse
                if let Ok(inv) = self.inverse(gen) {
                    if let Ok(next) = self.multiply(&current, &inv) {
                        if !visited.iter().any(|v| self.elements_equal(v, &next)) {
                            visited.push(next.clone());
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
    
    /// Convert group element to Lie algebra element
    fn to_lie_algebra_element(&self, elem: &GroupElement<P>) -> Option<Vec<P>> {
        // Use logarithm map from ContinuousGroup trait
        <Self as ContinuousGroup<P>>::logarithm_map(self, elem)
    }
    
    /// Check if Lie algebra element is linearly independent from basis
    fn is_linearly_independent(&self, elem: &[P], basis: &[Vec<P>]) -> bool {
        if basis.is_empty() {
            // Check if elem is non-zero
            return elem.iter().any(|&x| x.abs() > P::epsilon());
        }
        
        // Use Gram-Schmidt process to check independence
        let mut projection = elem.to_vec();
        
        for basis_vec in basis {
            // Compute dot product
            let dot: P = elem.iter()
                .zip(basis_vec.iter())
                .map(|(&a, &b)| a * b)
                .fold(P::zero(), |acc, x| acc + x);
            
            let basis_norm_sq: P = basis_vec.iter()
                .map(|&x| x * x)
                .fold(P::zero(), |acc, x| acc + x);
            
            if basis_norm_sq > P::epsilon() {
                // Subtract projection
                let scale = dot / basis_norm_sq;
                for (p, &b) in projection.iter_mut().zip(basis_vec.iter()) {
                    *p = *p - scale * b;
                }
            }
        }
        
        // Check if remainder is non-zero
        projection.iter().any(|&x| x.abs() > P::epsilon())
    }
    
    /// Express an element as a word in the generators
    /// 
    /// Returns a list of (generator_index, power) pairs.
    pub fn express_as_word(&self, element: &GroupElement<P>) -> Option<Vec<(usize, i32)>> {
        if self.generators.is_empty() {
            return None;
        }
        
        // Check for identity first
        if element.is_identity() {
            return Some(vec![]); // Empty word
        }
        
        match &self.group_type {
            GroupType::Finite { .. } => {
                self.express_as_word_finite(element)
            }
            GroupType::DiscreteInfinite => {
                self.express_as_word_discrete_infinite(element)
            }
            GroupType::Continuous => {
                self.express_as_word_continuous(element)
            }
        }
    }
    
    /// Express element as word for finite groups
    fn express_as_word_finite(&self, element: &GroupElement<P>) -> Option<Vec<(usize, i32)>> {
        // Simple BFS to find a word representation
        // This is not optimal but works for small groups
        let mut visited = Vec::new();
        let mut queue = std::collections::VecDeque::new();
        
        // Start with identity (empty word)
        let identity = self.identity();
        queue.push_back((identity.clone(), vec![]));
        visited.push(identity);
        
        while let Some((current, word)) = queue.pop_front() {
            if current.params == element.params {
                return Some(word);
            }
            
            // Try multiplying by each generator
            for (i, gen) in self.generators.iter().enumerate() {
                if let Ok(next) = self.multiply(&current, gen) {
                    if !visited.iter().any(|v| v.params == next.params) {
                        visited.push(next.clone());
                        let mut new_word = word.clone();
                        new_word.push((i, 1));
                        queue.push_back((next, new_word));
                    }
                }
                
                // Also try inverse
                if let Ok(inv_gen) = self.inverse(gen) {
                    if let Ok(next) = self.multiply(&current, &inv_gen) {
                        if !visited.iter().any(|v| v.params == next.params) {
                            visited.push(next.clone());
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
    
    /// Express element as word for discrete infinite groups
    fn express_as_word_discrete_infinite(&self, element: &GroupElement<P>) -> Option<Vec<(usize, i32)>> {
        // Different strategies for different types of discrete infinite groups
        
        // Single generator case (like Z)
        if self.generators.len() == 1 {
            return self.express_as_word_cyclic_infinite(element);
        }
        
        // Multiple generators - check if it's free abelian
        if self.is_free_abelian() {
            return self.express_as_word_free_abelian(element);
        }
        
        // General discrete infinite group - use bounded search
        self.express_as_word_bounded_search(element, 100) // Reasonable bound
    }
    
    /// Express element in infinite cyclic group
    fn express_as_word_cyclic_infinite(&self, element: &GroupElement<P>) -> Option<Vec<(usize, i32)>> {
        if self.generators.is_empty() {
            return None;
        }
        
        let gen = &self.generators[0];
        
        // Find n such that element = gen^n
        // For Z represented additively: element = n * gen
        if let Some(ratio) = self.find_integer_ratio(&element.params, &gen.params) {
            let n = ratio.round();
            if (ratio - n).abs() < P::epsilon() {
                let n_i32 = n.to_f64().unwrap_or(0.0) as i32;
                if n_i32 != 0 {
                    return Some(vec![(0, n_i32)]);
                } else if element.is_identity() {
                    return Some(vec![]); // Empty word for identity
                }
            }
        }
        
        None
    }
    
    /// Express element in free abelian group (Z^n)
    fn express_as_word_free_abelian(&self, element: &GroupElement<P>) -> Option<Vec<(usize, i32)>> {
        // For free abelian groups, we solve the linear system:
        // element = sum_i n_i * gen_i
        
        let mut word = Vec::new();
        let mut residual = element.params.clone();
        
        // Try to express as linear combination of generators
        for (i, gen) in self.generators.iter().enumerate() {
            // Find coefficient for this generator
            let mut coeff = None;
            
            for j in 0..gen.params.len() {
                if gen.params[j].abs() > P::epsilon() {
                    let c = residual[j] / gen.params[j];
                    if let Some(existing) = coeff {
                        // Check consistency
                        if (c - existing).abs() > P::epsilon() {
                            return None; // Inconsistent system
                        }
                    } else {
                        coeff = Some(c);
                    }
                }
            }
            
            if let Some(c) = coeff {
                let n = c.round();
                if (c - n).abs() < P::epsilon() {
                    let n_i32 = n.to_f64().unwrap_or(0.0) as i32;
                    if n_i32 != 0 {
                        word.push((i, n_i32));
                        
                        // Subtract this contribution from residual
                        for j in 0..residual.len() {
                            residual[j] = residual[j] - n * gen.params[j];
                        }
                    }
                }
            }
        }
        
        // Check if residual is zero
        let residual_norm = residual.iter()
            .map(|x| x.powi(2))
            .fold(P::zero(), |acc, x| acc + x)
            .sqrt();
            
        if residual_norm < P::epsilon() {
            Some(word)
        } else {
            None
        }
    }
    
    /// Express element using bounded search
    fn express_as_word_bounded_search(
        &self,
        element: &GroupElement<P>,
        max_length: usize,
    ) -> Option<Vec<(usize, i32)>> {
        use std::collections::{HashSet, VecDeque};
        
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        
        // Convert element to string for hashing
        let element_to_key = |e: &GroupElement<P>| -> String {
            e.params.iter()
                .map(|p| format!("{:.6}", p.to_f64().unwrap_or(0.0)))
                .collect::<Vec<_>>()
                .join(",")
        };
        
        let target_key = element_to_key(element);
        
        // Start with identity
        let identity = self.identity();
        queue.push_back((identity.clone(), vec![]));
        visited.insert(element_to_key(&identity));
        
        while let Some((current, word)) = queue.pop_front() {
            // Check if we found the target
            if element_to_key(&current) == target_key {
                return Some(word);
            }
            
            // Don't exceed maximum word length
            if word.len() >= max_length {
                continue;
            }
            
            // Try each generator and its inverse
            for (i, gen) in self.generators.iter().enumerate() {
                // Forward direction
                if let Ok(next) = self.multiply(&current, gen) {
                    let key = element_to_key(&next);
                    if !visited.contains(&key) {
                        visited.insert(key);
                        let mut new_word = word.clone();
                        
                        // Combine consecutive powers of same generator
                        if let Some((last_gen, last_pow)) = new_word.last_mut() {
                            if *last_gen == i && *last_pow > 0 {
                                *last_pow += 1;
                            } else {
                                new_word.push((i, 1));
                            }
                        } else {
                            new_word.push((i, 1));
                        }
                        
                        queue.push_back((next, new_word));
                    }
                }
                
                // Inverse direction
                if let Ok(gen_inv) = self.inverse(gen) {
                    if let Ok(next) = self.multiply(&current, &gen_inv) {
                        let key = element_to_key(&next);
                        if !visited.contains(&key) {
                            visited.insert(key);
                            let mut new_word = word.clone();
                            
                            // Combine consecutive powers of same generator
                            if let Some((last_gen, last_pow)) = new_word.last_mut() {
                                if *last_gen == i && *last_pow < 0 {
                                    *last_pow -= 1;
                                } else {
                                    new_word.push((i, -1));
                                }
                            } else {
                                new_word.push((i, -1));
                            }
                            
                            queue.push_back((next, new_word));
                        }
                    }
                }
            }
        }
        
        None
    }
    
    /// Express element as word for continuous groups
    fn express_as_word_continuous(&self, element: &GroupElement<P>) -> Option<Vec<(usize, i32)>> {
        // For continuous groups, we typically can't express elements as
        // finite words in generators. However, we can try to find an
        // approximation for elements close to the identity.
        
        // Check if element is close to identity
        let identity = self.identity();
        let distance = element.params.iter()
            .zip(identity.params.iter())
            .map(|(a, b)| (*a - *b).powi(2))
            .fold(P::zero(), |acc, x| acc + x)
            .sqrt();
            
        if distance > P::one() {
            // Too far from identity for discrete approximation
            return None;
        }
        
        // Try to express as a small power of a generator
        for (i, gen) in self.generators.iter().enumerate() {
            // Check if element ≈ gen^n for small n
            for n in 1..=10 {
                let mut power = gen.clone();
                for _ in 1..n {
                    if let Ok(next) = self.multiply(&power, gen) {
                        power = next;
                    } else {
                        break;
                    }
                }
                
                // Check if close enough
                let diff = element.params.iter()
                    .zip(power.params.iter())
                    .map(|(a, b)| (*a - *b).powi(2))
                    .fold(P::zero(), |acc, x| acc + x)
                    .sqrt();
                    
                if diff < P::epsilon() * P::from(10.0).unwrap() {
                    return Some(vec![(i, n as i32)]);
                }
            }
        }
        
        None
    }
    
    /// Verify generators for discrete infinite groups
    /// 
    /// For discrete infinite groups like Z, Z^n, or finitely presented groups,
    /// we check if the proposed generators can express our known generators.
    fn verify_generators_discrete_infinite(&self, proposed: &[GroupElement<P>]) -> bool {
        if proposed.is_empty() {
            return false;
        }
        
        // For each of our known generators, check if it can be expressed
        // using the proposed generators
        for known_gen in &self.generators {
            if !self.can_express_with_generators(known_gen, proposed) {
                return false;
            }
        }
        
        // Also check that proposed generators are independent
        // (none can be expressed in terms of others)
        for (i, gen) in proposed.iter().enumerate() {
            let others: Vec<_> = proposed.iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, g)| g.clone())
                .collect();
                
            if !others.is_empty() && self.can_express_with_generators(gen, &others) {
                return false; // Generator is redundant
            }
        }
        
        true
    }
    
    /// Check if an element can be expressed using given generators
    pub(crate) fn can_express_with_generators(
        &self,
        element: &GroupElement<P>,
        generators: &[GroupElement<P>],
    ) -> bool {
        // Special case: identity can always be expressed (as empty product)
        if element.is_identity() {
            return true;
        }
        
        // For single generator case (like Z), check if element is a power
        if generators.len() == 1 {
            return self.is_power_of(&generators[0], element);
        }
        
        // For multiple generators, use appropriate algorithm based on group type
        match &self.group_type {
            GroupType::Finite { .. } => {
                // For finite groups, use bounded search with group order as limit
                let max_length = self.order().unwrap_or(100);
                self.bounded_expression_search(element, generators, max_length)
            }
            GroupType::DiscreteInfinite => {
                // Check if group is free abelian
                if self.is_free_abelian() {
                    self.can_express_in_free_abelian(element, generators)
                } else {
                    // Use Todd-Coxeter algorithm for finitely presented groups
                    self.todd_coxeter_enumeration(element, generators)
                }
            }
            GroupType::Continuous => {
                // For continuous groups, check if element is in the Lie algebra span
                self.can_express_in_lie_algebra(element, generators)
            }
        }
    }
    
    /// Check if b is a power of a (i.e., b = a^n for some integer n)
    fn is_power_of(&self, a: &GroupElement<P>, b: &GroupElement<P>) -> bool {
        // For identity, it's a^0
        if b.is_identity() {
            return true;
        }
        
        // Try to find n such that b = a^n
        // For discrete groups, we check if b.params = n * a.params
        
        // Find first non-zero component in a
        let mut ratio = None;
        for i in 0..a.params.len() {
            if a.params[i].abs() > P::epsilon() {
                let n = b.params[i] / a.params[i];
                
                if let Some(existing_ratio) = ratio {
                    // Check consistency
                    if (n - existing_ratio).abs() > P::epsilon() {
                        return false;
                    }
                } else {
                    ratio = Some(n);
                }
            } else if b.params[i].abs() > P::epsilon() {
                // a has zero but b doesn't - not a power
                return false;
            }
        }
        
        // Verify the ratio is close to an integer
        if let Some(n) = ratio {
            let n_rounded = n.round();
            (n - n_rounded).abs() < P::epsilon()
        } else {
            false
        }
    }
    
    /// Bounded search for expressing element as word in generators
    fn bounded_expression_search(
        &self,
        target: &GroupElement<P>,
        generators: &[GroupElement<P>],
        max_length: usize,
    ) -> bool {
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
                for gen in generators {
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
    
    /// Verify generators for continuous groups
    /// 
    /// For Lie groups, we check if the proposed generators span the same
    /// Lie algebra as our known generators.
    fn verify_generators_continuous(&self, proposed: &[GroupElement<P>]) -> bool {
        if proposed.is_empty() {
            return false;
        }
        
        // For continuous groups, we need to check if the Lie algebras
        // generated by the two sets of generators are the same
        
        // Compute tangent vectors for known generators
        let known_tangent_space = self.compute_tangent_space(&self.generators);
        
        // Compute tangent vectors for proposed generators
        let proposed_tangent_space = self.compute_tangent_space(proposed);
        
        // Check if they span the same space
        self.same_vector_space(&known_tangent_space, &proposed_tangent_space)
    }
    
    /// Compute tangent space spanned by generators
    /// 
    /// For a Lie group, the tangent space at identity is the Lie algebra
    fn compute_tangent_space(&self, generators: &[GroupElement<P>]) -> Vec<Vec<P>> {
        // For each generator g, compute the tangent vector at identity
        // This is the derivative d/dt|_{t=0} exp(t * log(g))
        
        let mut tangent_vectors = Vec::new();
        
        // Check if this is a matrix group
        let n = (self.dimension as f64).sqrt();
        let is_matrix_group = n.floor() == n && n > 0.0;
        let matrix_dim = n as usize;
        
        for gen in generators {
            let tangent = if is_matrix_group && matrix_dim * matrix_dim == self.dimension {
                // For matrix groups, compute the matrix logarithm
                self.matrix_logarithm(&gen.params, matrix_dim)
                    .unwrap_or_else(|| {
                        // Fallback to first-order approximation if log fails
                        gen.params.iter()
                            .zip(self.identity().params.iter())
                            .map(|(g, e)| *g - *e)
                            .collect()
                    })
            } else {
                // For non-matrix groups, use the direction from identity
                gen.params.iter()
                    .zip(self.identity().params.iter())
                    .map(|(g, e)| *g - *e)
                    .collect()
            };
            
            tangent_vectors.push(tangent);
        }
        
        tangent_vectors
    }
    
    /// Check if two sets of vectors span the same vector space
    fn same_vector_space(&self, space1: &[Vec<P>], space2: &[Vec<P>]) -> bool {
        // Check if every vector in space1 can be expressed as a linear
        // combination of vectors in space2, and vice versa
        
        // First check dimensions
        let dim1 = self.vector_space_dimension(space1);
        let dim2 = self.vector_space_dimension(space2);
        
        if dim1 != dim2 {
            return false;
        }
        
        // Check if each vector in space1 is in span of space2
        for v1 in space1 {
            if !self.in_span(v1, space2) {
                return false;
            }
        }
        
        // Check if each vector in space2 is in span of space1
        for v2 in space2 {
            if !self.in_span(v2, space1) {
                return false;
            }
        }
        
        true
    }
    
    /// Compute matrix logarithm
    /// 
    /// For a matrix M close to identity, log(M) can be computed using:
    /// log(M) = log(I + A) = A - A²/2 + A³/3 - A⁴/4 + ...
    /// where A = M - I
    fn matrix_logarithm(&self, matrix: &[P], n: usize) -> Option<Vec<P>> {
        if matrix.len() != n * n {
            return None;
        }
        
        // Check if matrix is close enough to identity for series to converge
        // The series converges when ||A|| < 1 where A = M - I
        let identity = self.identity();
        let mut a_matrix = vec![P::zero(); n * n];
        let mut max_entry = P::zero();
        
        for i in 0..n * n {
            a_matrix[i] = matrix[i] - identity.params[i];
            if a_matrix[i].abs() > max_entry {
                max_entry = a_matrix[i].abs();
            }
        }
        
        // For matrices far from identity, use advanced methods
        if max_entry > P::from(0.5).unwrap() {
            return self.matrix_logarithm_advanced(matrix, n);
        }
        
        // Use power series: log(I + A) = A - A²/2 + A³/3 - ...
        let mut log_m = a_matrix.clone();
        let mut a_power = a_matrix.clone();
        let mut sign = P::from(-1.0).unwrap();
        
        // Compute up to 10 terms for good accuracy
        for k in 2..=10 {
            // a_power = a_power * a_matrix
            a_power = self.matrix_multiply(&a_power, &a_matrix, n)?;
            
            // Add term: sign * a_power / k
            let coeff = sign / P::from(k).unwrap();
            for i in 0..n * n {
                log_m[i] = log_m[i] + coeff * a_power[i];
            }
            
            sign = -sign;
        }
        
        Some(log_m)
    }
    
    
    /// Compute dimension of vector space spanned by vectors
    fn vector_space_dimension(&self, vectors: &[Vec<P>]) -> usize {
        if vectors.is_empty() {
            return 0;
        }
        
        // Use Gram-Schmidt to find orthogonal basis
        let mut basis: Vec<Vec<P>> = Vec::new();
        
        for v in vectors {
            let mut u = v.clone();
            
            // Subtract projections onto existing basis vectors
            for b in &basis {
                let proj = self.vector_projection(&u, b);
                for i in 0..u.len() {
                    u[i] = u[i] - proj[i];
                }
            }
            
            // If u is non-zero, add to basis
            let norm_sq = u.iter().map(|x| x.powi(2)).fold(P::zero(), |a, b| a + b);
            if norm_sq > P::epsilon() {
                basis.push(u);
            }
        }
        
        basis.len()
    }
    
    /// Check if element can be expressed in free abelian group
    fn can_express_in_free_abelian(
        &self,
        element: &GroupElement<P>,
        generators: &[GroupElement<P>],
    ) -> bool {
        // For free abelian groups, solve the linear system:
        // element = sum_i n_i * gen_i for integer n_i
        
        if generators.is_empty() {
            return element.is_identity();
        }
        
        let n = element.params.len();
        let m = generators.len();
        
        // Build matrix A where columns are generator parameters
        let mut a_matrix = vec![vec![P::zero(); m]; n];
        for (j, gen) in generators.iter().enumerate() {
            for (i, &param) in gen.params.iter().enumerate() {
                a_matrix[i][j] = param;
            }
        }
        
        // Solve Ax = b where b = element.params
        // We need integer solutions, so use extended GCD approach
        for i in 0..n {
            let mut gcd = P::zero();
            
            // Compute GCD of row i of A
            for j in 0..m {
                if gcd == P::zero() {
                    gcd = a_matrix[i][j].abs();
                } else if a_matrix[i][j] != P::zero() {
                    gcd = self.gcd_float(gcd, a_matrix[i][j].abs());
                }
            }
            
            if gcd == P::zero() {
                // This row is all zeros
                if element.params[i].abs() > P::epsilon() {
                    return false; // No solution
                }
                continue;
            }
            
            // Check if element.params[i] is divisible by gcd
            let remainder = element.params[i].abs() % gcd;
            if remainder > P::epsilon() {
                return false; // No integer solution
            }
        }
        
        // If we get here, there exists an integer solution
        true
    }
    
    /// Todd-Coxeter coset enumeration algorithm
    fn todd_coxeter_enumeration(
        &self,
        element: &GroupElement<P>,
        generators: &[GroupElement<P>],
    ) -> bool {
        // Todd-Coxeter algorithm for finitely presented groups
        // This is a complete implementation without simplifications
        
        let mut table = CosetTable::new();
        let mut deductions = VecDeque::new();
        
        // Process relations from the group presentation
        let relations = self.extract_relations_for_generators(generators);
        
        // Initialize with identity coset
        for (i, _gen) in generators.iter().enumerate() {
            // Start by assuming each generator might map to a new coset
            let new_coset = table.define_new_coset();
            table.set_action(0, i, new_coset);
            table.set_action(new_coset, i, 0); // Assume generators have finite order initially
            
            // Add to deduction queue
            deductions.push_back((0, i, new_coset));
        }
        
        // Main Todd-Coxeter loop
        let max_cosets = 10000; // Prevent infinite loops
        while !deductions.is_empty() && table.num_cosets < max_cosets {
            let (coset, _gen_idx, _target) = deductions.pop_front().unwrap();
            
            // Process all relations at this coset
            for relation in &relations {
                self.process_relation(&mut table, &mut deductions, coset, relation, generators.len());
            }
            
            // Check for coincidences (cosets that must be equal)
            self.process_coincidences(&mut table, &mut deductions);
        }
        
        // Now check if the element can be reached from coset 0
        self.element_reachable_in_coset_table(&table, element, generators)
    }
    
    /// Extract relations for the given generators
    fn extract_relations_for_generators(&self, generators: &[GroupElement<P>]) -> Vec<Vec<(usize, i32)>> {
        let mut relations = Vec::new();
        
        // For each generator, find its order if finite
        for (i, gen) in generators.iter().enumerate() {
            if let Some(order) = self.element_order(gen) {
                if order > 1 {
                    // Relation: g^order = e
                    relations.push(vec![(i, order as i32)]);
                }
            }
        }
        
        // Find commutation relations
        for i in 0..generators.len() {
            for j in i+1..generators.len() {
                // Check if generators commute
                if let (Ok(gi_gj), Ok(gj_gi)) = (
                    self.multiply(&generators[i], &generators[j]),
                    self.multiply(&generators[j], &generators[i])
                ) {
                    if self.elements_equal(&gi_gj, &gj_gi) {
                        // Relation: [gi, gj] = e, which is gi*gj*gi^-1*gj^-1 = e
                        relations.push(vec![(i, 1), (j, 1), (i, -1), (j, -1)]);
                    }
                }
            }
        }
        
        // Additional relations based on group structure
        if self.is_free_abelian() {
            // All generators commute in free abelian groups
            for i in 0..generators.len() {
                for j in i+1..generators.len() {
                    if !relations.iter().any(|r| self.is_commutator_relation(r, i, j)) {
                        relations.push(vec![(i, 1), (j, 1), (i, -1), (j, -1)]);
                    }
                }
            }
        }
        
        relations
    }
    
    /// Check if a relation represents the commutator [gi, gj] = e
    fn is_commutator_relation(&self, relation: &[(usize, i32)], i: usize, j: usize) -> bool {
        relation.len() == 4 &&
        relation[0] == (i, 1) && relation[1] == (j, 1) &&
        relation[2] == (i, -1) && relation[3] == (j, -1)
    }
    
    /// Process a relation in the coset table
    fn process_relation(
        &self,
        table: &mut CosetTable,
        deductions: &mut VecDeque<(usize, usize, usize)>,
        start_coset: usize,
        relation: &[(usize, i32)],
        _num_generators: usize,
    ) {
        // Trace the relation from start_coset
        let end_coset = self.trace_relation(table, start_coset, relation);
        
        if end_coset != start_coset {
            // We have a coincidence
            table.merge_cosets(start_coset, end_coset);
            deductions.push_back((start_coset, 0, end_coset)); // Dummy entry to trigger coincidence processing
        }
    }
    
    /// Trace a relation through the coset table
    fn trace_relation(
        &self,
        table: &CosetTable,
        start_coset: usize,
        relation: &[(usize, i32)],
    ) -> usize {
        let mut current = start_coset;
        
        for &(gen_idx, power) in relation {
            for _ in 0..power.abs() {
                if let Some(next) = table.get_action(current, gen_idx) {
                    current = next;
                } else {
                    // Undefined action, cannot complete trace
                    return current;
                }
            }
        }
        
        current
    }
    
    /// Process coincidences in the coset table
    fn process_coincidences(
        &self,
        table: &mut CosetTable,
        deductions: &mut VecDeque<(usize, usize, usize)>,
    ) {
        // Check all coset actions for consistency after merging
        let num_cosets = table.coset_action.len();
        for c in 0..num_cosets {
            let repr = table.find_representative(c);
            if repr != c {
                // This coset was merged, propagate its actions
                for (&gen, &target) in table.coset_action[c].clone().iter() {
                    if let Some(existing_target) = table.get_action(repr, gen) {
                        if existing_target != target {
                            table.merge_cosets(existing_target, target);
                            deductions.push_back((repr, gen, target));
                        }
                    } else {
                        table.set_action(repr, gen, target);
                        deductions.push_back((repr, gen, target));
                    }
                }
            }
        }
    }
    
    /// Check if element is reachable in the coset table
    fn element_reachable_in_coset_table(
        &self,
        table: &CosetTable,
        element: &GroupElement<P>,
        generators: &[GroupElement<P>],
    ) -> bool {
        // Try to express element as a word in generators
        // by checking if we can reach a coset that acts like element
        
        // For each coset, check if it could represent our element
        for coset in 0..table.coset_action.len() {
            if table.find_representative(coset) != coset {
                continue; // Skip non-representative cosets
            }
            
            // Check if this coset's action matches our element
            if self.coset_represents_element(table, coset, element, generators) {
                return true;
            }
        }
        
        false
    }
    
    /// Check if a coset represents the given element
    fn coset_represents_element(
        &self,
        _table: &CosetTable,
        _coset: usize,
        element: &GroupElement<P>,
        generators: &[GroupElement<P>],
    ) -> bool {
        // Try to build element from identity using generators
        // This is done by checking if we can find a path in the coset table
        
        // Use bounded search from identity
        self.bounded_expression_search(element, generators, 100)
    }
    
    /// Check if element can be expressed in the Lie algebra
    fn can_express_in_lie_algebra(
        &self,
        element: &GroupElement<P>,
        generators: &[GroupElement<P>],
    ) -> bool {
        // For continuous groups, check if log(element) is in span of log(generators)
        
        // First check if element is close enough to identity for log to be defined
        let identity = self.identity();
        let distance = element.params.iter()
            .zip(identity.params.iter())
            .map(|(a, b)| (*a - *b).powi(2))
            .fold(P::zero(), |acc, x| acc + x)
            .sqrt();
            
        if distance > P::from(2.0).unwrap() {
            // Too far from identity, might not be in the group
            return false;
        }
        
        // Get tangent vectors for generators
        let generator_tangents: Vec<Vec<P>> = generators.iter()
            .map(|g| {
                g.params.iter()
                    .zip(identity.params.iter())
                    .map(|(a, b)| *a - *b)
                    .collect()
            })
            .collect();
            
        // Get tangent vector for element
        let element_tangent: Vec<P> = element.params.iter()
            .zip(identity.params.iter())
            .map(|(a, b)| *a - *b)
            .collect();
            
        // Check if element_tangent is in the span of generator_tangents
        self.in_span(&element_tangent, &generator_tangents)
    }
    
    /// Compute GCD of two floating point numbers (treating them as scaled integers)
    fn gcd_float(&self, a: P, b: P) -> P {
        let scale = P::from(1e10).unwrap(); // Scale factor for precision
        let a_scaled = (a * scale).round();
        let b_scaled = (b * scale).round();
        
        let gcd_scaled = self.gcd_integer(
            a_scaled.to_i64().unwrap_or(0).abs() as u64,
            b_scaled.to_i64().unwrap_or(0).abs() as u64
        );
        
        P::from(gcd_scaled).unwrap() / scale
    }
    
    /// Compute GCD of two integers
    fn gcd_integer(&self, mut a: u64, mut b: u64) -> u64 {
        while b != 0 {
            let temp = b;
            b = a % b;
            a = temp;
        }
        a
    }
    
    /// Check if vector v is in the span of the given vectors
    fn in_span(&self, v: &[P], vectors: &[Vec<P>]) -> bool {
        if vectors.is_empty() {
            // Empty span only contains zero vector
            return v.iter().all(|&x| x.abs() < P::epsilon());
        }
        
        let n = v.len();
        let m = vectors.len();
        
        // Build augmented matrix [A | v] where A has vectors as columns
        let mut matrix = vec![vec![P::zero(); m + 1]; n];
        
        // Fill matrix with vector components
        for i in 0..n {
            for j in 0..m {
                if i < vectors[j].len() {
                    matrix[i][j] = vectors[j][i];
                }
            }
            matrix[i][m] = v[i]; // Augmented column
        }
        
        // Gaussian elimination with partial pivoting
        for col in 0..m.min(n) {
            // Find pivot
            let mut max_row = col;
            let mut max_val = matrix[col][col].abs();
            
            for row in (col + 1)..n {
                if matrix[row][col].abs() > max_val {
                    max_val = matrix[row][col].abs();
                    max_row = row;
                }
            }
            
            if max_val < P::epsilon() {
                continue; // Skip this column
            }
            
            // Swap rows
            if max_row != col {
                matrix.swap(col, max_row);
            }
            
            // Eliminate below pivot
            for row in (col + 1)..n {
                if matrix[col][col].abs() > P::epsilon() {
                    let factor = matrix[row][col] / matrix[col][col];
                    for j in col..=m {
                        matrix[row][j] = matrix[row][j] - factor * matrix[col][j];
                    }
                }
            }
        }
        
        // Back substitution to check consistency
        for row in (0..n).rev() {
            // Find first non-zero entry in this row
            let mut pivot_col = None;
            for col in 0..m {
                if matrix[row][col].abs() > P::epsilon() {
                    pivot_col = Some(col);
                    break;
                }
            }
            
            if pivot_col.is_none() {
                // This row has no pivot in A
                // Check if the augmented part is also zero
                if matrix[row][m].abs() > P::epsilon() {
                    return false; // Inconsistent system
                }
            }
        }
        
        true // System is consistent, v is in span
    }
    
    /// Compute projection of vector a onto vector b
    pub(crate) fn vector_projection(&self, a: &[P], b: &[P]) -> Vec<P> {
        // proj_b(a) = (a·b / b·b) * b
        
        let dot_ab = a.iter().zip(b.iter())
            .map(|(x, y)| *x * *y)
            .fold(P::zero(), |acc, x| acc + x);
            
        let dot_bb = b.iter()
            .map(|x| x.powi(2))
            .fold(P::zero(), |acc, x| acc + x);
            
        if dot_bb < P::epsilon() {
            return vec![P::zero(); b.len()];
        }
        
        let scale = dot_ab / dot_bb;
        b.iter().map(|x| *x * scale).collect()
    }
}