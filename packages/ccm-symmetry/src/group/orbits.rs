//! Orbit computation and analysis
//! 
//! This module provides methods for computing and analyzing orbits under group actions.

use num_traits::Float;
use crate::group::{SymmetryGroup, GroupType};
use crate::actions::GroupAction;
use std::collections::{HashSet, VecDeque};
use std::hash::{Hash, Hasher};

/// Orbit of an element under group action
pub struct Orbit<T> {
    /// Representative element of the orbit
    pub representative: T,
    /// Elements in the orbit (may be partial for infinite groups)
    pub elements: Vec<T>,
    /// Whether the orbit is finite
    pub is_finite: bool,
}

impl<P: Float> SymmetryGroup<P> {
    /// Check if two elements are in the same orbit
    /// 
    /// Two elements a and b are in the same orbit if there exists a group element g
    /// such that g·a = b.
    /// 
    /// # Arguments
    /// 
    /// * `a` - First element
    /// * `b` - Second element  
    /// * `action` - The group action to use
    /// 
    /// # Returns
    /// 
    /// True if a and b are in the same orbit, false otherwise
    pub fn same_orbit<T: Clone + PartialEq + Hash>(
        &self,
        a: &T,
        b: &T,
        action: &dyn GroupAction<P, Target = T>,
    ) -> bool {
        // Quick check: if a == b, they're in the same orbit
        if a == b {
            return true;
        }
        
        match &self.group_type {
            GroupType::Finite { elements } => {
                // For finite groups, check all group elements
                for g in elements {
                    if let Ok(transformed) = action.apply(g, a) {
                        if transformed == *b {
                            return true;
                        }
                    }
                }
                false
            }
            GroupType::DiscreteInfinite => {
                // For discrete infinite groups, use bounded search
                self.same_orbit_discrete_infinite(a, b, action)
            }
            GroupType::Continuous => {
                // For continuous groups, check if b is reachable from a
                self.same_orbit_continuous(a, b, action)
            }
        }
    }
    
    /// Compute the orbit of an element
    /// 
    /// For finite groups, returns the complete orbit.
    /// For infinite groups, returns a partial orbit up to a bound.
    pub fn compute_orbit<T: Clone + PartialEq + Hash>(
        &self,
        x: &T,
        action: &dyn GroupAction<P, Target = T>,
    ) -> Orbit<T> {
        match &self.group_type {
            GroupType::Finite { .. } => self.compute_finite_orbit(x, action),
            GroupType::DiscreteInfinite => self.compute_discrete_infinite_orbit(x, action),
            GroupType::Continuous => self.compute_continuous_orbit(x, action),
        }
    }
    
    /// Compute orbit for finite groups
    fn compute_finite_orbit<T: Clone + PartialEq + Hash>(
        &self,
        x: &T,
        action: &dyn GroupAction<P, Target = T>,
    ) -> Orbit<T> {
        let mut orbit_elements = Vec::new();
        let mut seen = HashSet::new();
        
        // Add the initial element
        orbit_elements.push(x.clone());
        seen.insert(hash_element(x));
        
        if let Some(elements) = self.elements() {
            for g in elements {
                if let Ok(transformed) = action.apply(&g, x) {
                    let hash = hash_element(&transformed);
                    if !seen.contains(&hash) {
                        seen.insert(hash);
                        orbit_elements.push(transformed);
                    }
                }
            }
        }
        
        Orbit {
            representative: x.clone(),
            elements: orbit_elements,
            is_finite: true,
        }
    }
    
    /// Check if two elements are in the same orbit for discrete infinite groups
    fn same_orbit_discrete_infinite<T: Clone + PartialEq + Hash>(
        &self,
        a: &T,
        b: &T,
        action: &dyn GroupAction<P, Target = T>,
    ) -> bool {
        // Use bidirectional search: search from both a and b
        let max_depth = 20; // Reasonable bound for practical computation
        
        let mut forward_frontier = vec![a.clone()];
        let mut backward_frontier = vec![b.clone()];
        let mut forward_seen = HashSet::new();
        let mut backward_seen = HashSet::new();
        
        forward_seen.insert(hash_element(a));
        backward_seen.insert(hash_element(b));
        
        for _depth in 0..max_depth {
            // Check if frontiers overlap
            for elem in &forward_frontier {
                if backward_seen.contains(&hash_element(elem)) {
                    return true;
                }
            }
            
            // Expand smaller frontier for efficiency
            if forward_frontier.len() <= backward_frontier.len() {
                forward_frontier = self.expand_frontier(&forward_frontier, action, &mut forward_seen);
            } else {
                backward_frontier = self.expand_frontier(&backward_frontier, action, &mut backward_seen);
            }
            
            // If either frontier is empty, no path exists
            if forward_frontier.is_empty() || backward_frontier.is_empty() {
                break;
            }
            
            // Early termination for large frontiers
            if forward_frontier.len() + backward_frontier.len() > 10000 {
                break;
            }
        }
        
        false
    }
    
    /// Expand frontier for orbit search
    fn expand_frontier<T: Clone + PartialEq + Hash>(
        &self,
        frontier: &[T],
        action: &dyn GroupAction<P, Target = T>,
        seen: &mut HashSet<u64>,
    ) -> Vec<T> {
        let mut new_frontier = Vec::new();
        
        for elem in frontier {
            // Apply generators
            for gen in &self.generators {
                if let Ok(transformed) = action.apply(gen, elem) {
                    let hash = hash_element(&transformed);
                    if !seen.contains(&hash) {
                        seen.insert(hash);
                        new_frontier.push(transformed);
                    }
                }
                
                // Also try inverse of generator
                if let Ok(gen_inv) = self.inverse(gen) {
                    if let Ok(transformed) = action.apply(&gen_inv, elem) {
                        let hash = hash_element(&transformed);
                        if !seen.contains(&hash) {
                            seen.insert(hash);
                            new_frontier.push(transformed);
                        }
                    }
                }
            }
        }
        
        new_frontier
    }
    
    /// Check if two elements are in the same orbit for continuous groups
    fn same_orbit_continuous<T: Clone + PartialEq>(
        &self,
        a: &T,
        b: &T,
        action: &dyn GroupAction<P, Target = T>,
    ) -> bool {
        // For continuous groups, we need to check if there's a continuous path
        // from a to b through the group action
        
        // Strategy 1: Check if stabilizers are conjugate
        let stab_a = self.stabilizer(a, action);
        let stab_b = self.stabilizer(b, action);
        
        // If stabilizers have different dimensions, not in same orbit
        if stab_a.generators.len() != stab_b.generators.len() {
            return false;
        }
        
        // Strategy 2: Use infinitesimal generators to explore the orbit
        // Check if b is reachable by applying combinations of generators
        self.check_continuous_reachability(a, b, action)
    }
    
    /// Check if b is reachable from a via continuous group action
    fn check_continuous_reachability<T: Clone + PartialEq>(
        &self,
        a: &T,
        b: &T,
        action: &dyn GroupAction<P, Target = T>,
    ) -> bool {
        // Try to reach b from a using combinations of infinitesimal generators
        let epsilon = P::from(0.01).unwrap();
        let max_steps = 100;
        
        // Try each generator direction
        for gen in &self.generators {
            let mut current = a.clone();
            
            // Forward direction
            for _ in 0..max_steps {
                if let Ok(g) = self.exponential_map(&gen.params, epsilon) {
                    if let Ok(next) = action.apply(&g, &current) {
                        if next == *b {
                            return true;
                        }
                        current = next;
                    }
                }
            }
            
            // Backward direction
            current = a.clone();
            for _ in 0..max_steps {
                if let Ok(g) = self.exponential_map(&gen.params, -epsilon) {
                    if let Ok(next) = action.apply(&g, &current) {
                        if next == *b {
                            return true;
                        }
                        current = next;
                    }
                }
            }
        }
        
        false
    }
    
    /// Compute orbit for discrete infinite groups
    fn compute_discrete_infinite_orbit<T: Clone + PartialEq + Hash>(
        &self,
        x: &T,
        action: &dyn GroupAction<P, Target = T>,
    ) -> Orbit<T> {
        let mut orbit_elements = Vec::new();
        let mut seen = HashSet::new();
        let mut queue = VecDeque::new();
        
        // Add initial element
        orbit_elements.push(x.clone());
        seen.insert(hash_element(x));
        queue.push_back(x.clone());
        
        let max_orbit_size = 1000; // Reasonable bound
        
        while let Some(elem) = queue.pop_front() {
            if orbit_elements.len() >= max_orbit_size {
                break;
            }
            
            // Apply generators and their inverses
            for gen in &self.generators {
                // Apply generator
                if let Ok(transformed) = action.apply(gen, &elem) {
                    let hash = hash_element(&transformed);
                    if !seen.contains(&hash) {
                        seen.insert(hash);
                        orbit_elements.push(transformed.clone());
                        queue.push_back(transformed);
                    }
                }
                
                // Apply inverse
                if let Ok(gen_inv) = self.inverse(gen) {
                    if let Ok(transformed) = action.apply(&gen_inv, &elem) {
                        let hash = hash_element(&transformed);
                        if !seen.contains(&hash) {
                            seen.insert(hash);
                            orbit_elements.push(transformed.clone());
                            queue.push_back(transformed);
                        }
                    }
                }
            }
        }
        
        Orbit {
            representative: x.clone(),
            elements: orbit_elements,
            is_finite: queue.is_empty(), // If queue is empty, we found all elements
        }
    }
    
    /// Compute orbit for continuous groups
    fn compute_continuous_orbit<T: Clone + PartialEq + Hash>(
        &self,
        x: &T,
        action: &dyn GroupAction<P, Target = T>,
    ) -> Orbit<T> {
        // For continuous groups, we sample the orbit
        let mut orbit_elements = Vec::new();
        let mut seen = HashSet::new();
        
        // Add initial element
        orbit_elements.push(x.clone());
        seen.insert(hash_element(x));
        
        // Sample along generator directions
        let samples_per_generator = 10;
        for gen in &self.generators {
            let _current = x.clone();
            
            for i in 1..=samples_per_generator {
                let t = P::from(i).unwrap() / P::from(samples_per_generator).unwrap();
                if let Ok(g) = self.exponential_map(&gen.params, t) {
                    if let Ok(transformed) = action.apply(&g, x) {
                        let hash = hash_element(&transformed);
                        if !seen.contains(&hash) {
                            seen.insert(hash);
                            orbit_elements.push(transformed);
                        }
                    }
                }
            }
        }
        
        Orbit {
            representative: x.clone(),
            elements: orbit_elements,
            is_finite: false, // Continuous orbits are typically infinite
        }
    }
    
}

/// Helper function to hash an element
fn hash_element<T: Hash>(elem: &T) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    elem.hash(&mut hasher);
    hasher.finish()
}