//! Word search algorithms for group elements
//! 
//! This module provides various algorithms to express group elements
//! as words in the generators, including adaptive search strategies.

use num_traits::Float;
use std::collections::{HashSet, BinaryHeap};
use std::cmp::Ordering;
use crate::group::{GroupElement, SymmetryGroup};

/// Search strategies for adaptive word search
#[derive(Clone, Copy, Debug)]
pub enum SearchStrategy {
    BreadthFirst,
    DepthLimited(usize),
    BiDirectional,
    Heuristic,
}

/// Growth strategies for search depth
#[derive(Clone, Copy, Debug)]
pub enum GrowthStrategy {
    Linear,
    Polynomial,
    Exponential,
}

impl<P: Float> SymmetryGroup<P> {
    /// Check if element can be expressed as a word in the generators
    pub(crate) fn can_express_as_word(&self, g: &GroupElement<P>) -> bool {
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
        
        // For multiple generators, use adaptive word search
        self.adaptive_word_search(g)
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
    pub(crate) fn bounded_word_search(&self, target: &GroupElement<P>, max_length: usize) -> bool {
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
    
    /// Adaptive word search that adjusts strategy based on group structure
    pub(crate) fn adaptive_word_search(&self, target: &GroupElement<P>) -> bool {
        // Start with heuristic analysis to determine initial parameters
        let (initial_depth, _growth_strategy) = self.analyze_search_parameters(target);
        
        // Use multiple search strategies in parallel
        let strategies = vec![
            SearchStrategy::BreadthFirst,
            SearchStrategy::DepthLimited(initial_depth),
            SearchStrategy::BiDirectional,
            SearchStrategy::Heuristic,
        ];
        
        // Try each strategy with adaptive refinement
        for strategy in strategies {
            if self.execute_search_strategy(target, strategy) {
                return true;
            }
        }
        
        // If all strategies fail, try combined approach with larger bounds
        self.combined_adaptive_search(target, initial_depth * 2)
    }
    
    /// Analyze target to determine optimal search parameters
    fn analyze_search_parameters(&self, target: &GroupElement<P>) -> (usize, GrowthStrategy) {
        // Compute norm of target
        let target_norm = target.params.iter()
            .map(|p| p.powi(2))
            .fold(P::zero(), |acc, x| acc + x)
            .sqrt();
        
        // Estimate distance from identity
        let identity = self.identity();
        let _distance_from_identity = target.params.iter()
            .zip(&identity.params)
            .map(|(a, b)| (*a - *b).powi(2))
            .fold(P::zero(), |acc, x| acc + x)
            .sqrt();
        
        // Analyze generator structure
        let max_gen_norm = self.generators.iter()
            .map(|g| g.params.iter().map(|p| p.powi(2)).fold(P::zero(), |acc, x| acc + x).sqrt())
            .fold(P::zero(), |acc, x| if x > acc { x } else { acc });
        
        // Determine initial depth based on analysis
        let initial_depth = if max_gen_norm > P::epsilon() {
            // Estimate based on norm ratios
            let ratio = target_norm / max_gen_norm;
            (ratio.to_f64().unwrap_or(10.0).ceil() as usize).max(3).min(20)
        } else {
            10 // Default depth
        };
        
        // Choose growth strategy based on group structure
        let growth_strategy = match self.generators.len() {
            1 => GrowthStrategy::Linear,           // Single generator: linear growth
            2..=4 => GrowthStrategy::Polynomial,   // Few generators: polynomial growth
            _ => GrowthStrategy::Exponential,      // Many generators: exponential growth
        };
        
        (initial_depth, growth_strategy)
    }
    
    /// Execute a specific search strategy
    fn execute_search_strategy(&self, target: &GroupElement<P>, strategy: SearchStrategy) -> bool {
        match strategy {
            SearchStrategy::BreadthFirst => self.bounded_word_search(target, 15),
            SearchStrategy::DepthLimited(depth) => self.depth_limited_search(target, depth),
            SearchStrategy::BiDirectional => self.bidirectional_search(target),
            SearchStrategy::Heuristic => self.heuristic_guided_search(target),
        }
    }
    
    /// Depth-limited search with iterative deepening
    fn depth_limited_search(&self, target: &GroupElement<P>, max_depth: usize) -> bool {
        // Iterative deepening: try progressively deeper searches
        for depth in 1..=max_depth {
            if self.bounded_word_search(target, depth) {
                return true;
            }
        }
        false
    }
    
    /// Bidirectional search from both identity and target
    fn bidirectional_search(&self, target: &GroupElement<P>) -> bool {
        // Search from both directions
        let mut forward_set = HashSet::new();
        let mut backward_set = HashSet::new();
        
        let element_to_key = |e: &GroupElement<P>| -> String {
            e.params.iter()
                .map(|p| format!("{:.6}", p.to_f64().unwrap_or(0.0)))
                .collect::<Vec<_>>()
                .join(",")
        };
        
        // Initialize sets
        let identity = self.identity();
        forward_set.insert(element_to_key(&identity));
        backward_set.insert(element_to_key(target));
        
        let mut forward_frontier = vec![identity];
        let mut backward_frontier = vec![target.clone()];
        
        // Alternate between forward and backward search
        for _depth in 0..10 {
            // Forward step
            let mut new_forward = Vec::new();
            for elem in forward_frontier {
                for gen in &self.generators {
                    if let Ok(product) = self.multiply(&elem, gen) {
                        let key = element_to_key(&product);
                        if backward_set.contains(&key) {
                            return true; // Found connection
                        }
                        if !forward_set.contains(&key) {
                            forward_set.insert(key);
                            new_forward.push(product);
                        }
                    }
                }
            }
            forward_frontier = new_forward;
            
            // Backward step
            let mut new_backward = Vec::new();
            for elem in backward_frontier {
                for gen in &self.generators {
                    if let Ok(gen_inv) = self.inverse(gen) {
                        if let Ok(product) = self.multiply(&elem, &gen_inv) {
                            let key = element_to_key(&product);
                            if forward_set.contains(&key) {
                                return true; // Found connection
                            }
                            if !backward_set.contains(&key) {
                                backward_set.insert(key);
                                new_backward.push(product);
                            }
                        }
                    }
                }
            }
            backward_frontier = new_backward;
            
            if forward_frontier.is_empty() && backward_frontier.is_empty() {
                break;
            }
        }
        
        false
    }
    
    /// Heuristic-guided search using distance estimates
    fn heuristic_guided_search(&self, target: &GroupElement<P>) -> bool {
        #[derive(Clone)]
        struct SearchNode<P: Float> {
            element: GroupElement<P>,
            depth: usize,
            estimated_distance: P,
        }
        
        impl<P: Float> PartialEq for SearchNode<P> {
            fn eq(&self, other: &Self) -> bool {
                self.estimated_distance == other.estimated_distance
            }
        }
        
        impl<P: Float> Eq for SearchNode<P> {}
        
        impl<P: Float> PartialOrd for SearchNode<P> {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                // Reverse order for min-heap behavior
                other.estimated_distance.partial_cmp(&self.estimated_distance)
            }
        }
        
        impl<P: Float> Ord for SearchNode<P> {
            fn cmp(&self, other: &Self) -> Ordering {
                self.partial_cmp(other).unwrap_or(Ordering::Equal)
            }
        }
        
        // Distance heuristic
        let distance = |elem: &GroupElement<P>| -> P {
            elem.params.iter()
                .zip(&target.params)
                .map(|(a, b)| (*a - *b).powi(2))
                .fold(P::zero(), |acc, x| acc + x)
                .sqrt()
        };
        
        let mut visited = HashSet::new();
        let mut queue = BinaryHeap::new();
        
        let element_to_key = |e: &GroupElement<P>| -> String {
            e.params.iter()
                .map(|p| format!("{:.6}", p.to_f64().unwrap_or(0.0)))
                .collect::<Vec<_>>()
                .join(",")
        };
        
        // Start with identity
        let identity = self.identity();
        queue.push(SearchNode {
            element: identity.clone(),
            depth: 0,
            estimated_distance: distance(&identity),
        });
        visited.insert(element_to_key(&identity));
        
        let max_depth = 20;
        let max_nodes = 10000;
        let mut nodes_explored = 0;
        
        while let Some(node) = queue.pop() {
            nodes_explored += 1;
            
            if nodes_explored > max_nodes || node.depth >= max_depth {
                break;
            }
            
            // Check if we found the target
            if node.estimated_distance < P::epsilon() {
                return true;
            }
            
            // Explore neighbors
            for gen in &self.generators {
                // Try forward direction
                if let Ok(product) = self.multiply(&node.element, gen) {
                    let key = element_to_key(&product);
                    if !visited.contains(&key) {
                        visited.insert(key);
                        let dist = distance(&product);
                        if dist < node.estimated_distance * P::from(2.0).unwrap() {
                            // Only add if we're not moving too far away
                            queue.push(SearchNode {
                                element: product,
                                depth: node.depth + 1,
                                estimated_distance: dist,
                            });
                        }
                    }
                }
                
                // Try inverse direction
                if let Ok(gen_inv) = self.inverse(gen) {
                    if let Ok(product) = self.multiply(&node.element, &gen_inv) {
                        let key = element_to_key(&product);
                        if !visited.contains(&key) {
                            visited.insert(key);
                            let dist = distance(&product);
                            if dist < node.estimated_distance * P::from(2.0).unwrap() {
                                queue.push(SearchNode {
                                    element: product,
                                    depth: node.depth + 1,
                                    estimated_distance: dist,
                                });
                            }
                        }
                    }
                }
            }
        }
        
        false
    }
    
    /// Combined adaptive search using multiple strategies
    fn combined_adaptive_search(&self, target: &GroupElement<P>, max_depth: usize) -> bool {
        // Try a combination of strategies with larger bounds
        // This is a last resort when individual strategies fail
        
        // First, try bounded search with adaptive depth increases
        for factor in &[1, 2, 3, 5] {
            let depth = (max_depth * factor).min(50);
            if self.bounded_word_search(target, depth) {
                return true;
            }
        }
        
        // If still not found, the element is likely not in the group
        false
    }
}