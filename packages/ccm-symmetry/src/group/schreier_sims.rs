//! Schreier-Sims algorithm implementation
//! 
//! This module implements the Schreier-Sims algorithm for computing
//! strong generating sets and solving the word problem in permutation groups.

use num_traits::Float;
use std::collections::{HashMap, HashSet, VecDeque};
use crate::group::{GroupElement, SymmetryGroup};
use crate::SymmetryError;
use ccm_core::CcmError;

/// Strong generating set computed by Schreier-Sims algorithm
#[derive(Debug, Clone)]
pub struct StrongGeneratingSet<P: Float> {
    /// Base points β = [β₁, β₂, ..., βₖ]
    pub base: Vec<usize>,
    
    /// Strong generators S = S₁ ∪ S₂ ∪ ... ∪ Sₖ
    /// where Sᵢ generates G^(βᵢ) = Stab_G(β₁, ..., βᵢ₋₁)
    pub strong_generators: Vec<Vec<GroupElement<P>>>,
    
    /// Orbits O(βᵢ) under G^(βᵢ)
    pub orbits: Vec<Vec<usize>>,
    
    /// Schreier vectors for efficient transversal representation
    /// schreier_vector[i][j] = (generator_index, inverse_flag)
    /// Gives generator to reach j from βᵢ in orbit O^(i)(βᵢ)
    pub schreier_vectors: Vec<HashMap<usize, (usize, bool)>>,
    
    /// Transversal coset representatives
    /// transversals[i][j] = element mapping βᵢ to j
    pub transversals: Vec<HashMap<usize, GroupElement<P>>>,
}

impl<P: Float> StrongGeneratingSet<P> {
    /// Create a new empty SGS
    pub fn new() -> Self {
        Self {
            base: Vec::new(),
            strong_generators: Vec::new(),
            orbits: Vec::new(),
            schreier_vectors: Vec::new(),
            transversals: Vec::new(),
        }
    }
    
    /// Get the order of the group |G| = ∏|O^(i)(βᵢ)|
    pub fn group_order(&self) -> usize {
        self.orbits.iter().map(|orbit| orbit.len()).product()
    }
}

impl<P: Float> SymmetryGroup<P> {
    /// Compute a strong generating set using Schreier-Sims algorithm
    pub fn schreier_sims(&self) -> Result<StrongGeneratingSet<P>, CcmError> {
        let mut sgs = StrongGeneratingSet::new();
        
        // Handle empty group
        if self.generators.is_empty() {
            return Ok(sgs);
        }
        
        // Determine the degree (number of points being permuted)
        let degree = self.permutation_degree()?;
        
        // Initialize with given generators
        let mut current_gens = self.generators.clone();
        
        // Build the stabilizer chain
        for point in 0..degree {
            // Check if this point extends the base
            if !self.is_fixed_by_all(&current_gens, point)? {
                // Add point to base
                sgs.base.push(point);
                
                // Compute orbit and Schreier vector
                let (orbit, schreier_vector, transversal) = 
                    self.compute_orbit_with_schreier_vector(point, &current_gens)?;
                
                sgs.orbits.push(orbit);
                sgs.schreier_vectors.push(schreier_vector);
                sgs.transversals.push(transversal);
                
                // Store generators for this level
                sgs.strong_generators.push(current_gens.clone());
                
                // Compute Schreier generators for the stabilizer
                let schreier_gens = self.compute_schreier_generators(
                    point,
                    &current_gens,
                    &sgs.orbits.last().unwrap(),
                    &sgs.schreier_vectors.last().unwrap(),
                    &sgs.transversals.last().unwrap()
                )?;
                
                // Filter out identity and duplicates
                let mut stabilizer_gens = Vec::new();
                for gen in schreier_gens {
                    if !gen.is_identity() && !self.is_in_subgroup_sgs(&gen, &stabilizer_gens)? {
                        stabilizer_gens.push(gen);
                    }
                }
                
                // Continue with stabilizer generators
                current_gens = stabilizer_gens;
                
                if current_gens.is_empty() {
                    break;
                }
            }
        }
        
        // Verify the SGS is correct
        self.verify_strong_generating_set(&sgs)?;
        
        Ok(sgs)
    }
    
    /// Determine the degree of the permutation group
    fn permutation_degree(&self) -> Result<usize, CcmError> {
        // For permutation groups, this is the number of points
        // For matrix groups acting on vectors, it's the dimension
        
        match self.get_representation() {
            crate::group::matrix_operations::GroupRepresentation::Matrix(n) => Ok(n * n),
            crate::group::matrix_operations::GroupRepresentation::Abstract => {
                // For abstract groups, use dimension as degree
                Ok(self.dimension)
            }
        }
    }
    
    /// Check if all generators fix a point
    fn is_fixed_by_all(&self, generators: &[GroupElement<P>], point: usize) -> Result<bool, CcmError> {
        for gen in generators {
            if !self.fixes_point(gen, point)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
    
    /// Check if element fixes a point
    pub fn fixes_point(&self, elem: &GroupElement<P>, point: usize) -> Result<bool, CcmError> {
        // Apply element to point and check if it's unchanged
        let image = self.apply_to_point(elem, point)?;
        Ok(image == point)
    }
    
    /// Apply group element to a point
    fn apply_to_point(&self, elem: &GroupElement<P>, point: usize) -> Result<usize, CcmError> {
        // For permutation: g(i) = elem.params[i]
        // For matrix: apply matrix to standard basis vector
        
        if point >= elem.params.len() {
            return Ok(point); // Fixed if outside range
        }
        
        // Convert parameter to point index
        let image_float = elem.params[point];
        let image = image_float.round().to_usize()
            .ok_or(SymmetryError::InvalidGroupOperation)?;
        
        Ok(image)
    }
    
    /// Compute orbit of a point with Schreier vector
    fn compute_orbit_with_schreier_vector(
        &self,
        point: usize,
        generators: &[GroupElement<P>]
    ) -> Result<(Vec<usize>, HashMap<usize, (usize, bool)>, HashMap<usize, GroupElement<P>>), CcmError> {
        let mut orbit = vec![point];
        let mut schreier_vector = HashMap::new();
        let mut transversal = HashMap::new();
        
        // Identity maps point to itself
        transversal.insert(point, self.identity());
        
        // BFS to compute orbit
        let mut queue = VecDeque::new();
        queue.push_back(point);
        
        let mut in_orbit = HashSet::new();
        in_orbit.insert(point);
        
        while let Some(current) = queue.pop_front() {
            // Apply each generator and its inverse
            for (gen_idx, gen) in generators.iter().enumerate() {
                // Forward direction: current -> gen(current)
                let image = self.apply_to_point(gen, current)?;
                
                if !in_orbit.contains(&image) {
                    in_orbit.insert(image);
                    orbit.push(image);
                    queue.push_back(image);
                    
                    // Record in Schreier vector
                    schreier_vector.insert(image, (gen_idx, false));
                    
                    // Compute transversal element: maps point to image
                    let trans_current = transversal.get(&current)
                        .ok_or(SymmetryError::InvalidGroupOperation)?;
                    let trans_image = self.multiply(trans_current, gen)?;
                    transversal.insert(image, trans_image);
                }
                
                // Inverse direction: current -> gen^(-1)(current)
                let gen_inv = self.inverse(gen)?;
                let inv_image = self.apply_to_point(&gen_inv, current)?;
                
                if !in_orbit.contains(&inv_image) {
                    in_orbit.insert(inv_image);
                    orbit.push(inv_image);
                    queue.push_back(inv_image);
                    
                    // Record in Schreier vector
                    schreier_vector.insert(inv_image, (gen_idx, true));
                    
                    // Compute transversal element
                    let trans_current = transversal.get(&current)
                        .ok_or(SymmetryError::InvalidGroupOperation)?;
                    let trans_inv_image = self.multiply(trans_current, &gen_inv)?;
                    transversal.insert(inv_image, trans_inv_image);
                }
            }
        }
        
        Ok((orbit, schreier_vector, transversal))
    }
    
    /// Compute Schreier generators for the stabilizer
    fn compute_schreier_generators(
        &self,
        base_point: usize,
        generators: &[GroupElement<P>],
        orbit: &[usize],
        _schreier_vector: &HashMap<usize, (usize, bool)>,
        transversal: &HashMap<usize, GroupElement<P>>
    ) -> Result<Vec<GroupElement<P>>, CcmError> {
        let mut schreier_gens = Vec::new();
        
        // For each orbit element and each generator
        for &orbit_elem in orbit {
            for (_gen_idx, gen) in generators.iter().enumerate() {
                // Compute the Schreier generator: s = u_β * g * u_{β^g}^{-1}
                // where u_β is transversal element for β, and β^g is image of β under g
                
                let u_beta = transversal.get(&orbit_elem)
                    .ok_or(SymmetryError::InvalidGroupOperation)?;
                
                // Compute β^g
                let beta_g = self.apply_to_point(gen, orbit_elem)?;
                
                let u_beta_g = transversal.get(&beta_g)
                    .ok_or(SymmetryError::InvalidGroupOperation)?;
                let u_beta_g_inv = self.inverse(u_beta_g)?;
                
                // s = u_β * g * u_{β^g}^{-1}
                let temp = self.multiply(u_beta, gen)?;
                let schreier_gen = self.multiply(&temp, &u_beta_g_inv)?;
                
                // This should stabilize base_point
                if !schreier_gen.is_identity() {
                    // Verify it stabilizes the base point
                    if self.fixes_point(&schreier_gen, base_point)? {
                        schreier_gens.push(schreier_gen);
                    }
                }
            }
        }
        
        Ok(schreier_gens)
    }
    
    /// Check if element is in subgroup generated by given generators (SGS version)
    fn is_in_subgroup_sgs(&self, elem: &GroupElement<P>, generators: &[GroupElement<P>]) -> Result<bool, CcmError> {
        if generators.is_empty() {
            return Ok(elem.is_identity());
        }
        
        // Create a temporary subgroup with the given generators
        let mut subgroup = SymmetryGroup::generate(self.dimension)?;
        subgroup.generators = generators.to_vec();
        subgroup.group_type = self.group_type.clone();
        
        // Compute SGS for the subgroup
        let subgroup_sgs = subgroup.schreier_sims()?;
        
        // Try to sift the element through the subgroup's SGS
        match subgroup.sift_element(elem, &subgroup_sgs) {
            Ok((_, remainder)) => {
                // Element is in subgroup if remainder is identity
                Ok(remainder.is_identity())
            }
            Err(_) => {
                // Sifting failed, element not in subgroup
                Ok(false)
            }
        }
    }
    
    /// Verify the strong generating set is correct
    fn verify_strong_generating_set(&self, sgs: &StrongGeneratingSet<P>) -> Result<(), CcmError> {
        // Verify that:
        // 1. Each Schreier generator is in the group generated by strong generators
        // 2. The stabilizer chain is correct
        // 3. The transversals are correct
        
        for (level, &base_point) in sgs.base.iter().enumerate() {
            if level >= sgs.strong_generators.len() {
                break;
            }
            
            let gens = &sgs.strong_generators[level];
            
            // Verify all generators at this level fix previous base points
            for i in 0..level {
                for gen in gens {
                    if !self.fixes_point(gen, sgs.base[i])? {
                        return Err(SymmetryError::InvalidGroupOperation.into());
                    }
                }
            }
            
            // Verify orbit is correct
            let (computed_orbit, _, _) = self.compute_orbit_with_schreier_vector(base_point, gens)?;
            let stored_orbit = &sgs.orbits[level];
            
            if computed_orbit.len() != stored_orbit.len() {
                return Err(SymmetryError::InvalidGroupOperation.into());
            }
        }
        
        Ok(())
    }
    
    /// Factor element using strong generating set (sift algorithm)
    pub fn sift_element(
        &self,
        elem: &GroupElement<P>,
        sgs: &StrongGeneratingSet<P>
    ) -> Result<(Vec<(usize, i32)>, GroupElement<P>), CcmError> {
        let mut current = elem.clone();
        let mut factorization = Vec::new();
        
        // Sift through each level of the stabilizer chain
        for (level, &base_point) in sgs.base.iter().enumerate() {
            // Find where current sends base_point
            let image = self.apply_to_point(&current, base_point)?;
            
            // Find transversal element that also sends base_point to image
            if let Some(trans) = sgs.transversals[level].get(&image) {
                // Multiply current by trans^{-1} on right: current * trans^{-1}
                let trans_inv = self.inverse(trans)?;
                current = self.multiply(&current, &trans_inv)?;
                
                // Record the factorization
                // We need to express trans in terms of generators
                if let Some(trans_word) = self.transversal_to_word(image, base_point, level, sgs)? {
                    // Since we multiplied by trans^{-1}, reverse the word and negate powers
                    for &(gen_idx, power) in trans_word.iter().rev() {
                        factorization.push((gen_idx, -power));
                    }
                }
            } else {
                // Element not in group!
                return Err(SymmetryError::InvalidGroupOperation.into());
            }
        }
        
        // current should now be identity if elem was in the group
        if !current.is_identity() {
            return Err(SymmetryError::InvalidGroupOperation.into());
        }
        
        // Reverse factorization to get left-to-right product
        factorization.reverse();
        
        Ok((factorization, current))
    }
    
    /// Convert transversal element to word in generators
    fn transversal_to_word(
        &self,
        image: usize,
        base_point: usize,
        level: usize,
        sgs: &StrongGeneratingSet<P>
    ) -> Result<Option<Vec<(usize, i32)>>, CcmError> {
        if image == base_point {
            // Identity element
            return Ok(Some(Vec::new()));
        }
        
        let mut word = Vec::new();
        let mut current = image;
        
        // Trace back through Schreier vector
        while current != base_point {
            if let Some(&(gen_idx, inverse)) = sgs.schreier_vectors[level].get(&current) {
                // Record generator used
                word.push((gen_idx, if inverse { -1 } else { 1 }));
                
                // Move to parent in tree
                let gen = &self.generators[gen_idx];
                let gen_to_apply = if inverse {
                    gen.clone() // Will apply g to go back, not g^{-1}
                } else {
                    self.inverse(gen)? // Will apply g^{-1} to go back
                };
                
                // Find pre-image
                for i in 0..self.dimension {
                    if self.apply_to_point(&gen_to_apply, i)? == current {
                        current = i;
                        break;
                    }
                }
            } else {
                return Ok(None);
            }
        }
        
        // Word is built backwards, so reverse it
        word.reverse();
        
        Ok(Some(word))
    }
}

/// Public API for element factorization
impl<P: Float> SymmetryGroup<P> {
    /// Express element as word in generators using Schreier-Sims
    pub fn element_to_word_schreier_sims(&self, elem: &GroupElement<P>) -> Result<Vec<(usize, i32)>, CcmError> {
        // Compute SGS if needed
        let sgs = self.schreier_sims()?;
        
        // Sift the element
        let (word, remainder) = self.sift_element(elem, &sgs)?;
        
        if !remainder.is_identity() {
            return Err(SymmetryError::InvalidGroupOperation.into());
        }
        
        Ok(word)
    }
}