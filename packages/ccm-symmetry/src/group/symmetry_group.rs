//! Main SymmetryGroup struct implementation
//! 
//! This module contains the primary SymmetryGroup struct that
//! unifies all group types under a common interface.

use num_traits::Float;
use crate::group::{GroupElement, GroupType, GroupPresentation, GroupRelation};
use ccm_core::CcmError;
use crate::SymmetryError;

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
    /// Group presentation (generators and relations)
    pub(crate) presentation: Option<GroupPresentation<P>>,
}

impl<P: Float> SymmetryGroup<P> {
    /// Generate symmetry group for n dimensions
    pub fn generate(n: usize) -> Result<Self, CcmError> {
        if n == 0 {
            return Err(SymmetryError::InvalidGroupOperation.into());
        }

        // Start with empty generators - will be populated based on specific group
        Ok(Self {
            dimension: n,
            generators: Vec::new(),
            group_type: GroupType::Continuous, // Default to continuous
            cached_order: None,
            presentation: None,
        })
    }
    
    /// Create the symmetric group S_n
    pub fn symmetric_group(n: usize) -> Result<Self, CcmError> {
        if n == 0 {
            return Err(SymmetryError::InvalidGroupOperation.into());
        }
        
        // For S_n acting on n objects, we use n×n permutation matrices
        let dimension = n * n;
        let mut group = Self {
            dimension,
            generators: Vec::new(),
            group_type: GroupType::Finite { elements: Vec::new() },
            cached_order: Some(factorial(n)),
            presentation: None,
        };
        
        // Add transposition generators (i, i+1) for i = 0..n-1
        for i in 0..n-1 {
            let mut perm_matrix = vec![P::zero(); dimension];
            // Create permutation matrix for transposition (i, i+1)
            // Row j tells us where position j maps to
            for j in 0..n {
                if j == i {
                    // Position i maps to position i+1
                    perm_matrix[i * n + (i + 1)] = P::one();
                } else if j == i + 1 {
                    // Position i+1 maps to position i
                    perm_matrix[(i + 1) * n + i] = P::one();
                } else {
                    // All other positions map to themselves
                    perm_matrix[j * n + j] = P::one();
                }
            }
            group.generators.push(GroupElement::from_params(perm_matrix));
        }
        
        // Generate all elements for small groups
        if n <= 5 {
            group.generate_finite_elements()?;
        }
        
        Ok(group)
    }
    
    /// Generate all elements for finite groups
    fn generate_finite_elements(&mut self) -> Result<(), CcmError> {
        // Extract elements temporarily to avoid borrow issues
        let mut temp_elements = if let GroupType::Finite { elements } = &mut self.group_type {
            core::mem::take(elements)
        } else {
            return Ok(());
        };
        
        temp_elements.clear();
        temp_elements.push(GroupElement::identity(self.dimension));
        
        // Use generators to build all elements
        let mut new_elements = Vec::new();
        let mut changed = true;
        let mut iteration = 0;
        
        while changed && temp_elements.len() < 1000 { // Safety limit
            changed = false;
            iteration += 1;
            let current_elements = temp_elements.clone();
            
            // Try multiplying each existing element by each generator
            for g in &current_elements {
                for gen in &self.generators {
                    // Multiply from left: gen * g
                    let product_left = self.multiply_elements(gen, g)?;
                    if !temp_elements.iter().any(|e| element_equal(e, &product_left)) &&
                       !new_elements.iter().any(|e| element_equal(e, &product_left)) {
                        new_elements.push(product_left);
                        changed = true;
                    }
                    
                    // Multiply from right: g * gen
                    let product_right = self.multiply_elements(g, gen)?;
                    if !temp_elements.iter().any(|e| element_equal(e, &product_right)) &&
                       !new_elements.iter().any(|e| element_equal(e, &product_right)) {
                        new_elements.push(product_right);
                        changed = true;
                    }
                }
            }
            temp_elements.extend(new_elements.drain(..));
        }
        
        // Put elements back
        if let GroupType::Finite { elements } = &mut self.group_type {
            *elements = temp_elements;
        }
        
        Ok(())
    }
    
    /// Multiply two elements without borrowing self
    fn multiply_elements(&self, a: &GroupElement<P>, b: &GroupElement<P>) -> Result<GroupElement<P>, CcmError> {
        if a.dimension() != self.dimension || b.dimension() != self.dimension {
            return Err(SymmetryError::InvalidGroupOperation.into());
        }
        
        // For permutation matrices, multiply
        let n = (self.dimension as f64).sqrt() as usize;
        if n * n == self.dimension {
            let mut result = vec![P::zero(); self.dimension];
            
            for i in 0..n {
                for j in 0..n {
                    let mut sum = P::zero();
                    for k in 0..n {
                        sum = sum + a.params[i * n + k] * b.params[k * n + j];
                    }
                    result[i * n + j] = sum;
                }
            }
            
            Ok(GroupElement::from_params(result))
        } else {
            // Generic multiplication - component-wise for now
            let params = a.params.iter()
                .zip(&b.params)
                .map(|(x, y)| *x * *y)
                .collect();
            Ok(GroupElement::from_params(params))
        }
    }

    /// Get the identity element
    pub fn identity(&self) -> GroupElement<P> {
        GroupElement::identity(self.dimension)
    }
    
    /// Get all elements (for finite groups)
    pub fn all_elements(&self) -> Vec<GroupElement<P>> {
        match &self.group_type {
            GroupType::Finite { elements } => elements.clone(),
            _ => vec![self.identity()], // For infinite groups, return just identity
        }
    }

    /// Get group element from parameters
    pub fn element(&self, params: &[P]) -> Result<GroupElement<P>, CcmError> {
        if params.len() != self.dimension {
            return Err(SymmetryError::InvalidGroupOperation.into());
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
    
    /// Set the group presentation
    pub fn set_presentation(&mut self, presentation: GroupPresentation<P>) {
        self.presentation = Some(presentation);
    }
    
    /// Get the group presentation if available
    pub fn presentation(&self) -> Option<&GroupPresentation<P>> {
        self.presentation.as_ref()
    }
    
    /// Build a presentation from the current generators and known relations
    pub fn build_presentation(&mut self) -> Result<(), CcmError> {
        use crate::group::GroupRelation;
        
        // Generate default generator names
        let generator_names: Vec<String> = (0..self.generators.len())
            .map(|i| format!("g{}", i))
            .collect();
        
        // Find relations based on group type
        let mut relations = Vec::new();
        
        match &self.group_type {
            GroupType::Finite { .. } => {
                // For finite groups, find relations by computing generator orders
                for (i, gen) in self.generators.iter().enumerate() {
                    if let Some(order) = self.element_order(gen) {
                        if order > 1 {
                            // Add relation g^order = 1
                            relations.push(GroupRelation {
                                word: vec![(i, order as i32)],
                                name: Some(format!("g{}^{} = 1", i, order)),
                            });
                        }
                    }
                }
                
                // Find commutator relations
                for i in 0..self.generators.len() {
                    for j in i+1..self.generators.len() {
                        let gi = &self.generators[i];
                        let gj = &self.generators[j];
                        
                        // Compute [gi, gj] = gi * gj * gi^-1 * gj^-1
                        if let (Ok(gi_gj), Ok(gj_gi)) = (self.multiply(gi, gj), self.multiply(gj, gi)) {
                            if self.elements_equal(&gi_gj, &gj_gi) {
                                // Generators commute
                                relations.push(GroupRelation {
                                    word: vec![(i, 1), (j, 1), (i, -1), (j, -1)],
                                    name: Some(format!("[g{}, g{}] = 1", i, j)),
                                });
                            }
                        }
                    }
                }
            }
            GroupType::DiscreteInfinite => {
                // For discrete infinite groups, we can only find some relations
                // Check if generators have finite order
                for (i, gen) in self.generators.iter().enumerate() {
                    // Try small orders up to a reasonable limit
                    for order in 2..=12 {
                        if let Ok(power) = self.power(gen, order) {
                            if power.is_identity() {
                                relations.push(GroupRelation {
                                    word: vec![(i, order)],
                                    name: Some(format!("g{}^{} = 1", i, order)),
                                });
                                break;
                            }
                        }
                    }
                }
            }
            GroupType::Continuous => {
                // For continuous groups, relations come from Lie algebra structure
                relations.extend(self.compute_lie_algebra_relations());
            }
        }
        
        self.presentation = Some(GroupPresentation {
            generator_names,
            generators: self.generators.clone(),
            relations,
        });
        
        Ok(())
    }
    
    /// Compute relations for continuous groups based on Lie algebra structure
    fn compute_lie_algebra_relations(&self) -> Vec<GroupRelation> {
        let mut relations = Vec::new();
        
        // For matrix Lie groups, we can compute commutation relations
        let n = (self.dimension as f64).sqrt() as usize;
        if n * n == self.dimension {
            // This is likely a matrix group
            
            // Compute commutators of generators
            for i in 0..self.generators.len() {
                for j in i+1..self.generators.len() {
                    if let Ok(commutator) = self.commutator(&self.generators[i], &self.generators[j]) {
                        // Check if commutator is zero (generators commute)
                        if commutator.is_identity() {
                            // [g_i, g_j] = 1, which means g_i g_j = g_j g_i
                            relations.push(GroupRelation {
                                word: vec![(i, 1), (j, 1), (i, -1), (j, -1)],
                                name: Some(format!("[g{}, g{}] = 1", i, j)),
                            });
                        } else {
                            // Try to express commutator in terms of generators
                            if let Some(commutator_word) = self.express_as_linear_combination(&commutator) {
                                // [g_i, g_j] = linear combination of generators
                                let mut relation_word = vec![(i, 1), (j, 1), (i, -1), (j, -1)];
                                
                                // Add the negative of the linear combination
                                for (gen_idx, coeff) in commutator_word {
                                    relation_word.push((gen_idx, -coeff));
                                }
                                
                                relations.push(GroupRelation {
                                    word: relation_word,
                                    name: Some(format!("[g{}, g{}] relation", i, j)),
                                });
                            }
                        }
                    }
                }
            }
            
            // For specific groups, add known relations
            relations.extend(self.add_specific_group_relations(n));
        }
        
        // Add relations from Jacobi identity if we have enough generators
        if self.generators.len() >= 3 {
            relations.extend(self.compute_jacobi_relations());
        }
        
        relations
    }
    
    /// Express element as linear combination of Lie algebra generators
    fn express_as_linear_combination(&self, element: &GroupElement<P>) -> Option<Vec<(usize, i32)>> {
        // For elements close to identity, we can use logarithm
        if let Some(lie_element) = self.to_lie_algebra_element_local(element) {
            // Try to express as integer linear combination of generator logarithms
            return self.solve_integer_linear_system(&lie_element);
        }
        
        None
    }
    
    /// Convert group element to Lie algebra element (local version)
    fn to_lie_algebra_element_local(&self, element: &GroupElement<P>) -> Option<Vec<P>> {
        use crate::group::continuous::ContinuousGroup;
        <Self as ContinuousGroup<P>>::logarithm_map(self, element)
    }
    
    /// Solve for integer coefficients in linear combination
    fn solve_integer_linear_system(&self, target: &[P]) -> Option<Vec<(usize, i32)>> {
        let n = self.generators.len();
        if n == 0 || target.len() == 0 {
            return None;
        }
        
        // Get Lie algebra representations of generators
        let mut gen_logs = Vec::new();
        for gen in &self.generators {
            if let Some(log_gen) = self.to_lie_algebra_element_local(gen) {
                gen_logs.push(log_gen);
            } else {
                return None; // Can't compute logarithm
            }
        }
        
        // Build the coefficient matrix A where A*x = target
        // Each column is a generator's Lie algebra representation
        let m = target.len(); // Number of equations
        let mut a_matrix = vec![vec![P::zero(); n]; m];
        
        for j in 0..n {
            for i in 0..m.min(gen_logs[j].len()) {
                a_matrix[i][j] = gen_logs[j][i];
            }
        }
        
        // Convert to rational/integer form for exact computation
        let scale_factor = P::from(10000.0).unwrap();
        let mut int_matrix = vec![vec![0i64; n]; m];
        let mut int_target = vec![0i64; m];
        
        for i in 0..m {
            for j in 0..n {
                int_matrix[i][j] = (a_matrix[i][j] * scale_factor).round().to_i64().unwrap_or(0);
            }
            int_target[i] = (target[i] * scale_factor).round().to_i64().unwrap_or(0);
        }
        
        // Try different approaches based on system size
        if n <= 3 {
            // For small systems, use brute force search
            for coeffs in Self::generate_small_integer_combinations(n, 10) {
                if self.check_linear_combination(&coeffs, target) {
                    let mut result = Vec::new();
                    for (i, &c) in coeffs.iter().enumerate() {
                        if c != 0 {
                            result.push((i, c));
                        }
                    }
                    return Some(result);
                }
            }
        }
        
        // For larger systems, use lattice reduction
        if let Some(solution) = self.solve_integer_system_lattice(&int_matrix, &int_target) {
            // Convert solution to (index, coefficient) pairs
            let mut result = Vec::new();
            for (i, &coeff) in solution.iter().enumerate() {
                if coeff != 0 {
                    result.push((i, coeff));
                }
            }
            return Some(result);
        }
        
        // If exact methods fail, try approximate methods
        self.solve_integer_system_approximate(&a_matrix, target)
    }
    
    /// Generate small integer combinations for brute force search
    fn generate_small_integer_combinations(n: usize, max_abs: i32) -> Vec<Vec<i32>> {
        let mut combinations = Vec::new();
        
        if n == 1 {
            for c in -max_abs..=max_abs {
                if c != 0 {
                    combinations.push(vec![c]);
                }
            }
        } else if n == 2 {
            for c1 in -max_abs..=max_abs {
                for c2 in -max_abs..=max_abs {
                    if c1 != 0 || c2 != 0 {
                        combinations.push(vec![c1, c2]);
                    }
                }
            }
        } else if n == 3 {
            for c1 in -max_abs..=max_abs {
                for c2 in -max_abs..=max_abs {
                    for c3 in -max_abs..=max_abs {
                        if c1 != 0 || c2 != 0 || c3 != 0 {
                            combinations.push(vec![c1, c2, c3]);
                        }
                    }
                }
            }
        }
        
        combinations
    }
    
    /// Check if linear combination of generator logarithms equals target
    fn check_linear_combination(&self, coeffs: &[i32], target: &[P]) -> bool {
        // Compute linear combination of generator logarithms
        let mut result = vec![P::zero(); target.len()];
        
        for (i, &coeff) in coeffs.iter().enumerate() {
            if coeff != 0 {
                if let Some(gen_log) = self.to_lie_algebra_element_local(&self.generators[i]) {
                    for (j, &val) in gen_log.iter().enumerate() {
                        if j < result.len() {
                            result[j] = result[j] + P::from(coeff).unwrap() * val;
                        }
                    }
                }
            }
        }
        
        // Check if close to target
        result.iter().zip(target.iter())
            .all(|(a, b)| (*a - *b).abs() < P::epsilon() * P::from(10.0).unwrap())
    }
    
    /// Add relations specific to known Lie groups
    fn add_specific_group_relations(&self, n: usize) -> Vec<GroupRelation> {
        let relations = Vec::new();
        
        // Detect specific groups and add their relations
        match n {
            2 => {
                // SO(2) is abelian - all generators commute
                // This is usually already captured by commutator relations
            }
            3 => {
                // Could be SO(3) or SU(2)
                // SO(3) has specific relations from the Lie algebra so(3)
                if self.is_special_orthogonal_group_continuous() {
                    // so(3) basis elements satisfy [e_i, e_j] = ε_{ijk} e_k
                    // These are usually captured by commutator relations
                }
            }
            _ => {
                // For larger groups, relations are more complex
            }
        }
        
        relations
    }
    
    /// Compute relations from Jacobi identity
    fn compute_jacobi_relations(&self) -> Vec<GroupRelation> {
        let mut relations = Vec::new();
        
        // Jacobi identity: [[X,Y],Z] + [[Y,Z],X] + [[Z,X],Y] = 0
        // In group terms: conjugation relations
        
        // For three generators, we have the Hall-Witt identity
        if self.generators.len() >= 3 {
            // Take first three generators
            for i in 0..self.generators.len().min(3) {
                for j in i+1..self.generators.len().min(3) {
                    for k in j+1..self.generators.len().min(3) {
                        // Compute [[g_i, g_j], g_k] and cyclic permutations
                        if let Ok(hall_witt) = self.compute_hall_witt_identity(i, j, k) {
                            if !hall_witt.is_empty() {
                                relations.push(GroupRelation {
                                    word: hall_witt,
                                    name: Some(format!("Hall-Witt({}, {}, {})", i, j, k)),
                                });
                            }
                        }
                    }
                }
            }
        }
        
        relations
    }
    
    /// Compute Hall-Witt identity for three generators
    fn compute_hall_witt_identity(&self, i: usize, j: usize, k: usize) -> Result<Vec<(usize, i32)>, CcmError> {
        // Hall-Witt: [x,[y,z]][y,[z,x]][z,[x,y]] = 1
        // This is a group-theoretic version of the Jacobi identity
        
        let x = &self.generators[i];
        let y = &self.generators[j];
        let z = &self.generators[k];
        
        // Compute [y,z]
        let yz_comm = self.commutator(y, z)?;
        // Compute [x,[y,z]]
        let x_yz = self.commutator(x, &yz_comm)?;
        
        // Compute [z,x]
        let zx_comm = self.commutator(z, x)?;
        // Compute [y,[z,x]]
        let y_zx = self.commutator(y, &zx_comm)?;
        
        // Compute [x,y]
        let xy_comm = self.commutator(x, y)?;
        // Compute [z,[x,y]]
        let z_xy = self.commutator(z, &xy_comm)?;
        
        // Compute the product
        let temp = self.multiply(&x_yz, &y_zx)?;
        let hall_witt_element = self.multiply(&temp, &z_xy)?;
        
        // Check if it's identity (as it should be for Lie groups)
        if hall_witt_element.is_identity() {
            // Return empty word - the identity is already satisfied
            Ok(Vec::new())
        } else {
            // Try to express as word in generators
            match self.element_to_word_schreier_sims(&hall_witt_element) {
                Ok(word) => Ok(word),
                Err(_) => {
                    // If we can't express it directly, try to find an approximate representation
                    // First check if it's close to identity (numerical error)
                    if self.is_approximately_identity(&hall_witt_element) {
                        return Ok(Vec::new());
                    }
                    
                    // Try to express as a linear combination in the Lie algebra
                    if let Some(lie_elem) = self.to_lie_algebra_element_local(&hall_witt_element) {
                        if let Some(coeffs) = self.solve_integer_linear_system(&lie_elem) {
                            // Build word from coefficients
                            let mut word = Vec::new();
                            for (gen_idx, power) in coeffs {
                                word.push((gen_idx, power));
                            }
                            return Ok(word);
                        }
                    }
                    
                    // If all else fails, return an error rather than a placeholder
                    Err(SymmetryError::InvalidGroupOperation.into())
                }
            }
        }
    }
    
    /// Check if this is a special orthogonal group (continuous version)
    fn is_special_orthogonal_group_continuous(&self) -> bool {
        // Check if generators are skew-symmetric matrices
        let n = (self.dimension as f64).sqrt() as usize;
        if n * n != self.dimension {
            return false;
        }
        
        for gen in &self.generators {
            if !self.is_skew_symmetric(&gen.params, n) {
                return false;
            }
        }
        
        true
    }
    
    /// Check if matrix is skew-symmetric
    fn is_skew_symmetric(&self, matrix: &[P], n: usize) -> bool {
        for i in 0..n {
            for j in 0..n {
                let a_ij = matrix[i * n + j];
                let a_ji = matrix[j * n + i];
                
                if (a_ij + a_ji).abs() > P::epsilon() * P::from(10.0).unwrap() {
                    return false;
                }
            }
        }
        true
    }
    
    /// Compute commutator [a,b] = a*b*a^(-1)*b^(-1)
    pub fn commutator(&self, a: &GroupElement<P>, b: &GroupElement<P>) -> Result<GroupElement<P>, CcmError> {
        // Compute a * b
        let ab = self.multiply(a, b)?;
        
        // Compute a^(-1)
        let a_inv = self.inverse(a)?;
        
        // Compute b^(-1)
        let b_inv = self.inverse(b)?;
        
        // Compute a * b * a^(-1)
        let aba_inv = self.multiply(&ab, &a_inv)?;
        
        // Compute [a,b] = a * b * a^(-1) * b^(-1)
        self.multiply(&aba_inv, &b_inv)
    }
    
    /// Solve integer linear system using lattice reduction
    fn solve_integer_system_lattice(&self, matrix: &[Vec<i64>], target: &[i64]) -> Option<Vec<i32>> {
        let m = matrix.len();
        let n = if m > 0 { matrix[0].len() } else { 0 };
        
        if m == 0 || n == 0 {
            return None;
        }
        
        // For overdetermined systems, find least squares solution
        if m > n {
            return self.solve_overdetermined_integer_system(matrix, target);
        }
        
        // For square or underdetermined systems, use Hermite Normal Form
        // Build augmented matrix [A | b]
        let mut augmented = vec![vec![0i64; n + 1]; m];
        for i in 0..m {
            for j in 0..n {
                augmented[i][j] = matrix[i][j];
            }
            augmented[i][n] = target[i];
        }
        
        // Compute Hermite Normal Form
        if let Some((h, _u)) = self.hermite_normal_form(&augmented) {
            // Check if system is consistent
            // The last column of H should match the transformed target
            let mut solution = vec![0i32; n];
            
            // Back-substitution to find integer solution
            for i in (0..m.min(n)).rev() {
                let mut sum = h[i][n];
                for j in i+1..n {
                    sum -= h[i][j] * solution[j] as i64;
                }
                
                if h[i][i] != 0 {
                    if sum % h[i][i] == 0 {
                        solution[i] = (sum / h[i][i]) as i32;
                    } else {
                        return None; // No integer solution
                    }
                } else if sum != 0 {
                    return None; // Inconsistent system
                }
            }
            
            // Verify solution
            let mut verification = vec![0i64; m];
            for i in 0..m {
                for j in 0..n {
                    verification[i] += matrix[i][j] * solution[j] as i64;
                }
                if (verification[i] - target[i]).abs() > 0 {
                    return None;
                }
            }
            
            Some(solution)
        } else {
            None
        }
    }
    
    /// Solve overdetermined integer system using least squares
    fn solve_overdetermined_integer_system(&self, matrix: &[Vec<i64>], target: &[i64]) -> Option<Vec<i32>> {
        let m = matrix.len();
        let n = matrix[0].len();
        
        // Compute A^T A and A^T b
        let mut ata = vec![vec![0i64; n]; n];
        let mut atb = vec![0i64; n];
        
        for i in 0..n {
            for j in 0..n {
                for k in 0..m {
                    ata[i][j] += matrix[k][i] * matrix[k][j];
                }
            }
            for k in 0..m {
                atb[i] += matrix[k][i] * target[k];
            }
        }
        
        // Solve normal equations
        self.solve_integer_system_lattice(&ata, &atb)
    }
    
    /// Compute Hermite Normal Form of integer matrix
    fn hermite_normal_form(&self, matrix: &[Vec<i64>]) -> Option<(Vec<Vec<i64>>, Vec<Vec<i64>>)> {
        let m = matrix.len();
        let n = if m > 0 { matrix[0].len() } else { 0 };
        
        if m == 0 || n == 0 {
            return None;
        }
        
        // Initialize H as copy of matrix and U as identity
        let mut h = matrix.to_vec();
        let mut u = vec![vec![0i64; m]; m];
        for i in 0..m {
            u[i][i] = 1;
        }
        
        // Hermite reduction
        let mut col = 0;
        for row in 0..m {
            if col >= n {
                break;
            }
            
            // Find pivot
            let mut pivot_row = row;
            let mut min_val = i64::MAX;
            for i in row..m {
                if h[i][col] != 0 && h[i][col].abs() < min_val {
                    min_val = h[i][col].abs();
                    pivot_row = i;
                }
            }
            
            if min_val == i64::MAX {
                col += 1;
                continue;
            }
            
            // Swap rows
            if pivot_row != row {
                h.swap(row, pivot_row);
                u.swap(row, pivot_row);
            }
            
            // Ensure positive diagonal
            if h[row][col] < 0 {
                for j in 0..n {
                    h[row][j] = -h[row][j];
                }
                for j in 0..m {
                    u[row][j] = -u[row][j];
                }
            }
            
            // Reduce other rows
            for i in 0..m {
                if i != row && h[i][col] != 0 {
                    let q = h[i][col] / h[row][col];
                    for j in 0..n {
                        h[i][j] -= q * h[row][j];
                    }
                    for j in 0..m {
                        u[i][j] -= q * u[row][j];
                    }
                }
            }
            
            col += 1;
        }
        
        Some((h, u))
    }
    
    /// Solve integer system using approximate methods
    fn solve_integer_system_approximate(&self, matrix: &[Vec<P>], target: &[P]) -> Option<Vec<(usize, i32)>> {
        let m = matrix.len();
        let n = if m > 0 { matrix[0].len() } else { 0 };
        
        if m == 0 || n == 0 {
            return None;
        }
        
        // Use least squares to find approximate real solution
        let mut solution = vec![P::zero(); n];
        
        // For small systems, use direct computation
        if n <= 3 && m >= n {
            // Compute pseudo-inverse using normal equations
            // (A^T A)^{-1} A^T b
            
            let mut ata = vec![vec![P::zero(); n]; n];
            let mut atb = vec![P::zero(); n];
            
            // Compute A^T A
            for i in 0..n {
                for j in 0..n {
                    for k in 0..m {
                        ata[i][j] = ata[i][j] + matrix[k][i] * matrix[k][j];
                    }
                }
                // Compute A^T b
                for k in 0..m {
                    atb[i] = atb[i] + matrix[k][i] * target[k];
                }
            }
            
            // Solve using Gaussian elimination
            if let Some(x) = self.solve_linear_system(&ata, &atb) {
                solution = x;
            } else {
                return None;
            }
        }
        
        // Round to nearest integers and check
        let mut int_solution = vec![0i32; n];
        for i in 0..n {
            int_solution[i] = solution[i].round().to_i32().unwrap_or(0);
        }
        
        // Verify the integer solution
        let mut max_error = P::zero();
        for i in 0..m {
            let mut sum = P::zero();
            for j in 0..n {
                sum = sum + matrix[i][j] * P::from(int_solution[j]).unwrap();
            }
            let error = (sum - target[i]).abs();
            if error > max_error {
                max_error = error;
            }
        }
        
        // Accept if error is small enough
        if max_error < P::epsilon() * P::from(100.0).unwrap() {
            let mut result = Vec::new();
            for (i, &coeff) in int_solution.iter().enumerate() {
                if coeff != 0 {
                    result.push((i, coeff));
                }
            }
            Some(result)
        } else {
            None
        }
    }
    
    /// Solve linear system using Gaussian elimination
    fn solve_linear_system(&self, a: &[Vec<P>], b: &[P]) -> Option<Vec<P>> {
        let n = a.len();
        if n == 0 || a[0].len() != n || b.len() != n {
            return None;
        }
        
        // Create augmented matrix
        let mut aug = vec![vec![P::zero(); n + 1]; n];
        for i in 0..n {
            for j in 0..n {
                aug[i][j] = a[i][j];
            }
            aug[i][n] = b[i];
        }
        
        // Forward elimination
        for i in 0..n {
            // Find pivot
            let mut max_row = i;
            for k in i+1..n {
                if aug[k][i].abs() > aug[max_row][i].abs() {
                    max_row = k;
                }
            }
            
            if aug[max_row][i].abs() < P::epsilon() {
                return None; // Singular matrix
            }
            
            aug.swap(i, max_row);
            
            // Eliminate column
            for k in i+1..n {
                let factor = aug[k][i] / aug[i][i];
                for j in i..=n {
                    aug[k][j] = aug[k][j] - factor * aug[i][j];
                }
            }
        }
        
        // Back substitution
        let mut x = vec![P::zero(); n];
        for i in (0..n).rev() {
            x[i] = aug[i][n];
            for j in i+1..n {
                x[i] = x[i] - aug[i][j] * x[j];
            }
            x[i] = x[i] / aug[i][i];
        }
        
        Some(x)
    }
    
    /// Check if element is approximately the identity (within numerical tolerance)
    fn is_approximately_identity(&self, element: &GroupElement<P>) -> bool {
        let identity = self.identity();
        
        // Check if all parameters are close to identity parameters
        if element.params.len() != identity.params.len() {
            return false;
        }
        
        let tolerance = P::epsilon() * P::from(1000.0).unwrap();
        for (a, b) in element.params.iter().zip(&identity.params) {
            if (*a - *b).abs() > tolerance {
                return false;
            }
        }
        
        true
    }
}

/// Compute factorial
fn factorial(n: usize) -> usize {
    (1..=n).product()
}

/// Check if two group elements are equal
fn element_equal<P: Float>(a: &GroupElement<P>, b: &GroupElement<P>) -> bool {
    if a.params.len() != b.params.len() {
        return false;
    }
    
    for (x, y) in a.params.iter().zip(&b.params) {
        if (*x - *y).abs() > P::epsilon() {
            return false;
        }
    }
    
    true
}

#[cfg(test)]
mod test_group_generation {
    use super::*;
    
    #[test]
    fn test_s2_generation() {
        let s2 = SymmetryGroup::<f64>::symmetric_group(2).unwrap();
        assert_eq!(s2.generators().len(), 1, "S2 should have 1 generator");
        
        // Check the generator
        let gen = &s2.generators()[0];
        // For S2, the generator should be the transposition (0 1)
        // As a 2x2 matrix: [[0,1],[1,0]]
        assert_eq!(gen.params.len(), 4);
        assert_eq!(gen.params[0], 0.0); // (0,0)
        assert_eq!(gen.params[1], 1.0); // (0,1)
        assert_eq!(gen.params[2], 1.0); // (1,0)
        assert_eq!(gen.params[3], 0.0); // (1,1)
        
        // Check that gen^2 = identity
        let gen_squared = s2.multiply_elements(gen, gen).unwrap();
        let identity = GroupElement::<f64>::identity(4);
        
        // Debug: print the squared result
        println!("Gen squared params: {:?}", gen_squared.params);
        println!("Identity params: {:?}", identity.params);
        
        assert!(element_equal(&gen_squared, &identity), "Generator squared should be identity");
        
        let elements = s2.all_elements();
        assert_eq!(elements.len(), 2, "S2 should have 2 elements");
    }
    
    #[test]
    fn test_s3_generation() {
        let s3 = SymmetryGroup::<f64>::symmetric_group(3).unwrap();
        assert_eq!(s3.generators().len(), 2, "S3 should have 2 generators");
        
        let elements = s3.all_elements();
        assert_eq!(elements.len(), 6, "S3 should have 6 elements");
    }
}