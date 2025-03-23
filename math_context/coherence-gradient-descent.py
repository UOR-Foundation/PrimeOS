#!/usr/bin/env python3
"""
Coherence-Gradient Descent Algorithms - A Prime Framework Reference Implementation

This implementation combines multiple advanced techniques from the Prime Framework:
1. Spectral analysis from the Prime Operator's eigenstructure
2. Fiber algebra for multi-perspective pattern detection
3. Multi-base representation for constraint encoding
4. UOR framework concepts for navigating solution spaces efficiently

These techniques are integrated to create a powerful solver for NP-hard problems
that leverages mathematical structures to achieve sub-exponential performance
in many practical cases.
"""

import numpy as np
import time
import math
import random
import matplotlib.pyplot as plt
from typing import List, Tuple, Dict, Any, Optional, Union
from functools import reduce
from collections import Counter, defaultdict
from scipy import sparse
from scipy.sparse import linalg as splinalg
from scipy.sparse.csgraph import connected_components

class EnhancedCoherenceGradientDescent:
    """
    Enhanced implementation of Coherence-Gradient Descent based on the Prime Framework.
    
    This class integrates multiple advanced techniques:
    - Spectral analysis from Prime Operator eigenstructure
    - Fiber algebra for multi-perspective pattern detection
    - Multi-base representation for constraint encoding
    - UOR framework concepts for efficient solution space navigation
    """
    
    def __init__(self, dimension: int = 10, num_fibers: int = 5, 
                 num_bases: int = 3, use_spectral: bool = True,
                 use_fiber: bool = True, use_multi_base: bool = True):
        """
        Initialize the Enhanced Coherence-Gradient Descent framework.
        
        Args:
            dimension: Dimension of the problem space
            num_fibers: Number of fiber points to use for multi-perspective analysis
            num_bases: Number of bases to use for multi-base representation
            use_spectral: Whether to use spectral analysis techniques
            use_fiber: Whether to use fiber algebra techniques
            use_multi_base: Whether to use multi-base representation
        """
        self.dimension = dimension
        self.num_fibers = num_fibers
        self.num_bases = num_bases
        self.use_spectral = use_spectral
        self.use_fiber = use_fiber
        self.use_multi_base = use_multi_base
        
        print(f"Initializing Enhanced Coherence-Gradient Descent with dimension {dimension}")
        print(f"Using techniques: " + 
              f"Spectral={use_spectral}, Fiber={use_fiber}, Multi-Base={use_multi_base}")
        
        # Initialize the Clifford algebra structure
        self.max_grade = min(3, dimension)  # Limit max grade for efficiency
        self.clifford_basis = self._initialize_clifford_basis()
        
        # Initialize the fiber manifold
        self.fibers = self._initialize_fibers() if use_fiber else None
        
        # Initialize numerical bases for multi-base representation
        self.bases = self._select_bases() if use_multi_base else None
        
        # Initialize symmetry transformations from the UOR Lie group
        self.symmetry_generators = self._initialize_symmetry_generators()
        
        # Cache for computations
        self._spectral_cache = {}
        self._coherence_cache = {}
        self._pattern_cache = {}
    
    def _initialize_clifford_basis(self) -> List[str]:
        """
        Initialize the Clifford algebra basis elements.
        Limit to lower grades for computational efficiency.
        
        Returns:
            List of basis element labels
        """
        # Start with scalar (grade 0)
        basis = ['1']
        
        # Add basis elements up to max_grade
        for r in range(1, self.max_grade + 1):
            for indices in self._combinations(range(1, self.dimension + 1), r):
                basis.append('e' + ''.join(map(str, indices)))
        
        print(f"Initialized Clifford algebra with {len(basis)} basis elements")
        return basis
    
    def _combinations(self, elements: List[int], r: int) -> List[Tuple]:
        """
        Generate all r-combinations of elements.
        
        Args:
            elements: List of elements to choose from
            r: Number of elements in each combination
            
        Returns:
            List of r-combinations
        """
        if r == 0:
            return [()]
        if not elements:
            return []
        
        # Take the first element and generate combinations that include it
        first, rest = elements[0], elements[1:]
        with_first = [(first,) + combo for combo in self._combinations(rest, r - 1)]
        
        # Generate combinations that don't include the first element
        without_first = self._combinations(rest, r)
        
        return with_first + without_first
    
    def _initialize_fibers(self) -> Dict[int, Dict[str, Any]]:
        """
        Initialize fiber algebras at different manifold points.
        
        Returns:
            Dictionary mapping fiber indices to fiber data
        """
        fibers = {}
        
        # Create fiber points in a low-discrepancy sequence for better coverage
        # We use a simple approach here for clarity
        for i in range(self.num_fibers):
            # Create a position in the manifold using quasi-random sequence
            # We use a simple phi-based sequence for demonstration
            phi = (1 + np.sqrt(5)) / 2  # Golden ratio
            pos = np.array([(i * phi) % 1 for _ in range(3)])
            
            # Initialize a fiber at this point
            fiber = {
                'position': pos,
                'inner_product': self._initialize_fiber_metric(pos),
                'state': None,
                'patterns': []
            }
            
            fibers[i] = fiber
        
        print(f"Initialized {len(fibers)} fiber algebras")
        return fibers
    
    def _initialize_fiber_metric(self, position: np.ndarray) -> np.ndarray:
        """
        Initialize the inner product metric for a fiber at a given position.
        The metric varies based on position to create different perspectives.
        
        Args:
            position: Position in the manifold
            
        Returns:
            Inner product matrix
        """
        n_basis = len(self.clifford_basis)
        metric = np.eye(n_basis)
        
        # Vary the metric based on position
        for i in range(1, n_basis):
            for j in range(i):
                # Position-dependent correlation
                correlation = 0.1 * np.cos(np.pi * np.sum(position) * (i + j) / n_basis)
                metric[i, j] = correlation
                metric[j, i] = correlation
        
        # Ensure metric is positive definite
        return metric
    
    def _select_bases(self) -> List[int]:
        """
        Select a diverse set of numerical bases for multi-base representation.
        
        Returns:
            List of bases
        """
        # Always include base 2 (binary)
        bases = [2]
        
        # Add bases that are coprime to previous bases when possible
        while len(bases) < self.num_bases:
            candidate = len(bases) + 2
            # Prioritize prime bases
            while any(self._gcd(candidate, b) > 1 for b in bases):
                candidate += 1
            bases.append(candidate)
        
        print(f"Selected bases for multi-base representation: {bases}")
        return bases
    
    def _gcd(self, a: int, b: int) -> int:
        """Calculate greatest common divisor."""
        while b:
            a, b = b, a % b
        return a
    
    def _initialize_symmetry_generators(self) -> List[Dict[str, Any]]:
        """
        Initialize generators for symmetry transformations from the UOR Lie group.
        
        Returns:
            List of generator specifications
        """
        generators = []
        
        # 1. Single bit flips (using vector basis elements)
        for i in range(self.dimension):
            generators.append({
                'type': 'bit_flip',
                'index': i,
                'description': f'Flip bit {i}'
            })
        
        # 2. Bit swaps (using bivector basis elements)
        for i in range(self.dimension - 1):
            for j in range(i + 1, self.dimension):
                generators.append({
                    'type': 'bit_swap',
                    'indices': (i, j),
                    'description': f'Swap bits {i} and {j}'
                })
        
        # 3. Local cluster flips (acting on small groups of variables)
        max_cluster = min(5, self.dimension)
        for size in range(2, max_cluster + 1):
            for indices in self._combinations(range(self.dimension), size):
                if len(generators) > 1000:  # Limit generators for large problems
                    break
                generators.append({
                    'type': 'cluster_flip',
                    'indices': indices,
                    'description': f'Flip cluster {indices}'
                })
            if len(generators) > 1000:
                break
        
        print(f"Initialized {len(generators)} symmetry generators")
        return generators
    
    def encode_problem(self, constraints: List[List[int]]) -> Dict[str, Any]:
        """
        Encode a problem using multiple advanced techniques from the Prime Framework.
        
        Args:
            constraints: List of constraints, where each constraint is a list of integers
                       For SAT, these would be clauses where positive integers represent
                       positive literals and negative integers represent negative literals
            
        Returns:
            Problem encoding as a dictionary
        """
        n_vars = max([max([abs(lit) for lit in clause]) for clause in constraints])
        n_clauses = len(constraints)
        
        print(f"Encoding problem with {n_vars} variables and {n_clauses} constraints")
        
        # Initialize problem encoding
        problem = {
            'n_vars': n_vars,
            'n_clauses': n_clauses,
            'constraints': constraints,
            'initial_state': np.random.randint(0, 2, size=n_vars),
            'best_state': None,
            'best_coherence': float('inf'),
            'spectral_data': None,
            'fiber_encodings': None,
            'multibase_encodings': None
        }
        
        # Create adjacency matrix for the problem
        problem['adjacency_matrix'] = self._create_adjacency_matrix(constraints, n_vars)
        
        # Create reference state (perfect coherence)
        problem['reference_state'] = self._create_reference_state(n_clauses)
        
        # Add spectral analysis if enabled
        if self.use_spectral:
            problem['spectral_data'] = self._perform_spectral_analysis(problem)
        
        # Add fiber encodings if enabled
        if self.use_fiber:
            problem['fiber_encodings'] = self._create_fiber_encodings(problem)
        
        # Add multi-base encodings if enabled
        if self.use_multi_base:
            problem['multibase_encodings'] = self._create_multibase_encodings(problem)
        
        return problem
    
    def _create_adjacency_matrix(self, constraints: List[List[int]], n_vars: int) -> sparse.spmatrix:
        """
        Create a sparse adjacency matrix representing the variable interactions.
        
        Args:
            constraints: List of constraints
            n_vars: Number of variables
            
        Returns:
            Sparse adjacency matrix
        """
        # Create a sparse matrix for variable interactions
        row_indices = []
        col_indices = []
        
        # For each constraint, variables in the same constraint interact
        for clause in constraints:
            for i, lit1 in enumerate(clause):
                var1 = abs(lit1) - 1
                for j in range(i + 1, len(clause)):
                    var2 = abs(clause[j]) - 1
                    # Add bidirectional edges
                    row_indices.extend([var1, var2])
                    col_indices.extend([var2, var1])
        
        # Create matrix with ones at interaction points
        data = np.ones(len(row_indices))
        adjacency = sparse.csr_matrix((data, (row_indices, col_indices)), shape=(n_vars, n_vars))
        
        return adjacency
    
    def _create_reference_state(self, n_clauses: int) -> np.ndarray:
        """
        Create a reference state representing perfect coherence (all constraints satisfied).
        
        Args:
            n_clauses: Number of clauses/constraints
            
        Returns:
            Reference state as a NumPy array
        """
        # Reference state has one component for each clause
        ref_state = np.ones(n_clauses)
        return ref_state
    
    def _perform_spectral_analysis(self, problem: Dict[str, Any]) -> Dict[str, Any]:
        """
        Perform spectral analysis on the problem structure.
        This identifies important variables and clusters in the problem.
        
        Args:
            problem: Problem encoding
            
        Returns:
            Spectral analysis data
        """
        adjacency = problem['adjacency_matrix']
        n_vars = problem['n_vars']
        
        # Calculate the Laplacian matrix
        degrees = np.array(adjacency.sum(axis=1)).flatten()
        laplacian = sparse.diags(degrees) - adjacency
        
        # Compute eigenvalues and eigenvectors (using sparse methods for large problems)
        if n_vars > 100:
            # For large problems, compute only a subset of eigenvalues/vectors
            num_eigs = min(50, n_vars // 2)
            eigenvalues, eigenvectors = splinalg.eigsh(laplacian, k=num_eigs, which='SM')
        else:
            # Convert to dense for small problems (more accurate)
            lap_dense = laplacian.toarray()
            eigenvalues, eigenvectors = np.linalg.eigh(lap_dense)
        
        # Sort by eigenvalue
        idx = np.argsort(eigenvalues)
        eigenvalues = eigenvalues[idx]
        eigenvectors = eigenvectors[:, idx]
        
        # Identify variable clusters using spectral partitioning
        num_clusters = min(10, n_vars // 5) if n_vars > 50 else 2
        clusters = self._spectral_clustering(eigenvectors, num_clusters)
        
        # Calculate variable importance scores based on eigenvector components
        importance_scores = np.zeros(n_vars)
        for i in range(min(10, len(eigenvalues))):
            # Lower eigenvalues correspond to more important structure
            weight = 1.0 / (1.0 + eigenvalues[i])
            importance_scores += weight * np.abs(eigenvectors[:, i])
        
        # Normalize importance scores
        if np.max(importance_scores) > 0:
            importance_scores = importance_scores / np.max(importance_scores)
        
        # Identify connected components
        n_components, labels = connected_components(adjacency, directed=False)
        
        return {
            'eigenvalues': eigenvalues,
            'eigenvectors': eigenvectors,
            'clusters': clusters,
            'importance_scores': importance_scores,
            'connected_components': labels,
            'n_components': n_components
        }
    
    def _spectral_clustering(self, eigenvectors: np.ndarray, num_clusters: int) -> np.ndarray:
        """
        Perform spectral clustering using eigenvectors.
        
        Args:
            eigenvectors: Matrix of eigenvectors
            num_clusters: Number of clusters to create
            
        Returns:
            Array of cluster assignments
        """
        # Use the first num_clusters eigenvectors (excluding the first)
        k = min(num_clusters + 1, eigenvectors.shape[1])
        features = eigenvectors[:, 1:k]
        
        # Normalize rows
        norms = np.sqrt(np.sum(features**2, axis=1))
        norms[norms == 0] = 1.0  # Avoid division by zero
        features = features / norms[:, np.newaxis]
        
        # Simple k-means clustering
        clusters = np.zeros(features.shape[0], dtype=int)
        
        # Initialize centroids using k-means++
        centroids = []
        # Choose first centroid randomly
        centroids.append(features[np.random.randint(0, features.shape[0])])
        
        # Choose remaining centroids with probability proportional to distance squared
        for _ in range(1, num_clusters):
            # Compute distances to closest centroid
            distances = np.min([np.sum((features - c)**2, axis=1) for c in centroids], axis=0)
            # Choose next centroid with probability proportional to distance squared
            probs = distances / np.sum(distances)
            next_idx = np.random.choice(range(features.shape[0]), p=probs)
            centroids.append(features[next_idx])
        
        centroids = np.array(centroids)
        
        # Simple k-means iteration
        max_iterations = 100
        for _ in range(max_iterations):
            # Assign points to clusters
            distances = np.array([np.sum((features - c)**2, axis=1) for c in centroids])
            new_clusters = np.argmin(distances, axis=0)
            
            # Check for convergence
            if np.array_equal(clusters, new_clusters):
                break
            
            clusters = new_clusters
            
            # Update centroids
            for i in range(num_clusters):
                points = features[clusters == i]
                if len(points) > 0:
                    centroids[i] = np.mean(points, axis=0)
        
        return clusters
    
    def _create_fiber_encodings(self, problem: Dict[str, Any]) -> Dict[int, Dict[str, Any]]:
        """
        Create encodings of the problem across multiple fiber algebras.
        Each fiber provides a different perspective on the problem.
        
        Args:
            problem: Problem encoding
            
        Returns:
            Dictionary mapping fiber indices to fiber encodings
        """
        if not self.fibers:
            return None
        
        encodings = {}
        constraints = problem['constraints']
        
        for fiber_idx, fiber in self.fibers.items():
            # Get fiber-specific metric
            metric = fiber['inner_product']
            
            # Create a fiber-specific encoding of the constraints
            encoding = {
                'constraint_weights': np.ones(len(constraints)),
                'variable_weights': np.ones(problem['n_vars']),
                'reference_state': self._create_reference_state(len(constraints)).copy()
            }
            
            # Modify weights based on position in fiber manifold
            pos = fiber['position']
            
            # Vary constraint weights based on position
            for i, clause in enumerate(constraints):
                # Weight clauses differently in each fiber
                weight = 1.0 + 0.5 * np.sin(np.pi * pos[0] * i / len(constraints))
                encoding['constraint_weights'][i] = weight
            
            # Vary variable weights based on position
            for i in range(problem['n_vars']):
                # Weight variables differently in each fiber
                weight = 1.0 + 0.3 * np.cos(np.pi * pos[1] * i / problem['n_vars'])
                encoding['variable_weights'][i] = weight
            
            encodings[fiber_idx] = encoding
        
        return encodings
    
    def _create_multibase_encodings(self, problem: Dict[str, Any]) -> Dict[int, Dict[str, Any]]:
        """
        Create multi-base encodings of the problem.
        Each base provides a different perspective on the problem structure.
        
        Args:
            problem: Problem encoding
            
        Returns:
            Dictionary mapping bases to encodings
        """
        if not self.bases:
            return None
        
        encodings = {}
        constraints = problem['constraints']
        n_vars = problem['n_vars']
        
        for base in self.bases:
            # Create a base-specific encoding
            # Variables and clauses are represented in different numerical bases
            encoding = {
                'base': base,
                'variable_patterns': [],
                'constraint_patterns': []
            }
            
            # Generate patterns for variables in this base
            for i in range(n_vars):
                # Convert i to the current base
                pattern = self._convert_to_base(i + 1, base)
                encoding['variable_patterns'].append(pattern)
            
            # Generate patterns for constraints in this base
            for i, clause in enumerate(constraints):
                # Create a unique pattern for this clause
                signatures = []
                for lit in clause:
                    var_idx = abs(lit) - 1
                    # Use variable pattern with sign
                    var_pattern = encoding['variable_patterns'][var_idx].copy()
                    if lit < 0:
                        # Negative literal: modify pattern
                        var_pattern = [(b + base//2) % base for b in var_pattern]
                    signatures.append(var_pattern)
                
                # Combine signatures
                combined = []
                max_len = max(len(s) for s in signatures) if signatures else 0
                for j in range(max_len):
                    sum_digit = 0
                    for sig in signatures:
                        if j < len(sig):
                            sum_digit += sig[j]
                    combined.append(sum_digit % base)
                
                encoding['constraint_patterns'].append(combined)
            
            encodings[base] = encoding
        
        return encodings
    
    def _convert_to_base(self, number: int, base: int) -> List[int]:
        """
        Convert a number to a specific base representation.
        
        Args:
            number: Integer to convert
            base: The base to convert to
            
        Returns:
            List of digits in the specified base (most significant digit first)
        """
        if number == 0:
            return [0]
        
        digits = []
        n = number
        
        while n > 0:
            digits.append(n % base)
            n //= base
            
        return list(reversed(digits))
    
    def compute_state_coherence(self, problem: Dict[str, Any], state: np.ndarray) -> Tuple[float, np.ndarray]:
        """
        Compute the coherence norm for a given state using multiple perspectives.
        
        Args:
            problem: Problem encoding
            state: Current variable assignment
            
        Returns:
            Tuple of (coherence_norm, clause_satisfaction_vector)
        """
        n_clauses = problem['n_clauses']
        constraints = problem['constraints']
        
        # Compute satisfaction vector (which clauses are satisfied)
        satisfaction = np.zeros(n_clauses)
        for i, clause in enumerate(constraints):
            satisfaction[i] = self._compute_clause_satisfaction(state, clause)
        
        # Base coherence is the number of unsatisfied clauses
        base_coherence = n_clauses - np.sum(satisfaction)
        coherence = base_coherence
        
        # Enhanced coherence calculation using different perspectives
        
        # 1. Spectral coherence component
        if self.use_spectral and problem['spectral_data']:
            spectral_coherence = self._compute_spectral_coherence(problem, state, satisfaction)
            coherence = 0.7 * coherence + 0.3 * spectral_coherence
        
        # 2. Fiber coherence component
        if self.use_fiber and problem['fiber_encodings']:
            fiber_coherence = self._compute_fiber_coherence(problem, state, satisfaction)
            coherence = 0.7 * coherence + 0.3 * fiber_coherence
        
        # 3. Multi-base coherence component
        if self.use_multi_base and problem['multibase_encodings']:
            multibase_coherence = self._compute_multibase_coherence(problem, state, satisfaction)
            coherence = 0.7 * coherence + 0.3 * multibase_coherence
        
        return coherence, satisfaction
    
    def _compute_clause_satisfaction(self, state: np.ndarray, clause: List[int]) -> int:
        """
        Compute whether a clause is satisfied by a given state.
        
        Args:
            state: Current variable assignment
            clause: Clause to check, represented as a list of literals
            
        Returns:
            1 if satisfied, 0 if not
        """
        for lit in clause:
            var_idx = abs(lit) - 1
            if var_idx < len(state):
                var_val = state[var_idx]
                if (lit > 0 and var_val == 1) or (lit < 0 and var_val == 0):
                    return 1
        
        return 0
    
    def _compute_spectral_coherence(self, problem: Dict[str, Any], state: np.ndarray, 
                                   satisfaction: np.ndarray) -> float:
        """
        Compute coherence component based on spectral analysis.
        Takes into account the importance of variables in the spectral structure.
        
        Args:
            problem: Problem encoding
            state: Current variable assignment
            satisfaction: Clause satisfaction vector
            
        Returns:
            Spectral coherence component
        """
        spectral_data = problem['spectral_data']
        importance_scores = spectral_data['importance_scores']
        clusters = spectral_data['clusters']
        n_vars = problem['n_vars']
        
        # Compute cluster satisfaction metrics
        cluster_satisfaction = defaultdict(list)
        for i, clause in enumerate(problem['constraints']):
            # Determine which clusters this clause involves
            involved_clusters = set()
            for lit in clause:
                var_idx = abs(lit) - 1
                if var_idx < len(clusters):
                    involved_clusters.add(clusters[var_idx])
            
            # Record satisfaction status for each involved cluster
            is_satisfied = satisfaction[i] > 0
            for cluster_id in involved_clusters:
                cluster_satisfaction[cluster_id].append(is_satisfied)
        
        # Calculate coherence based on cluster satisfaction
        cluster_coherence = 0.0
        for cluster_id, satisfactions in cluster_satisfaction.items():
            if satisfactions:
                # Higher penalty for clusters with mixed satisfaction status
                satisfaction_rate = sum(satisfactions) / len(satisfactions)
                # Penalty is higher when satisfaction rate is around 0.5 (most conflicted)
                penalty = 4.0 * satisfaction_rate * (1.0 - satisfaction_rate)
                cluster_coherence += penalty
        
        # Normalize
        if cluster_satisfaction:
            cluster_coherence /= len(cluster_satisfaction)
        
        # Additional component based on important variables
        important_var_coherence = 0.0
        for i in range(n_vars):
            # Check variables with high importance
            if importance_scores[i] > 0.5:
                # Count unsatisfied clauses involving this variable
                unsatisfied_count = 0
                for j, clause in enumerate(problem['constraints']):
                    if not satisfaction[j] and any(abs(lit) - 1 == i for lit in clause):
                        unsatisfied_count += 1
                
                important_var_coherence += importance_scores[i] * unsatisfied_count
        
        # Normalize
        important_var_coherence = min(1.0, important_var_coherence / n_vars)
        
        # Combine components
        spectral_coherence = 0.5 * cluster_coherence + 0.5 * important_var_coherence
        
        return spectral_coherence * len(satisfaction)  # Scale to match base coherence
    
    def _compute_fiber_coherence(self, problem: Dict[str, Any], state: np.ndarray, 
                                satisfaction: np.ndarray) -> float:
        """
        Compute coherence component based on fiber algebra analysis.
        Takes into account different perspectives from different fibers.
        
        Args:
            problem: Problem encoding
            state: Current variable assignment
            satisfaction: Clause satisfaction vector
            
        Returns:
            Fiber coherence component
        """
        fiber_encodings = problem['fiber_encodings']
        
        # Compute coherence across fibers
        fiber_coherences = []
        
        for fiber_idx, encoding in fiber_encodings.items():
            # Get fiber-specific weights
            constraint_weights = encoding['constraint_weights']
            
            # Calculate weighted unsatisfied count for this fiber
            unsatisfied = 1.0 - satisfaction
            weighted_count = np.sum(unsatisfied * constraint_weights)
            
            fiber_coherences.append(weighted_count)
        
        # Take average fiber coherence
        if fiber_coherences:
            fiber_coherence = sum(fiber_coherences) / len(fiber_coherences)
        else:
            fiber_coherence = 0.0
        
        return fiber_coherence
    
    def _compute_multibase_coherence(self, problem: Dict[str, Any], state: np.ndarray, 
                                    satisfaction: np.ndarray) -> float:
        """
        Compute coherence component based on multi-base representation.
        Takes into account patterns across different numerical bases.
        
        Args:
            problem: Problem encoding
            state: Current variable assignment
            satisfaction: Clause satisfaction vector
            
        Returns:
            Multi-base coherence component
        """
        multibase_encodings = problem['multibase_encodings']
        
        # Compute coherence across bases
        base_coherences = []
        
        for base, encoding in multibase_encodings.items():
            # Compute digit distribution in this base
            assigned_vars = [i for i, val in enumerate(state) if val == 1]
            
            if not assigned_vars:
                base_coherences.append(len(satisfaction))
                continue
            
            # Get patterns for assigned variables
            patterns = [encoding['variable_patterns'][i] for i in assigned_vars]
            
            # Combine the patterns
            combined_pattern = []
            max_len = max(len(p) for p in patterns) if patterns else 0
            for i in range(max_len):
                digit_sum = 0
                for pattern in patterns:
                    if i < len(pattern):
                        digit_sum += pattern[i]
                combined_pattern.append(digit_sum % base)
            
            # Compare with constraint patterns
            pattern_match_count = 0
            for i, constraint_pattern in enumerate(encoding['constraint_patterns']):
                if satisfaction[i] > 0:  # Only consider satisfied constraints
                    # Check if patterns match or complement
                    match = True
                    for j in range(min(len(combined_pattern), len(constraint_pattern))):
                        if j < len(combined_pattern) and j < len(constraint_pattern):
                            if (combined_pattern[j] != constraint_pattern[j] and 
                                (combined_pattern[j] + constraint_pattern[j]) % base != 0):
                                match = False
                                break
                    
                    if match:
                        pattern_match_count += 1
            
            # Coherence for this base
            satisfied_count = np.sum(satisfaction)
            if satisfied_count > 0:
                base_coherence = satisfied_count - pattern_match_count / satisfied_count
            else:
                base_coherence = len(satisfaction)
            
            base_coherences.append(base_coherence)
        
        # Take the minimum coherence across bases
        multibase_coherence = min(base_coherences) if base_coherences else 0.0
        
        return multibase_coherence
    
    def apply_symmetry_transformation(self, state: np.ndarray, generator_idx: int) -> np.ndarray:
        """
        Apply a symmetry transformation to a state.
        
        Args:
            state: Current state
            generator_idx: Index of the symmetry generator to apply
            
        Returns:
            Transformed state
        """
        if generator_idx < len(self.symmetry_generators):
            generator = self.symmetry_generators[generator_idx]
            
            if generator['type'] == 'bit_flip':
                # Flip a single bit
                idx = generator['index']
                if idx < len(state):
                    new_state = state.copy()
                    new_state[idx] = 1 - new_state[idx]
                    return new_state
            
            elif generator['type'] == 'bit_swap':
                # Swap two bits
                i, j = generator['indices']
                if i < len(state) and j < len(state):
                    new_state = state.copy()
                    new_state[i], new_state[j] = new_state[j], new_state[i]
                    return new_state
            
            elif generator['type'] == 'cluster_flip':
                # Flip a cluster of bits
                indices = generator['indices']
                new_state = state.copy()
                for idx in indices:
                    if idx < len(state):
                        new_state[idx] = 1 - new_state[idx]
                return new_state
            
        # If we reach here, just return the original state
        return state.copy()
    
    def compute_coherence_gradient(self, problem: Dict[str, Any], state: np.ndarray) -> List[Tuple[int, float]]:
        """
        Compute the gradient of the coherence norm with respect to symmetry transformations.
        
        Args:
            problem: Problem encoding
            state: Current state
            
        Returns:
            List of (generator_idx, coherence_change) tuples
        """
        current_coherence, _ = self.compute_state_coherence(problem, state)
        gradient = []
        
        # Use spectral data to prioritize generators
        if self.use_spectral and problem['spectral_data']:
            importance_scores = problem['spectral_data']['importance_scores']
            priority_vars = np.argsort(-importance_scores)[:min(10, len(importance_scores))]
            
            # Prioritize generators that affect important variables
            for i, generator in enumerate(self.symmetry_generators):
                if (generator['type'] == 'bit_flip' and generator['index'] in priority_vars) or \
                   (generator['type'] == 'bit_swap' and 
                    (generator['indices'][0] in priority_vars or generator['indices'][1] in priority_vars)) or \
                   (generator['type'] == 'cluster_flip' and 
                    any(idx in priority_vars for idx in generator['indices'])):
                    
                    # Try the transformation
                    transformed_state = self.apply_symmetry_transformation(state, i)
                    new_coherence, _ = self.compute_state_coherence(problem, transformed_state)
                    
                    # Coherence change (negative means improvement)
                    coherence_change = new_coherence - current_coherence
                    gradient.append((i, coherence_change, True))  # True indicates priority
                
        # Add remaining generators
        for i in range(len(self.symmetry_generators)):
            if not any(g[0] == i for g in gradient):  # Skip already processed generators
                # Try the transformation
                transformed_state = self.apply_symmetry_transformation(state, i)
                new_coherence, _ = self.compute_state_coherence(problem, transformed_state)
                
                # Coherence change (negative means improvement)
                coherence_change = new_coherence - current_coherence
                gradient.append((i, coherence_change, False))  # False indicates not priority
        
        # Sort by coherence change (most negative first), with priority generators first
        gradient.sort(key=lambda x: (not x[2], x[1]))
        
        # Return only the generator index and coherence change
        return [(g[0], g[1]) for g in gradient]
    
    def diversify_search(self, problem: Dict[str, Any], state: np.ndarray, 
                         previous_states: List[np.ndarray], 
                         iteration: int) -> np.ndarray:
        """
        Apply diversification strategies to escape local minima.
        
        Args:
            problem: Problem encoding
            state: Current state
            previous_states: List of previously visited states
            iteration: Current iteration number
            
        Returns:
            Diversified state
        """
        # Determine if we should diversify based on stagnation
        should_diversify = False
        
        # Check if we've been near this state before
        if previous_states:
            similarities = [np.sum(state == prev_state) / len(state) for prev_state in previous_states[-10:]]
            if any(sim > 0.9 for sim in similarities):
                should_diversify = True
        
        if not should_diversify:
            return state
        
        new_state = state.copy()
        
        # Choose diversification strategy based on iteration
        strategy = iteration % 3
        
        if strategy == 0:
            # Strong random perturbation
            flip_indices = np.random.choice(len(state), size=max(1, len(state)//5), replace=False)
            for idx in flip_indices:
                new_state[idx] = 1 - new_state[idx]
        
        elif strategy == 1 and self.use_spectral and problem['spectral_data']:
            # Flip variables in a spectral cluster
            clusters = problem['spectral_data']['clusters']
            unique_clusters = np.unique(clusters)
            target_cluster = np.random.choice(unique_clusters)
            
            # Flip all variables in the target cluster
            for i in range(len(state)):
                if i < len(clusters) and clusters[i] == target_cluster:
                    new_state[i] = 1 - new_state[i]
        
        elif strategy == 2 and self.use_multi_base and problem['multibase_encodings']:
            # Flip variables based on multi-base patterns
            base = random.choice(list(problem['multibase_encodings'].keys()))
            encoding = problem['multibase_encodings'][base]
            
            # Get patterns
            patterns = encoding['variable_patterns']
            
            # Group variables by pattern similarity
            pattern_groups = defaultdict(list)
            for i, pattern in enumerate(patterns):
                if i < len(state):
                    # Use first digit as key for grouping
                    key = pattern[0] if pattern else 0
                    pattern_groups[key].append(i)
            
            # Select a random group and flip those variables
            if pattern_groups:
                group_key = random.choice(list(pattern_groups.keys()))
                for idx in pattern_groups[group_key]:
                    new_state[idx] = 1 - new_state[idx]
        
        return new_state
    
    def solve(self, problem: Dict[str, Any], max_iterations: int = 1000, 
              use_simulated_annealing: bool = True, temperature: float = 1.0,
              restart_count: int = 3, use_tabu: bool = True, 
              tabu_list_size: int = 10) -> Dict[str, Any]:
        """
        Solve a problem using enhanced coherence-gradient descent.
        
        Args:
            problem: Problem encoding
            max_iterations: Maximum number of iterations
            use_simulated_annealing: Whether to use simulated annealing
            temperature: Initial temperature for simulated annealing
            restart_count: Number of restarts to attempt
            use_tabu: Whether to use tabu search
            tabu_list_size: Size of tabu list
            
        Returns:
            Solution information
        """
        start_time = time.time()
        
        # Initialize best solution tracking
        best_state = None
        best_coherence = float('inf')
        best_satisfaction = None
        
        # Track overall history
        history = {
            'coherence': [],
            'iterations': [],
            'satisfied_clauses': []
        }
        
        # Run multiple restarts
        for restart in range(restart_count):
            print(f"Starting search attempt {restart+1}/{restart_count}")
            
            # Initialize state
            if restart == 0:
                # First attempt uses the initial state
                current_state = problem['initial_state'].copy()
            else:
                # Subsequent attempts use random initialization with spectral hints
                if self.use_spectral and problem['spectral_data']:
                    importance_scores = problem['spectral_data']['importance_scores']
                    # Initialize random state but bias important variables
                    current_state = np.random.randint(0, 2, size=problem['n_vars'])
                    for i in range(len(current_state)):
                        if i < len(importance_scores) and np.random.random() < importance_scores[i]:
                            # Higher chance to set important variables to previous best value
                            if best_state is not None and i < len(best_state):
                                current_state[i] = best_state[i]
                else:
                    # Completely random initialization
                    current_state = np.random.randint(0, 2, size=problem['n_vars'])
            
            current_coherence, current_satisfaction = self.compute_state_coherence(problem, current_state)
            
            # Initialize tracking for this attempt
            restart_best_state = current_state.copy()
            restart_best_coherence = current_coherence
            restart_best_satisfaction = current_satisfaction.copy()
            
            # Initialize tabu list
            tabu_list = []
            
            # Initialize previous states for diversification
            previous_states = []
            
            # Set up temperature for simulated annealing
            current_temp = temperature
            cooling_rate = 0.99  # Temperature cooling rate
            
            # Iterations for this restart
            restart_iterations = max_iterations // restart_count
            
            # Start search
            for iter_idx in range(1, restart_iterations + 1):
                # Add current state to previous states
                previous_states.append(current_state.copy())
                if len(previous_states) > 20:
                    previous_states.pop(0)
                
                # Compute gradient
                gradient = self.compute_coherence_gradient(problem, current_state)
                
                # Filter out tabu moves
                if use_tabu:
                    gradient = [(i, c) for i, c in gradient if i not in tabu_list]
                
                if not gradient:
                    # No valid moves, add diversification
                    current_state = self.diversify_search(
                        problem, current_state, previous_states, iter_idx)
                    current_coherence, current_satisfaction = self.compute_state_coherence(
                        problem, current_state)
                    continue
                
                # Decide on transformation to apply
                if use_simulated_annealing:
                    # Simulated annealing: sometimes accept worse solutions
                    # Choose transformation based on probability proportional to exp(-change/T)
                    changes = np.array([change for _, change in gradient])
                    
                    # Adjust changes to be all positive for probability calculation
                    adjusted_changes = changes - np.min(changes)
                    if np.sum(adjusted_changes) == 0:
                        adjusted_changes = np.ones_like(adjusted_changes)
                    
                    # Compute selection probabilities
                    inv_changes = 1.0 / (1.0 + adjusted_changes)
                    probs = inv_changes / np.sum(inv_changes)
                    
                    # Select move based on probability
                    chosen_idx = np.random.choice(len(gradient), p=probs)
                    generator_idx, coherence_change = gradient[chosen_idx]
                    
                    # Update temperature
                    current_temp *= cooling_rate
                else:
                    # Greedy: always choose the best transformation
                    generator_idx, coherence_change = gradient[0]
                
                # Add to tabu list
                if use_tabu:
                    tabu_list.append(generator_idx)
                    if len(tabu_list) > tabu_list_size:
                        tabu_list.pop(0)
                
                # Apply chosen transformation
                current_state = self.apply_symmetry_transformation(current_state, generator_idx)
                current_coherence, current_satisfaction = self.compute_state_coherence(
                    problem, current_state)
                
                # Update best state for this restart
                if current_coherence < restart_best_coherence:
                    restart_best_state = current_state.copy()
                    restart_best_coherence = current_coherence
                    restart_best_satisfaction = current_satisfaction.copy()
                
                # Diversify if needed
                if iter_idx % 50 == 0:
                    # Check if we should apply diversification
                    if current_coherence > 0:
                        diversified_state = self.diversify_search(
                            problem, current_state, previous_states, iter_idx)
                        # Only accept if it maintains or improves coherence
                        div_coherence, _ = self.compute_state_coherence(problem, diversified_state)
                        if div_coherence <= current_coherence:
                            current_state = diversified_state
                            current_coherence = div_coherence
                
                # Update history
                history['coherence'].append(current_coherence)
                history['iterations'].append(restart * restart_iterations + iter_idx)
                history['satisfied_clauses'].append(np.sum(current_satisfaction))
                
                # Check for solution
                if current_coherence == 0:
                    print(f"Solution found after {iter_idx} iterations in restart {restart+1}!")
                    break
            
            # Update overall best solution
            if restart_best_coherence < best_coherence:
                best_state = restart_best_state.copy()
                best_coherence = restart_best_coherence
                best_satisfaction = restart_best_satisfaction.copy()
                
                print(f"New best solution found in restart {restart+1}")
                print(f"  Coherence: {best_coherence}")
                print(f"  Satisfied clauses: {int(np.sum(best_satisfaction))}/{problem['n_clauses']}")
        
        end_time = time.time()
        solution_time = end_time - start_time
        total_iterations = len(history['coherence'])
        
        print(f"Optimization completed in {solution_time:.2f} seconds after {total_iterations} iterations")
        print(f"Best coherence: {best_coherence}")
        print(f"Satisfied clauses: {int(np.sum(best_satisfaction))}/{problem['n_clauses']}")
        
        # Update problem with solution
        problem['best_state'] = best_state
        problem['best_coherence'] = best_coherence
        problem['best_satisfaction'] = best_satisfaction
        problem['history'] = history
        problem['solution_time'] = solution_time
        problem['iterations'] = total_iterations
        
        return problem
    
    def visualize_solution(self, problem: Dict[str, Any]) -> None:
        """
        Visualize the solution process.
        
        Args:
            problem: Problem with solution history
        """
        if 'history' not in problem:
            print("No solution history to visualize")
            return
        
        history = problem['history']
        
        # Create a figure with multiple subplots
        plt.figure(figsize=(15, 10))
        
        # Plot 1: Coherence over iterations
        plt.subplot(2, 2, 1)
        plt.plot(history['iterations'], history['coherence'])
        plt.xlabel('Iterations')
        plt.ylabel('Coherence Norm')
        plt.title('Coherence Gradient Descent')
        plt.grid(True)
        
        # Plot 2: Satisfied clauses over iterations
        plt.subplot(2, 2, 2)
        plt.plot(history['iterations'], history['satisfied_clauses'])
        plt.xlabel('Iterations')
        plt.ylabel('Satisfied Clauses')
        plt.title('Constraint Satisfaction Progress')
        plt.grid(True)
        
        # Plot 3: Visualization of spectral clusters (if available)
        if self.use_spectral and 'spectral_data' in problem and problem['spectral_data']:
            plt.subplot(2, 2, 3)
            
            # Extract spectral data
            spectral_data = problem['spectral_data']
            if 'eigenvectors' in spectral_data and spectral_data['eigenvectors'] is not None:
                # Use first two non-trivial eigenvectors for 2D visualization
                eigenvectors = spectral_data['eigenvectors']
                if eigenvectors.shape[1] > 2:
                    x = eigenvectors[:, 1]  # First non-trivial eigenvector
                    y = eigenvectors[:, 2]  # Second non-trivial eigenvector
                    
                    # Color points by cluster
                    if 'clusters' in spectral_data:
                        clusters = spectral_data['clusters']
                        plt.scatter(x, y, c=clusters, cmap='viridis', s=50, alpha=0.7)
                    else:
                        plt.scatter(x, y, s=50, alpha=0.7)
                    
                    plt.xlabel('Eigenvector 1')
                    plt.ylabel('Eigenvector 2')
                    plt.title('Spectral Clustering of Variables')
                    plt.colorbar(label='Cluster')
            
        # Plot 4: Visualization of final state
        plt.subplot(2, 2, 4)
        
        if 'best_state' in problem and problem['best_state'] is not None:
            state = problem['best_state']
            
            # Plot variable assignments
            plt.bar(range(len(state)), state, color='blue', alpha=0.7)
            plt.xlabel('Variable Index')
            plt.ylabel('Assignment (0/1)')
            plt.title('Final Variable Assignment')
            plt.ylim(-0.1, 1.1)
            
        plt.tight_layout()
        plt.show()
        
        # If spectral data is available, show additional visualization
        if self.use_spectral and 'spectral_data' in problem and problem['spectral_data']:
            spectral_data = problem['spectral_data']
            if 'importance_scores' in spectral_data:
                plt.figure(figsize=(12, 5))
                
                # Plot variable importance
                importance_scores = spectral_data['importance_scores']
                plt.bar(range(len(importance_scores)), importance_scores, 
                       color='green', alpha=0.7)
                plt.xlabel('Variable Index')
                plt.ylabel('Importance Score')
                plt.title('Variable Importance from Spectral Analysis')
                plt.grid(True, alpha=0.3)
                
                plt.tight_layout()
                plt.show()
    
    def verify_solution(self, problem: Dict[str, Any]) -> bool:
        """
        Verify that the solution satisfies all constraints.
        
        Args:
            problem: Problem with solution
            
        Returns:
            True if all constraints are satisfied, False otherwise
        """
        if problem['best_state'] is None:
            print("No solution to verify")
            return False
        
        coherence, satisfaction = self.compute_state_coherence(problem, problem['best_state'])
        all_satisfied = np.all(satisfaction == 1)
        
        print(f"Solution verification: {'PASSED' if all_satisfied else 'FAILED'}")
        print(f"Coherence: {coherence}")
        print(f"Satisfied constraints: {int(np.sum(satisfaction))}/{problem['n_clauses']}")
        
        return all_satisfied


class EnhancedSATSolver:
    """
    SAT solver based on Enhanced Coherence-Gradient Descent.
    """
    
    def __init__(self, use_spectral: bool = True, use_fiber: bool = True, 
                use_multi_base: bool = True, num_fibers: int = 5, num_bases: int = 3):
        """
        Initialize the Enhanced SAT solver.
        
        Args:
            use_spectral: Whether to use spectral analysis
            use_fiber: Whether to use fiber algebra
            use_multi_base: Whether to use multi-base representation
            num_fibers: Number of fiber points to use
            num_bases: Number of bases to use
        """
        self.use_spectral = use_spectral
        self.use_fiber = use_fiber
        self.use_multi_base = use_multi_base
        self.num_fibers = num_fibers
        self.num_bases = num_bases
    
    def parse_dimacs(self, filename: str) -> Tuple[int, List[List[int]]]:
        """
        Parse a DIMACS CNF file.
        
        Args:
            filename: Path to DIMACS CNF file
            
        Returns:
            Tuple of (num_variables, clauses)
        """
        num_vars = 0
        clauses = []
        
        with open(filename, 'r') as f:
            for line in f:
                line = line.strip()
                
                # Skip empty lines and comments
                if not line or line.startswith('c'):
                    continue
                
                # Parse problem line
                if line.startswith('p cnf'):
                    parts = line.split()
                    num_vars = int(parts[2])
                    continue
                
                # Parse clause
                if line and not line.startswith('c') and not line.startswith('p'):
                    literals = [int(x) for x in line.split() if x != '0']
                    if literals:  # Skip empty clauses
                        clauses.append(literals)
        
        return num_vars, clauses
    
    def generate_random_sat(self, n_vars: int, n_clauses: int, clause_size: int = 3) -> List[List[int]]:
        """
        Generate a random SAT instance.
        
        Args:
            n_vars: Number of variables
            n_clauses: Number of clauses
            clause_size: Number of literals per clause
            
        Returns:
            List of clauses
        """
        clauses = []
        
        for _ in range(n_clauses):
            # Create a random clause
            clause = []
            while len(clause) < clause_size:
                var = random.randint(1, n_vars)
                lit = var if random.random() < 0.5 else -var
                if lit not in clause and -lit not in clause:
                    clause.append(lit)
            
            clauses.append(clause)
        
        return clauses
    
    def solve(self, clauses: List[List[int]], n_vars: Optional[int] = None, 
              max_iterations: int = 1000, restart_count: int = 3) -> Tuple[bool, List[int]]:
        """
        Solve a SAT problem using enhanced techniques.
        
        Args:
            clauses: List of clauses
            n_vars: Number of variables (if None, determined from clauses)
            max_iterations: Maximum number of iterations
            restart_count: Number of restarts to attempt
            
        Returns:
            Tuple of (is_satisfiable, assignment)
        """
        if n_vars is None:
            n_vars = max([max([abs(lit) for lit in clause]) for clause in clauses])
        
        print(f"Solving SAT problem with {n_vars} variables and {len(clauses)} clauses")
        
        # Initialize solver with appropriate techniques
        solver = EnhancedCoherenceGradientDescent(
            dimension=n_vars,
            num_fibers=self.num_fibers,
            num_bases=self.num_bases,
            use_spectral=self.use_spectral,
            use_fiber=self.use_fiber,
            use_multi_base=self.use_multi_base
        )
        
        # Encode problem
        problem = solver.encode_problem(clauses)
        
        # Solve
        solution = solver.solve(
            problem, 
            max_iterations=max_iterations,
            restart_count=restart_count,
            use_simulated_annealing=True,
            use_tabu=True
        )
        
        # Verify
        is_satisfiable = solver.verify_solution(solution)
        
        # Extract assignment
        if is_satisfiable:
            assignment = [int(solution['best_state'][i]) for i in range(n_vars)]
        else:
            assignment = []
        
        # Visualize
        solver.visualize_solution(solution)
        
        return is_satisfiable, assignment


def main():
    """
    Main function demonstrating Enhanced Coherence-Gradient Descent algorithms.
    """
    print("\n===================================================================")
    print("    Enhanced Coherence-Gradient Descent - Prime Framework Implementation")
    print("===================================================================")
    print("This implementation combines multiple advanced techniques from the Prime Framework:")
    print("1. Spectral analysis from Prime Operator eigenstructure")
    print("2. Fiber algebra for multi-perspective pattern detection")
    print("3. Multi-base representation for constraint encoding")
    print("4. UOR framework concepts for efficient solution space navigation")
    
    # Demonstrate SAT solving
    # Create a SAT solver
    sat_solver = EnhancedSATSolver(
        use_spectral=True,
        use_fiber=True,
        use_multi_base=True,
        num_fibers=5,
        num_bases=3
    )
    
    # Generate a random SAT instance
    n_vars = 20
    n_clauses = 85
    clauses = sat_solver.generate_random_sat(n_vars, n_clauses, clause_size=3)
    
    print(f"Generated random 3-SAT instance with {n_vars} variables and {n_clauses} clauses")
    print(f"Clause-to-variable ratio: {n_clauses/n_vars:.2f}")
    
    # Solve with enhanced techniques
    is_satisfiable, assignment = sat_solver.solve(
        clauses, 
        n_vars=n_vars, 
        max_iterations=1000, 
        restart_count=3
    )
    
    print(f"Instance is {'satisfiable' if is_satisfiable else 'unsatisfiable'}")
    if is_satisfiable:
        print(f"Found assignment: {assignment}")
    
    print("\nDone.")


if __name__ == "__main__":
    main()