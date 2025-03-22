/**
 * Coherence-gradient descent algorithm implementation for the Prime Framework
 * Based on multi-perspective optimization using fiber algebra
 */

// Import core if available
let Prime;
try {
  Prime = require("../../core.js");
} catch (e) {
  // Handle case where core isn't available yet
  Prime = {};
}

// Try to import math utilities
let mathUtils;
try {
  mathUtils = require("./index.js");
} catch (e) {
  // Create minimal placeholder if not available
  mathUtils = {
    optimization: {
      gradientDescent: () => {
        throw new Error("Math utilities not available");
      },
    },
  };
}

/**
 * Clifford Algebra implementation for multi-dimensional space modeling
 */
class CliffordAlgebraFiber {
  /**
   * Create a new Clifford Algebra fiber
   *
   * @param {Object} options - Configuration options
   * @param {number} options.dimension - Dimension of the space (default: 3)
   * @param {Array} options.signature - Signature of the space (default: all positive)
   * @param {Array} options.position - Position in the reference manifold (default: origin)
   */
  constructor(options = {}) {
    this.dimension = options.dimension || 3;
    this.signature = options.signature || Array(this.dimension).fill(1);
    this.position = options.position || Array(3).fill(0); // Manifold position
    this.basis = this._generateBasis();
    this.innerProductMetric = this._initializeMetric();
    this.state = null;
    this.patterns = [];
  }

  /**
   * Generate basis elements for this algebra
   *
   * @private
   * @returns {Array} Array of basis element names
   */
  _generateBasis() {
    const basis = ["1"]; // Scalar basis

    // Generate all basis elements (2^dimension of them)
    for (let i = 1; i < 1 << this.dimension; i++) {
      let name = "";
      for (let j = 0; j < this.dimension; j++) {
        if (i & (1 << j)) {
          name += `e${j + 1}`;
        }
      }
      basis.push(name);
    }

    return basis;
  }

  /**
   * Initialize the inner product metric for this fiber
   * The metric varies based on position to create different perspectives
   *
   * @private
   * @returns {Array} Inner product matrix
   */
  _initializeMetric() {
    const n = this.basis.length;
    const metric = Array(n)
      .fill()
      .map(() => Array(n).fill(0));

    // Initialize diagonal elements based on signature
    for (let i = 0; i < n; i++) {
      metric[i][i] = 1; // Start with identity
    }

    // Vary the metric based on position in the manifold
    for (let i = 1; i < n; i++) {
      for (let j = 0; j < i; j++) {
        // Position-dependent correlation
        const correlation =
          0.1 *
          Math.cos(
            (Math.PI * this.position.reduce((sum, v) => sum + v, 0) * (i + j)) /
              n,
          );
        metric[i][j] = correlation;
        metric[j][i] = correlation;
      }
    }

    return metric;
  }

  /**
   * Get the grade of a basis element
   *
   * @param {string} element - Basis element name
   * @returns {number} Grade of the element
   */
  getGrade(element) {
    if (element === "1") return 0;

    // Count the number of vector basis elements in the product
    const matches = element.match(/e\d+/g);
    return matches ? matches.length : 0;
  }

  /**
   * Calculate the inner product of two elements
   *
   * @param {string} a - First basis element
   * @param {string} b - Second basis element
   * @returns {number} Inner product value
   */
  innerProduct(a, b) {
    const idxA = this.basis.indexOf(a);
    const idxB = this.basis.indexOf(b);

    if (idxA === -1 || idxB === -1) {
      throw new Error(`Basis elements not found: ${a}, ${b}`);
    }

    return this.innerProductMetric[idxA][idxB];
  }

  /**
   * Set the state vector for this fiber
   *
   * @param {Array} state - State vector in the Clifford algebra
   */
  setState(state) {
    if (!Array.isArray(state) || state.length !== this.basis.length) {
      throw new Error(`State vector must have length ${this.basis.length}`);
    }

    this.state = state.slice();
  }

  /**
   * Get the current state vector
   *
   * @returns {Array} Current state vector
   */
  getState() {
    return this.state ? this.state.slice() : null;
  }

  /**
   * Calculate the norm of a state vector using the inner product metric
   *
   * @param {Array} state - State vector
   * @returns {number} Norm value
   */
  calculateNorm(state) {
    if (!state) return 0;

    let norm = 0;
    for (let i = 0; i < state.length; i++) {
      for (let j = 0; j < state.length; j++) {
        norm += state[i] * this.innerProductMetric[i][j] * state[j];
      }
    }

    return Math.sqrt(Math.max(0, norm)); // Ensure non-negative
  }

  /**
   * Store a detected pattern
   *
   * @param {Object} pattern - Pattern object
   * @param {string} pattern.type - Type of pattern
   * @param {Array} pattern.components - Components involved in the pattern
   */
  addPattern(pattern) {
    this.patterns.push(pattern);
  }

  /**
   * Get all stored patterns
   *
   * @returns {Array} Array of pattern objects
   */
  getPatterns() {
    return this.patterns.slice();
  }
}

/**
 * Enhanced Coherence-Gradient Descent implementation based on the Prime Framework
 * Combines multi-view optimization with fiber algebra
 */
class CoherenceGradientDescent {
  /**
   * Create a new instance of coherence-gradient descent optimizer
   *
   * @param {Object} options - Configuration options
   * @param {number} options.dimension - Dimension of the problem space (default: 10)
   * @param {number} options.numFibers - Number of fiber points to use (default: 5)
   * @param {boolean} options.useSpectral - Whether to use spectral analysis (default: true)
   * @param {boolean} options.useFiber - Whether to use fiber algebra (default: true)
   */
  constructor(options = {}) {
    this.dimension = options.dimension || 10;
    this.numFibers = options.numFibers || 5;
    this.useSpectral = options.useSpectral !== false;
    this.useFiber = options.useFiber !== false;

    // Initialize the Clifford algebra structure
    this.maxGrade = Math.min(3, this.dimension); // Limit max grade for efficiency

    // Initialize the fiber manifold if enabled
    this.fibers = this.useFiber ? this._initializeFibers() : null;

    // Initialize generators for symmetry transformations
    this.symmetryGenerators = this._initializeSymmetryGenerators();

    // Caches for computation
    this._spectralCache = {};
    this._coherenceCache = {};
    this._patternCache = {};
  }

  /**
   * Initialize fiber algebras at different manifold points
   *
   * @private
   * @returns {Array} Array of fiber objects
   */
  _initializeFibers() {
    const fibers = [];

    // Create fiber points in a low-discrepancy sequence for better coverage
    const phi = (1 + Math.sqrt(5)) / 2; // Golden ratio for quasi-random sequence

    for (let i = 0; i < this.numFibers; i++) {
      // Create a position in the manifold using quasi-random sequence
      const pos = [
        (i * phi) % 1,
        (i * phi * phi) % 1,
        (i * phi * phi * phi) % 1,
      ];

      // Create a fiber at this point
      const fiber = new CliffordAlgebraFiber({
        dimension: this.dimension,
        position: pos,
      });

      fibers.push(fiber);
    }

    return fibers;
  }

  /**
   * Initialize generators for symmetry transformations
   *
   * @private
   * @returns {Array} Array of generator specifications
   */
  _initializeSymmetryGenerators() {
    const generators = [];

    // 1. Single bit flips (using vector basis elements)
    for (let i = 0; i < this.dimension; i++) {
      generators.push({
        type: "bit_flip",
        index: i,
        description: `Flip bit ${i}`,
      });
    }

    // 2. Bit swaps (using bivector basis elements)
    for (let i = 0; i < this.dimension - 1; i++) {
      for (let j = i + 1; j < this.dimension; j++) {
        generators.push({
          type: "bit_swap",
          indices: [i, j],
          description: `Swap bits ${i} and ${j}`,
        });
      }
    }

    // 3. Local cluster flips (acting on small groups of variables)
    const maxCluster = Math.min(5, this.dimension);
    for (let size = 2; size <= maxCluster; size++) {
      for (let start = 0; start <= this.dimension - size; start++) {
        const indices = Array(size)
          .fill()
          .map((_, i) => start + i);
        generators.push({
          type: "cluster_flip",
          indices,
          description: `Flip cluster ${JSON.stringify(indices)}`,
        });
      }
    }

    return generators;
  }

  /**
   * Apply a symmetry transformation to a state
   *
   * @param {Array} state - Current state vector
   * @param {number} generatorIdx - Index of the symmetry generator to apply
   * @returns {Array} Transformed state vector
   */
  applyTransformation(state, generatorIdx) {
    if (generatorIdx < 0 || generatorIdx >= this.symmetryGenerators.length) {
      throw new Error(`Invalid generator index: ${generatorIdx}`);
    }

    const generator = this.symmetryGenerators[generatorIdx];
    const newState = state.slice();

    switch (generator.type) {
      case "bit_flip":
        {
          const idx = generator.index;
          if (idx < state.length) {
            newState[idx] = 1 - newState[idx];
          }
        }
        break;

      case "bit_swap":
        {
          const [i, j] = generator.indices;
          if (i < state.length && j < state.length) {
            [newState[i], newState[j]] = [newState[j], newState[i]];
          }
        }
        break;

      case "cluster_flip":
        {
          for (const idx of generator.indices) {
            if (idx < state.length) {
              newState[idx] = 1 - newState[idx];
            }
          }
        }
        break;
    }

    return newState;
  }

  /**
   * Encode a problem for optimization
   *
   * @param {Object} problem - Problem specification
   * @param {Array} problem.constraints - Array of constraint functions
   * @param {Array} [problem.weights] - Optional weights for constraints
   * @param {Array} [problem.initialState] - Optional initial state
   * @returns {Object} Encoded problem
   */
  encodeProblem(problem) {
    const constraints = problem.constraints;
    if (!Array.isArray(constraints)) {
      throw new Error("Problem must have an array of constraints");
    }

    const n = problem.dimension || this.dimension;
    const encoded = {
      n_vars: n,
      n_constraints: constraints.length,
      constraints,
      weights: problem.weights || Array(constraints.length).fill(1),
      initialState:
        problem.initialState ||
        Array(n)
          .fill()
          .map(() => (Math.random() < 0.5 ? 0 : 1)),
      bestState: null,
      bestCoherence: Infinity,
    };

    // Create reference state (perfect coherence - all constraints satisfied)
    encoded.referenceState = Array(constraints.length).fill(1);

    // Add spectral analysis if enabled
    if (this.useSpectral) {
      encoded.spectralData = this._performSpectralAnalysis(encoded);
    }

    // Add fiber encodings if enabled
    if (this.useFiber && this.fibers) {
      encoded.fiberEncodings = this._createFiberEncodings(encoded);
    }

    return encoded;
  }

  /**
   * Perform spectral analysis on the problem structure
   * Identifies important variables and their relationships
   *
   * @private
   * @param {Object} problem - Encoded problem
   * @returns {Object} Spectral analysis data
   */
  _performSpectralAnalysis(problem) {
    // Create an approximation of variable interactions based on constraints
    const n = problem.n_vars;
    const adjacency = Array(n)
      .fill()
      .map(() => Array(n).fill(0));

    // For each constraint, track which variables interact
    for (let i = 0; i < problem.constraints.length; i++) {
      const constraint = problem.constraints[i];

      // This is an approximation - in a real system, we would analyze
      // the constraint function to determine which variables interact
      const involvedVars = this._identifyInvolvedVariables(constraint, n);

      for (let j = 0; j < involvedVars.length; j++) {
        for (let k = j + 1; k < involvedVars.length; k++) {
          const var1 = involvedVars[j];
          const var2 = involvedVars[k];
          adjacency[var1][var2] += 1;
          adjacency[var2][var1] += 1;
        }
      }
    }

    // Compute importance scores based on connectivity
    const importanceScores = Array(n).fill(0);
    for (let i = 0; i < n; i++) {
      importanceScores[i] = adjacency[i].reduce((sum, val) => sum + val, 0);
    }

    // Normalize importance scores
    const maxScore = Math.max(...importanceScores);
    if (maxScore > 0) {
      for (let i = 0; i < n; i++) {
        importanceScores[i] /= maxScore;
      }
    }

    // Identify clusters using a simple approach
    const clusters = this._identifyClusters(adjacency);

    return {
      adjacencyMatrix: adjacency,
      importanceScores,
      clusters,
    };
  }

  /**
   * Identify which variables are involved in a constraint (approximation)
   *
   * @private
   * @param {Function} constraint - Constraint function
   * @param {number} n - Number of variables
   * @returns {Array} Indices of involved variables
   */
  _identifyInvolvedVariables(constraint, n) {
    // This is an approximation - in a real system, we would analyze
    // the constraint function more thoroughly

    // For demo purposes, we'll use a random subset
    // In production, we'd determine this by analyzing the constraint function

    // Default to random subset
    const involved = [];
    const count = Math.max(2, Math.floor(n / 5));

    while (involved.length < count) {
      const idx = Math.floor(Math.random() * n);
      if (!involved.includes(idx)) {
        involved.push(idx);
      }
    }

    return involved;
  }

  /**
   * Identify variable clusters using a simple clustering algorithm
   *
   * @private
   * @param {Array} adjacency - Adjacency matrix
   * @returns {Array} Array of cluster assignments
   */
  _identifyClusters(adjacency) {
    const n = adjacency.length;

    // Very simple clustering - in production we'd use a more sophisticated approach
    const numClusters = Math.min(10, Math.max(2, Math.floor(n / 5)));
    const clusters = Array(n).fill(0);

    // Assign variables to clusters based on connectivity patterns
    for (let i = 0; i < n; i++) {
      // Find most connected variables
      const connections = adjacency[i].slice();

      // Assign to most connected cluster
      const clusterCounts = Array(numClusters).fill(0);

      for (let j = 0; j < n; j++) {
        if (i !== j && connections[j] > 0) {
          clusterCounts[clusters[j]] += connections[j];
        }
      }

      // Find cluster with most connections
      let bestCluster = 0;
      let maxConnections = -1;

      for (let c = 0; c < numClusters; c++) {
        if (clusterCounts[c] > maxConnections) {
          maxConnections = clusterCounts[c];
          bestCluster = c;
        }
      }

      clusters[i] = bestCluster;
    }

    return clusters;
  }

  /**
   * Create encodings of the problem for different fiber algebras
   * Each fiber provides a different perspective on the problem
   *
   * @private
   * @param {Object} problem - Encoded problem
   * @returns {Array} Array of fiber-specific encodings
   */
  _createFiberEncodings(problem) {
    if (!this.fibers) return null;

    const encodings = [];

    for (let i = 0; i < this.fibers.length; i++) {
      const fiber = this.fibers[i];

      // Create fiber-specific encoding
      const encoding = {
        fiberIndex: i,
        constraintWeights: problem.weights.slice(),
        variableWeights: Array(problem.n_vars).fill(1),
        referenceState: problem.referenceState.slice(),
      };

      // Modify weights based on position in fiber manifold
      const pos = fiber.position;

      // Vary constraint weights
      for (let j = 0; j < encoding.constraintWeights.length; j++) {
        const weight =
          1.0 +
          0.5 *
            Math.sin(
              (Math.PI * pos[0] * j) / encoding.constraintWeights.length,
            );
        encoding.constraintWeights[j] *= weight;
      }

      // Vary variable weights
      for (let j = 0; j < encoding.variableWeights.length; j++) {
        const weight =
          1.0 +
          0.3 *
            Math.cos((Math.PI * pos[1] * j) / encoding.variableWeights.length);
        encoding.variableWeights[j] *= weight;
      }

      encodings.push(encoding);
    }

    return encodings;
  }

  /**
   * Compute the coherence norm for a given state
   *
   * @param {Object} problem - Encoded problem
   * @param {Array} state - Current state
   * @returns {Object} Coherence norm and constraint satisfaction
   */
  computeStateCoherence(problem, state) {
    const n_constraints = problem.n_constraints;

    // Compute constraint satisfaction vector
    const satisfaction = Array(n_constraints).fill(0);
    for (let i = 0; i < n_constraints; i++) {
      const constraint = problem.constraints[i];
      satisfaction[i] = this._evaluateConstraint(constraint, state);
    }

    // Base coherence is the sum of unsatisfied constraints (weighted)
    let baseCoherence = 0;
    for (let i = 0; i < n_constraints; i++) {
      if (satisfaction[i] < 1) {
        baseCoherence += problem.weights[i] * (1 - satisfaction[i]);
      }
    }

    let coherence = baseCoherence;

    // Enhanced coherence calculation using different perspectives

    // 1. Spectral coherence component
    if (this.useSpectral && problem.spectralData) {
      const spectralCoherence = this._computeSpectralCoherence(
        problem,
        state,
        satisfaction,
      );
      coherence = 0.7 * coherence + 0.3 * spectralCoherence;
    }

    // 2. Fiber coherence component
    if (this.useFiber && problem.fiberEncodings) {
      const fiberCoherence = this._computeFiberCoherence(
        problem,
        state,
        satisfaction,
      );
      coherence = 0.7 * coherence + 0.3 * fiberCoherence;
    }

    return {
      coherence,
      satisfaction,
    };
  }

  /**
   * Evaluate a constraint (abstract method)
   *
   * @private
   * @param {Function} constraint - Constraint function
   * @param {Array} state - Current state
   * @returns {number} Satisfaction level (0-1)
   */
  _evaluateConstraint(constraint, state) {
    // In a real system, we'd call the constraint function
    if (typeof constraint === "function") {
      const result = constraint(state);
      // Normalize result to 0-1 range if it's not already
      return typeof result === "boolean"
        ? result
          ? 1
          : 0
        : Math.min(1, Math.max(0, result));
    }

    // For demo purposes, return a random value if constraint isn't a function
    return Math.random();
  }

  /**
   * Compute coherence component based on spectral analysis
   *
   * @private
   * @param {Object} problem - Encoded problem
   * @param {Array} state - Current state
   * @param {Array} satisfaction - Constraint satisfaction vector
   * @returns {number} Spectral coherence component
   */
  _computeSpectralCoherence(problem, state, satisfaction) {
    const spectralData = problem.spectralData;
    const importanceScores = spectralData.importanceScores;
    const clusters = spectralData.clusters;

    // Create cluster satisfaction metrics
    const clusterSatisfaction = {};

    for (let i = 0; i < problem.constraints.length; i++) {
      // Approximate which clusters this constraint involves
      const involved = this._identifyInvolvedVariables(
        problem.constraints[i],
        problem.n_vars,
      );
      const involvedClusters = new Set();

      for (const varIdx of involved) {
        if (varIdx < clusters.length) {
          involvedClusters.add(clusters[varIdx]);
        }
      }

      // Record satisfaction status for each involved cluster
      const isSatisfied = satisfaction[i] > 0.5;

      for (const clusterId of involvedClusters) {
        if (!clusterSatisfaction[clusterId]) {
          clusterSatisfaction[clusterId] = [];
        }
        clusterSatisfaction[clusterId].push(isSatisfied);
      }
    }

    // Calculate coherence based on cluster satisfaction
    let clusterCoherence = 0;

    for (const clusterId in clusterSatisfaction) {
      if (Object.hasOwnProperty.call(clusterSatisfaction, clusterId)) {
        const satisfactions = clusterSatisfaction[clusterId];
        if (satisfactions.length > 0) {
          // Higher penalty for clusters with mixed satisfaction status
          const satisfactionRate =
            satisfactions.filter(Boolean).length / satisfactions.length;
          // Penalty is higher when satisfaction rate is around 0.5 (most conflicted)
          const penalty = 4.0 * satisfactionRate * (1.0 - satisfactionRate);
          clusterCoherence += penalty;
        }
      }
    }

    // Normalize
    if (Object.keys(clusterSatisfaction).length > 0) {
      clusterCoherence /= Object.keys(clusterSatisfaction).length;
    }

    // Additional component based on important variables
    let importantVarCoherence = 0;

    for (let i = 0; i < problem.n_vars; i++) {
      // Check variables with high importance
      if (importanceScores[i] > 0.5) {
        // Compute contribution for this important variable
        const involvedConstraints = [];

        for (let j = 0; j < problem.constraints.length; j++) {
          const involved = this._identifyInvolvedVariables(
            problem.constraints[j],
            problem.n_vars,
          );
          if (involved.includes(i) && satisfaction[j] < 0.5) {
            involvedConstraints.push(j);
          }
        }

        if (involvedConstraints.length > 0) {
          importantVarCoherence +=
            importanceScores[i] * involvedConstraints.length;
        }
      }
    }

    // Normalize
    importantVarCoherence = Math.min(
      1.0,
      importantVarCoherence / problem.n_vars,
    );

    // Combine components
    const spectralCoherence =
      0.5 * clusterCoherence + 0.5 * importantVarCoherence;

    // Scale to match base coherence
    return spectralCoherence * satisfaction.length;
  }

  /**
   * Compute coherence component based on fiber algebra analysis
   *
   * @private
   * @param {Object} problem - Encoded problem
   * @param {Array} state - Current state
   * @param {Array} satisfaction - Constraint satisfaction vector
   * @returns {number} Fiber coherence component
   */
  _computeFiberCoherence(problem, state, satisfaction) {
    const fiberEncodings = problem.fiberEncodings;
    const fiberCoherences = [];

    for (const encoding of fiberEncodings) {
      // Get fiber-specific weights
      const constraintWeights = encoding.constraintWeights;

      // Calculate weighted unsatisfied count for this fiber
      let weightedCount = 0;
      for (let i = 0; i < satisfaction.length; i++) {
        weightedCount += (1 - satisfaction[i]) * constraintWeights[i];
      }

      fiberCoherences.push(weightedCount);
    }

    // Take average fiber coherence
    return fiberCoherences.length > 0
      ? fiberCoherences.reduce((sum, val) => sum + val, 0) /
          fiberCoherences.length
      : 0;
  }

  /**
   * Compute the gradient of the coherence norm with respect to symmetry transformations
   *
   * @param {Object} problem - Encoded problem
   * @param {Array} state - Current state
   * @returns {Array} Array of (generator index, coherence change) pairs
   */
  computeCoherenceGradient(problem, state) {
    const { coherence } = this.computeStateCoherence(problem, state);
    const gradient = [];

    // Use spectral data to prioritize generators if available
    const importantIndices = new Set();

    if (this.useSpectral && problem.spectralData) {
      const importanceScores = problem.spectralData.importanceScores;

      // Find top important variables
      const threshold = 0.5;
      for (let i = 0; i < importanceScores.length; i++) {
        if (importanceScores[i] > threshold) {
          importantIndices.add(i);
        }
      }
    }

    // Evaluate all transformations
    for (let i = 0; i < this.symmetryGenerators.length; i++) {
      const generator = this.symmetryGenerators[i];
      let isPriority = false;

      // Check if this generator affects important variables
      if (generator.type === "bit_flip") {
        isPriority = importantIndices.has(generator.index);
      } else if (generator.type === "bit_swap") {
        isPriority =
          importantIndices.has(generator.indices[0]) ||
          importantIndices.has(generator.indices[1]);
      } else if (generator.type === "cluster_flip") {
        isPriority = generator.indices.some((idx) => importantIndices.has(idx));
      }

      // Apply the transformation
      const newState = this.applyTransformation(state, i);
      const { coherence: newCoherence } = this.computeStateCoherence(
        problem,
        newState,
      );

      // Coherence change (negative means improvement)
      const coherenceChange = newCoherence - coherence;

      gradient.push({
        generatorIndex: i,
        coherenceChange,
        isPriority,
      });
    }

    // Sort by priority first, then by coherence change
    gradient.sort((a, b) => {
      if (a.isPriority !== b.isPriority) {
        return a.isPriority ? -1 : 1;
      }
      return a.coherenceChange - b.coherenceChange;
    });

    // Return simplified gradient with just index and change
    return gradient.map((g) => [g.generatorIndex, g.coherenceChange]);
  }

  /**
   * Add diversification to escape local minima
   *
   * @param {Object} problem - Encoded problem
   * @param {Array} state - Current state
   * @param {Array} previousStates - Previous visited states
   * @param {number} iteration - Current iteration
   * @returns {Array} Diversified state
   */
  diversifySearch(problem, state, previousStates, iteration) {
    // Determine if we should diversify based on stagnation
    let shouldDiversify = false;

    // Check if we've been in similar states before
    if (previousStates && previousStates.length > 0) {
      const similarities = previousStates.map((prevState) => {
        return (
          state.reduce(
            (count, val, i) => count + (val === prevState[i] ? 1 : 0),
            0,
          ) / state.length
        );
      });

      if (similarities.some((sim) => sim > 0.9)) {
        shouldDiversify = true;
      }
    }

    if (!shouldDiversify) {
      return state;
    }

    const newState = state.slice();

    // Choose diversification strategy based on iteration
    const strategy = iteration % 3;

    if (strategy === 0) {
      // Strong random perturbation
      const numToFlip = Math.max(1, Math.floor(state.length / 5));
      const positions = [];

      while (positions.length < numToFlip) {
        const pos = Math.floor(Math.random() * state.length);
        if (!positions.includes(pos)) {
          positions.push(pos);
        }
      }

      for (const pos of positions) {
        newState[pos] = 1 - newState[pos];
      }
    } else if (strategy === 1 && this.useSpectral && problem.spectralData) {
      // Flip variables in a spectral cluster
      const clusters = problem.spectralData.clusters;
      const uniqueClusters = [...new Set(clusters)];

      if (uniqueClusters.length > 0) {
        const targetCluster =
          uniqueClusters[Math.floor(Math.random() * uniqueClusters.length)];

        // Flip all variables in the target cluster
        for (let i = 0; i < newState.length; i++) {
          if (i < clusters.length && clusters[i] === targetCluster) {
            newState[i] = 1 - newState[i];
          }
        }
      }
    } else if (strategy === 2) {
      // Apply a random symmetry transformation
      const generatorIdx = Math.floor(
        Math.random() * this.symmetryGenerators.length,
      );
      return this.applyTransformation(state, generatorIdx);
    }

    return newState;
  }

  /**
   * Solve a problem using coherence-gradient descent
   *
   * @param {Object} problem - Encoded problem
   * @param {Object} options - Solver options
   * @param {number} [options.maxIterations=1000] - Maximum number of iterations
   * @param {boolean} [options.useSimulatedAnnealing=true] - Whether to use simulated annealing
   * @param {number} [options.temperature=1.0] - Initial temperature for annealing
   * @param {number} [options.restartCount=3] - Number of restarts to attempt
   * @param {boolean} [options.useTabu=true] - Whether to use tabu search
   * @param {number} [options.tabuListSize=10] - Size of tabu list
   * @returns {Object} Solution information
   */
  solve(problem, options = {}) {
    const maxIterations = options.maxIterations || 1000;
    const useSimulatedAnnealing = options.useSimulatedAnnealing !== false;
    const temperature = options.temperature || 1.0;
    const restartCount = options.restartCount || 3;
    const useTabu = options.useTabu !== false;
    const tabuListSize = options.tabuListSize || 10;

    // Initialize tracking
    let bestState = null;
    let bestCoherence = Infinity;
    let bestSatisfaction = null;

    // History tracking
    const history = {
      coherence: [],
      iterations: [],
      satisfiedConstraints: [],
    };

    // Run multiple restarts
    for (let restart = 0; restart < restartCount; restart++) {
      // Initialize state
      let currentState;

      if (restart === 0) {
        // First attempt uses the initial state from the problem
        currentState = problem.initialState ? problem.initialState.slice() : 
          Array(problem.dimension || problem.n_vars || 6).fill(0);
      } else {
        // Subsequent attempts use random initialization with spectral hints
        if (this.useSpectral && problem.spectralData) {
          const importanceScores = problem.spectralData.importanceScores;

          // Initialize random state but bias important variables
          currentState = Array(problem.dimension || problem.n_vars || 6)
            .fill()
            .map(() => (Math.random() < 0.5 ? 0 : 1));

          for (let i = 0; i < currentState.length; i++) {
            if (
              importanceScores && 
              i < importanceScores.length &&
              Math.random() < importanceScores[i]
            ) {
              // Higher chance to set important variables to previous best value
              if (bestState && i < bestState.length) {
                currentState[i] = bestState[i];
              }
            }
          }
        } else {
          // Completely random initialization
          currentState = Array(problem.dimension || problem.n_vars || 6)
            .fill()
            .map(() => (Math.random() < 0.5 ? 0 : 1));
        }
      }

      // Get initial coherence
      let currentCoherence, currentSatisfaction;
      try {
        const result = this.computeStateCoherence(problem, currentState);
        currentCoherence = result.coherence;
        currentSatisfaction = result.satisfaction;
      } catch (e) {
        // If coherence calculation fails, use a default value
        currentCoherence = problem.constraints ? problem.constraints.length : 10;
        currentSatisfaction = problem.constraints ? 
          Array(problem.constraints.length).fill(0) : [];
      }

      // Initialize tracking for this attempt
      let restartBestState = currentState.slice();
      let restartBestCoherence = currentCoherence;
      let restartBestSatisfaction = currentSatisfaction ? currentSatisfaction.slice() : [];

      // Initialize tabu list
      const tabuList = [];

      // Initialize previous states for diversification
      const previousStates = [];

      // Set up temperature for simulated annealing
      let currentTemp = temperature;
      const coolingRate = 0.99; // Temperature cooling rate

      // Iterations for this restart
      const restartIterations = Math.floor(maxIterations / restartCount);

      // Start search for this restart
      for (let iter = 0; iter < restartIterations; iter++) {
        // Add current state to previous states
        previousStates.push(currentState.slice());
        if (previousStates.length > 20) {
          previousStates.shift();
        }

        // Compute gradient
        let gradient;
        try {
          gradient = this.computeCoherenceGradient(problem, currentState);
        } catch (e) {
          // If gradient computation fails, create a random gradient
          gradient = Array(Math.min(10, this.symmetryGenerators.length))
            .fill()
            .map((_, i) => [i, Math.random() * 2 - 1]);
        }

        // Filter out tabu moves
        const filteredGradient = useTabu && tabuList.length > 0
          ? gradient.filter(([genIdx]) => !tabuList.includes(genIdx))
          : gradient;

        if (!filteredGradient || filteredGradient.length === 0) {
          // No valid moves, add diversification
          currentState = this.diversifySearch(
            problem,
            currentState,
            previousStates,
            iter,
          );

          try {
            const result = this.computeStateCoherence(problem, currentState);
            currentCoherence = result.coherence;
            currentSatisfaction = result.satisfaction;
          } catch (e) {
            // If coherence calculation fails, use a default value
            currentCoherence = restartBestCoherence;
            currentSatisfaction = restartBestSatisfaction;
          }

          continue;
        }

        // Decide which transformation to apply
        let generatorIdx, coherenceChange;

        if (useSimulatedAnnealing) {
          // Simulated annealing: sometimes accept worse solutions
          if (Math.random() < 0.8) {
            // Usually pick the best transformation
            [generatorIdx, coherenceChange] = filteredGradient[0];
          } else {
            // Sometimes randomly explore
            const randIdx = Math.floor(Math.random() * filteredGradient.length);
            [generatorIdx, coherenceChange] = filteredGradient[randIdx];
          }

          // Update temperature
          currentTemp *= coolingRate;
        } else {
          // Greedy: always choose the best transformation
          [generatorIdx, coherenceChange] = filteredGradient[0];
        }

        // Add to tabu list
        if (useTabu) {
          tabuList.push(generatorIdx);
          if (tabuList.length > tabuListSize) {
            tabuList.shift();
          }
        }

        // Apply chosen transformation
        try {
          currentState = this.applyTransformation(currentState, generatorIdx);
        } catch (e) {
          // If transformation fails, make a random change
          const idx = Math.floor(Math.random() * currentState.length);
          currentState[idx] = 1 - currentState[idx];
        }

        // Compute new coherence
        let coherence, satisfaction;
        try {
          const result = this.computeStateCoherence(problem, currentState);
          coherence = result.coherence;
          satisfaction = result.satisfaction;
        } catch (e) {
          // If coherence calculation fails, use previous values
          coherence = currentCoherence;
          satisfaction = currentSatisfaction;
        }

        // Update tracking
        if (coherence < restartBestCoherence) {
          restartBestState = currentState.slice();
          restartBestCoherence = coherence;
          restartBestSatisfaction = satisfaction ? satisfaction.slice() : [];
        }

        // Update current coherence
        currentCoherence = coherence;
        currentSatisfaction = satisfaction;

        // Diversify if needed (less frequently than in the Python version)
        if (iter % 50 === 0 && coherence > 0) {
          const diversifiedState = this.diversifySearch(
            problem,
            currentState,
            previousStates,
            iter,
          );

          // Only accept if it maintains or improves coherence
          let divCoherence;
          try {
            const result = this.computeStateCoherence(problem, diversifiedState);
            divCoherence = result.coherence;
          } catch (e) {
            divCoherence = coherence + 1; // Assume worse
          }

          if (divCoherence <= coherence) {
            currentState = diversifiedState;
            currentCoherence = divCoherence;
          }
        }

        // Update history
        history.coherence.push(coherence);
        history.iterations.push(restart * restartIterations + iter);
        if (satisfaction) {
          history.satisfiedConstraints.push(
            satisfaction.reduce((sum, val) => sum + (val > 0.5 ? 1 : 0), 0)
          );
        } else {
          history.satisfiedConstraints.push(0);
        }

        // Check for perfect solution
        if (coherence === 0) {
          break;
        }
      }

      // Update overall best solution
      if (restartBestCoherence < bestCoherence) {
        bestState = restartBestState.slice();
        bestCoherence = restartBestCoherence;
        bestSatisfaction = restartBestSatisfaction ? restartBestSatisfaction.slice() : [];
      }
    }

    // Update problem with solution
    problem.bestState = bestState;
    problem.bestCoherence = bestCoherence;
    problem.bestSatisfaction = bestSatisfaction ? bestSatisfaction.slice() : [];
    problem.history = history;

    return {
      minimum: bestState, // Add minimum property for compatibility
      state: bestState,
      coherence: bestCoherence,
      value: bestCoherence, // Add value property for compatibility
      satisfaction: bestSatisfaction,
      history,
      problem,
    };
  }
}

// Export the public API
module.exports = {
  CliffordAlgebraFiber,
  CoherenceGradientDescent,
};
