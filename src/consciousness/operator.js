/**
 * Consciousness Operator - Spectral representation of mental states
 *
 * This module implements a mathematical operator for consciousness states
 * using spectral decomposition and eigenspace mapping techniques.
 *
 * Key features:
 * - Represents mental states as points in a high-dimensional manifold
 * - Uses spectral decomposition to identify principal components of awareness
 * - Calculates coherence metrics between different states
 * - Supports integration across different eigenspaces
 */

// Try to import core if available
let Prime;
try {
  Prime = require('../core.js');
} catch (e) {
  // Handle case where core isn't available yet
  Prime = {};
}

// Import required modules
const { Manifold } = require('../framework/base0/manifold.js');
const MathUtils = require('../framework/math/index.js');

/**
 * ConsciousnessOperator class provides the mathematical foundations for
 * representing and transforming consciousness states.
 */
class ConsciousnessOperator {
  /**
   * Create a new consciousness operator
   *
   * @param {Object} options - Configuration options
   * @param {number} options.dimension - Dimension of the consciousness space (default: 7)
   * @param {boolean} options.useSpectralDecomposition - Whether to use spectral decomposition (default: true)
   * @param {number} options.eigenspaceOrder - Order of eigenspace mapping (default: 3)
   * @param {Array} options.eigenvalues - Custom eigenvalues (default: automatically generated)
   * @param {Function} options.coherenceMetric - Custom coherence metric (default: built-in metric)
   */
  constructor(options = {}) {
    this.dimension = options.dimension || 7;
    this.useSpectralDecomposition = options.useSpectralDecomposition !== false;
    this.eigenspaceOrder = options.eigenspaceOrder || 3;

    // Initialize eigenspace
    this.eigenvalues = options.eigenvalues || this._generateEigenvalues();
    this.eigenvectors = this._generateEigenvectors();

    // Custom coherence metric
    this.coherenceMetric =
      options.coherenceMetric || this._defaultCoherenceMetric;

    // State transformation cache
    this._transformCache = new Map();
    this._coherenceCache = new Map();

    // Initialize operator statistics
    this._stats = {
      applications: 0,
      coherenceChecks: 0,
      cacheHits: 0,
      timeSpent: 0,
    };
  }

  /**
   * Generate eigenvalues for the consciousness operator
   *
   * @private
   * @returns {Array} Array of eigenvalues
   */
  _generateEigenvalues() {
    // Generate decreasing eigenvalues with specific pattern
    // - Larger gaps between first few eigenvalues
    // - Smaller gaps between later eigenvalues
    const values = [];

    // First eigenvalue (highest)
    values.push(1.0);

    // Generate remaining eigenvalues with decreasing pattern
    for (let i = 1; i < this.dimension; i++) {
      // Quadratic decrease pattern
      const value = 1.0 / (1 + i * i);
      values.push(value);
    }

    return values;
  }

  /**
   * Generate eigenvectors for the consciousness operator
   *
   * @private
   * @returns {Array} Array of eigenvectors
   */
  _generateEigenvectors() {
    // Create orthogonal basis vectors
    const vectors = [];

    for (let i = 0; i < this.dimension; i++) {
      // Create vector with 1 at position i, 0 elsewhere
      const vector = new Array(this.dimension).fill(0);
      vector[i] = 1;
      vectors.push(vector);
    }

    return vectors;
  }

  /**
   * Default coherence metric between consciousness states
   *
   * @private
   * @param {Array} state1 - First consciousness state
   * @param {Array} state2 - Second consciousness state
   * @returns {number} Coherence value (0-1)
   */
  _defaultCoherenceMetric(state1, state2) {
    if (
      !state1 ||
      !state2 ||
      !Array.isArray(state1) ||
      !Array.isArray(state2)
    ) {
      return 0;
    }

    const minLength = Math.min(state1.length, state2.length);

    if (minLength === 0) {
      return 0;
    }

    // Calculate dot product
    let dotProduct = 0;
    let magnitude1 = 0;
    let magnitude2 = 0;

    for (let i = 0; i < minLength; i++) {
      dotProduct += state1[i] * state2[i];
      magnitude1 += state1[i] * state1[i];
      magnitude2 += state2[i] * state2[i];
    }

    // Normalize by magnitudes to get cosine similarity
    const magnitudeFactor = Math.sqrt(magnitude1 * magnitude2);

    if (magnitudeFactor < 1e-10) {
      return 0;
    }

    // Convert from -1,1 to 0,1 range
    return (dotProduct / magnitudeFactor + 1) / 2;
  }

  /**
   * Apply the consciousness operator to a state
   *
   * @param {Object} state - Consciousness state to transform
   * @returns {Object} Transformed consciousness state
   */
  apply(state) {
    const startTime = Date.now();
    this._stats.applications++;

    // Generate a state ID for caching
    const stateId = this._getStateId(state);

    // Check cache
    if (this._transformCache.has(stateId)) {
      this._stats.cacheHits++;
      const cachedResult = this._transformCache.get(stateId);
      this._stats.timeSpent += Date.now() - startTime;
      return cachedResult;
    }

    // Create a deep copy of the state to avoid modifying the original
    const stateCopy = this._deepCopyState(state);

    // Extract the vector representation
    let vector = this._extractStateVector(stateCopy);

    // Apply spectral transformation if enabled
    if (this.useSpectralDecomposition) {
      vector = this._applySpectralTransformation(vector);
    }

    // Update the state with transformed vector
    const transformedState = this._updateStateWithVector(stateCopy, vector);

    // Add consciousness metrics
    transformedState._consciousness = {
      complexity: this.computeComplexity(transformedState),
      coherence: this.computeCoherence(transformedState, state),
      eigenspaceProjection: this._computeEigenspaceProjection(vector),
      timestamp: Date.now(),
    };

    // Cache the result
    this._transformCache.set(stateId, transformedState);

    // Update stats
    this._stats.timeSpent += Date.now() - startTime;

    return transformedState;
  }

  /**
   * Extract state vector from a consciousness state object
   *
   * @private
   * @param {Object} state - Consciousness state
   * @returns {Array} Vector representation
   */
  _extractStateVector(state) {
    // If state is already an array, return a copy
    if (Array.isArray(state)) {
      return [...state];
    }

    // If state has a vector property, use it
    if (state.vector && Array.isArray(state.vector)) {
      return [...state.vector];
    }

    // If state has a manifold property with coordinates, use it
    if (state.manifold && Array.isArray(state.manifold.coordinates)) {
      return [...state.manifold.coordinates];
    }

    // Create vector from state properties
    const vector = new Array(this.dimension).fill(0);

    // Fill vector with available state attributes
    if (state.attention && typeof state.attention === 'number') {
      vector[0] = Math.min(1, Math.max(0, state.attention));
    }

    if (state.awareness && typeof state.awareness === 'number') {
      vector[1] = Math.min(1, Math.max(0, state.awareness));
    }

    if (state.coherence && typeof state.coherence === 'number') {
      vector[2] = Math.min(1, Math.max(0, state.coherence));
    }

    if (state.integration && typeof state.integration === 'number') {
      vector[3] = Math.min(1, Math.max(0, state.integration));
    }

    if (state.differentiation && typeof state.differentiation === 'number') {
      vector[4] = Math.min(1, Math.max(0, state.differentiation));
    }

    if (state.selfReference && typeof state.selfReference === 'number') {
      vector[5] = Math.min(1, Math.max(0, state.selfReference));
    }

    if (state.temporalBinding && typeof state.temporalBinding === 'number') {
      vector[6] = Math.min(1, Math.max(0, state.temporalBinding));
    }

    // If we have extra dimensions, fill them with values from state.attributes if available
    if (
      this.dimension > 7 &&
      state.attributes &&
      typeof state.attributes === 'object'
    ) {
      const attributeKeys = Object.keys(state.attributes);
      for (let i = 7; i < this.dimension && i - 7 < attributeKeys.length; i++) {
        const value = state.attributes[attributeKeys[i - 7]];
        if (typeof value === 'number') {
          vector[i] = Math.min(1, Math.max(0, value));
        }
      }
    }

    return vector;
  }

  /**
   * Apply spectral transformation to a state vector
   *
   * @private
   * @param {Array} vector - State vector to transform
   * @returns {Array} Transformed vector
   */
  _applySpectralTransformation(vector) {
    // Project onto eigenspace
    const projections = this.eigenvectors.map((eigenvector, i) => {
      // Calculate projection onto this eigenvector
      let projection = 0;
      for (let j = 0; j < vector.length && j < eigenvector.length; j++) {
        projection += vector[j] * eigenvector[j];
      }

      // Scale by eigenvalue
      return projection * this.eigenvalues[i];
    });

    // Reconstruct vector from eigenspace
    const transformedVector = new Array(this.dimension).fill(0);

    for (let i = 0; i < this.dimension; i++) {
      for (
        let j = 0;
        j < projections.length && j < this.eigenvectors.length;
        j++
      ) {
        transformedVector[i] += projections[j] * this.eigenvectors[j][i];
      }
    }

    // Normalize
    const magnitude = Math.sqrt(
      transformedVector.reduce((sum, val) => sum + val * val, 0),
    );

    if (magnitude > 1e-10) {
      for (let i = 0; i < transformedVector.length; i++) {
        transformedVector[i] /= magnitude;
      }
    }

    return transformedVector;
  }

  /**
   * Update state object with transformed vector
   *
   * @private
   * @param {Object} state - State to update
   * @param {Array} vector - Transformed vector
   * @returns {Object} Updated state
   */
  _updateStateWithVector(state, vector) {
    // If state is an array, just return the vector
    if (Array.isArray(state)) {
      return vector;
    }

    // Create a deep copy for the result
    const result = this._deepCopyState(state);

    // Store the vector
    result.vector = vector;

    // Update state attributes from vector components
    if (vector.length > 0) result.attention = vector[0];
    if (vector.length > 1) result.awareness = vector[1];
    if (vector.length > 2) result.coherence = vector[2];
    if (vector.length > 3) result.integration = vector[3];
    if (vector.length > 4) result.differentiation = vector[4];
    if (vector.length > 5) result.selfReference = vector[5];
    if (vector.length > 6) result.temporalBinding = vector[6];

    // Update additional attributes if present
    if (result.attributes && typeof result.attributes === 'object') {
      const attributeKeys = Object.keys(result.attributes);
      for (let i = 7; i < vector.length && i - 7 < attributeKeys.length; i++) {
        result.attributes[attributeKeys[i - 7]] = vector[i];
      }
    }

    // Update manifold coordinates if present
    if (result.manifold && Array.isArray(result.manifold.coordinates)) {
      const copyLength = Math.min(
        vector.length,
        result.manifold.coordinates.length,
      );
      for (let i = 0; i < copyLength; i++) {
        result.manifold.coordinates[i] = vector[i];
      }
    }

    return result;
  }

  /**
   * Calculate eigenspace projection metrics
   *
   * @private
   * @param {Array} vector - State vector
   * @returns {Object} Projection metrics
   */
  _computeEigenspaceProjection(vector) {
    const projections = this.eigenvectors.map((eigenvector, i) => {
      // Calculate projection onto this eigenvector
      let projection = 0;
      for (let j = 0; j < vector.length && j < eigenvector.length; j++) {
        projection += vector[j] * eigenvector[j];
      }

      return {
        eigenvalue: this.eigenvalues[i],
        magnitude: Math.abs(projection),
        contribution: Math.pow(projection, 2),
      };
    });

    // Calculate total squared projections
    const totalContribution = projections.reduce(
      (sum, p) => sum + p.contribution,
      0,
    );

    // Normalize contributions if possible
    if (totalContribution > 1e-10) {
      projections.forEach((p) => {
        p.normalizedContribution = p.contribution / totalContribution;
      });
    } else {
      projections.forEach((p) => {
        p.normalizedContribution = 0;
      });
    }

    // Sort by contribution (highest first)
    projections.sort(
      (a, b) => b.normalizedContribution - a.normalizedContribution,
    );

    // Calculate participation ratio (effective dimensionality)
    const participationRatio =
      totalContribution > 1e-10
        ? 1 /
          projections.reduce(
            (sum, p) => sum + Math.pow(p.normalizedContribution, 2),
            0,
          )
        : 0;

    return {
      projections: projections.slice(0, this.eigenspaceOrder),
      participationRatio,
      dominantMode: projections[0]?.normalizedContribution || 0,
      timeScale: this._calculateTimeScale(projections),
    };
  }

  /**
   * Calculate characteristic time scale from eigenvalue spectrum
   *
   * @private
   * @param {Array} projections - Eigenspace projections
   * @returns {number} Characteristic time scale
   */
  _calculateTimeScale(projections) {
    // Weight eigenvalues by their contributions
    let weightedSum = 0;
    let totalWeight = 0;

    for (const p of projections) {
      if (p.eigenvalue > 1e-10) {
        const weight = p.normalizedContribution;
        weightedSum += weight * (1 / p.eigenvalue);
        totalWeight += weight;
      }
    }

    // Characteristic time scale
    return totalWeight > 1e-10 ? weightedSum / totalWeight : 1.0;
  }

  /**
   * Compute complexity of a consciousness state
   *
   * @param {Object} state - Consciousness state
   * @returns {number} Complexity value (0-1)
   */
  computeComplexity(state) {
    // Extract vector representation
    const vector = this._extractStateVector(state);

    // Compute eigenspace projection
    const projection = this._computeEigenspaceProjection(vector);

    // Complexity is related to participation ratio
    // Normalized to 0-1 range (assuming dimension as maximum)
    const normalizedPR = projection.participationRatio / this.dimension;

    // Adjust to favor intermediate complexity (neither too simple nor too complex)
    // Peak complexity at ~1/3 of the dimension
    const complexityFactor = 3 * normalizedPR * (1 - normalizedPR);

    // Combine with dominant mode contribution (inverse relationship)
    const dominanceFactor = 1 - projection.dominantMode;

    return 0.7 * complexityFactor + 0.3 * dominanceFactor;
  }

  /**
   * Compute coherence between two consciousness states
   *
   * @param {Object} state1 - First consciousness state
   * @param {Object} state2 - Second consciousness state
   * @returns {number} Coherence value (0-1)
   */
  computeCoherence(state1, state2) {
    this._stats.coherenceChecks++;

    // Generate cache ID
    const id1 = this._getStateId(state1);
    const id2 = this._getStateId(state2);
    const cacheId = `${id1}_${id2}`;

    // Check cache
    if (this._coherenceCache.has(cacheId)) {
      this._stats.cacheHits++;
      return this._coherenceCache.get(cacheId);
    }

    // Extract vector representations
    const vector1 = this._extractStateVector(state1);
    const vector2 = this._extractStateVector(state2);

    // Calculate coherence using metric
    const coherence = this.coherenceMetric(vector1, vector2);

    // Cache result
    this._coherenceCache.set(cacheId, coherence);

    return coherence;
  }

  /**
   * Get system-wide coherence of a set of states
   *
   * @param {Array} states - Array of consciousness states
   * @returns {Object} System coherence metrics
   */
  computeSystemCoherence(states) {
    if (!Array.isArray(states) || states.length === 0) {
      return {
        globalCoherence: 0,
        averagePairwise: 0,
        minPairwise: 1,
        maxPairwise: 0,
        integratedInformation: 0,
      };
    }

    // Calculate pairwise coherence between all states
    const pairwiseCoherences = [];

    for (let i = 0; i < states.length; i++) {
      for (let j = i + 1; j < states.length; j++) {
        const coherence = this.computeCoherence(states[i], states[j]);
        pairwiseCoherences.push(coherence);
      }
    }

    if (pairwiseCoherences.length === 0) {
      return {
        globalCoherence: 0,
        averagePairwise: 0,
        minPairwise: 1,
        maxPairwise: 0,
        integratedInformation: 0,
      };
    }

    // Calculate statistics
    const averagePairwise =
      pairwiseCoherences.reduce((sum, c) => sum + c, 0) /
      pairwiseCoherences.length;
    const minPairwise = Math.min(...pairwiseCoherences);
    const maxPairwise = Math.max(...pairwiseCoherences);

    // Calculate global coherence as weighted average of pairwise coherences
    // Gives more weight to more coherent pairs
    const weightedSum = pairwiseCoherences.reduce((sum, c) => sum + c * c, 0);
    const globalCoherence =
      weightedSum / pairwiseCoherences.reduce((sum, c) => sum + Math.abs(c), 0);

    // Calculate a basic approximation of integrated information (Φ)
    // In a real system this would use proper IIT calculations
    const stateVectors = states.map((state) => this._extractStateVector(state));
    const integratedInformation =
      this._approximateIntegratedInformation(stateVectors);

    return {
      globalCoherence,
      averagePairwise,
      minPairwise,
      maxPairwise,
      integratedInformation,
    };
  }

  /**
   * Approximate integrated information for a set of state vectors
   *
   * @private
   * @param {Array} vectors - Array of state vectors
   * @returns {number} Phi value
   */
  _approximateIntegratedInformation(vectors) {
    if (vectors.length < 2) return 0;

    // Calculate average vector
    const avgVector = new Array(this.dimension).fill(0);

    for (const vector of vectors) {
      for (let i = 0; i < this.dimension && i < vector.length; i++) {
        avgVector[i] += vector[i] / vectors.length;
      }
    }

    // Calculate variance from average
    let totalVariance = 0;

    for (const vector of vectors) {
      for (let i = 0; i < this.dimension && i < vector.length; i++) {
        totalVariance += Math.pow(vector[i] - avgVector[i], 2);
      }
    }

    totalVariance /= vectors.length;

    // Calculate divergence between pairs
    let totalDivergence = 0;
    let pairCount = 0;

    for (let i = 0; i < vectors.length; i++) {
      for (let j = i + 1; j < vectors.length; j++) {
        let divergence = 0;
        const minLength = Math.min(vectors[i].length, vectors[j].length);

        for (let k = 0; k < minLength && k < this.dimension; k++) {
          divergence += Math.pow(vectors[i][k] - vectors[j][k], 2);
        }

        totalDivergence += Math.sqrt(divergence);
        pairCount++;
      }
    }

    const avgDivergence = pairCount > 0 ? totalDivergence / pairCount : 0;

    // Phi is proportional to variance but inversely related to divergence
    // Higher variance with lower divergence suggests integrated information
    return pairCount > 0
      ? Math.min(1, Math.max(0, totalVariance / (avgDivergence + 0.01)))
      : 0;
  }

  /**
   * Generate a unique ID for a state
   *
   * @private
   * @param {Object} state - Consciousness state
   * @returns {string} State ID
   */
  _getStateId(state) {
    if (!state) return 'null';

    if (state._id) return state._id;

    // Extract vector and create hash from it
    const vector = this._extractStateVector(state);

    // Create a simple hash
    const hash = vector
      .reduce((h, v, i) => h + Math.round(v * 1000) * (i + 1), 0)
      .toString(36);

    return hash;
  }

  /**
   * Create a deep copy of a state
   *
   * @private
   * @param {Object} state - Consciousness state
   * @returns {Object} Copy of state
   */
  _deepCopyState(state) {
    if (!state) return null;

    if (Array.isArray(state)) {
      return [...state];
    }

    return JSON.parse(JSON.stringify(state));
  }

  /**
   * Custom coherence metric function
   *
   * @param {Function} metricFn - Custom coherence metric function
   */
  setCoherenceMetric(metricFn) {
    if (typeof metricFn !== 'function') {
      throw new Error('Coherence metric must be a function');
    }

    this.coherenceMetric = metricFn;
    this._coherenceCache.clear();
  }

  /**
   * Get operator statistics
   *
   * @returns {Object} Operator statistics
   */
  getStats() {
    const averageTime =
      this._stats.applications > 0
        ? this._stats.timeSpent / this._stats.applications
        : 0;

    const cacheEfficiency =
      this._stats.applications + this._stats.coherenceChecks > 0
        ? this._stats.cacheHits /
          (this._stats.applications + this._stats.coherenceChecks)
        : 0;

    return {
      ...this._stats,
      averageTime,
      cacheEfficiency,
    };
  }

  /**
   * Reset operator statistics
   */
  resetStats() {
    this._stats = {
      applications: 0,
      coherenceChecks: 0,
      cacheHits: 0,
      timeSpent: 0,
    };
  }

  /**
   * Clear transformation and coherence caches
   */
  clearCaches() {
    this._transformCache.clear();
    this._coherenceCache.clear();
  }
}

module.exports = ConsciousnessOperator;
