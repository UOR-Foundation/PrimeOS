/**
 * Temporal Integration - Framework for maintaining experiential continuity
 *
 * This module implements the temporal integration framework needed for consciousness
 * simulation, allowing experiences to maintain continuity over time.
 *
 * Key features:
 * - Maintains state history in temporal buffer
 * - Calculates temporal coherence metrics
 * - Implements windowed coherence calculation
 * - Provides integration across time scales
 */

// Try to import core if available
let Prime;
try {
  Prime = require("../core.js");
} catch (e) {
  // Handle case where core isn't available yet
  Prime = {};
}

/**
 * TemporalIntegration provides mechanisms for maintaining continuity of experience
 */
class TemporalIntegration {
  /**
   * Create a new temporal integration system
   *
   * @param {Object} options - Configuration options
   * @param {number} options.windowSize - Size of integration window (default: 10)
   * @param {number} options.shortTermCapacity - Capacity of short-term buffer (default: 100)
   * @param {number} options.longTermCapacity - Capacity of long-term buffer (default: 1000)
   * @param {number} options.decayRate - Rate of temporal decay (default: 0.05)
   * @param {number} options.integrationCoefficient - Strength of temporal integration (default: 0.7)
   */
  constructor(options = {}) {
    this.windowSize = options.windowSize || 10;
    this.shortTermCapacity = options.shortTermCapacity || 100;
    this.longTermCapacity = options.longTermCapacity || 1000;
    this.decayRate = options.decayRate || 0.05;
    this.integrationCoefficient = options.integrationCoefficient || 0.7;

    // Temporal buffers
    this.shortTermBuffer = [];
    this.longTermBuffer = [];
    this.significantStateBuffer = [];

    // Integration window (most recent states for integration)
    this.integrationWindow = [];

    // Time scales for integration
    this.timeScales = [
      { name: "immediate", span: 3, weight: 0.6 },
      { name: "recent", span: 10, weight: 0.3 },
      { name: "extended", span: 30, weight: 0.1 },
    ];

    // Internal state
    this._initialized = false;
    this._currentIntegration = null;
    this._lastUpdateTime = 0;

    // Performance tracking
    this._stats = {
      integrations: 0,
      skippedIntegrations: 0,
      significantStates: 0,
      totalIntegrationTime: 0,
    };
  }

  /**
   * Initialize the temporal integration system
   *
   * @param {Object} initialState - Initial state
   * @returns {boolean} Whether initialization was successful
   */
  initialize(initialState) {
    if (!initialState) {
      return false;
    }

    // Create deep copy of initial state
    const stateCopy = this._deepCopy(initialState);

    // Add temporal metadata
    const stateWithMetadata = this._addTemporalMetadata(stateCopy);

    // Store in all buffers
    this.shortTermBuffer = [stateWithMetadata];
    this.longTermBuffer = [this._createCompressedState(stateWithMetadata)];
    this.integrationWindow = [stateWithMetadata];
    this.significantStateBuffer = [];

    this._currentIntegration = stateWithMetadata;
    this._lastUpdateTime = Date.now();
    this._initialized = true;

    return true;
  }

  /**
   * Integrate a new state with temporal context
   *
   * @param {Object} newState - New state to integrate
   * @returns {Object} Temporally integrated state
   */
  integrate(newState) {
    if (!this._initialized) {
      this.initialize(newState);
      return this._deepCopy(newState);
    }

    const startTime = Date.now();

    // Create copy to avoid modifying original
    const stateCopy = this._deepCopy(newState);

    // Add temporal metadata
    const stateWithMetadata = this._addTemporalMetadata(stateCopy);

    // Check if this is a significant state that should be preserved
    const isSignificant = this._isSignificantState(stateWithMetadata);

    // Update buffers
    this._updateBuffers(stateWithMetadata, isSignificant);

    // Check if we should perform integration
    // (Throttle integration to avoid excessive computation)
    const timeSinceLastUpdate = Date.now() - this._lastUpdateTime;
    const shouldIntegrate =
      this.integrationWindow.length > 1 && timeSinceLastUpdate > 100;

    // Perform temporal integration
    let integratedState;

    if (shouldIntegrate) {
      this._stats.integrations++;
      this._lastUpdateTime = Date.now();

      // Perform multi-scale temporal integration
      integratedState = this._temporallyIntegrate(stateWithMetadata);

      // Update current integration
      this._currentIntegration = integratedState;
    } else {
      this._stats.skippedIntegrations++;

      // Use lightweight blending with previous integration
      integratedState = this._blendWithCurrentIntegration(stateWithMetadata);
    }

    // Update stats
    this._stats.totalIntegrationTime += Date.now() - startTime;

    return integratedState;
  }

  /**
   * Add temporal metadata to a state
   *
   * @private
   * @param {Object} state - State to enhance
   * @returns {Object} State with temporal metadata
   */
  _addTemporalMetadata(state) {
    // Add _temporal field if not present
    if (!state._temporal) {
      state._temporal = {};
    }

    // Update temporal metadata
    state._temporal = {
      ...state._temporal,
      timestamp: Date.now(),
      sequence: this.shortTermBuffer.length,
      integrated: false,
      significance: 0,
    };

    return state;
  }

  /**
   * Update all temporal buffers with a new state
   *
   * @private
   * @param {Object} state - State to add
   * @param {boolean} isSignificant - Whether state is significant
   */
  _updateBuffers(state, isSignificant) {
    // Update short-term buffer
    this.shortTermBuffer.push(state);

    // Trim short-term buffer if needed
    if (this.shortTermBuffer.length > this.shortTermCapacity) {
      this.shortTermBuffer.shift();
    }

    // Update integration window (moving window of recent states)
    this.integrationWindow.push(state);

    // Trim integration window to configured size
    if (this.integrationWindow.length > this.windowSize) {
      this.integrationWindow.shift();
    }

    // Update long-term buffer (compressed)
    // Only add every Nth state or significant states
    const longTermSamplingRate = Math.max(
      1,
      Math.floor(this.shortTermCapacity / 20),
    );
    if (
      isSignificant ||
      this.shortTermBuffer.length % longTermSamplingRate === 0
    ) {
      const compressedState = this._createCompressedState(state);
      this.longTermBuffer.push(compressedState);
    }

    // Trim long-term buffer if needed
    if (this.longTermBuffer.length > this.longTermCapacity) {
      this.longTermBuffer.shift();
    }

    // Update significant state buffer if needed
    if (isSignificant) {
      this._stats.significantStates++;
      this.significantStateBuffer.push(state);

      // Trim significant buffer to reasonable size
      const maxSignificantStates = Math.min(this.longTermCapacity, 100);
      if (this.significantStateBuffer.length > maxSignificantStates) {
        this.significantStateBuffer.shift();
      }
    }
  }

  /**
   * Check if a state is significant enough to preserve
   *
   * @private
   * @param {Object} state - State to check
   * @returns {boolean} Whether state is significant
   */
  _isSignificantState(state) {
    if (this.shortTermBuffer.length < 2) {
      return true; // First state is always significant
    }

    // Get previous state
    const previousState = this.shortTermBuffer[this.shortTermBuffer.length - 1];

    // Calculate significance based on change magnitude
    const changeMagnitude = this._calculateChangeMagnitude(
      previousState,
      state,
    );

    // Significant if change exceeds threshold
    const changeThreshold = 0.15;
    const isSignificantChange = changeMagnitude > changeThreshold;

    // Also flag states with high awareness or coherence as significant
    const highMeasures = state.awareness > 0.8 || state.coherence > 0.8;

    // Store significance value
    state._temporal.significance = Math.max(
      changeMagnitude,
      state.awareness || 0,
      state.coherence || 0,
    );

    return isSignificantChange || highMeasures;
  }

  /**
   * Calculate magnitude of change between states
   *
   * @private
   * @param {Object} state1 - First state
   * @param {Object} state2 - Second state
   * @returns {number} Change magnitude (0-1)
   */
  _calculateChangeMagnitude(state1, state2) {
    // Extract vectors
    const vec1 = this._extractStateVector(state1);
    const vec2 = this._extractStateVector(state2);

    // Calculate Euclidean distance
    let sumSquares = 0;
    const minLength = Math.min(vec1.length, vec2.length);

    for (let i = 0; i < minLength; i++) {
      sumSquares += Math.pow(vec1[i] - vec2[i], 2);
    }

    // Normalize to 0-1 range (assuming max distance of sqrt(n) in n-dimensional space)
    const maxDistance = Math.sqrt(minLength);
    return Math.min(1, Math.sqrt(sumSquares) / maxDistance);
  }

  /**
   * Create compressed version of a state for long-term storage
   *
   * @private
   * @param {Object} state - State to compress
   * @returns {Object} Compressed state
   */
  _createCompressedState(state) {
    // Extract essential information only
    const vector = this._extractStateVector(state);

    // Create minimal representation
    return {
      vector,
      _temporal: {
        timestamp: state._temporal.timestamp,
        sequence: state._temporal.sequence,
        significance: state._temporal.significance || 0,
      },
    };
  }

  /**
   * Extract vector representation of a state
   *
   * @private
   * @param {Object} state - State to extract from
   * @returns {Array} Vector representation
   */
  _extractStateVector(state) {
    // Use vector if available
    if (state.vector && Array.isArray(state.vector)) {
      return [...state.vector];
    }

    // Otherwise construct from properties
    const vector = [];

    // Add common properties
    for (const prop of [
      "attention",
      "awareness",
      "coherence",
      "integration",
      "differentiation",
      "selfReference",
      "temporalBinding",
    ]) {
      if (typeof state[prop] === "number") {
        vector.push(state[prop]);
      } else {
        vector.push(0);
      }
    }

    return vector;
  }

  /**
   * Perform full temporal integration across multiple time scales
   *
   * @private
   * @param {Object} currentState - Current state to integrate
   * @returns {Object} Integrated state
   */
  _temporallyIntegrate(currentState) {
    // Create copy as base for integration
    const integrated = this._deepCopy(currentState);

    // Get vectors from different time scales
    const timeScaleVectors = this._getTimeScaleVectors();

    // Extract current vector
    const currentVector = this._extractStateVector(currentState);

    // Combine vectors from all time scales
    const combinedVector = this._combineTimeScaleVectors(
      currentVector,
      timeScaleVectors,
    );

    // Update state with combined vector
    this._updateStateWithVector(integrated, combinedVector);

    // Mark as integrated
    integrated._temporal.integrated = true;
    integrated._temporal.integrationTimestamp = Date.now();
    integrated._temporal.timeScales = this.timeScales.map((ts) => ts.name);

    // Add temporal binding measure
    integrated.temporalBinding =
      this._calculateTemporalBinding(timeScaleVectors);

    return integrated;
  }

  /**
   * Get vector representations for different time scales
   *
   * @private
   * @returns {Object} Vectors for each time scale
   */
  _getTimeScaleVectors() {
    const result = {};

    // Process each time scale
    for (const timeScale of this.timeScales) {
      const span = Math.min(timeScale.span, this.shortTermBuffer.length);

      if (span <= 0) {
        result[timeScale.name] = null;
        continue;
      }

      // Get states for this time scale (most recent states)
      const states = this.shortTermBuffer.slice(-span);

      // Calculate weighted average vector
      const vector = this._calculateWeightedAverageVector(states);

      result[timeScale.name] = {
        vector,
        span,
        weight: timeScale.weight,
      };
    }

    return result;
  }

  /**
   * Calculate weighted average vector for a set of states
   *
   * @private
   * @param {Array} states - States to average
   * @returns {Array} Weighted average vector
   */
  _calculateWeightedAverageVector(states) {
    if (!states || states.length === 0) {
      return [];
    }

    // Determine vector dimension from first state
    const firstVector = this._extractStateVector(states[0]);
    const vectorLength = firstVector.length;

    // Initialize result vector
    const result = new Array(vectorLength).fill(0);

    // Calculate time-based weights (more recent = higher weight)
    const timeWeights = states.map((state, index) => {
      // Exponential weighting: weight = exp((i - (n-1)) * factor)
      const position = index - (states.length - 1);
      const factor = 0.5;
      return Math.exp(position * factor);
    });

    // Calculate total weight
    const totalWeight = timeWeights.reduce((sum, w) => sum + w, 0);

    // Combine vectors with weights
    for (let i = 0; i < states.length; i++) {
      const vector = this._extractStateVector(states[i]);
      const weight = timeWeights[i] / totalWeight;

      for (let j = 0; j < vectorLength && j < vector.length; j++) {
        result[j] += vector[j] * weight;
      }
    }

    return result;
  }

  /**
   * Combine vectors from different time scales
   *
   * @private
   * @param {Array} currentVector - Current state vector
   * @param {Object} timeScaleVectors - Vectors from different time scales
   * @returns {Array} Combined vector
   */
  _combineTimeScaleVectors(currentVector, timeScaleVectors) {
    // Create copy of current vector as starting point
    const result = [...currentVector];

    // Track total weight applied
    let totalWeight = 0;

    // Apply each time scale with its weight
    for (const timeScale of this.timeScales) {
      const tsv = timeScaleVectors[timeScale.name];

      if (!tsv || !tsv.vector || tsv.vector.length === 0) {
        continue;
      }

      const weight = timeScale.weight * this.integrationCoefficient;
      totalWeight += weight;

      // Apply weighted contribution from this time scale
      for (let i = 0; i < result.length && i < tsv.vector.length; i++) {
        result[i] = result[i] * (1 - weight) + tsv.vector[i] * weight;
      }
    }

    return result;
  }

  /**
   * Update state with a vector representation
   *
   * @private
   * @param {Object} state - State to update
   * @param {Array} vector - Vector to update with
   */
  _updateStateWithVector(state, vector) {
    // Update vector property
    state.vector = [...vector];

    // Update common properties
    const props = [
      "attention",
      "awareness",
      "coherence",
      "integration",
      "differentiation",
      "selfReference",
      "temporalBinding",
    ];

    for (let i = 0; i < props.length && i < vector.length; i++) {
      state[props[i]] = vector[i];
    }
  }

  /**
   * Calculate temporal binding measure
   *
   * @private
   * @param {Object} timeScaleVectors - Vectors from different time scales
   * @returns {number} Temporal binding value (0-1)
   */
  _calculateTemporalBinding(timeScaleVectors) {
    // Temporal binding measures coherence across time scales
    const vectors = [];

    // Collect vectors from each time scale
    for (const timeScale of this.timeScales) {
      const tsv = timeScaleVectors[timeScale.name];
      if (tsv && tsv.vector) {
        vectors.push(tsv.vector);
      }
    }

    if (vectors.length < 2) {
      return 0; // Need at least two time scales for binding
    }

    // Calculate average similarity between time scales
    let totalSimilarity = 0;
    let comparisons = 0;

    for (let i = 0; i < vectors.length; i++) {
      for (let j = i + 1; j < vectors.length; j++) {
        totalSimilarity += this._calculateVectorSimilarity(
          vectors[i],
          vectors[j],
        );
        comparisons++;
      }
    }

    // Normalize by number of comparisons
    return comparisons > 0 ? totalSimilarity / comparisons : 0;
  }

  /**
   * Calculate similarity between two vectors
   *
   * @private
   * @param {Array} vec1 - First vector
   * @param {Array} vec2 - Second vector
   * @returns {number} Similarity value (0-1)
   */
  _calculateVectorSimilarity(vec1, vec2) {
    if (!vec1 || !vec2 || vec1.length === 0 || vec2.length === 0) {
      return 0;
    }

    // Use cosine similarity
    let dotProduct = 0;
    let mag1 = 0;
    let mag2 = 0;

    const minLength = Math.min(vec1.length, vec2.length);

    for (let i = 0; i < minLength; i++) {
      dotProduct += vec1[i] * vec2[i];
      mag1 += vec1[i] * vec1[i];
      mag2 += vec2[i] * vec2[i];
    }

    const magnitude = Math.sqrt(mag1) * Math.sqrt(mag2);

    if (magnitude < 1e-10) {
      return 0;
    }

    // Convert from [-1,1] to [0,1] range
    return (dotProduct / magnitude + 1) / 2;
  }

  /**
   * Simple blending of a state with current integration
   *
   * @private
   * @param {Object} state - New state to blend
   * @returns {Object} Blended state
   */
  _blendWithCurrentIntegration(state) {
    if (!this._currentIntegration) {
      return state;
    }

    // Create copy for blending
    const blended = this._deepCopy(state);

    // Extract vectors
    const stateVector = this._extractStateVector(state);
    const integrationVector = this._extractStateVector(
      this._currentIntegration,
    );

    // Apply simple linear blend
    const blendFactor = 0.3; // 30% from integration, 70% from current
    const blendedVector = stateVector.map((val, i) => {
      if (i < integrationVector.length) {
        return val * (1 - blendFactor) + integrationVector[i] * blendFactor;
      }
      return val;
    });

    // Update with blended vector
    this._updateStateWithVector(blended, blendedVector);

    // Mark as partially integrated
    blended._temporal.integrated = true;
    blended._temporal.integrationTimestamp = Date.now();
    blended._temporal.partialIntegration = true;

    // Set temporal binding based on previous value
    if (typeof this._currentIntegration.temporalBinding === "number") {
      blended.temporalBinding = this._currentIntegration.temporalBinding * 0.95;
    }

    return blended;
  }

  /**
   * Create a deep copy of an object
   *
   * @private
   * @param {Object} obj - Object to copy
   * @returns {Object} Deep copy
   */
  _deepCopy(obj) {
    if (!obj) return null;
    return JSON.parse(JSON.stringify(obj));
  }

  /**
   * Compute overall integration value for a state
   *
   * @param {Object} state - State to evaluate
   * @returns {number} Integration value (0-1)
   */
  computeIntegration(state) {
    // For non-integrated states, compute based on window coherence
    if (!state._temporal || !state._temporal.integrated) {
      return this._calculateWindowCoherence();
    }

    // For integrated states, use temporal binding
    if (typeof state.temporalBinding === "number") {
      return state.temporalBinding;
    }

    // Fallback to window coherence
    return this._calculateWindowCoherence();
  }

  /**
   * Calculate coherence across the integration window
   *
   * @private
   * @returns {number} Window coherence value (0-1)
   */
  _calculateWindowCoherence() {
    if (this.integrationWindow.length < 2) {
      return 0;
    }

    // Extract vectors from window
    const vectors = this.integrationWindow.map((state) =>
      this._extractStateVector(state),
    );

    // Calculate average similarity between consecutive states
    let totalSimilarity = 0;

    for (let i = 1; i < vectors.length; i++) {
      totalSimilarity += this._calculateVectorSimilarity(
        vectors[i - 1],
        vectors[i],
      );
    }

    // Normalize by number of comparisons
    return totalSimilarity / (vectors.length - 1);
  }

  /**
   * Get recent states from the temporal buffer
   *
   * @param {number} [count=10] - Number of states to retrieve
   * @returns {Array} Recent states
   */
  getRecentStates(count = 10) {
    const numStates = Math.min(count, this.shortTermBuffer.length);
    return this.shortTermBuffer.slice(-numStates);
  }

  /**
   * Get significant states from the buffer
   *
   * @param {number} [count=10] - Number of states to retrieve
   * @returns {Array} Significant states
   */
  getSignificantStates(count = 10) {
    const numStates = Math.min(count, this.significantStateBuffer.length);
    return this.significantStateBuffer.slice(-numStates);
  }

  /**
   * Find states most similar to a target state
   *
   * @param {Object} targetState - State to compare against
   * @param {number} [count=5] - Number of similar states to return
   * @returns {Array} Similar states with similarity scores
   */
  findSimilarStates(targetState, count = 5) {
    if (!targetState) {
      return [];
    }

    const targetVector = this._extractStateVector(targetState);

    // Combine short-term and significant buffers for search
    const searchBuffer = [
      ...this.shortTermBuffer,
      ...this.significantStateBuffer.filter(
        (s) => !this.shortTermBuffer.includes(s),
      ),
    ];

    // Calculate similarity for each state
    const withSimilarity = searchBuffer.map((state) => {
      const stateVector = this._extractStateVector(state);
      const similarity = this._calculateVectorSimilarity(
        targetVector,
        stateVector,
      );

      return {
        state,
        similarity,
      };
    });

    // Sort by similarity (descending) and return top matches
    withSimilarity.sort((a, b) => b.similarity - a.similarity);

    return withSimilarity.slice(0, count);
  }

  /**
   * Get system performance statistics
   *
   * @returns {Object} Performance statistics
   */
  getStats() {
    const averageIntegrationTime =
      this._stats.integrations > 0
        ? this._stats.totalIntegrationTime / this._stats.integrations
        : 0;

    const integrationRate =
      this._stats.integrations + this._stats.skippedIntegrations > 0
        ? this._stats.integrations /
          (this._stats.integrations + this._stats.skippedIntegrations)
        : 0;

    return {
      ...this._stats,
      shortTermBufferSize: this.shortTermBuffer.length,
      longTermBufferSize: this.longTermBuffer.length,
      significantBufferSize: this.significantStateBuffer.length,
      averageIntegrationTime,
      integrationRate,
      windowCoherence: this._calculateWindowCoherence(),
    };
  }

  /**
   * Reset the temporal integration system
   */
  reset() {
    this.shortTermBuffer = [];
    this.longTermBuffer = [];
    this.integrationWindow = [];
    this.significantStateBuffer = [];

    this._currentIntegration = null;
    this._lastUpdateTime = 0;
    this._initialized = false;

    this._stats = {
      integrations: 0,
      skippedIntegrations: 0,
      significantStates: 0,
      totalIntegrationTime: 0,
    };
  }
}

module.exports = TemporalIntegration;
