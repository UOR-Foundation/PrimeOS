/**
 * Attention Mechanism - Focus allocation based on coherence gradients
 * 
 * This module implements the attention mechanism needed for consciousness
 * simulation, focusing on areas of high coherence gradient.
 * 
 * Key features:
 * - Computes coherence gradients across state space
 * - Allocates attention based on coherence maximization
 * - Implements natural attention decay over time
 * - Provides visualization of attention fields
 * - Supports external influence on attention focus
 */

// Try to import core if available
let Prime;
try {
  Prime = require("../core.js");
} catch (e) {
  // Handle case where core isn't available yet
  Prime = {};
}

// Import required modules
const MathUtils = require("../framework/math/index.js");
const { Manifold } = require("../framework/base0/manifold.js");

/**
 * AttentionMechanism provides mechanisms for focusing on areas of high coherence gradient
 */
class AttentionMechanism {
  /**
   * Create a new attention mechanism
   * 
   * @param {Object} options - Configuration options
   * @param {number} options.attentionCapacity - Maximum attention capacity (default: 1.0)
   * @param {number} options.fieldDimension - Dimensions of attention field (default: 7)
   * @param {number} options.decayRate - Rate of attention decay (default: 0.1)
   * @param {number} options.gradientSensitivity - Sensitivity to coherence gradients (default: 0.7)
   * @param {number} options.focusSharpness - Sharpness of attention focus (default: 2.0)
   * @param {Function} options.coherenceFunction - Function to calculate coherence (default: internal)
   */
  constructor(options = {}) {
    this.attentionCapacity = options.attentionCapacity || 1.0;
    this.fieldDimension = options.fieldDimension || 7;
    this.decayRate = options.decayRate || 0.1;
    this.gradientSensitivity = options.gradientSensitivity || 0.7;
    this.focusSharpness = options.focusSharpness || 2.0;
    this.coherenceFunction = options.coherenceFunction || this._defaultCoherenceFunction;
    
    // Initialize attention field
    this.attentionField = this._createAttentionField();
    
    // Track focus points
    this.focusPoints = [];
    this.priorityQueue = [];
    
    // Coherence gradients
    this.gradientField = {};
    this.lastCoherenceMap = {};
    
    // Internal state tracking
    this._attendedRegions = new Map();
    this._lastUpdateTime = Date.now();
    this._currentCapacityUsed = 0;
    
    // Performance tracking
    this._stats = {
      focusShifts: 0,
      gradientUpdates: 0,
      attentionAllocations: 0,
      externalFocusEvents: 0,
      totalProcessingTime: 0
    };
  }
  
  /**
   * Create initial attention field
   * 
   * @private
   * @returns {Object} Attention field
   */
  _createAttentionField() {
    const field = {
      dimension: this.fieldDimension,
      values: new Array(this.fieldDimension).fill(0),
      weights: new Array(this.fieldDimension).fill(1),
      mask: new Array(this.fieldDimension).fill(1),
      hotspots: [],
      globalAttention: 0.3 // Initial moderate attention level
    };
    
    // Set higher weights for consciousness-essential dimensions
    if (field.weights.length >= 7) {
      field.weights[0] = 1.5; // attention
      field.weights[1] = 1.3; // awareness
      field.weights[2] = 1.2; // coherence
      field.weights[5] = 1.2; // self-reference
    }
    
    return field;
  }
  
  /**
   * Initialize attention with a given state
   * 
   * @param {Object} state - Initial consciousness state
   * @returns {boolean} Success flag
   */
  initialize(state) {
    if (!state) {
      return false;
    }
    
    // Extract state vector
    const stateVector = this._extractStateVector(state);
    
    // Set initial moderate attention across field
    for (let i = 0; i < this.fieldDimension && i < stateVector.length; i++) {
      // Attention proportional to state value and dimension weight
      this.attentionField.values[i] = 0.3 * stateVector[i] * this.attentionField.weights[i];
    }
    
    // Initialize gradient field with zeros
    for (let i = 0; i < this.fieldDimension; i++) {
      this.gradientField[i] = 0;
    }
    
    // Record initial coherence map
    this.lastCoherenceMap = this._createCoherenceMap(state);
    
    this._lastUpdateTime = Date.now();
    return true;
  }
  
  /**
   * Update attention based on new state
   * 
   * @param {Object} state - Current consciousness state
   * @param {Object} [previousState=null] - Previous consciousness state
   * @returns {Object} Updated attention field
   */
  update(state, previousState = null) {
    const startTime = Date.now();
    
    // Apply natural decay based on time elapsed
    this._applyAttentionDecay();
    
    // Calculate coherence gradients
    this._updateCoherenceGradients(state, previousState);
    
    // Allocate attention based on gradients
    this._allocateAttentionBasedOnGradients();
    
    // Update focus points
    this._updateFocusPoints(state);
    
    // Update stats
    this._stats.totalProcessingTime += (Date.now() - startTime);
    
    // Update last update time
    this._lastUpdateTime = Date.now();
    
    return this.attentionField;
  }
  
  /**
   * Apply natural attention decay over time
   * 
   * @private
   */
  _applyAttentionDecay() {
    // Calculate time since last update
    const now = Date.now();
    const elapsed = (now - this._lastUpdateTime) / 1000; // Convert to seconds
    
    // Skip if no significant time has passed
    if (elapsed < 0.01) {
      return;
    }
    
    // Calculate decay factor based on elapsed time
    const decayFactor = Math.min(1, this.decayRate * elapsed);
    
    // Apply decay to attention field values
    for (let i = 0; i < this.attentionField.values.length; i++) {
      // Dimensions decay at slightly different rates
      const dimensionDecayModifier = 1 + (i % 3 - 1) * 0.1; // 0.9, 1.0, or 1.1
      const effectiveDecay = decayFactor * dimensionDecayModifier;
      
      // Apply decay but maintain minimum attention
      this.attentionField.values[i] = Math.max(
        0.05, 
        this.attentionField.values[i] * (1 - effectiveDecay)
      );
    }
    
    // Also decay global attention
    this.attentionField.globalAttention = Math.max(
      0.1,
      this.attentionField.globalAttention * (1 - decayFactor * 0.5)
    );
    
    // Update current capacity used
    this._updateCapacityUsed();
  }
  
  /**
   * Update coherence gradients based on state changes
   * 
   * @private
   * @param {Object} state - Current consciousness state
   * @param {Object} previousState - Previous consciousness state
   */
  _updateCoherenceGradients(state, previousState) {
    this._stats.gradientUpdates++;
    
    // Create coherence map for current state
    const currentCoherenceMap = this._createCoherenceMap(state);
    
    // If we have a previous state, use it for more accurate gradient calculation
    if (previousState) {
      const prevCoherenceMap = this._createCoherenceMap(previousState);
      
      // Calculate precise gradients from state-to-state transition
      for (let i = 0; i < this.fieldDimension; i++) {
        const currentValue = currentCoherenceMap[i] || 0;
        const prevValue = prevCoherenceMap[i] || 0;
        
        // Gradient is the rate of change in coherence
        this.gradientField[i] = currentValue - prevValue;
      }
    } 
    // Otherwise use the stored last coherence map
    else {
      for (let i = 0; i < this.fieldDimension; i++) {
        const currentValue = currentCoherenceMap[i] || 0;
        const lastValue = this.lastCoherenceMap[i] || 0;
        
        // Gradient is the rate of change in coherence
        this.gradientField[i] = currentValue - lastValue;
      }
    }
    
    // Update last coherence map
    this.lastCoherenceMap = currentCoherenceMap;
    
    // Identify significant gradients as hotspots
    this._identifyHotspots();
  }
  
  /**
   * Create a coherence map for a state
   * 
   * @private
   * @param {Object} state - Consciousness state
   * @returns {Object} Coherence map
   */
  _createCoherenceMap(state) {
    if (!state) {
      return {};
    }
    
    const coherenceMap = {};
    const vector = this._extractStateVector(state);
    
    // Calculate dimensional coherence values
    for (let i = 0; i < this.fieldDimension && i < vector.length; i++) {
      // Base coherence is the value itself
      let baseCoherence = vector[i];
      
      // Adjust for interdimensional coherence where appropriate
      if (i === 2 && vector.length > 3) { // coherence affects integration
        baseCoherence = (baseCoherence + vector[3]) / 2;
      }
      if (i === 5 && vector.length > 2) { // self-reference affects coherence
        baseCoherence = (baseCoherence + vector[2]) / 2;
      }
      
      coherenceMap[i] = baseCoherence;
    }
    
    // Add overall coherence if available in state
    if (typeof state.coherence === 'number') {
      coherenceMap['global'] = state.coherence;
    }
    
    return coherenceMap;
  }
  
  /**
   * Identify hotspots based on significant gradients
   * 
   * @private
   */
  _identifyHotspots() {
    const hotspots = [];
    
    // Find highest absolute gradients
    const gradientEntries = Object.entries(this.gradientField)
      .map(([dim, value]) => ({ dimension: parseInt(dim), value }))
      .filter(entry => !isNaN(entry.dimension) && Math.abs(entry.value) > 0.05)
      .sort((a, b) => Math.abs(b.value) - Math.abs(a.value));
    
    // Select top hotspots (positive and negative gradients)
    for (const entry of gradientEntries.slice(0, 3)) {
      hotspots.push({
        dimension: entry.dimension,
        value: entry.value,
        intensity: Math.min(1, Math.abs(entry.value) * this.gradientSensitivity),
        type: entry.value > 0 ? 'increasing' : 'decreasing'
      });
    }
    
    this.attentionField.hotspots = hotspots;
  }
  
  /**
   * Allocate attention based on coherence gradients
   * 
   * @private
   */
  _allocateAttentionBasedOnGradients() {
    this._stats.attentionAllocations++;
    
    // Calculate attention available for reallocation
    const maxAttentionForReallocation = this._calculateAvailableAttention();
    
    // If no attention available for reallocation, just return
    if (maxAttentionForReallocation <= 0.05) {
      return;
    }
    
    // Calculate total absolute gradient to normalize allocation
    let totalAbsGradient = 0;
    for (let i = 0; i < this.fieldDimension; i++) {
      totalAbsGradient += Math.abs(this.gradientField[i]);
    }
    
    // Avoid division by zero
    if (totalAbsGradient < 0.001) {
      totalAbsGradient = 0.001;
    }
    
    // Allocate attention proportionally to gradient magnitude
    for (let i = 0; i < this.fieldDimension; i++) {
      // Only focus on positive gradients (increasing coherence)
      if (this.gradientField[i] > 0) {
        // Calculate attention allocation for this dimension
        const gradientProportion = Math.abs(this.gradientField[i]) / totalAbsGradient;
        const allocation = maxAttentionForReallocation * gradientProportion * this.gradientSensitivity;
        
        // Add to current attention level
        this.attentionField.values[i] = Math.min(
          1.0,
          this.attentionField.values[i] + allocation
        );
      }
    }
    
    // Adjust global attention based on overall coherence change
    if (this.lastCoherenceMap['global'] !== undefined) {
      const globalGradient = this.lastCoherenceMap['global'] - 
                            (this.lastCoherenceMap['global'] || 0.5);
                            
      if (globalGradient > 0) {
        // Increasing global coherence raises attention
        this.attentionField.globalAttention = Math.min(
          1.0,
          this.attentionField.globalAttention + 0.1 * globalGradient
        );
      }
    }
    
    // Update capacity used
    this._updateCapacityUsed();
  }
  
  /**
   * Update focus points based on attention field and current state
   * 
   * @private
   * @param {Object} state - Current consciousness state
   */
  _updateFocusPoints(state) {
    // Get attention field values
    const attentionValues = [...this.attentionField.values];
    
    // Find highest attention values
    const sorted = attentionValues
      .map((value, dimension) => ({ dimension, value }))
      .sort((a, b) => b.value - a.value);
    
    // Clear old focus points that no longer have high attention
    this.focusPoints = this.focusPoints.filter(fp => {
      return attentionValues[fp.dimension] >= 0.4;
    });
    
    // Add new focus points for high attention areas
    for (const { dimension, value } of sorted) {
      // Only add focus points for high attention areas
      if (value >= 0.7) {
        // Check if this dimension is already a focus point
        const existingIdx = this.focusPoints.findIndex(fp => fp.dimension === dimension);
        
        if (existingIdx >= 0) {
          // Update existing focus point
          this.focusPoints[existingIdx].intensity = value;
          this.focusPoints[existingIdx].timestamp = Date.now();
        } else {
          // Add new focus point
          this.focusPoints.push({
            dimension,
            intensity: value,
            vector: state ? this._extractStateVector(state) : null,
            timestamp: Date.now()
          });
          
          this._stats.focusShifts++;
        }
      }
    }
    
    // Sort focus points by intensity
    this.focusPoints.sort((a, b) => b.intensity - a.intensity);
    
    // If we have too many focus points, keep only the strongest ones
    const maxFocusPoints = Math.floor(this.attentionCapacity * 2);
    if (this.focusPoints.length > maxFocusPoints) {
      this.focusPoints = this.focusPoints.slice(0, maxFocusPoints);
    }
  }
  
  /**
   * Calculate attention available for reallocation
   * 
   * @private
   * @returns {number} Available attention
   */
  _calculateAvailableAttention() {
    // Calculate current attention
    let currentTotal = this.attentionField.values.reduce((sum, val) => sum + val, 0);
    
    // Scale by dimension to get normalized value
    currentTotal /= this.fieldDimension;
    
    // Calculate how much attention can be allocated
    const available = Math.max(0, this.attentionCapacity - currentTotal);
    
    // Return a portion of available attention for allocation
    return available * 0.7;
  }
  
  /**
   * Update the capacity used tracking
   * 
   * @private
   */
  _updateCapacityUsed() {
    // Calculate current attention
    let currentTotal = this.attentionField.values.reduce((sum, val) => sum + val, 0);
    
    // Scale by dimension to get normalized value
    currentTotal /= this.fieldDimension;
    
    // Update tracking
    this._currentCapacityUsed = currentTotal;
  }
  
  /**
   * Focus attention explicitly on a specific dimension
   * 
   * @param {number} dimension - Dimension to focus on
   * @param {number} intensity - Intensity of focus (0-1)
   * @param {Object} [metadata={}] - Additional focus metadata
   * @returns {boolean} Success flag
   */
  focus(dimension, intensity = 1.0, metadata = {}) {
    // Validate inputs
    if (dimension < 0 || dimension >= this.fieldDimension || intensity <= 0) {
      return false;
    }
    
    this._stats.externalFocusEvents++;
    
    // Calculate available capacity
    const available = this.attentionCapacity - this._currentCapacityUsed;
    
    // Check if we have capacity
    if (intensity > available && this.attentionField.values[dimension] < intensity) {
      // Not enough capacity for full intensity, try reduced intensity
      intensity = available * 0.8;
      
      // If still not enough, remove least important focus
      if (intensity < 0.2 && this.focusPoints.length > 0) {
        // Remove least important focus
        const leastImportant = this.focusPoints[this.focusPoints.length - 1];
        this.attentionField.values[leastImportant.dimension] *= 0.5;
        this.focusPoints.pop();
        
        // Recalculate capacity
        this._updateCapacityUsed();
      }
    }
    
    // Apply focus
    this.attentionField.values[dimension] = Math.min(1.0, intensity);
    
    // Add to focus points
    const existingIdx = this.focusPoints.findIndex(fp => fp.dimension === dimension);
    
    if (existingIdx >= 0) {
      // Update existing focus point
      this.focusPoints[existingIdx].intensity = intensity;
      this.focusPoints[existingIdx].timestamp = Date.now();
      this.focusPoints[existingIdx].metadata = metadata;
    } else {
      // Add new focus point
      this.focusPoints.push({
        dimension,
        intensity,
        timestamp: Date.now(),
        metadata
      });
      
      this._stats.focusShifts++;
    }
    
    // Update capacity used
    this._updateCapacityUsed();
    
    // Sort focus points by intensity
    this.focusPoints.sort((a, b) => b.intensity - a.intensity);
    
    return true;
  }
  
  /**
   * Release focus from a specific dimension
   * 
   * @param {number} dimension - Dimension to release focus from
   * @returns {boolean} Success flag
   */
  releaseFocus(dimension) {
    // Validate dimension
    if (dimension < 0 || dimension >= this.fieldDimension) {
      return false;
    }
    
    // Reduce attention for the dimension
    this.attentionField.values[dimension] *= 0.3;
    
    // Remove from focus points
    const index = this.focusPoints.findIndex(fp => fp.dimension === dimension);
    
    if (index >= 0) {
      this.focusPoints.splice(index, 1);
      this._updateCapacityUsed();
      return true;
    }
    
    return false;
  }
  
  /**
   * Set attention mask to filter attention allocation
   * 
   * @param {Array} mask - Array of mask values (0-1) for each dimension
   * @returns {boolean} Success flag
   */
  setAttentionMask(mask) {
    if (!Array.isArray(mask) || mask.length !== this.fieldDimension) {
      return false;
    }
    
    // Apply mask (ensure values are in 0-1 range)
    for (let i = 0; i < this.fieldDimension; i++) {
      this.attentionField.mask[i] = Math.min(1, Math.max(0, mask[i]));
      
      // Apply mask to current values
      this.attentionField.values[i] *= this.attentionField.mask[i];
    }
    
    // Update capacity used
    this._updateCapacityUsed();
    
    return true;
  }
  
  /**
   * Apply attention field to a state
   * 
   * @param {Object} state - State to apply attention to
   * @returns {Object} Attention-modulated state
   */
  applyAttentionToState(state) {
    if (!state) {
      return null;
    }
    
    // Create a deep copy to avoid modifying the original
    const modulated = this._deepCopy(state);
    
    // Extract vector
    const vector = this._extractStateVector(modulated);
    
    // Apply attention modulation
    for (let i = 0; i < vector.length && i < this.fieldDimension; i++) {
      // Apply attention with sharpening/contrast enhancement
      const attention = this.attentionField.values[i];
      const attended = this._attentionModulateValue(vector[i], attention);
      
      // Update vector element
      vector[i] = attended;
    }
    
    // Update state with modulated vector
    this._updateStateWithVector(modulated, vector);
    
    // Add attention metadata
    if (!modulated._attention) {
      modulated._attention = {};
    }
    
    modulated._attention = {
      field: [...this.attentionField.values],
      globalAttention: this.attentionField.globalAttention,
      focusPoints: this.focusPoints.map(fp => ({
        dimension: fp.dimension,
        intensity: fp.intensity
      })),
      capacity: this.attentionCapacity,
      timestamp: Date.now()
    };
    
    return modulated;
  }
  
  /**
   * Modulate a value with attention
   * 
   * @private
   * @param {number} value - Value to modulate
   * @param {number} attention - Attention value (0-1)
   * @returns {number} Modulated value
   */
  _attentionModulateValue(value, attention) {
    // No modulation if attention is neutral (0.5)
    if (Math.abs(attention - 0.5) < 0.01) {
      return value;
    }
    
    // For low attention, suppress the value
    if (attention < 0.5) {
      const suppressionFactor = 1 - 2 * (0.5 - attention);
      return value * suppressionFactor;
    }
    
    // For high attention, enhance the value (with contrast)
    const enhancement = (attention - 0.5) * 2;
    
    // Apply non-linear enhancement with sharpness factor
    const sharpness = this.focusSharpness;
    
    // Enhanced value with contrast adjustment
    return Math.min(1, value + (1 - value) * enhancement * Math.pow(value, sharpness - 1));
  }
  
  /**
   * Extract state vector from an object
   * 
   * @private
   * @param {Object} state - State object
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
    
    // Create vector from state properties
    const vector = new Array(this.fieldDimension).fill(0);
    
    // Fill vector with available state attributes
    if (state.attention !== undefined) vector[0] = state.attention;
    if (state.awareness !== undefined) vector[1] = state.awareness;
    if (state.coherence !== undefined) vector[2] = state.coherence;
    if (state.integration !== undefined) vector[3] = state.integration;
    if (state.differentiation !== undefined) vector[4] = state.differentiation;
    if (state.selfReference !== undefined) vector[5] = state.selfReference;
    if (state.temporalBinding !== undefined) vector[6] = state.temporalBinding;
    
    return vector;
  }
  
  /**
   * Update state with transformed vector
   * 
   * @private
   * @param {Object} state - State to update
   * @param {Array} vector - Vector to update with
   * @returns {Object} Updated state
   */
  _updateStateWithVector(state, vector) {
    // If state is an array, just return the vector
    if (Array.isArray(state)) {
      return vector;
    }
    
    // Store the vector
    state.vector = [...vector];
    
    // Update state attributes from vector components
    if (vector.length > 0) state.attention = vector[0];
    if (vector.length > 1) state.awareness = vector[1];
    if (vector.length > 2) state.coherence = vector[2];
    if (vector.length > 3) state.integration = vector[3];
    if (vector.length > 4) state.differentiation = vector[4];
    if (vector.length > 5) state.selfReference = vector[5];
    if (vector.length > 6) state.temporalBinding = vector[6];
    
    return state;
  }
  
  /**
   * Create deep copy of an object
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
   * Default coherence function between states
   * 
   * @private
   * @param {Object} state1 - First state
   * @param {Object} state2 - Second state
   * @returns {number} Coherence value (0-1)
   */
  _defaultCoherenceFunction(state1, state2) {
    if (!state1 || !state2) return 0;
    
    const vec1 = this._extractStateVector(state1);
    const vec2 = this._extractStateVector(state2);
    
    // Calculate cosine similarity
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
   * Get current attention field
   * 
   * @returns {Array} Attention field values array
   */
  getAttentionField() {
    return [...this.attentionField.values];
  }
  
  /**
   * Get detailed attention field information
   * 
   * @returns {Object} Detailed attention field
   */
  getDetailedAttentionField() {
    return {
      values: [...this.attentionField.values],
      globalAttention: this.attentionField.globalAttention,
      hotspots: [...this.attentionField.hotspots],
      dimension: this.fieldDimension,
      capacity: this.attentionCapacity,
      used: this._currentCapacityUsed
    };
  }
  
  /**
   * Get focus points
   * 
   * @returns {Array} Focus points
   */
  getFocusPoints() {
    return this.focusPoints.map(fp => ({...fp}));
  }
  
  /**
   * Generate visualization data for attention field
   * 
   * @returns {Object} Visualization data
   */
  getVisualizationData() {
    // Create dimensional labels based on field dimensions
    const dimensionLabels = [];
    
    for (let i = 0; i < this.fieldDimension; i++) {
      switch (i) {
        case 0: dimensionLabels.push('Attention'); break;
        case 1: dimensionLabels.push('Awareness'); break;
        case 2: dimensionLabels.push('Coherence'); break;
        case 3: dimensionLabels.push('Integration'); break;
        case 4: dimensionLabels.push('Differentiation'); break;
        case 5: dimensionLabels.push('Self-Reference'); break;
        case 6: dimensionLabels.push('Temporal Binding'); break;
        default: dimensionLabels.push(`Dimension ${i}`);
      }
    }
    
    // Create dataset for visualization
    const dataset = [];
    
    for (let i = 0; i < this.fieldDimension; i++) {
      dataset.push({
        dimension: i,
        label: dimensionLabels[i],
        attention: this.attentionField.values[i],
        gradient: this.gradientField[i] || 0,
        isFocus: this.focusPoints.some(fp => fp.dimension === i)
      });
    }
    
    return {
      dimensions: dimensionLabels,
      dataset,
      globalAttention: this.attentionField.globalAttention,
      hotspots: this.attentionField.hotspots,
      focusPoints: this.focusPoints.map(fp => ({...fp}))
    };
  }
  
  /**
   * Get performance statistics
   * 
   * @returns {Object} Performance statistics
   */
  getStats() {
    const averageProcessingTime = this._stats.gradientUpdates > 0
      ? this._stats.totalProcessingTime / this._stats.gradientUpdates
      : 0;
    
    return {
      ...this._stats,
      currentCapacity: this._currentCapacityUsed,
      maxCapacity: this.attentionCapacity,
      availableCapacity: this.attentionCapacity - this._currentCapacityUsed,
      focusCount: this.focusPoints.length,
      averageProcessingTime
    };
  }
  
  /**
   * Reset the attention mechanism
   */
  reset() {
    // Reset attention field
    this.attentionField = this._createAttentionField();
    
    // Clear focus points and gradients
    this.focusPoints = [];
    this.gradientField = {};
    this.lastCoherenceMap = {};
    
    // Reset tracking
    this._attendedRegions.clear();
    this._lastUpdateTime = Date.now();
    this._currentCapacityUsed = 0;
    
    // Reset stats
    this._stats = {
      focusShifts: 0,
      gradientUpdates: 0,
      attentionAllocations: 0,
      externalFocusEvents: 0,
      totalProcessingTime: 0
    };
  }
}

module.exports = AttentionMechanism;