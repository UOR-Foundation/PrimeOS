/**
 * Threshold Manager - Adaptive threshold management for state transitions
 * 
 * This module implements the threshold management needed for consciousness
 * simulation, adapting thresholds for state transitions based on system state.
 * 
 * Key features:
 * - Manages dynamic thresholds for state transitions
 * - Implements adaptive arousal level modeling
 * - Supports gradation of consciousness levels
 * - Regulates access to consciousness based on coherence
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

/**
 * ThresholdManager provides adaptive threshold management for state transitions
 */
class ThresholdManager {
  /**
   * Create a new threshold manager
   * 
   * @param {Object} options - Configuration options
   * @param {number} options.baseCoherenceThreshold - Base coherence threshold (default: 0.7)
   * @param {number} options.minimumThreshold - Minimum threshold value (default: 0.3)
   * @param {number} options.maximumThreshold - Maximum threshold value (default: 0.9)
   * @param {number} options.adaptationRate - Rate of threshold adaptation (default: 0.1)
   * @param {Object} options.dimensionThresholds - Specific thresholds for dimensions
   */
  constructor(options = {}) {
    this.baseCoherenceThreshold = options.baseCoherenceThreshold || 0.7;
    this.minimumThreshold = options.minimumThreshold || 0.3;
    this.maximumThreshold = options.maximumThreshold || 0.9;
    this.adaptationRate = options.adaptationRate || 0.1;
    
    // Define dimension-specific thresholds
    this.dimensionThresholds = options.dimensionThresholds || {
      attention: 0.6,
      awareness: 0.7,
      coherence: 0.7,
      integration: 0.6,
      differentiation: 0.5,
      selfReference: 0.8,
      temporalBinding: 0.6
    };
    
    // Adaptive thresholds that will change with system state
    this.adaptiveThresholds = { ...this.dimensionThresholds };
    
    // Arousal level modeling
    this.arousalLevel = 0.5; // Neutral arousal
    this.arousalBase = 0.5;  // Resting arousal
    this.arousalFluctuation = 0.0;
    this.arousalDirection = 0;
    this.arousalMomentum = 0;
    
    // Consciousness levels
    this.consciousnessLevels = [
      { name: 'unconscious', threshold: 0.0 }, 
      { name: 'subconscious', threshold: 0.3 },
      { name: 'conscious', threshold: 0.6 },
      { name: 'metaconscious', threshold: 0.85 }
    ];
    
    // Access regulation
    this.accessHistory = [];
    this.accessDeniedHistory = [];
    this._currentStateAccess = new Map();
    
    // Threshold adaptation history
    this.thresholdHistory = [];
    this._lastUpdateTime = Date.now();
    
    // Performance tracking
    this._stats = {
      stateTransitions: 0,
      thresholdAdjustments: 0,
      accessGranted: 0,
      accessDenied: 0,
      arousalShifts: 0,
      totalProcessingTime: 0
    };
  }
  
  /**
   * Initialize threshold manager
   * 
   * @param {Object} state - Initial consciousness state
   * @returns {boolean} Success flag
   */
  initialize(state) {
    if (!state) {
      return false;
    }
    
    // Set initial arousal based on state
    if (state.attention !== undefined) {
      this.arousalLevel = Math.min(0.8, Math.max(0.3, state.attention));
      this.arousalBase = this.arousalLevel;
    }
    
    // Initialize adaptive thresholds
    this._updateAdaptiveThresholds(state);
    
    // Record initial thresholds
    this._recordThresholdState();
    
    this._lastUpdateTime = Date.now();
    return true;
  }
  
  /**
   * Update thresholds based on system state
   * 
   * @param {Object} state - Current consciousness state
   * @param {Object} [previousState=null] - Previous state
   * @returns {Object} Updated thresholds
   */
  update(state, previousState = null) {
    const startTime = Date.now();
    
    // Update arousal level
    this._updateArousalLevel(state, previousState);
    
    // Update adaptive thresholds
    this._updateAdaptiveThresholds(state);
    
    // Record threshold state
    this._recordThresholdState();
    
    // Update stats
    this._stats.thresholdAdjustments++;
    this._stats.totalProcessingTime += (Date.now() - startTime);
    
    this._lastUpdateTime = Date.now();
    
    return this.adaptiveThresholds;
  }
  
  /**
   * Check if a state transition exceeds current thresholds
   * 
   * @param {Object} currentState - Current consciousness state
   * @param {Object} newState - New consciousness state
   * @returns {Object} Transition evaluation
   */
  evaluateTransition(currentState, newState) {
    this._stats.stateTransitions++;
    
    // Extract vectors
    const currentVector = this._extractStateVector(currentState);
    const newVector = this._extractStateVector(newState);
    
    // Check which dimensions exceed thresholds
    const transitions = {};
    const thresholdExceeded = {};
    
    // For each dimension, check if change exceeds threshold
    for (let i = 0; i < currentVector.length && i < newVector.length; i++) {
      const dimension = this._getDimensionName(i);
      const threshold = this.adaptiveThresholds[dimension] || this.baseCoherenceThreshold;
      
      // Calculate change magnitude
      const change = Math.abs(newVector[i] - currentVector[i]);
      const normalizedChange = change / Math.max(0.01, currentVector[i]);
      
      // Record transition
      transitions[dimension] = {
        from: currentVector[i],
        to: newVector[i],
        change,
        normalizedChange,
        threshold,
        exceeds: normalizedChange > threshold
      };
      
      // Track which thresholds were exceeded
      thresholdExceeded[dimension] = normalizedChange > threshold;
    }
    
    // Calculate overall state change
    const overallChange = this._calculateOverallChange(currentVector, newVector);
    
    // Calculate coherence between states
    const coherence = this._calculateCoherence(currentVector, newVector);
    
    // Determine if state change is significant
    const significantChange = overallChange > this.baseCoherenceThreshold ||
                             Object.values(thresholdExceeded).some(Boolean);
    
    // Create evaluation result
    const evaluation = {
      isSignificant: significantChange,
      overallChange,
      coherence,
      transitions,
      thresholdExceeded,
      timestamp: Date.now()
    };
    
    return evaluation;
  }
  
  /**
   * Regulate access to consciousness based on coherence
   * 
   * @param {Object} state - State seeking access
   * @param {Object} [context={}] - Access context
   * @returns {Object} Access decision
   */
  regulateAccess(state, context = {}) {
    const stateId = this._getStateId(state);
    const coherenceValue = this._getCoherenceValue(state);
    
    // Check if state already has access
    const hasExistingAccess = this._currentStateAccess.has(stateId);
    
    // Determine required threshold based on context
    let requiredThreshold = this.baseCoherenceThreshold;
    
    // Adjust threshold based on context
    if (context.importance && typeof context.importance === 'number') {
      // Lower threshold for important information
      requiredThreshold *= Math.max(0.7, 1 - context.importance * 0.3);
    }
    
    if (context.urgency && typeof context.urgency === 'number') {
      // Lower threshold for urgent information
      requiredThreshold *= Math.max(0.7, 1 - context.urgency * 0.3);
    }
    
    // Adjust threshold based on arousal
    // Higher arousal = higher threshold (more selective)
    // Lower arousal = lower threshold (more permissive)
    const arousalFactor = (this.arousalLevel - 0.5) * 0.2 + 1;
    requiredThreshold *= arousalFactor;
    
    // Ensure threshold remains in valid range
    requiredThreshold = Math.min(this.maximumThreshold, 
                               Math.max(this.minimumThreshold, requiredThreshold));
    
    // Check if state meets threshold
    const meetsThreshold = coherenceValue >= requiredThreshold;
    
    // Make access decision
    const accessGranted = meetsThreshold || 
                         (hasExistingAccess && coherenceValue >= requiredThreshold * 0.7);
    
    // Create access record
    const accessRecord = {
      stateId,
      coherence: coherenceValue,
      threshold: requiredThreshold,
      granted: accessGranted,
      context: { ...context },
      timestamp: Date.now()
    };
    
    // Update tracking
    if (accessGranted) {
      this._currentStateAccess.set(stateId, {
        lastAccess: Date.now(),
        coherence: coherenceValue
      });
      
      this.accessHistory.push(accessRecord);
      this._stats.accessGranted++;
      
      // Trim history if needed
      if (this.accessHistory.length > 100) {
        this.accessHistory.splice(0, this.accessHistory.length - 100);
      }
    } else {
      this._currentStateAccess.delete(stateId);
      
      this.accessDeniedHistory.push(accessRecord);
      this._stats.accessDenied++;
      
      // Trim history if needed
      if (this.accessDeniedHistory.length > 100) {
        this.accessDeniedHistory.splice(0, this.accessDeniedHistory.length - 100);
      }
    }
    
    // Clean up old access records
    this._cleanupAccessRecords();
    
    // Return access decision
    return {
      granted: accessGranted,
      coherence: coherenceValue,
      threshold: requiredThreshold,
      explanation: this._generateAccessExplanation(accessGranted, coherenceValue, requiredThreshold),
      timestamp: Date.now()
    };
  }
  
  /**
   * Determine consciousness level for a state
   * 
   * @param {Object} state - Consciousness state
   * @returns {Object} Consciousness level
   */
  determineConsciousnessLevel(state) {
    // Extract key values
    const coherence = this._getCoherenceValue(state);
    const selfReference = state.selfReference || 
                         (state.vector && state.vector.length > 5 ? state.vector[5] : 0);
    
    // Calculate integrated consciousness value
    const integrated = coherence * 0.6 + selfReference * 0.4;
    
    // Find appropriate level
    let level = this.consciousnessLevels[0]; // Default to lowest level
    
    for (const lvl of this.consciousnessLevels) {
      if (integrated >= lvl.threshold) {
        level = lvl;
      } else {
        break;
      }
    }
    
    // Calculate progress to next level
    let progressToNext = 1.0;
    const currentIndex = this.consciousnessLevels.indexOf(level);
    
    if (currentIndex < this.consciousnessLevels.length - 1) {
      const nextLevel = this.consciousnessLevels[currentIndex + 1];
      const range = nextLevel.threshold - level.threshold;
      
      if (range > 0) {
        progressToNext = Math.min(1, Math.max(0, (integrated - level.threshold) / range));
      }
    }
    
    return {
      level: level.name,
      threshold: level.threshold,
      integrated,
      coherence,
      selfReference,
      progressToNext
    };
  }
  
  /**
   * Update arousal level based on state
   * 
   * @private
   * @param {Object} state - Current consciousness state
   * @param {Object} previousState - Previous state
   */
  _updateArousalLevel(state, previousState) {
    // Extract current attention and awareness
    const attention = state.attention || 
                     (state.vector && state.vector.length > 0 ? state.vector[0] : 0.5);
    
    const awareness = state.awareness || 
                     (state.vector && state.vector.length > 1 ? state.vector[1] : 0.5);
    
    // Calculate target arousal
    const targetArousal = attention * 0.7 + awareness * 0.3;
    
    // If there's a previous state, check for significant changes
    if (previousState) {
      const prevAttention = previousState.attention || 
                           (previousState.vector && previousState.vector.length > 0 ? 
                            previousState.vector[0] : 0.5);
      
      const attentionChange = attention - prevAttention;
      
      // Significant attention change can shift arousal direction
      if (Math.abs(attentionChange) > 0.2) {
        this.arousalDirection = Math.sign(attentionChange);
        this.arousalMomentum = Math.min(0.3, Math.abs(attentionChange));
        this._stats.arousalShifts++;
      }
    }
    
    // Apply natural decay toward target
    const decayRate = 0.2;
    this.arousalLevel += (targetArousal - this.arousalLevel) * decayRate;
    
    // Apply directional momentum if present (gradually reducing)
    if (Math.abs(this.arousalMomentum) > 0.01) {
      this.arousalLevel += this.arousalDirection * this.arousalMomentum;
      this.arousalMomentum *= 0.9; // Decay momentum
    }
    
    // Add natural fluctuation
    this.arousalFluctuation = this.arousalFluctuation * 0.9 + (Math.random() - 0.5) * 0.04;
    this.arousalLevel += this.arousalFluctuation;
    
    // Ensure arousal remains in valid range
    this.arousalLevel = Math.min(1.0, Math.max(0.1, this.arousalLevel));
    
    // Update base if arousal stabilizes
    if (Math.abs(this.arousalLevel - this.arousalBase) < 0.05 &&
        Math.abs(this.arousalMomentum) < 0.02) {
      this.arousalBase = this.arousalBase * 0.95 + this.arousalLevel * 0.05;
    }
  }
  
  /**
   * Update adaptive thresholds based on system state
   * 
   * @private
   * @param {Object} state - Current consciousness state
   */
  _updateAdaptiveThresholds(state) {
    // Extract coherence as foundation for thresholds
    const coherence = state.coherence || 
                     (state.vector && state.vector.length > 2 ? state.vector[2] : 0.5);
    
    // Get additional state properties
    const selfReference = state.selfReference || 
                         (state.vector && state.vector.length > 5 ? state.vector[5] : 0.5);
    
    const temporalBinding = state.temporalBinding || 
                          (state.vector && state.vector.length > 6 ? state.vector[6] : 0.5);
    
    // Adjust base threshold based on coherence and arousal
    let adjustedBaseThreshold = this.baseCoherenceThreshold;
    
    // Higher coherence allows for higher thresholds (more selective)
    adjustedBaseThreshold += (coherence - 0.5) * 0.1;
    
    // Arousal affects threshold (higher arousal = higher threshold)
    adjustedBaseThreshold += (this.arousalLevel - 0.5) * 0.15;
    
    // Ensure base threshold is in valid range
    adjustedBaseThreshold = Math.min(this.maximumThreshold, 
                                   Math.max(this.minimumThreshold, adjustedBaseThreshold));
    
    // Update each dimension threshold with adaptive adjustments
    for (const dimension in this.dimensionThresholds) {
      // Start with original threshold
      let adaptiveThreshold = this.dimensionThresholds[dimension];
      
      // Apply base adjustment
      const deviation = adaptiveThreshold - this.baseCoherenceThreshold;
      adaptiveThreshold = adjustedBaseThreshold + deviation;
      
      // Apply dimension-specific adjustments
      switch (dimension) {
        case 'attention':
          // Attention threshold affected by arousal
          adaptiveThreshold += (this.arousalLevel - 0.5) * 0.2;
          break;
          
        case 'awareness':
          // Awareness threshold affected by self-reference
          adaptiveThreshold += (selfReference - 0.5) * 0.15;
          break;
          
        case 'coherence':
          // Coherence threshold is relatively stable
          break;
          
        case 'integration':
          // Integration threshold affected by temporal binding
          adaptiveThreshold += (temporalBinding - 0.5) * 0.15;
          break;
          
        case 'differentiation':
          // Differentiation threshold inversely affected by integration
          const integration = state.integration || 
                             (state.vector && state.vector.length > 3 ? state.vector[3] : 0.5);
          adaptiveThreshold -= (integration - 0.5) * 0.1;
          break;
          
        case 'selfReference':
          // Self-reference threshold highest during metaconsciousness
          if (selfReference > 0.8) {
            adaptiveThreshold -= 0.1; // Easier to maintain once established
          } else {
            adaptiveThreshold += 0.05; // Harder to establish initially
          }
          break;
          
        case 'temporalBinding':
          // Temporal binding threshold affected by coherence
          adaptiveThreshold += (coherence - 0.5) * 0.1;
          break;
      }
      
      // Apply adaptation rate
      this.adaptiveThresholds[dimension] = this.adaptiveThresholds[dimension] * (1 - this.adaptationRate) + 
                                          adaptiveThreshold * this.adaptationRate;
      
      // Ensure threshold remains in valid range
      this.adaptiveThresholds[dimension] = Math.min(this.maximumThreshold, 
                                             Math.max(this.minimumThreshold, this.adaptiveThresholds[dimension]));
    }
  }
  
  /**
   * Record current threshold state for history
   * 
   * @private
   */
  _recordThresholdState() {
    const thresholdState = {
      timestamp: Date.now(),
      arousal: this.arousalLevel,
      baseThreshold: this.baseCoherenceThreshold,
      thresholds: { ...this.adaptiveThresholds }
    };
    
    this.thresholdHistory.push(thresholdState);
    
    // Trim history if needed
    if (this.thresholdHistory.length > 100) {
      this.thresholdHistory.splice(0, this.thresholdHistory.length - 100);
    }
  }
  
  /**
   * Clean up old access records
   * 
   * @private
   */
  _cleanupAccessRecords() {
    const now = Date.now();
    const timeout = 300000; // 5 minutes
    
    // Remove old access records
    for (const [stateId, record] of this._currentStateAccess.entries()) {
      if (now - record.lastAccess > timeout) {
        this._currentStateAccess.delete(stateId);
      }
    }
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
    const vector = new Array(7).fill(0);
    
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
   * Get dimension name for index
   * 
   * @private
   * @param {number} index - Dimension index
   * @returns {string} Dimension name
   */
  _getDimensionName(index) {
    const dimensions = [
      'attention', 'awareness', 'coherence', 'integration', 
      'differentiation', 'selfReference', 'temporalBinding'
    ];
    
    return dimensions[index] || `dimension${index}`;
  }
  
  /**
   * Calculate overall change between two state vectors
   * 
   * @private
   * @param {Array} v1 - First vector
   * @param {Array} v2 - Second vector
   * @returns {number} Overall change (0-1)
   */
  _calculateOverallChange(v1, v2) {
    if (!v1 || !v2 || !v1.length || !v2.length) {
      return 0;
    }
    
    const minLength = Math.min(v1.length, v2.length);
    let sumSquaredChanges = 0;
    
    for (let i = 0; i < minLength; i++) {
      const change = v2[i] - v1[i];
      sumSquaredChanges += change * change;
    }
    
    // Normalize to 0-1 range (assume max possible change is vector of length 1 in every dimension)
    return Math.min(1, Math.sqrt(sumSquaredChanges / minLength));
  }
  
  /**
   * Calculate coherence between two state vectors
   * 
   * @private
   * @param {Array} v1 - First vector
   * @param {Array} v2 - Second vector
   * @returns {number} Coherence value (0-1)
   */
  _calculateCoherence(v1, v2) {
    if (!v1 || !v2 || !v1.length || !v2.length) {
      return 0;
    }
    
    // Calculate cosine similarity
    let dotProduct = 0;
    let mag1 = 0;
    let mag2 = 0;
    
    const minLength = Math.min(v1.length, v2.length);
    
    for (let i = 0; i < minLength; i++) {
      dotProduct += v1[i] * v2[i];
      mag1 += v1[i] * v1[i];
      mag2 += v2[i] * v2[i];
    }
    
    const magnitude = Math.sqrt(mag1) * Math.sqrt(mag2);
    
    if (magnitude < 1e-10) {
      return 0;
    }
    
    // Convert from [-1,1] to [0,1] range
    return (dotProduct / magnitude + 1) / 2;
  }
  
  /**
   * Get state ID for access tracking
   * 
   * @private
   * @param {Object} state - State object
   * @returns {string} State ID
   */
  _getStateId(state) {
    if (!state) return 'null';
    
    if (state.id) return state.id;
    
    // Extract vector and create hash from it
    const vector = this._extractStateVector(state);
    
    // Create a simple hash
    const hash = vector.reduce(
      (h, v, i) => h + Math.round(v * 1000) * (i + 1), 0
    ).toString(36);
    
    return hash + '_' + Date.now().toString(36);
  }
  
  /**
   * Get coherence value from state
   * 
   * @private
   * @param {Object} state - State object
   * @returns {number} Coherence value (0-1)
   */
  _getCoherenceValue(state) {
    if (!state) return 0;
    
    // If state has coherence property, use it
    if (typeof state.coherence === 'number') {
      return Math.min(1, Math.max(0, state.coherence));
    }
    
    // If state has vector, use coherence dimension
    if (state.vector && Array.isArray(state.vector) && state.vector.length > 2) {
      return Math.min(1, Math.max(0, state.vector[2]));
    }
    
    // Default coherence
    return 0.5;
  }
  
  /**
   * Generate explanation for access decision
   * 
   * @private
   * @param {boolean} granted - Whether access was granted
   * @param {number} coherence - State coherence
   * @param {number} threshold - Required threshold
   * @returns {string} Access explanation
   */
  _generateAccessExplanation(granted, coherence, threshold) {
    if (granted) {
      if (coherence > threshold * 1.2) {
        return "Access granted: high coherence";
      } else if (coherence > threshold) {
        return "Access granted: sufficient coherence";
      } else {
        return "Access maintained from previous access";
      }
    } else {
      const gap = threshold - coherence;
      
      if (gap > 0.3) {
        return "Access denied: insufficient coherence";
      } else {
        return "Access denied: coherence below threshold";
      }
    }
  }
  
  /**
   * Set arousal level directly
   * 
   * @param {number} level - New arousal level (0-1)
   * @param {Object} [context={}] - Arousal context
   * @returns {Object} Arousal update
   */
  setArousalLevel(level, context = {}) {
    // Validate input
    const newLevel = Math.min(1, Math.max(0, level));
    
    // Record arousal shift
    const previousLevel = this.arousalLevel;
    const delta = newLevel - previousLevel;
    
    // Set new level
    this.arousalLevel = newLevel;
    
    // Update thresholds if significant change
    if (Math.abs(delta) > 0.1) {
      this._stats.arousalShifts++;
      
      // Set momentum in appropriate direction
      this.arousalDirection = Math.sign(delta);
      this.arousalMomentum = Math.min(0.3, Math.abs(delta) * 0.5);
      
      // If sustained shift, update base
      if (context.sustained) {
        this.arousalBase = this.arousalBase * 0.7 + newLevel * 0.3;
      }
    }
    
    return {
      previous: previousLevel,
      current: this.arousalLevel,
      delta,
      momentum: this.arousalMomentum,
      direction: this.arousalDirection,
      timestamp: Date.now()
    };
  }
  
  /**
   * Get current arousal state
   * 
   * @returns {Object} Arousal state
   */
  getArousalState() {
    // Categorize arousal level
    let category;
    
    if (this.arousalLevel < 0.3) {
      category = 'low';
    } else if (this.arousalLevel < 0.5) {
      category = 'moderate-low';
    } else if (this.arousalLevel < 0.7) {
      category = 'moderate';
    } else if (this.arousalLevel < 0.9) {
      category = 'moderate-high';
    } else {
      category = 'high';
    }
    
    return {
      level: this.arousalLevel,
      base: this.arousalBase,
      category,
      momentum: this.arousalMomentum,
      direction: this.arousalDirection,
      fluctuation: this.arousalFluctuation
    };
  }
  
  /**
   * Get current thresholds
   * 
   * @returns {Object} Current thresholds
   */
  getCurrentThresholds() {
    return {
      base: this.baseCoherenceThreshold,
      adaptive: { ...this.adaptiveThresholds },
      minimum: this.minimumThreshold,
      maximum: this.maximumThreshold,
      arousal: this.arousalLevel
    };
  }
  
  /**
   * Get threshold history
   * 
   * @param {number} [count=10] - Number of history items
   * @returns {Array} Threshold history
   */
  getThresholdHistory(count = 10) {
    const numItems = Math.min(count, this.thresholdHistory.length);
    return this.thresholdHistory.slice(-numItems);
  }
  
  /**
   * Get system performance statistics
   * 
   * @returns {Object} Performance statistics
   */
  getStats() {
    const averageProcessingTime = this._stats.thresholdAdjustments > 0
      ? this._stats.totalProcessingTime / this._stats.thresholdAdjustments
      : 0;
    
    const accessRate = (this._stats.accessGranted + this._stats.accessDenied) > 0
      ? this._stats.accessGranted / (this._stats.accessGranted + this._stats.accessDenied)
      : 0;
    
    return {
      ...this._stats,
      averageProcessingTime,
      accessRate,
      currentArousal: this.arousalLevel,
      baseArousal: this.arousalBase,
      currentThresholdAverage: Object.values(this.adaptiveThresholds)
        .reduce((sum, val) => sum + val, 0) / Object.keys(this.adaptiveThresholds).length
    };
  }
  
  /**
   * Reset the threshold manager
   */
  reset() {
    // Reset thresholds to defaults
    this.adaptiveThresholds = { ...this.dimensionThresholds };
    
    // Reset arousal
    this.arousalLevel = 0.5;
    this.arousalBase = 0.5;
    this.arousalFluctuation = 0.0;
    this.arousalDirection = 0;
    this.arousalMomentum = 0;
    
    // Clear history
    this.accessHistory = [];
    this.accessDeniedHistory = [];
    this._currentStateAccess.clear();
    this.thresholdHistory = [];
    
    // Reset stats
    this._stats = {
      stateTransitions: 0,
      thresholdAdjustments: 0,
      accessGranted: 0,
      accessDenied: 0,
      arousalShifts: 0,
      totalProcessingTime: 0
    };
    
    this._lastUpdateTime = Date.now();
  }
}

module.exports = ThresholdManager;