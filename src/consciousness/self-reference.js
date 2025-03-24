/**
 * PrimeOS JavaScript Library - Self-Reference Module
 *
 * This module implements self-referential capabilities for PrimeOS,
 * allowing the system to examine and modify its own state.
 */

// Import Prime core
const Prime = require("../core");

// Ensure Consciousness namespace exists
Prime.Consciousness = Prime.Consciousness || {};

/**
 * Self-reference module for introspection and state examination
 * @class
 */
class SelfReference {
  /**
   * Create a new self-reference module
   * @param {Object} config - Configuration options
   */
  constructor(config = {}) {
    this.config = {
      stateHistorySize: config.stateHistorySize || 100,
      coherenceThreshold: config.coherenceThreshold || 0.7,
      minCoherence: config.minCoherence || 0.3,
      maxComplexity: config.maxComplexity || 0.9,
      selfUpdateInterval: config.selfUpdateInterval || 1000, // ms
      ...config,
    };

    // Internal state representation with initial neutral values
    this.currentState = {
      coherence: 0.5,
      complexity: 0.5,
      awareness: 0.5,
      integration: 0.5,
      differentiation: 0.5,
      stability: 0.5,
      adaptability: 0.5,
      timestamp: Date.now(),
    };

    // State history
    this.stateHistory = [];
    
    // State transition metrics
    this.stateTransitions = {
      count: 0,
      averageCoherenceChange: 0,
      significantTransitions: 0,
      lastTransitionTime: Date.now()
    };

    // Self-monitoring metrics
    this.selfMonitoring = {
      lastUpdateTime: Date.now(),
      updateCount: 0,
      averageUpdateInterval: 0,
      coherenceViolations: 0,
      stateRecoveries: 0
    };

    // System limitations model (self-aware of limitations)
    this.knownLimitations = [];
    this._initializeLimitations();
    
    // Coherence calculator for state comparisons
    this.coherenceCalculator = this._createCoherenceCalculator();
  }
  
  /**
   * Initialize system limitations model
   * @private
   */
  _initializeLimitations() {
    // Core system limitations
    this.knownLimitations = [
      {
        id: "numerical_precision",
        description: "Limited by IEEE-754 double precision floating point",
        severity: "medium",
        mitigationStrategy: "Use epsilon values for floating point comparisons",
        impact: "May cause small coherence calculation errors in edge cases"
      },
      {
        id: "computational_resources",
        description: "Constrained by available memory and processing power",
        severity: "medium",
        mitigationStrategy: "Limit state history size and use efficient calculations",
        impact: "May need to prune older states to maintain performance"
      },
      {
        id: "temporal_binding",
        description: "Limited temporal binding window for coherence calculation",
        severity: "medium",
        mitigationStrategy: "Weight recent events more heavily in calculations",
        impact: "May lose long-term temporal coherence patterns"
      },
      {
        id: "self_model_completeness",
        description: "Self-model cannot fully represent all system aspects",
        severity: "high",
        mitigationStrategy: "Focus on most critical state dimensions",
        impact: "Some state aspects may not be included in self-reference"
      }
    ];
  }
  
  /**
   * Create coherence calculator for comparing states
   * @private
   * @returns {Function} Coherence calculation function
   */
  _createCoherenceCalculator() {
    return (state1, state2) => {
      if (!state1 || !state2) return 0;
      
      // Extract key metrics for comparison
      const keys = Object.keys(state1).filter(k => 
        typeof state1[k] === 'number' && 
        typeof state2[k] === 'number' &&
        k !== 'timestamp'
      );
      
      if (keys.length === 0) return 0;
      
      // Calculate vector similarity between states
      let dotProduct = 0;
      let mag1 = 0;
      let mag2 = 0;
      
      for (const key of keys) {
        dotProduct += state1[key] * state2[key];
        mag1 += state1[key] * state1[key];
        mag2 += state2[key] * state2[key];
      }
      
      const magnitude = Math.sqrt(mag1) * Math.sqrt(mag2);
      
      if (magnitude < 1e-10) return 0;
      
      // Convert from [-1,1] to [0,1] range
      return (dotProduct / magnitude + 1) / 2;
    };
  }

  /**
   * Examine current system state
   * @param {Object} options - Examination options
   * @param {boolean} options.includeHistory - Whether to include state history
   * @param {boolean} options.includeTransitions - Whether to include state transitions
   * @param {boolean} options.includeLimitations - Whether to include known limitations
   * @returns {Object} Current state with metadata
   */
  async examine(options = {}) {
    // Update self-monitoring metrics
    this._updateSelfMonitoring();
    
    // Record current state in history
    this._recordStateInHistory();

    // Build result object with current state
    const result = {
      state: { ...this.currentState },
      selfMonitoring: { ...this.selfMonitoring }
    };
    
    // Add optional components based on request
    if (options.includeHistory) {
      result.history = this.stateHistory.slice(-10); // Last 10 states
    }
    
    if (options.includeTransitions) {
      result.transitions = { ...this.stateTransitions };
    }
    
    if (options.includeLimitations) {
      result.limitations = [...this.knownLimitations];
    }

    return result;
  }

  /**
   * Modify system state
   * @param {Object} delta - State changes to apply
   * @param {Object} options - Modification options
   * @param {boolean} options.enforceCoherence - Whether to enforce coherence
   * @param {boolean} options.recordTransition - Whether to record as a transition
   * @returns {Object} Updated state
   */
  async modifyState(delta, options = {}) {
    // Store previous state for coherence calculation
    const previousState = { ...this.currentState };
    
    // Create a copy of the current state to modify
    const newState = { ...this.currentState };
    
    // Track if any changes were made
    let changed = false;
    
    // Apply changes within bounds for all numeric properties
    Object.keys(delta).forEach(key => {
      if (typeof delta[key] === 'number' && key !== 'timestamp') {
        // Handle both absolute values and deltas
        if (Math.abs(delta[key]) <= 1 && this.currentState[key] !== undefined) {
          // Treat as a delta if small value
          newState[key] = Math.max(0, Math.min(1, this.currentState[key] + delta[key]));
        } else {
          // Treat as absolute value (ensure within 0-1 range)
          newState[key] = Math.max(0, Math.min(1, delta[key]));
        }
        changed = true;
      }
    });
    
    // If no changes were actually made, return current state
    if (!changed) {
      return { ...this.currentState };
    }
    
    // Update timestamp
    newState.timestamp = Date.now();
    
    // Check coherence if enabled
    if (options.enforceCoherence !== false) {
      const coherence = this.coherenceCalculator(previousState, newState);
      
      // If coherence is too low, adjust the state
      if (coherence < this.config.minCoherence) {
        // Record the coherence violation
        this.selfMonitoring.coherenceViolations++;
        
        // Create a blended state with better coherence
        const blendFactor = 0.7; // Weight toward previous state for stability
        Object.keys(newState).forEach(key => {
          if (typeof newState[key] === 'number' && key !== 'timestamp') {
            newState[key] = (blendFactor * previousState[key]) + 
                           ((1 - blendFactor) * newState[key]);
          }
        });
        
        // Record state recovery
        this.selfMonitoring.stateRecoveries++;
      }
    }
    
    // Apply the new state
    this.currentState = newState;
    
    // Record state change
    this._recordStateInHistory();
    
    // Update transition metrics if requested
    if (options.recordTransition !== false) {
      this._recordStateTransition(previousState, newState);
    }

    // Return updated state
    return { ...this.currentState };
  }
  
  /**
   * Record a state transition and update metrics
   * @private
   * @param {Object} fromState - Previous state
   * @param {Object} toState - New state
   */
  _recordStateTransition(fromState, toState) {
    // Calculate coherence between states
    const coherence = this.coherenceCalculator(fromState, toState);
    
    // Update transition count
    this.stateTransitions.count++;
    
    // Update average coherence change
    const coherenceChange = Math.abs(toState.coherence - fromState.coherence);
    this.stateTransitions.averageCoherenceChange = 
      ((this.stateTransitions.averageCoherenceChange * (this.stateTransitions.count - 1)) + 
       coherenceChange) / this.stateTransitions.count;
    
    // Record if this was a significant transition
    if (coherenceChange > 0.2) {
      this.stateTransitions.significantTransitions++;
    }
    
    // Update last transition time
    this.stateTransitions.lastTransitionTime = Date.now();
  }
  
  /**
   * Update self-monitoring metrics
   * @private
   */
  _updateSelfMonitoring() {
    const now = Date.now();
    const elapsed = now - this.selfMonitoring.lastUpdateTime;
    
    this.selfMonitoring.updateCount++;
    
    // Update average update interval
    this.selfMonitoring.averageUpdateInterval = 
      ((this.selfMonitoring.averageUpdateInterval * (this.selfMonitoring.updateCount - 1)) + 
       elapsed) / this.selfMonitoring.updateCount;
    
    this.selfMonitoring.lastUpdateTime = now;
  }

  /**
   * Analyze system limitations
   * @returns {Array<Object>} System limitations
   */
  async analyzeLimitations() {
    // Return known limitations
    return [...this.knownLimitations];
  }

  /**
   * Get state history
   * @param {Object} options - Query options
   * @returns {Array<Object>} State history
   */
  async getStateHistory(options = {}) {
    // Apply filters if provided
    let history = [...this.stateHistory];

    if (options.timeRange) {
      const [start, end] = options.timeRange;
      history = history.filter(
        (state) => state.timestamp >= start && state.timestamp <= end,
      );
    }

    if (options.minCoherence) {
      history = history.filter(
        (state) => state.coherence >= options.minCoherence,
      );
    }

    return history;
  }

  /**
   * Analyze state changes over time
   * @returns {Object} Analysis results
   */
  async analyzeStateChanges() {
    if (this.stateHistory.length < 2) {
      return {
        coherenceTrend: "stable",
        complexityTrend: "stable",
        awarenessTrend: "stable",
      };
    }

    // Calculate trends
    const first = this.stateHistory[0];
    const last = this.stateHistory[this.stateHistory.length - 1];

    const coherenceDelta = last.coherence - first.coherence;
    const complexityDelta = last.complexity - first.complexity;
    const awarenessDelta = last.awareness - first.awareness;

    // Determine trend directions
    const getTrend = (delta) => {
      if (Math.abs(delta) < 0.05) return "stable";
      return delta > 0 ? "increasing" : "decreasing";
    };

    return {
      coherenceTrend: getTrend(coherenceDelta),
      complexityTrend: getTrend(complexityDelta),
      awarenessTrend: getTrend(awarenessDelta),
    };
  }

  /**
   * Create initial self model based on state
   * @param {Object} state - Initial state
   * @param {Object} options - Self model options
   * @param {boolean} options.includeAllFields - Whether to include all state fields
   * @param {Array<string>} options.fields - Specific fields to include
   * @returns {Object} Initial self model
   */
  createInitialSelfModel(state, options = {}) {
    // Update self monitoring
    this._updateSelfMonitoring();
    
    // Create base self model
    const selfModel = {
      id: this._generateModelId(),
      timestamp: Date.now(),
      created: Date.now(),
      version: 1.0,
      source: 'SelfReference.createInitialSelfModel',
      metrics: {},
      components: {},
      stateReference: { id: this._generateStateId(state) }
    };
    
    // Determine which fields to include
    const fieldsToInclude = options.includeAllFields ? 
      Object.keys(state).filter(k => typeof state[k] === 'number') :
      (options.fields || ['coherence', 'complexity', 'awareness', 'integration', 'differentiation']);
    
    // Copy specified fields from state
    fieldsToInclude.forEach(field => {
      if (state[field] !== undefined) {
        selfModel.metrics[field] = state[field];
      } else if (this.currentState[field] !== undefined) {
        selfModel.metrics[field] = this.currentState[field];
      }
    });
    
    // Set core metrics if not already present
    if (selfModel.metrics.coherence === undefined) {
      selfModel.metrics.coherence = state.coherence || this.currentState.coherence;
    }
    
    if (selfModel.metrics.complexity === undefined) {
      selfModel.metrics.complexity = state.complexity || this.currentState.complexity;
    }
    
    if (selfModel.metrics.awareness === undefined) {
      selfModel.metrics.awareness = state.awareness || this.currentState.awareness;
    }
    
    // Calculate component relationships
    selfModel.components = {
      memory: { coherence: this._estimateComponentCoherence(state, 'memory') },
      attention: { coherence: this._estimateComponentCoherence(state, 'attention') },
      temporal: { coherence: this._estimateComponentCoherence(state, 'temporal') }
    };
    
    // Reset state to match the model
    this.currentState = {
      ...this.currentState,
      ...selfModel.metrics,
      timestamp: Date.now()
    };
    
    // Store in history
    this._recordStateInHistory();

    return selfModel;
  }

  /**
   * Update self model with new state information
   * @param {Object} state - Current system state
   * @param {Object} selfModel - Previous self model
   * @param {Object} options - Update options
   * @param {boolean} options.enforceCoherence - Whether to enforce coherence
   * @param {number} options.minCoherenceThreshold - Minimum coherence threshold
   * @returns {Object} Updated self model
   */
  update(state, selfModel, options = {}) {
    // Default options
    const updateOptions = {
      enforceCoherence: true,
      minCoherenceThreshold: this.config.minCoherence,
      ...options
    };
    
    // Store previous state for coherence calculation
    const previousState = { ...this.currentState };
    
    // Update self monitoring
    this._updateSelfMonitoring();
    
    // Extract metrics from state
    const metrics = {};
    Object.keys(state).forEach(key => {
      if (typeof state[key] === 'number' && key !== 'timestamp') {
        metrics[key] = state[key];
      }
    });
    
    // Calculate coherence between current and new state
    const newStateCoherence = this.coherenceCalculator(previousState, metrics);
    
    // Check if we need to enforce coherence
    if (updateOptions.enforceCoherence && 
        newStateCoherence < updateOptions.minCoherenceThreshold) {
      
      // Record violation
      this.selfMonitoring.coherenceViolations++;
      
      // Blend new values with old to maintain coherence
      const blendFactor = Math.max(0.5, newStateCoherence);
      Object.keys(metrics).forEach(key => {
        if (previousState[key] !== undefined) {
          metrics[key] = (blendFactor * previousState[key]) + 
                        ((1 - blendFactor) * metrics[key]);
        }
      });
      
      // Record recovery
      this.selfMonitoring.stateRecoveries++;
    }
    
    // Update the current state with metrics from system state
    this.currentState = {
      ...this.currentState,
      ...metrics,
      timestamp: Date.now()
    };
    
    // Record state transition
    this._recordStateTransition(previousState, this.currentState);

    // Record the updated state in history
    this._recordStateInHistory();
    
    // Update self model version
    const newModelVersion = (selfModel.version || 1.0) + 0.1;
    
    // Create component relationship updates
    const updatedComponents = {
      memory: { 
        coherence: this._estimateComponentCoherence(state, 'memory'),
        lastUpdate: Date.now()
      },
      attention: { 
        coherence: this._estimateComponentCoherence(state, 'attention'),
        lastUpdate: Date.now()
      },
      temporal: { 
        coherence: this._estimateComponentCoherence(state, 'temporal'),
        lastUpdate: Date.now()
      }
    };

    // Create updated self model
    const updatedModel = {
      ...selfModel,
      version: newModelVersion,
      lastUpdated: Date.now(),
      updateCount: (selfModel.updateCount || 0) + 1,
      metrics: {
        ...(selfModel.metrics || {}),
        ...this._extractMetrics(this.currentState)
      },
      components: {
        ...(selfModel.components || {}),
        ...updatedComponents
      },
      stateReference: {
        id: this._generateStateId(state),
        timestamp: state.timestamp || Date.now()
      },
      coherence: newStateCoherence
    };

    return updatedModel;
  }
  
  /**
   * Extract metrics from a state object
   * @private
   * @param {Object} state - State object
   * @returns {Object} Extracted metrics
   */
  _extractMetrics(state) {
    const metrics = {};
    
    Object.keys(state).forEach(key => {
      if (typeof state[key] === 'number' && key !== 'timestamp') {
        metrics[key] = state[key];
      }
    });
    
    return metrics;
  }
  
  /**
   * Estimate coherence between this component and another component
   * @private
   * @param {Object} state - System state
   * @param {string} componentType - Type of component
   * @returns {number} Estimated coherence
   */
  _estimateComponentCoherence(state, componentType) {
    // Default coherence estimates based on component type
    const baseCoherence = {
      'memory': 0.8,
      'attention': 0.7,
      'temporal': 0.75
    }[componentType] || 0.6;
    
    // If state has a specific coherence for this component, use it
    const componentCoherence = state[`${componentType}Coherence`];
    if (typeof componentCoherence === 'number') {
      return componentCoherence;
    }
    
    // Use global coherence as a modifier if available
    if (typeof state.coherence === 'number') {
      return baseCoherence * (0.5 + state.coherence / 2);
    }
    
    return baseCoherence;
  }
  
  /**
   * Generate a unique state ID
   * @private
   * @param {Object} state - State object
   * @returns {string} Unique state ID
   */
  _generateStateId(state) {
    // Create a simple hash from state content
    const stateString = JSON.stringify(state);
    let hash = 0;
    
    for (let i = 0; i < stateString.length; i++) {
      const char = stateString.charCodeAt(i);
      hash = ((hash << 5) - hash) + char;
      hash = hash & hash; // Convert to 32bit integer
    }
    
    // Combine with timestamp for uniqueness
    return `state_${Math.abs(hash)}_${Date.now()}`;
  }
  
  /**
   * Generate a unique model ID
   * @private
   * @returns {string} Unique model ID
   */
  _generateModelId() {
    return `model_${Date.now()}_${Math.floor(Math.random() * 10000)}`;
  }

  /**
   * Record state in history
   * @private
   * @param {Object} [extraData] - Additional data to store with state
   */
  _recordStateInHistory(extraData = {}) {
    // Create historical record with metadata
    const historyRecord = {
      ...this.currentState,
      _meta: {
        recordTime: Date.now(),
        stateId: this._generateStateId(this.currentState),
        ...extraData
      }
    };
    
    // Add to history
    this.stateHistory.push(historyRecord);

    // Limit history size
    if (this.stateHistory.length > this.config.stateHistorySize) {
      // Remove oldest entries while keeping important ones
      
      // Find oldest non-significant states to remove first
      const significantThreshold = 0.8; // Coherence threshold for significance
      const oldestNonSignificantIndex = this.stateHistory.findIndex(
        (state, index) => 
          index < this.stateHistory.length / 2 && // Only consider first half
          (!state.coherence || state.coherence < significantThreshold)
      );
      
      if (oldestNonSignificantIndex > 0) {
        // Remove oldest non-significant state
        this.stateHistory.splice(oldestNonSignificantIndex, 1);
      } else {
        // If all are significant or we're in the second half, remove oldest
        this.stateHistory.shift();
      }
    }
  }

  /**
   * Get statistics about self reference module
   * @param {Object} options - Stats options
   * @param {boolean} options.detailed - Whether to include detailed stats
   * @param {boolean} options.includeHistory - Whether to include history stats
   * @returns {Object} Stats about self reference operations
   */
  getStats(options = {}) {
    // Basic stats
    const stats = {
      historySize: this.stateHistory.length,
      averageCoherence:
        this.stateHistory.reduce((sum, state) => sum + (state.coherence || 0), 0) /
        (this.stateHistory.length || 1),
      currentCoherence: this.currentState.coherence,
      stateChanges: this.stateHistory.length,
      knownLimitationsCount: this.knownLimitations.length,
      selfReferenceUpdates: this.selfMonitoring.updateCount,
      coherenceViolations: this.selfMonitoring.coherenceViolations,
      stateRecoveries: this.selfMonitoring.stateRecoveries
    };
    
    // Include detailed stats if requested
    if (options.detailed) {
      stats.detailed = {
        averageUpdateInterval: this.selfMonitoring.averageUpdateInterval,
        coherenceHistory: this.stateHistory.map(s => s.coherence || 0),
        stateTransitions: { ...this.stateTransitions },
        metrics: {}
      };
      
      // Calculate metrics for all numeric properties
      const metricKeys = new Set();
      this.stateHistory.forEach(state => {
        Object.keys(state).forEach(key => {
          if (typeof state[key] === 'number' && key !== 'timestamp') {
            metricKeys.add(key);
          }
        });
      });
      
      // Calculate average for each metric
      metricKeys.forEach(key => {
        const values = this.stateHistory
          .map(state => state[key])
          .filter(val => typeof val === 'number');
          
        if (values.length > 0) {
          const sum = values.reduce((a, b) => a + b, 0);
          stats.detailed.metrics[key] = {
            average: sum / values.length,
            current: this.currentState[key] || 0,
            min: Math.min(...values),
            max: Math.max(...values)
          };
        }
      });
    }
    
    // Include history stats if requested
    if (options.includeHistory) {
      stats.historyStats = {
        oldestState: this.stateHistory.length > 0 ? 
          this.stateHistory[0].timestamp : null,
        newestState: this.stateHistory.length > 0 ? 
          this.stateHistory[this.stateHistory.length - 1].timestamp : null,
        timeSpan: this.stateHistory.length > 0 ? 
          (this.stateHistory[this.stateHistory.length - 1].timestamp - 
           this.stateHistory[0].timestamp) : 0,
        significantStates: this.stateHistory.filter(
          state => state.coherence && state.coherence > 0.8
        ).length
      };
    }

    return stats;
  }

  /**
   * Reset self reference module
   * @param {Object} options - Reset options
   * @param {boolean} options.keepLimitations - Whether to keep known limitations
   * @param {boolean} options.keepHistory - Whether to keep state history
   */
  reset(options = {}) {
    // Reset to initial neutral state
    this.currentState = {
      coherence: 0.5,
      complexity: 0.5,
      awareness: 0.5,
      integration: 0.5,
      differentiation: 0.5,
      stability: 0.5,
      adaptability: 0.5,
      timestamp: Date.now(),
    };

    // Clear history if not keeping it
    if (!options.keepHistory) {
      this.stateHistory = [];
    }
    
    // Reset state transitions
    this.stateTransitions = {
      count: 0,
      averageCoherenceChange: 0,
      significantTransitions: 0,
      lastTransitionTime: Date.now()
    };
    
    // Reset self-monitoring
    this.selfMonitoring = {
      lastUpdateTime: Date.now(),
      updateCount: 0,
      averageUpdateInterval: 0,
      coherenceViolations: 0,
      stateRecoveries: 0
    };
    
    // Reset limitations if not keeping them
    if (!options.keepLimitations) {
      this.knownLimitations = [];
      this._initializeLimitations();
    }
    
    // Record initialization state
    this._recordStateInHistory({ event: 'reset' });
  }
}

// Add to Prime.Consciousness namespace
Prime.Consciousness.SelfReference = SelfReference;

// Export both the module and enhanced Prime
module.exports = {
  SelfReference,
  Prime,
};
