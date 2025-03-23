/**
 * PrimeOS JavaScript Library - Self-Reference Module
 *
 * This module implements self-referential capabilities for PrimeOS,
 * allowing the system to examine and modify its own state.
 */

// Import Prime core
const Prime = require('../core');

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
      ...config,
    };

    // Internal state representation
    this.currentState = {
      coherence: 0.8,
      complexity: 0.5,
      awareness: 0.6,
      timestamp: Date.now(),
    };

    // State history
    this.stateHistory = [];

    // System limitations model (self-aware of limitations)
    this.knownLimitations = [
      {
        id: 'numerical_precision',
        description: 'Limited by IEEE-754 double precision floating point',
        severity: 'medium',
      },
      {
        id: 'computational_resources',
        description: 'Constrained by available memory and processing power',
        severity: 'medium',
      },
      {
        id: 'domain_knowledge',
        description: 'Limited to domains covered in training data',
        severity: 'high',
      },
    ];
  }

  /**
   * Examine current system state
   * @returns {Object} Current state
   */
  async examine() {
    // Record current state in history
    this._recordStateInHistory();

    // Return a copy of the current state
    return { ...this.currentState };
  }

  /**
   * Modify system state
   * @param {Object} delta - State changes to apply
   * @returns {Object} Updated state
   */
  async modifyState(delta) {
    // Apply changes within bounds
    if (delta.coherence !== undefined) {
      this.currentState.coherence = Math.max(
        0,
        Math.min(1, this.currentState.coherence + delta.coherence),
      );
    }

    if (delta.complexity !== undefined) {
      this.currentState.complexity = Math.max(
        0,
        Math.min(1, this.currentState.complexity + delta.complexity),
      );
    }

    if (delta.awareness !== undefined) {
      this.currentState.awareness = Math.max(
        0,
        Math.min(1, this.currentState.awareness + delta.awareness),
      );
    }

    // Update timestamp
    this.currentState.timestamp = Date.now();

    // Record state change
    this._recordStateInHistory();

    // Return updated state
    return { ...this.currentState };
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
        coherenceTrend: 'stable',
        complexityTrend: 'stable',
        awarenessTrend: 'stable',
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
      if (Math.abs(delta) < 0.05) return 'stable';
      return delta > 0 ? 'increasing' : 'decreasing';
    };

    return {
      coherenceTrend: getTrend(coherenceDelta),
      complexityTrend: getTrend(complexityDelta),
      awarenessTrend: getTrend(awarenessDelta),
    };
  }

  /**
   * Record state in history
   * @private
   */
  _recordStateInHistory() {
    // Add current state to history
    this.stateHistory.push({ ...this.currentState });

    // Limit history size
    if (this.stateHistory.length > this.config.stateHistorySize) {
      this.stateHistory.shift();
    }
  }
}

// Add to Prime.Consciousness namespace
Prime.Consciousness.SelfReference = SelfReference;

// Export both the module and enhanced Prime
module.exports = {
  SelfReference,
  Prime,
};
