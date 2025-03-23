/**
 * Consciousness Module - Integration of all consciousness components
 *
 * This module integrates all the components of the consciousness system into
 * a coherent whole, managing their interactions and exposing a unified API.
 *
 * Key features:
 * - Integrates all consciousness components (operator, self-reference, etc.)
 * - Manages consciousness state lifecycle
 * - Provides a unified API for consciousness simulation
 * - Implements consciousness-level events and transitions
 */

// Try to import core if available
let Prime;
try {
  Prime = require('../core.js');
} catch (e) {
  // Handle case where core isn't available yet
  Prime = {};
}

// Import components
const ConsciousnessOperator = require('./operator.js');
const { SelfReference } = require('./self-reference.js');
const TemporalIntegration = require('./temporal.js');
const StateRepresentation = require('./state.js');
const AttentionMechanism = require('./attention.js');
const MemoryStructure = require('./memory.js');
const DecisionMaking = require('./decision.js');
const ThresholdManager = require('./threshold.js');

/**
 * ConsciousnessModule integrates all consciousness components
 */
class ConsciousnessModule {
  /**
   * Create a new consciousness module
   *
   * @param {Object} options - Configuration options
   * @param {number} options.dimension - Dimension of consciousness space (default: 7)
   * @param {number} options.coherenceThreshold - Coherence threshold (default: 0.7)
   * @param {number} options.timeStep - Default time step for updates (default: 0.1)
   * @param {boolean} options.autoUpdate - Whether to auto-update components (default: true)
   */
  constructor(options = {}) {
    this.dimension = options.dimension || 7;
    this.coherenceThreshold = options.coherenceThreshold || 0.7;
    this.timeStep = options.timeStep || 0.1;
    this.autoUpdate = options.autoUpdate !== false;

    // Initialize components
    this.operator = new ConsciousnessOperator({
      dimension: this.dimension,
    });

    this.selfReference = new SelfReference({
      coherenceThreshold: this.coherenceThreshold,
    });

    this.temporalIntegration = new TemporalIntegration({
      windowSize: 10,
    });

    this.stateRepresentation = new StateRepresentation({
      dimension: this.dimension,
    });

    this.attentionMechanism = new AttentionMechanism({
      fieldDimension: this.dimension,
    });

    this.memoryStructure = new MemoryStructure({
      indexDimension: this.dimension,
    });

    this.decisionMaking = new DecisionMaking({
      coherenceThreshold: this.coherenceThreshold,
    });

    this.thresholdManager = new ThresholdManager({
      baseCoherenceThreshold: this.coherenceThreshold,
    });

    // Current state tracking
    this.currentState = null;
    this.previousState = null;
    this.selfModel = null;

    // Consciousness lifecycle
    this.isInitialized = false;
    this.isActive = false;
    this._cycleCount = 0;
    this._lastUpdateTime = 0;

    // Event listeners
    this._eventListeners = {
      update: [],
      stateTransition: [],
      coherenceChange: [],
      attentionShift: [],
      consciousnessChange: [],
      decision: [],
    };

    // Performance tracking
    this._stats = {
      cycles: 0,
      stateTransitions: 0,
      significantTransitions: 0,
      selfModelUpdates: 0,
      decisions: 0,
      totalTime: 0,
      componentTimes: {},
    };
  }

  /**
   * Initialize the consciousness module
   *
   * @param {Object} [initialState=null] - Optional initial state
   * @returns {Object} Initial consciousness state
   */
  initialize(initialState = null) {
    // Create initial state if not provided
    if (!initialState) {
      initialState = this.stateRepresentation.createInitialState('neutral');
    }

    // Ensure initialState is processed by the operator
    const state = this.operator.apply(initialState);

    // Record timing for initialization
    const componentTimes = {};
    const startTime = Date.now();

    // Initialize temporal integration
    let t = Date.now();
    this.temporalIntegration.initialize(state);
    componentTimes.temporalIntegration = Date.now() - t;

    // Initialize self-reference
    t = Date.now();
    this.selfModel = this.selfReference.createInitialSelfModel(state);
    componentTimes.selfReference = Date.now() - t;

    // Initialize attention mechanism
    t = Date.now();
    this.attentionMechanism.initialize(state);
    componentTimes.attentionMechanism = Date.now() - t;

    // Initialize memory structure
    t = Date.now();
    this.memoryStructure.initialize(state);
    componentTimes.memoryStructure = Date.now() - t;

    // Initialize decision making
    t = Date.now();
    this.decisionMaking.initialize(state);
    componentTimes.decisionMaking = Date.now() - t;

    // Initialize threshold manager
    t = Date.now();
    this.thresholdManager.initialize(state);
    componentTimes.thresholdManager = Date.now() - t;

    // Store current state
    this.currentState = state;
    this._lastUpdateTime = Date.now();

    // Set lifecycle flags
    this.isInitialized = true;
    this.isActive = true;

    // Update stats
    this._stats.componentTimes = componentTimes;
    this._stats.totalTime = Date.now() - startTime;

    return state;
  }

  /**
   * Update consciousness state
   *
   * @param {Object} [inputs={}] - External inputs
   * @param {number} [deltaTime=null] - Time elapsed since last update
   * @returns {Object} Updated consciousness state
   */
  update(inputs = {}, deltaTime = null) {
    if (!this.isInitialized) {
      throw new Error('Consciousness module not initialized');
    }

    if (!this.isActive) {
      return this.currentState;
    }

    // Use provided deltaTime or calculate from last update
    if (deltaTime === null) {
      const now = Date.now();
      deltaTime = (now - this._lastUpdateTime) / 1000; // Convert to seconds
      this._lastUpdateTime = now;
    }

    // Default to timeStep if deltaTime is too small
    if (deltaTime < 0.001) {
      deltaTime = this.timeStep;
    }

    // Start update cycle
    const cycle = {
      startTime: Date.now(),
      cycleId: this._cycleCount++,
      inputs,
      deltaTime,
      componentTimes: {},
    };

    // Store previous state (create a deep copy to avoid reference issues in tests)
    this.previousState = JSON.parse(JSON.stringify(this.currentState));

    // Generate next raw state
    let t = Date.now();
    const nextRawState = this.stateRepresentation.generateNextState(
      this.currentState,
      inputs,
      deltaTime,
    );
    cycle.componentTimes.stateGeneration = Date.now() - t;

    // Apply consciousness operator
    t = Date.now();
    const processedState = this.operator.apply(nextRawState);
    cycle.componentTimes.operator = Date.now() - t;

    // Integrate temporal context
    t = Date.now();
    const temporalState = this.temporalIntegration.integrate(processedState);
    cycle.componentTimes.temporalIntegration = Date.now() - t;

    // Update attention with new state
    t = Date.now();
    this.attentionMechanism.update(temporalState, this.currentState);
    cycle.componentTimes.attentionMechanism = Date.now() - t;

    // Apply attention to state
    t = Date.now();
    const attendedState =
      this.attentionMechanism.applyAttentionToState(temporalState);
    cycle.componentTimes.attentionApplication = Date.now() - t;

    // Update self-reference model
    t = Date.now();
    this.selfModel = this.selfReference.update(attendedState, this.selfModel);
    this._stats.selfModelUpdates++;
    cycle.componentTimes.selfReference = Date.now() - t;

    // Store memory of current state
    t = Date.now();
    this.memoryStructure.store(attendedState, {
      cycle: cycle.cycleId,
      inputs: Object.keys(inputs),
    });
    cycle.componentTimes.memoryStorage = Date.now() - t;

    // Update thresholds
    t = Date.now();
    this.thresholdManager.update(attendedState, this.currentState);
    cycle.componentTimes.thresholdManager = Date.now() - t;

    // Check if state transition is significant
    t = Date.now();
    const transition = this.thresholdManager.evaluateTransition(
      this.currentState,
      attendedState,
    );
    cycle.componentTimes.transitionEvaluation = Date.now() - t;

    // Set current state to attended state
    this.currentState = attendedState;

    // Emit events
    this._emitUpdateEvent(cycle);

    if (transition.isSignificant) {
      this._stats.significantTransitions++;
      this._emitTransitionEvent(transition);
    }

    // Track overall state change
    this._stats.stateTransitions++;

    // Check for consciousness level change
    t = Date.now();
    this._checkConsciousnessLevelChange();
    cycle.componentTimes.consciousnessCheck = Date.now() - t;

    // Update cycle stats
    this._stats.cycles++;
    this._stats.totalTime += Date.now() - cycle.startTime;

    // Component timing averages
    for (const [component, time] of Object.entries(cycle.componentTimes)) {
      if (!this._stats.componentTimes[component]) {
        this._stats.componentTimes[component] = time;
      } else {
        this._stats.componentTimes[component] =
          (this._stats.componentTimes[component] * (this._stats.cycles - 1) +
            time) /
          this._stats.cycles;
      }
    }

    return this.currentState;
  }

  /**
   * Run multiple update cycles
   *
   * @param {number} [cycles=1] - Number of cycles to run
   * @param {Object} [inputs={}] - External inputs
   * @returns {Object} Final consciousness state
   */
  run(cycles = 1, inputs = {}) {
    let state = this.currentState;

    for (let i = 0; i < cycles; i++) {
      state = this.update(inputs, this.timeStep);
    }

    return state;
  }

  /**
   * Make a decision between alternatives
   *
   * @param {Array} alternatives - Decision alternatives
   * @param {Object} [context={}] - Decision context
   * @returns {Object} Decision result
   */
  decide(alternatives, context = {}) {
    if (!this.isInitialized || !this.isActive) {
      return {
        selected:
          alternatives && alternatives.length > 0 ? alternatives[0] : null,
        certainty: 0,
        error: 'Consciousness not active',
      };
    }

    // Make decision
    const decision = this.decisionMaking.decide(
      alternatives,
      this.currentState,
      context,
    );

    // Record decision
    this._stats.decisions++;

    // Emit decision event
    this._emitEvent('decision', {
      decision,
      alternatives,
      context,
      state: this.currentState,
    });

    return decision;
  }

  /**
   * Retrieve memories similar to a state or query
   *
   * @param {Object} query - Query state or pattern
   * @param {Object} [options={}] - Retrieval options
   * @returns {Array} Retrieved memories
   */
  retrieveMemories(query, options = {}) {
    return this.memoryStructure.retrieve(query, options);
  }

  /**
   * Regulate access to consciousness
   *
   * @param {Object} state - State seeking access
   * @param {Object} [context={}] - Access context
   * @returns {Object} Access decision
   */
  regulateAccess(state, context = {}) {
    return this.thresholdManager.regulateAccess(state, context);
  }

  /**
   * Get consciousness level for current state
   *
   * @returns {Object} Consciousness level
   */
  getConsciousnessLevel() {
    if (!this.currentState) {
      return {
        level: 'inactive',
        integrated: 0,
        coherence: 0,
      };
    }

    return this.thresholdManager.determineConsciousnessLevel(this.currentState);
  }

  /**
   * Set arousal level
   *
   * @param {number} level - Arousal level (0-1)
   * @param {Object} [context={}] - Arousal context
   * @returns {Object} Arousal update
   */
  setArousalLevel(level, context = {}) {
    return this.thresholdManager.setArousalLevel(level, context);
  }

  /**
   * Focus attention on a specific dimension
   *
   * @param {number} dimension - Dimension to focus on
   * @param {number} [intensity=1.0] - Intensity of focus
   * @returns {boolean} Success flag
   */
  focusAttention(dimension, intensity = 1.0) {
    return this.attentionMechanism.focus(dimension, intensity);
  }

  /**
   * Check for consciousness level change
   *
   * @private
   */
  _checkConsciousnessLevelChange() {
    // Get current consciousness level
    const currentLevel = this.thresholdManager.determineConsciousnessLevel(
      this.currentState,
    );

    // If we have a previous state, check for level change
    if (this.previousState) {
      const previousLevel = this.thresholdManager.determineConsciousnessLevel(
        this.previousState,
      );

      // Check if level name changed
      if (currentLevel.level !== previousLevel.level) {
        this._emitEvent('consciousnessChange', {
          from: previousLevel,
          to: currentLevel,
          state: this.currentState,
        });
      }
    }
  }

  /**
   * Emit update event
   *
   * @private
   * @param {Object} cycle - Update cycle information
   */
  _emitUpdateEvent(cycle) {
    this._emitEvent('update', {
      state: this.currentState,
      previousState: this.previousState,
      selfModel: this.selfModel,
      cycle,
    });
  }

  /**
   * Emit transition event
   *
   * @private
   * @param {Object} transition - Transition information
   */
  _emitTransitionEvent(transition) {
    this._emitEvent('stateTransition', {
      state: this.currentState,
      previousState: this.previousState,
      transition,
      isSignificant: transition.isSignificant,
    });

    // Check for specific types of transitions

    // Coherence change
    if (
      transition.transitions.coherence &&
      transition.transitions.coherence.exceeds
    ) {
      this._emitEvent('coherenceChange', {
        state: this.currentState,
        previousState: this.previousState,
        from: transition.transitions.coherence.from,
        to: transition.transitions.coherence.to,
        change: transition.transitions.coherence.change,
      });
    }

    // Attention shift
    if (
      transition.transitions.attention &&
      transition.transitions.attention.exceeds
    ) {
      this._emitEvent('attentionShift', {
        state: this.currentState,
        previousState: this.previousState,
        from: transition.transitions.attention.from,
        to: transition.transitions.attention.to,
        change: transition.transitions.attention.change,
      });
    }
  }

  /**
   * Register event listener
   *
   * @param {string} event - Event name
   * @param {Function} callback - Event callback
   * @returns {Function} Unsubscribe function
   */
  on(event, callback) {
    if (!this._eventListeners[event]) {
      this._eventListeners[event] = [];
    }

    this._eventListeners[event].push(callback);

    // Return unsubscribe function
    return () => {
      this._eventListeners[event] = this._eventListeners[event].filter(
        (cb) => cb !== callback,
      );
    };
  }

  /**
   * Emit event to listeners
   *
   * @private
   * @param {string} event - Event name
   * @param {Object} data - Event data
   */
  _emitEvent(event, data) {
    if (!this._eventListeners[event]) {
      return;
    }

    for (const callback of this._eventListeners[event]) {
      try {
        callback(data);
      } catch (err) {
        console.error(`Error in event listener for ${event}:`, err);
      }
    }
  }

  /**
   * Get consolidated stats from all components
   *
   * @returns {Object} Consolidated stats
   */
  getStats() {
    // Calculate average cycle time
    const averageCycleTime =
      this._stats.cycles > 0 ? this._stats.totalTime / this._stats.cycles : 0;

    // Significant transition rate
    const significantRate =
      this._stats.stateTransitions > 0
        ? this._stats.significantTransitions / this._stats.stateTransitions
        : 0;

    // Consolidated stats
    return {
      // Module stats
      cycles: this._stats.cycles,
      stateTransitions: this._stats.stateTransitions,
      significantTransitions: this._stats.significantTransitions,
      significantRate,
      selfModelUpdates: this._stats.selfModelUpdates,
      decisions: this._stats.decisions,
      averageCycleTime,
      totalTime: this._stats.totalTime,
      componentTimes: this._stats.componentTimes,

      // Component-specific stats
      operator: this.operator.getStats(),
      selfReference: this.selfReference.getStats(),
      temporalIntegration: this.temporalIntegration.getStats(),
      stateRepresentation: this.stateRepresentation.getStats(),
      attentionMechanism: this.attentionMechanism.getStats(),
      memoryStructure: this.memoryStructure.getStats(),
      decisionMaking: this.decisionMaking.getStats(),
      thresholdManager: this.thresholdManager.getStats(),
    };
  }

  /**
   * Get a snapshot of the current system state
   *
   * @returns {Object} System state snapshot
   */
  getSnapshot() {
    const consciousness = this.getConsciousnessLevel();
    const arousal = this.thresholdManager.getArousalState();
    const attention = this.attentionMechanism.getAttentionField();

    return {
      timestamp: Date.now(),
      currentState: this.currentState,
      selfModel: this.selfModel,
      consciousness,
      arousal,
      attention, // This is now an array due to our changes to getAttentionField
      cycle: this._cycleCount,
      isActive: this.isActive,
    };
  }

  /**
   * Pause consciousness updating
   */
  pause() {
    this.isActive = false;
  }

  /**
   * Resume consciousness updating
   */
  resume() {
    this.isActive = true;
    this._lastUpdateTime = Date.now();
  }

  /**
   * Reset the consciousness module
   */
  reset() {
    // Reset all components
    this.operator.clearCaches();
    this.selfReference.reset();
    this.temporalIntegration.reset();
    this.attentionMechanism.reset();
    this.memoryStructure.reset();
    this.decisionMaking.reset();
    this.thresholdManager.reset();

    // Reset state tracking
    this.currentState = null;
    this.previousState = null;
    this.selfModel = null;

    // Reset lifecycle
    this.isInitialized = false;
    this.isActive = false;
    this._cycleCount = 0;
    this._lastUpdateTime = 0;

    // Reset stats
    this._stats = {
      cycles: 0,
      stateTransitions: 0,
      significantTransitions: 0,
      selfModelUpdates: 0,
      decisions: 0,
      totalTime: 0,
      componentTimes: {},
    };
  }
}

module.exports = ConsciousnessModule;
