/**
 * Self-Referential Loop - System for self-observation and modeling
 * 
 * This module implements self-referential loops that enable a system to observe and model
 * its own states, a key aspect of consciousness simulation based on coherence principles.
 * 
 * Key features:
 * - Enables system to observe and model its own states
 * - Tracks coherence between observed and modeled states
 * - Supports multiple levels of self-reference (meta-modeling)
 * - Implements quantum-inspired probability calculations
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
 * SelfReferentialLoop enables a system to observe and model its own states
 */
class SelfReferentialLoop {
  /**
   * Create a new self-referential loop
   * 
   * @param {Object} options - Configuration options
   * @param {number} options.coherenceThreshold - Coherence threshold for self-model (default: 0.7)
   * @param {boolean} options.useQuantumProbability - Whether to use quantum probability (default: true)
   * @param {number} options.maxRecursionDepth - Maximum recursion depth for self-reference (default: 3)
   * @param {Function} options.coherenceFunction - Custom function to calculate coherence (default: built-in)
   */
  constructor(options = {}) {
    this.coherenceThreshold = options.coherenceThreshold || 0.7;
    this.useQuantumProbability = options.useQuantumProbability !== false;
    this.maxRecursionDepth = options.maxRecursionDepth || 3;
    this.coherenceFunction = options.coherenceFunction || this._defaultCoherenceFunction;
    
    // Internal state
    this._modelHistory = [];
    this._observationHistory = [];
    this._recursionHistory = [];
    
    // Density matrices for quantum-inspired calculations
    this._densityMatrices = new Map();
    
    // Performance tracking
    this._stats = {
      updates: 0,
      coherenceChecks: 0,
      recursions: 0,
      totalTime: 0
    };
  }
  
  /**
   * Create initial self-model based on a state
   * 
   * @param {Object} state - Initial state to model
   * @returns {Object} Initial self-model
   */
  createInitialSelfModel(state) {
    // Create deep copy as initial model
    const initialModel = this._deepCopy(state);
    
    // Add self-model specific properties
    initialModel._selfModel = {
      level: 1,
      createTime: Date.now(),
      updateTime: Date.now(),
      modelCoherence: 1.0,
      observationCount: 1,
      referential: true,
      recursionDepth: 0
    };
    
    // Initialize with perfect coherence (identical to original state)
    if (this.useQuantumProbability) {
      // Create initial density matrix representation
      this._initializeDensityMatrix(state, initialModel);
    }
    
    // Keep history
    this._modelHistory.push(this._snapshotModel(initialModel));
    this._observationHistory.push(this._snapshotObservation(state));
    
    return initialModel;
  }
  
  /**
   * Update self-model based on observed state
   * 
   * @param {Object} observedState - New observed state
   * @param {Object} currentModel - Current self-model
   * @returns {Object} Updated self-model
   */
  update(observedState, currentModel) {
    const startTime = Date.now();
    this._stats.updates++;
    
    // Ensure we have a valid model
    if (!currentModel || !currentModel._selfModel) {
      return this.createInitialSelfModel(observedState);
    }
    
    // Create new model instance
    const newModel = this._deepCopy(currentModel);
    
    // Update model metadata
    newModel._selfModel.updateTime = Date.now();
    newModel._selfModel.observationCount++;
    
    // Calculate coherence between observation and current model
    const coherence = this.computeCoherence(observedState, currentModel);
    
    // Determine update approach based on coherence level
    if (coherence >= this.coherenceThreshold) {
      // High coherence - small incremental update
      this._incrementalModelUpdate(newModel, observedState, coherence);
    } else {
      // Low coherence - larger update
      this._significantModelUpdate(newModel, observedState, coherence);
    }
    
    // Store coherence
    newModel._selfModel.modelCoherence = coherence;
    
    // Apply quantum-inspired updates if enabled
    if (this.useQuantumProbability) {
      this._updateDensityMatrix(observedState, newModel);
    }
    
    // Add recursive self-reference if appropriate
    if (this._shouldAddRecursion(newModel, coherence)) {
      this._addRecursiveReference(newModel);
    }
    
    // Keep history
    this._modelHistory.push(this._snapshotModel(newModel));
    this._observationHistory.push(this._snapshotObservation(observedState));
    
    // Update stats
    this._stats.totalTime += Date.now() - startTime;
    
    return newModel;
  }
  
  /**
   * Compute coherence between an observed state and a self-model
   * 
   * @param {Object} observedState - Observed state
   * @param {Object} selfModel - Self-model
   * @returns {number} Coherence value (0-1)
   */
  computeCoherence(observedState, selfModel) {
    this._stats.coherenceChecks++;
    
    // Use quantum density matrix if available and enabled
    if (this.useQuantumProbability && this._densityMatrices.has(this._getStateId(selfModel))) {
      return this._computeQuantumCoherence(observedState, selfModel);
    }
    
    // Otherwise use classical coherence function
    return this.coherenceFunction(observedState, selfModel);
  }
  
  /**
   * Default coherence function between state and model
   * 
   * @private
   * @param {Object} state - Observed state
   * @param {Object} model - Self-model
   * @returns {number} Coherence value (0-1)
   */
  _defaultCoherenceFunction(state, model) {
    // Extract relevant properties for comparison
    const properties = [
      'attention', 'awareness', 'coherence', 'integration', 
      'differentiation', 'temporalBinding', 'selfReference'
    ];
    
    let totalDiff = 0;
    let comparedProps = 0;
    
    // Compare properties that exist in both state and model
    for (const prop of properties) {
      if (typeof state[prop] === 'number' && typeof model[prop] === 'number') {
        totalDiff += Math.abs(state[prop] - model[prop]);
        comparedProps++;
      }
    }
    
    // Compare vectors if available
    if (Array.isArray(state.vector) && Array.isArray(model.vector)) {
      const minLength = Math.min(state.vector.length, model.vector.length);
      
      let vectorDiff = 0;
      for (let i = 0; i < minLength; i++) {
        vectorDiff += Math.abs(state.vector[i] - model.vector[i]);
      }
      
      // Add normalized vector difference
      if (minLength > 0) {
        totalDiff += vectorDiff / minLength;
        comparedProps++;
      }
    }
    
    // If no properties were compared, return minimum coherence
    if (comparedProps === 0) return 0;
    
    // Calculate coherence (1 - normalized difference)
    const avgDiff = totalDiff / comparedProps;
    return Math.max(0, 1 - avgDiff);
  }
  
  /**
   * Compute quantum coherence using density matrices
   * 
   * @private
   * @param {Object} state - Observed state
   * @param {Object} model - Self-model
   * @returns {number} Quantum coherence value (0-1)
   */
  _computeQuantumCoherence(state, model) {
    const modelDM = this._densityMatrices.get(this._getStateId(model));
    if (!modelDM) return this._defaultCoherenceFunction(state, model);
    
    // Create temporary state density matrix
    const stateVector = this._extractStateVector(state);
    const stateDM = this._createDensityMatrix(stateVector);
    
    // Calculate fidelity between density matrices
    // In quantum mechanics, fidelity measures overlap between quantum states
    // For pure states: F(ρ,σ) = Tr(ρσ)
    
    // Calculate trace product
    let fidelity = 0;
    const dim = Math.min(stateDM.length, modelDM.length);
    
    for (let i = 0; i < dim; i++) {
      for (let j = 0; j < dim; j++) {
        fidelity += stateDM[i][j] * modelDM[j][i];
      }
    }
    
    // Ensure fidelity is in [0,1] range
    return Math.min(1, Math.max(0, fidelity));
  }
  
  /**
   * Apply incremental update to model based on observation
   * 
   * @private
   * @param {Object} model - Model to update
   * @param {Object} observation - Observed state
   * @param {number} coherence - Coherence between model and observation
   */
  _incrementalModelUpdate(model, observation, coherence) {
    // Extract and update vector representations
    const obsVector = this._extractStateVector(observation);
    const modelVector = this._extractStateVector(model);
    
    // Apply small update (weighted average favoring current model)
    // Higher coherence means less adjustment needed
    const updateWeight = 0.2 * (1 - coherence);
    const modelWeight = 1 - updateWeight;
    
    // Update vector
    const updatedVector = modelVector.map((val, i) => {
      if (i < obsVector.length) {
        return val * modelWeight + obsVector[i] * updateWeight;
      }
      return val;
    });
    
    // Update model with new vector
    this._updateModelWithVector(model, updatedVector);
    
    // Update direct properties
    for (const prop of ['attention', 'awareness', 'coherence', 'integration', 
                        'differentiation', 'temporalBinding', 'selfReference']) {
      if (typeof observation[prop] === 'number' && typeof model[prop] === 'number') {
        model[prop] = model[prop] * modelWeight + observation[prop] * updateWeight;
      }
    }
  }
  
  /**
   * Apply significant update to model based on observation
   * 
   * @private
   * @param {Object} model - Model to update
   * @param {Object} observation - Observed state
   * @param {number} coherence - Coherence between model and observation
   */
  _significantModelUpdate(model, observation, coherence) {
    // Extract and update vector representations
    const obsVector = this._extractStateVector(observation);
    const modelVector = this._extractStateVector(model);
    
    // Apply larger update (weighted average with more weight to observation)
    // Lower coherence means more adjustment needed
    const updateWeight = 0.5 + 0.3 * (1 - coherence);
    const modelWeight = 1 - updateWeight;
    
    // Update vector
    const updatedVector = modelVector.map((val, i) => {
      if (i < obsVector.length) {
        return val * modelWeight + obsVector[i] * updateWeight;
      }
      return val;
    });
    
    // Update model with new vector
    this._updateModelWithVector(model, updatedVector);
    
    // Update direct properties
    for (const prop of ['attention', 'awareness', 'coherence', 'integration', 
                        'differentiation', 'temporalBinding', 'selfReference']) {
      if (typeof observation[prop] === 'number') {
        if (typeof model[prop] === 'number') {
          model[prop] = model[prop] * modelWeight + observation[prop] * updateWeight;
        } else {
          model[prop] = observation[prop];
        }
      }
    }
    
    // Copy additional properties if they exist in observation but not in model
    for (const prop in observation) {
      if (prop !== '_selfModel' && prop !== 'vector' && 
          observation[prop] !== undefined && model[prop] === undefined) {
        model[prop] = this._deepCopy(observation[prop]);
      }
    }
  }
  
  /**
   * Extract state vector from an object
   * 
   * @private
   * @param {Object} obj - State or model object
   * @returns {Array} Vector representation
   */
  _extractStateVector(obj) {
    // If object already has a vector, use it
    if (obj.vector && Array.isArray(obj.vector)) {
      return [...obj.vector];
    }
    
    // Otherwise create vector from properties
    const vector = [];
    
    // Add common numeric properties
    for (const prop of ['attention', 'awareness', 'coherence', 'integration', 
                        'differentiation', 'temporalBinding', 'selfReference']) {
      if (typeof obj[prop] === 'number') {
        vector.push(obj[prop]);
      } else {
        vector.push(0);
      }
    }
    
    return vector;
  }
  
  /**
   * Update model with a new vector representation
   * 
   * @private
   * @param {Object} model - Model to update
   * @param {Array} vector - New vector representation
   */
  _updateModelWithVector(model, vector) {
    // Update vector property
    model.vector = [...vector];
    
    // Update common numeric properties
    const props = ['attention', 'awareness', 'coherence', 'integration', 
                  'differentiation', 'temporalBinding', 'selfReference'];
    
    for (let i = 0; i < props.length && i < vector.length; i++) {
      model[props[i]] = vector[i];
    }
  }
  
  /**
   * Determine if recursion should be added based on model state and coherence
   * 
   * @private
   * @param {Object} model - Current model
   * @param {number} coherence - Current coherence level
   * @returns {boolean} Whether to add recursion
   */
  _shouldAddRecursion(model, coherence) {
    // Don't exceed maximum recursion depth
    if (model._selfModel.recursionDepth >= this.maxRecursionDepth) {
      return false;
    }
    
    // Add recursion if: 
    // 1. Coherence is high (model is accurate)
    // 2. We have enough observations for stability
    // 3. Model has been stable for some time
    // 4. Random chance based on coherence
    
    const highCoherence = coherence > this.coherenceThreshold;
    const enoughObservations = model._selfModel.observationCount > 5;
    const modelAge = Date.now() - model._selfModel.createTime;
    const isStable = modelAge > 2000 && this._modelHistory.length > 3;
    
    // Probability increases with coherence
    const randomThreshold = 0.1 + 0.4 * coherence;
    const randomChance = Math.random() < randomThreshold;
    
    return highCoherence && enoughObservations && isStable && randomChance;
  }
  
  /**
   * Add recursive self-reference to a model
   * 
   * @private
   * @param {Object} model - Model to enhance with recursion
   */
  _addRecursiveReference(model) {
    this._stats.recursions++;
    
    // Create a snapshot of the current model as meta-model
    const metaModel = this._deepCopy(model);
    
    // Set appropriate recursion level
    metaModel._selfModel.level += 1;
    model._selfModel.recursionDepth += 1;
    
    // Store meta-model in main model
    if (!model._metaModel) {
      model._metaModel = metaModel;
    } else {
      // If already has meta-model, update it
      model._metaModel = metaModel;
    }
    
    // Record recursion in history
    this._recursionHistory.push({
      timestamp: Date.now(),
      baseModelId: this._getStateId(model),
      recursionDepth: model._selfModel.recursionDepth,
      coherence: model._selfModel.modelCoherence
    });
  }
  
  /**
   * Initialize density matrix for quantum representation
   * 
   * @private
   * @param {Object} state - Observed state
   * @param {Object} model - Self-model
   */
  _initializeDensityMatrix(state, model) {
    const stateVector = this._extractStateVector(state);
    const modelVector = this._extractStateVector(model);
    
    // Create density matrices
    const stateDM = this._createDensityMatrix(stateVector);
    const modelDM = this._createDensityMatrix(modelVector);
    
    // Store model density matrix
    this._densityMatrices.set(this._getStateId(model), modelDM);
  }
  
  /**
   * Update density matrix after model change
   * 
   * @private
   * @param {Object} state - Observed state
   * @param {Object} model - Self-model
   */
  _updateDensityMatrix(state, model) {
    const modelId = this._getStateId(model);
    const stateVector = this._extractStateVector(state);
    const modelVector = this._extractStateVector(model);
    
    // Get current density matrix or create new one
    let currentDM = this._densityMatrices.get(modelId);
    if (!currentDM) {
      currentDM = this._createDensityMatrix(modelVector);
    }
    
    // Create state density matrix
    const stateDM = this._createDensityMatrix(stateVector);
    
    // Update density matrix (quantum mixing)
    // DM' = (1-w)·DM + w·DMstate
    const updateWeight = 0.3;
    const modelWeight = 1 - updateWeight;
    
    const updatedDM = [];
    for (let i = 0; i < currentDM.length; i++) {
      updatedDM[i] = [];
      for (let j = 0; j < currentDM[i].length; j++) {
        updatedDM[i][j] = currentDM[i][j] * modelWeight;
        if (i < stateDM.length && j < stateDM[i].length) {
          updatedDM[i][j] += stateDM[i][j] * updateWeight;
        }
      }
    }
    
    // Store updated density matrix
    this._densityMatrices.set(modelId, updatedDM);
  }
  
  /**
   * Create a density matrix from a state vector
   * 
   * @private
   * @param {Array} vector - State vector
   * @returns {Array} Density matrix
   */
  _createDensityMatrix(vector) {
    const dim = vector.length;
    const densityMatrix = [];
    
    // Normalize vector
    const magnitude = Math.sqrt(vector.reduce((sum, val) => sum + val * val, 0));
    const normalizedVector = magnitude > 0 
      ? vector.map(val => val / magnitude) 
      : vector.map(() => 1 / Math.sqrt(dim));
    
    // Create density matrix as outer product |ψ⟩⟨ψ|
    for (let i = 0; i < dim; i++) {
      densityMatrix[i] = [];
      for (let j = 0; j < dim; j++) {
        densityMatrix[i][j] = normalizedVector[i] * normalizedVector[j];
      }
    }
    
    return densityMatrix;
  }
  
  /**
   * Generate a unique ID for a state or model
   * 
   * @private
   * @param {Object} obj - State or model
   * @returns {string} Unique ID
   */
  _getStateId(obj) {
    if (!obj) return 'null';
    
    if (obj._id) return obj._id;
    
    // Extract vector and create hash from it
    const vector = this._extractStateVector(obj);
    
    // Create a simple hash
    const hash = vector.reduce(
      (h, v, i) => h + Math.round(v * 1000) * (i + 1), 0
    ).toString(36);
    
    // Add timestamp for uniqueness
    return hash + '_' + Date.now().toString(36);
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
   * Create a snapshot of a model for history
   * 
   * @private
   * @param {Object} model - Model to snapshot
   * @returns {Object} Lightweight snapshot
   */
  _snapshotModel(model) {
    return {
      id: this._getStateId(model),
      vector: [...model.vector],
      coherence: model._selfModel.modelCoherence,
      recursionDepth: model._selfModel.recursionDepth,
      timestamp: Date.now()
    };
  }
  
  /**
   * Create a snapshot of an observation for history
   * 
   * @private
   * @param {Object} state - State to snapshot
   * @returns {Object} Lightweight snapshot
   */
  _snapshotObservation(state) {
    return {
      id: this._getStateId(state),
      vector: this._extractStateVector(state),
      timestamp: Date.now()
    };
  }
  
  /**
   * Get historical model coherence
   * 
   * @param {number} [limit=10] - Number of historical points to return
   * @returns {Array} Historical coherence values
   */
  getHistoricalCoherence(limit = 10) {
    const historyLength = Math.min(this._modelHistory.length, limit);
    const history = [];
    
    for (let i = this._modelHistory.length - 1; i >= Math.max(0, this._modelHistory.length - historyLength); i--) {
      history.unshift({
        timestamp: this._modelHistory[i].timestamp,
        coherence: this._modelHistory[i].coherence,
        recursionDepth: this._modelHistory[i].recursionDepth
      });
    }
    
    return history;
  }
  
  /**
   * Get statistics about self-reference performance
   * 
   * @returns {Object} Performance statistics
   */
  getStats() {
    const averageTime = this._stats.updates > 0
      ? this._stats.totalTime / this._stats.updates
      : 0;
    
    const recursionRate = this._stats.updates > 0
      ? this._stats.recursions / this._stats.updates
      : 0;
    
    const currentRecursionDepth = this._modelHistory.length > 0
      ? this._modelHistory[this._modelHistory.length - 1].recursionDepth
      : 0;
    
    return {
      ...this._stats,
      averageTime,
      recursionRate,
      currentRecursionDepth,
      historyLength: this._modelHistory.length,
      observationCount: this._observationHistory.length
    };
  }
  
  /**
   * Reset history and statistics
   */
  reset() {
    this._modelHistory = [];
    this._observationHistory = [];
    this._recursionHistory = [];
    this._densityMatrices.clear();
    
    this._stats = {
      updates: 0,
      coherenceChecks: 0,
      recursions: 0,
      totalTime: 0
    };
  }
}

module.exports = SelfReferentialLoop;