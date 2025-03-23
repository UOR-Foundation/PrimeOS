/**
 * PrimeOS JavaScript Library - Neural Distributed Module
 * Integrates neural network computation with distributed processing
 */

// Import the Prime object from core
const Prime = require('../../core');

// Import validators
require('./dimension-validator');
require('./coherence-validator');

// Import the implementation from our distributed model file
const DistributedModelImplementation = require('./distributed-model-impl');

// Create the Neural Distributed module using IIFE
(function () {
  /**
   * Distributed Neural Model
   * Enhances NeuralModel with distributed computation capabilities
   * @extends Prime.Neural.Model.NeuralModel
   */
  class DistributedNeuralModel extends DistributedModelImplementation {
    /**
     * Create a new distributed neural network model
     * @param {Object} config - Model configuration
     * @param {number} config.inputSize - Size of the input layer
     * @param {Array} [config.layers=[]] - Array of layer configurations
     * @param {Object} [config.optimizer={}] - Optimizer configuration
     * @param {Object} [config.coherence={}] - Coherence configuration
     * @param {Object} [config.metadata={}] - Model metadata
     * @param {Object} [config.distributed={}] - Distributed configuration
     */
    constructor(config = {}) {
      // Validate the configuration
      if (Prime.Neural.Distributed.DimensionValidator) {
        Prime.Neural.Distributed.DimensionValidator.validateModelConfig(config);
      }

      // Store and preserve the original input size
      this.originalInputSize = config.inputSize || 10;

      // Call the implementation constructor with validated config
      super(config);

      // IMPORTANT: Restore original input size after layers are added
      this.inputSize = this.originalInputSize;

      // Enhanced distributed configuration
      this.distributedConfig = {
        enabled: config.distributed?.enabled ?? false,
        partitionScheme: config.distributed?.partitionScheme || 'data_parallel',
        syncFrequency: config.distributed?.syncFrequency || 10,
        synchronizationStrategy:
          config.distributed?.synchronizationStrategy || 'average',
        syncRecoveryStrategy:
          config.distributed?.syncRecoveryStrategy || 'local_fallback',
        clusterManager: config.distributed?.clusterManager,
        errorTolerance: config.distributed?.errorTolerance || 0.01,
        maxSyncRetries: config.distributed?.maxSyncRetries || 3,
        syncTimeout: config.distributed?.syncTimeout || 30000,
      };

      // Enhanced distributed state tracking
      this.distributedState = {
        isInitialized: false,
        activeNodes: [],
        lastSyncIteration: 0,
        lastParameterUpdate: 0,
        synchronizedIterations: 0,
        failedSynchronizations: 0,
        syncRetryCount: 0,
        lastCoherenceCheck: 0,
        nodeId: null,
        syncErrors: [],
        syncHistory: [],
      };

      // Log layer dimensions if validator is available
      if (Prime.Neural.Distributed.DimensionValidator) {
        Prime.Neural.Distributed.DimensionValidator.logLayerDimensions(
          this.layers,
        );
      }

      // Perform initial coherence check
      this._initialCoherenceCheck();

      // Set up cluster if distributed mode is enabled
      if (this.distributedConfig.enabled) {
        this._initializeDistributedMode();
      }
    }

    /**
     * Initialize distributed computation mode
     * @private
     */
    _initializeDistributedMode() {
      try {
        const clusterManager = this.distributedConfig.clusterManager;

        // Check for required cluster resources
        if (!clusterManager || !clusterManager.nodes || clusterManager.nodes.size === 0) {
          throw new Error('Cluster manager has no nodes available');
        }

        // Initialize cluster connection
        if (!Prime.Distributed || !Prime.Distributed.Cluster) {
          throw new Prime.ValidationError('Distributed modules not loaded');
        }

        // Register with cluster
        this.distributedState.nodeId = clusterManager.register(this);

        // Get active nodes
        this.distributedState.activeNodes = clusterManager.getActiveNodes();

        // Set initialization state
        this.distributedState.isInitialized = true;

        Prime.Logger.info(`Distributed mode initialized with ${this.distributedState.activeNodes.length} active nodes`);
        Prime.Logger.info(`Using partition scheme: ${this.distributedConfig.partitionScheme}`);
        Prime.Logger.info(`Using sync strategy: ${this.distributedConfig.synchronizationStrategy}`);
      } catch (error) {
        Prime.Logger.error(`Failed to initialize distributed mode: ${error.message}`);
        this.distributedState.isInitialized = false;
        this.distributedConfig.enabled = false;
      }
    }

    /**
     * Add a layer to the model
     * @param {Object} layerConfig - Configuration for the layer
     * @returns {DistributedNeuralModel} - Returns this for chaining
     */
    addLayer(layerConfig) {
      // Create layer configuration with proper input size
      const layerOptions = {
        ...layerConfig,
        inputSize: layerConfig.inputSize || this.inputSize,
      };

      // Validate layer configuration if validator is available
      if (Prime.Neural.Distributed.DimensionValidator) {
        Prime.Neural.Distributed.DimensionValidator.validateLayerConfig(
          layerOptions,
          this.layers.length,
        );
      }

      // Add the layer using the parent implementation
      super.addLayer(layerOptions);

      // Update input size for next layer
      this.inputSize = layerOptions.outputSize;

      return this;
    }

    /**
     * Performs initial coherence check
     * @private
     */
    _initialCoherenceCheck() {
      try {
        // Extract model parameters
        const params = this._extractModelParameters();

        // Verify parameter coherence
        const isCoherent = this._verifyParameterCoherence(params);

        if (!isCoherent) {
          Prime.Logger.warn('Initial model parameters failed coherence check');
        } else {
          Prime.Logger.debug('Initial coherence check passed successfully');
        }

        // Record coherence check time
        this.distributedState.lastCoherenceCheck = Date.now();
      } catch (error) {
        Prime.Logger.error(`Initial coherence check failed: ${error.message}`);
      }
    }

    /**
     * Extracts model parameters for synchronization
     * @returns {Object} - Model parameters (weights and biases)
     * @private
     */
    _extractModelParameters() {
      const parameters = {
        weights: this.layers.map((layer) => layer.weights),
        biases: this.layers.map((layer) => layer.biases),
        layerConfig: this.layers.map((layer) => ({
          inputSize: layer.inputSize,
          outputSize: layer.outputSize,
          type: layer.type,
          activation: layer.activation,
        })),
        metadata: {
          extractionTime: Date.now(),
          modelConfig: {
            inputSize: this.originalInputSize,
            layerCount: this.layers.length
          }
        }
      };

      // Validate parameters before returning
      if (!this._validateParameterStructure(parameters)) {
        throw new Prime.ValidationError('Parameter extraction produced invalid structure');
      }

      return parameters;
    }

    /**
     * Validates the structure of extracted parameters
     * @param {Object} parameters - Parameters to validate
     * @returns {Boolean} - True if structure is valid
     * @private
     */
    _validateParameterStructure(parameters) {
      // Basic structure checks
      if (!parameters ||
          !Array.isArray(parameters.weights) ||
          !Array.isArray(parameters.biases) ||
          !Array.isArray(parameters.layerConfig)) {
        return false;
      }

      // Check that arrays have expected length
      if (parameters.weights.length !== parameters.biases.length ||
          parameters.weights.length !== parameters.layerConfig.length) {
        return false;
      }

      // Check each layer's parameters
      for (let i = 0; i < parameters.layerConfig.length; i++) {
        const config = parameters.layerConfig[i];
        const weights = parameters.weights[i];
        const biases = parameters.biases[i];

        // Skip if this layer doesn't have parameters
        if (!weights || !biases) continue;

        // Check dimensions
        if (!Array.isArray(weights) || weights.length !== config.outputSize) {
          return false;
        }

        if (weights.length > 0 && (!Array.isArray(weights[0]) || weights[0].length !== config.inputSize)) {
          return false;
        }

        if (!Array.isArray(biases) || biases.length !== config.outputSize) {
          return false;
        }
      }

      return true;
    }

    /**
     * Applies parameters to the model
     * @param {Object} parameters - Parameters to apply
     * @returns {Boolean} - True if successful
     * @private
     */
    _applyParameters(parameters) {
      if (!this._validateParameterStructure(parameters)) {
        Prime.Logger.error('Cannot apply parameters: invalid structure');
        return false;
      }

      // Verify parameter coherence before applying
      if (!this._verifyParameterCoherence(parameters)) {
        Prime.Logger.error('Cannot apply parameters: failed coherence check');
        return false;
      }

      try {
        // Apply weights and biases to each layer
        for (let i = 0; i < this.layers.length && i < parameters.weights.length; i++) {
          if (parameters.weights[i]) {
            this.layers[i].weights = parameters.weights[i];
          }

          if (parameters.biases[i]) {
            this.layers[i].biases = parameters.biases[i];
          }
        }

        // Record update time
        this.distributedState.lastParameterUpdate = Date.now();
        return true;
      } catch (error) {
        Prime.Logger.error(`Failed to apply parameters: ${error.message}`);
        return false;
      }
    }

    /**
     * Verifies parameter coherence
     * @param {Object} parameters - Parameters to verify
     * @returns {Boolean} - True if parameters are coherent
     * @private
     */
    _verifyParameterCoherence(parameters) {
      // Use the coherence validator if available
      if (Prime.Neural.Distributed.CoherenceValidator) {
        // Calculate detailed coherence metrics
        const metrics = Prime.Neural.Distributed.CoherenceValidator.calculateCoherenceMetrics({
          layers: parameters.layerConfig.map((config, i) => ({
            ...config,
            weights: parameters.weights[i],
            biases: parameters.biases[i]
          }))
        });

        if (Prime.Logger && Prime.Logger.debug) {
          Prime.Logger.debug(`Parameter coherence metrics: ${JSON.stringify(metrics)}`);
        }

        return metrics.isCoherent;
      }

      // Fall back to dimension validator
      if (Prime.Neural.Distributed.DimensionValidator) {
        return Prime.Neural.Distributed.DimensionValidator.validateParameterCoherence(parameters);
      }

      // Basic coherence check
      if (!parameters || !parameters.weights) {
        return false;
      }

      // Check for NaN or Infinity
      for (const weightMatrix of parameters.weights) {
        if (!weightMatrix) continue;

        for (const row of weightMatrix) {
          for (const value of row) {
            if (!Number.isFinite(value) || Math.abs(value) > 1e6) {
              return false;
            }
          }
        }
      }

      return true;
    }

    /**
     * Synchronizes parameters across nodes
     * @returns {Promise<Boolean>} - True if successful
     */
    async synchronizeParameters() {
      if (!this.distributedConfig.enabled || !this.distributedState.isInitialized) {
        return true;
      }

      // Check if synchronization is needed based on frequency
      if (this.metrics.iteration - this.distributedState.lastSyncIteration < this.distributedConfig.syncFrequency) {
        return true;
      }

      try {
        // Reset retry counter for new synchronization attempt
        this.distributedState.syncRetryCount = 0;

        // Get local parameters
        const localParams = this._extractModelParameters();

        // Get remote parameters with timeout
        const syncPromise = this.distributedConfig.clusterManager.getNodeParameters();
        const timeoutPromise = new Promise((_, reject) => {
          setTimeout(() => reject(new Error('Synchronization timeout')), this.distributedConfig.syncTimeout);
        });

        const remoteResults = await Promise.race([syncPromise, timeoutPromise]);

        // Apply synchronization strategy to combine parameters
        const combinedParams = this._combineParameters(localParams, remoteResults);

        // Apply combined parameters
        const success = this._applyParameters(combinedParams);

        // Update state
        this.distributedState.synchronizedIterations++;
        this.distributedState.lastSyncIteration = this.metrics.iteration;

        // Record successful sync in history (keeping last 10 entries)
        this.distributedState.syncHistory.unshift({
          timestamp: Date.now(),
          iteration: this.metrics.iteration,
          nodeCount: remoteResults.length + 1,
          success: true
        });

        if (this.distributedState.syncHistory.length > 10) {
          this.distributedState.syncHistory.pop();
        }

        return success;
      } catch (error) {
        // Increment failure counters
        this.distributedState.failedSynchronizations++;
        this.distributedState.syncRetryCount++;

        // Record error
        this.distributedState.syncErrors.unshift({
          timestamp: Date.now(),
          message: error.message,
          iteration: this.metrics.iteration
        });

        // Keep only last 10 errors
        if (this.distributedState.syncErrors.length > 10) {
          this.distributedState.syncErrors.pop();
        }

        Prime.Logger.error(`Parameter synchronization failed: ${error.message}`);

        // Apply recovery strategy
        return this._handleSynchronizationFailure(error);
      }
    }

    /**
     * Combines local and remote parameters using configured strategy
     * @param {Object} localParams - Local parameters
     * @param {Array} remoteParams - Remote parameters
     * @returns {Object} - Combined parameters
     * @private
     */
    _combineParameters(localParams, remoteParams) {
      const strategy = this.distributedConfig.synchronizationStrategy;

      switch (strategy) {
        case 'average':
          return this._averageParameters(localParams, remoteParams);

        case 'weighted_average':
          return this._weightedAverageParameters(localParams, remoteParams);

        case 'majority_vote':
          return this._majorityVoteParameters(localParams, remoteParams);

        case 'parameter_server':
          // In parameter server mode, we just use the server's parameters
          const serverParams = remoteParams.find(p => p.isServer);
          return serverParams || localParams;

        default:
          // Default to simple averaging
          return this._averageParameters(localParams, remoteParams);
      }
    }

    /**
     * Averages parameters from multiple nodes
     * @param {Object} localParams - Local parameters
     * @param {Array} remoteParams - Remote parameters from other nodes
     * @returns {Object} - Averaged parameters
     * @private
     */
    _averageParameters(localParams, remoteParams) {
      const avgParams = {
        weights: [],
        biases: [],
        layerConfig: localParams.layerConfig,
        metadata: {
          combinationStrategy: 'average',
          nodeCount: remoteParams.length + 1,
          timestamp: Date.now()
        }
      };

      // Process each layer
      for (let layerIndex = 0; layerIndex < localParams.weights.length; layerIndex++) {
        // Skip if local layer doesn't exist
        if (!localParams.weights[layerIndex]) continue;

        // Average weights for this layer
        const localWeights = localParams.weights[layerIndex];
        avgParams.weights[layerIndex] = [];

        for (let i = 0; i < localWeights.length; i++) {
          avgParams.weights[layerIndex][i] = [];

          for (let j = 0; j < localWeights[i].length; j++) {
            let sum = localWeights[i][j];
            let count = 1;

            // Add weights from remote parameters
            for (const remote of remoteParams) {
              if (
                remote.weights &&
                remote.weights[layerIndex] &&
                remote.weights[layerIndex][i] &&
                remote.weights[layerIndex][i][j] !== undefined
              ) {
                sum += remote.weights[layerIndex][i][j];
                count++;
              }
            }

            avgParams.weights[layerIndex][i][j] = sum / count;
          }
        }

        // Average biases for this layer
        const localBiases = localParams.biases[layerIndex];
        avgParams.biases[layerIndex] = [];

        for (let i = 0; i < localBiases.length; i++) {
          let sum = localBiases[i];
          let count = 1;

          // Add biases from remote parameters
          for (const remote of remoteParams) {
            if (
              remote.biases &&
              remote.biases[layerIndex] &&
              remote.biases[layerIndex][i] !== undefined
            ) {
              sum += remote.biases[layerIndex][i];
              count++;
            }
          }

          avgParams.biases[layerIndex][i] = sum / count;
        }
      }

      return avgParams;
    }

    /**
     * Weighted average of parameters based on node performance
     * @param {Object} localParams - Local parameters
     * @param {Array} remoteParams - Remote parameters from other nodes
     * @returns {Object} - Weighted averaged parameters
     * @private
     */
    _weightedAverageParameters(localParams, remoteParams) {
      // Default weight for local node
      const localWeight = 1.0;

      // Get weights for remote nodes (default to 1.0 if no performance data)
      const remoteWeights = remoteParams.map(params =>
        params.metadata?.performance?.weight || 1.0
      );

      // Calculate total weight
      const totalWeight = localWeight + remoteWeights.reduce((sum, w) => sum + w, 0);

      // Initialize result structure
      const result = {
        weights: [],
        biases: [],
        layerConfig: localParams.layerConfig,
        metadata: {
          combinationStrategy: 'weighted_average',
          nodeCount: remoteParams.length + 1,
          weights: [localWeight, ...remoteWeights],
          timestamp: Date.now()
        }
      };

      // Process each layer
      for (let layerIndex = 0; layerIndex < localParams.weights.length; layerIndex++) {
        // Skip if local layer doesn't exist
        if (!localParams.weights[layerIndex]) continue;

        const localWeights = localParams.weights[layerIndex];
        result.weights[layerIndex] = [];

        // Process weights
        for (let i = 0; i < localWeights.length; i++) {
          result.weights[layerIndex][i] = [];

          for (let j = 0; j < localWeights[i].length; j++) {
            // Initialize with weighted local value
            let weightedSum = localWeights[i][j] * localWeight;

            // Add weighted remote values
            for (let r = 0; r < remoteParams.length; r++) {
              const remote = remoteParams[r];
              const weight = remoteWeights[r];

              if (
                remote.weights &&
                remote.weights[layerIndex] &&
                remote.weights[layerIndex][i] &&
                remote.weights[layerIndex][i][j] !== undefined
              ) {
                weightedSum += remote.weights[layerIndex][i][j] * weight;
              }
            }

            // Normalize by total weight
            result.weights[layerIndex][i][j] = weightedSum / totalWeight;
          }
        }

        // Process biases
        const localBiases = localParams.biases[layerIndex];
        result.biases[layerIndex] = [];

        for (let i = 0; i < localBiases.length; i++) {
          // Initialize with weighted local value
          let weightedSum = localBiases[i] * localWeight;

          // Add weighted remote values
          for (let r = 0; r < remoteParams.length; r++) {
            const remote = remoteParams[r];
            const weight = remoteWeights[r];

            if (
              remote.biases &&
              remote.biases[layerIndex] &&
              remote.biases[layerIndex][i] !== undefined
            ) {
              weightedSum += remote.biases[layerIndex][i] * weight;
            }
          }

          // Normalize by total weight
          result.biases[layerIndex][i] = weightedSum / totalWeight;
        }
      }

      return result;
    }

    /**
     * Majority vote for parameters (used for discrete choices)
     * @param {Object} localParams - Local parameters
     * @param {Array} remoteParams - Remote parameters from other nodes
     * @returns {Object} - Parameters selected by majority vote
     * @private
     */
    _majorityVoteParameters(localParams, remoteParams) {
      // This is primarily intended for categorical or binary parameters
      // For continuous parameters, we bin them and choose the most common value
      // Here we implement a simplified version for continuous params

      // Add local params to the voting pool
      const allParams = [localParams, ...remoteParams];

      const result = {
        weights: [],
        biases: [],
        layerConfig: localParams.layerConfig,
        metadata: {
          combinationStrategy: 'majority_vote',
          nodeCount: allParams.length,
          timestamp: Date.now()
        }
      };

      // Process each layer
      for (let layerIndex = 0; layerIndex < localParams.weights.length; layerIndex++) {
        // Skip if local layer doesn't exist
        if (!localParams.weights[layerIndex]) continue;

        const localWeights = localParams.weights[layerIndex];
        result.weights[layerIndex] = [];

        // Process weights
        for (let i = 0; i < localWeights.length; i++) {
          result.weights[layerIndex][i] = [];

          for (let j = 0; j < localWeights[i].length; j++) {
            // Collect all values for this position
            const values = [];

            for (const params of allParams) {
              if (
                params.weights &&
                params.weights[layerIndex] &&
                params.weights[layerIndex][i] &&
                params.weights[layerIndex][i][j] !== undefined
              ) {
                values.push(params.weights[layerIndex][i][j]);
              }
            }

            // Choose the median value (simplified majority vote for continuous values)
            values.sort((a, b) => a - b);
            const medianIndex = Math.floor(values.length / 2);
            result.weights[layerIndex][i][j] = values[medianIndex];
          }
        }

        // Process biases
        const localBiases = localParams.biases[layerIndex];
        result.biases[layerIndex] = [];

        for (let i = 0; i < localBiases.length; i++) {
          // Collect all values for this position
          const values = [];

          for (const params of allParams) {
            if (
              params.biases &&
              params.biases[layerIndex] &&
              params.biases[layerIndex][i] !== undefined
            ) {
              values.push(params.biases[layerIndex][i]);
            }
          }

          // Choose the median value
          values.sort((a, b) => a - b);
          const medianIndex = Math.floor(values.length / 2);
          result.biases[layerIndex][i] = values[medianIndex];
        }
      }

      return result;
    }

    /**
     * Handles synchronization failures
     * @param {Error} error - The error that occurred
     * @returns {Boolean} - True if recovery was successful
     * @private
     */
    _handleSynchronizationFailure(error) {
      const strategy = this.distributedConfig.syncRecoveryStrategy;
      const errorMessage = error.message || 'Unknown error';

      // Log detailed error information
      Prime.Logger.error(`Sync failure (${this.distributedState.syncRetryCount}/${this.distributedConfig.maxSyncRetries}): ${errorMessage}`);

      // Record failure in history
      this.distributedState.syncHistory.unshift({
        timestamp: Date.now(),
        iteration: this.metrics.iteration,
        success: false,
        error: errorMessage,
        strategy
      });

      if (this.distributedState.syncHistory.length > 10) {
        this.distributedState.syncHistory.pop();
      }

      // Check if we should retry
      if (this.distributedState.syncRetryCount < this.distributedConfig.maxSyncRetries) {
        // Exponential backoff for retries
        const backoffMs = Math.pow(2, this.distributedState.syncRetryCount) * 100;

        Prime.Logger.info(`Retrying synchronization in ${backoffMs}ms...`);

        // Schedule retry with backoff
        setTimeout(() => {
          this.synchronizeParameters().catch(e => {
            Prime.Logger.error(`Retry failed: ${e.message}`);
          });
        }, backoffMs);

        return true;
      }

      // Apply recovery strategy based on configuration
      switch (strategy) {
        case 'local_fallback':
          // Continue with local parameters
          Prime.Logger.warn('Using local fallback after synchronization failure');
          return true;

        case 'conservative_merge':
          // Try to merge with any available parameters
          Prime.Logger.warn('Attempting conservative merge with available parameters');
          return this._attemptConservativeMerge();

        case 'checkpoint_rollback':
          // Roll back to last known good state
          Prime.Logger.warn('Rolling back to last checkpoint');
          return this._rollbackToCheckpoint();

        case 'fail_fast':
          // Stop distributed training on error
          Prime.Logger.error('Distributed training halted due to synchronization failure');
          this.distributedConfig.enabled = false;
          return false;

        default:
          // Default to local fallback
          Prime.Logger.warn(`Unknown recovery strategy: ${strategy}, falling back to local parameters`);
          return true;
      }
    }

    /**
     * Attempts to merge with any available parameters after failure
     * @returns {Boolean} - True if successful
     * @private
     */
    _attemptConservativeMerge() {
      try {
        // Get local parameters
        const localParams = this._extractModelParameters();

        // Get any cached parameters from last successful sync
        const cachedParams = this.distributedState.lastSuccessfulParams;

        if (!cachedParams) {
          Prime.Logger.warn('No cached parameters available for conservative merge');
          return true; // Continue with local parameters
        }

        // Simple interpolation between local and last known good state
        const mergedParams = {
          weights: [],
          biases: [],
          layerConfig: localParams.layerConfig,
        };

        // Conservative blending factor (mostly use local params)
        const localWeight = 0.8;
        const cachedWeight = 0.2;

        // Process each layer
        for (let layerIndex = 0; layerIndex < localParams.weights.length; layerIndex++) {
          if (!localParams.weights[layerIndex] || !cachedParams.weights[layerIndex]) {
            mergedParams.weights[layerIndex] = localParams.weights[layerIndex];
            mergedParams.biases[layerIndex] = localParams.biases[layerIndex];
            continue;
          }

          // Blend weights
          mergedParams.weights[layerIndex] = [];
          for (let i = 0; i < localParams.weights[layerIndex].length; i++) {
            mergedParams.weights[layerIndex][i] = [];

            for (let j = 0; j < localParams.weights[layerIndex][i].length; j++) {
              const localVal = localParams.weights[layerIndex][i][j];
              const cachedVal = cachedParams.weights[layerIndex][i][j];

              if (localVal !== undefined && cachedVal !== undefined) {
                mergedParams.weights[layerIndex][i][j] =
                  localVal * localWeight + cachedVal * cachedWeight;
              } else {
                mergedParams.weights[layerIndex][i][j] = localVal;
              }
            }
          }

          // Blend biases
          mergedParams.biases[layerIndex] = [];
          for (let i = 0; i < localParams.biases[layerIndex].length; i++) {
            const localVal = localParams.biases[layerIndex][i];
            const cachedVal = cachedParams.biases[layerIndex][i];

            if (localVal !== undefined && cachedVal !== undefined) {
              mergedParams.biases[layerIndex][i] =
                localVal * localWeight + cachedVal * cachedWeight;
            } else {
              mergedParams.biases[layerIndex][i] = localVal;
            }
          }
        }

        // Apply merged parameters
        const success = this._applyParameters(mergedParams);

        if (success) {
          Prime.Logger.info('Conservative merge applied successfully');
        }

        return success;
      } catch (error) {
        Prime.Logger.error(`Conservative merge failed: ${error.message}`);
        return false;
      }
    }

    /**
     * Rolls back to last checkpoint
     * @returns {Boolean} - True if successful
     * @private
     */
    _rollbackToCheckpoint() {
      try {
        // Check if we have a checkpoint
        if (!this.distributedState.checkpoint) {
          Prime.Logger.warn('No checkpoint available for rollback');
          return true; // Continue with current parameters
        }

        // Apply checkpoint parameters
        const success = this._applyParameters(this.distributedState.checkpoint);

        if (success) {
          Prime.Logger.info('Rolled back to last checkpoint successfully');
        }

        return success;
      } catch (error) {
        Prime.Logger.error(`Checkpoint rollback failed: ${error.message}`);
        return false;
      }
    }

    /**
     * Creates a checkpoint of current parameters
     * @returns {Boolean} - True if successful
     */
    createCheckpoint() {
      try {
        // Extract current parameters
        const params = this._extractModelParameters();

        // Verify parameter coherence
        if (!this._verifyParameterCoherence(params)) {
          Prime.Logger.warn('Cannot create checkpoint: parameters failed coherence check');
          return false;
        }

        // Store checkpoint
        this.distributedState.checkpoint = params;
        this.distributedState.checkpointTime = Date.now();

        Prime.Logger.info('Created parameter checkpoint successfully');
        return true;
      } catch (error) {
        Prime.Logger.error(`Failed to create checkpoint: ${error.message}`);
        return false;
      }
    }

    /**
     * Performs distributed coherence check
     * @returns {Promise<Boolean>} - True if coherent
     */
    async performCoherenceCheck() {
      if (!this.distributedConfig.enabled || !this.distributedState.isInitialized) {
        return true;
      }

      try {
        // Extract current parameters
        const params = this._extractModelParameters();

        // Verify local coherence
        const isLocallyCoherent = this._verifyParameterCoherence(params);

        if (!isLocallyCoherent) {
          Prime.Logger.warn('Local parameters failed coherence check');
          return false;
        }

        // Record coherence check
        this.distributedState.lastCoherenceCheck = Date.now();

        // If we have the CoherenceValidator, get detailed metrics
        if (Prime.Neural.Distributed.CoherenceValidator) {
          const metrics = Prime.Neural.Distributed.CoherenceValidator.calculateCoherenceMetrics({
            layers: this.layers
          });

          if (Prime.Logger && Prime.Logger.debug) {
            Prime.Logger.debug(`Coherence metrics: ${JSON.stringify(metrics)}`);
          }
        }

        return true;
      } catch (error) {
        Prime.Logger.error(`Coherence check failed: ${error.message}`);
        return false;
      }
    }

    /**
     * Gets the current distributed status
     * @returns {Object} - Distributed status
     */
    getDistributedStatus() {
      return {
        enabled: this.distributedConfig.enabled,
        initialized: this.distributedState.isInitialized,
        partitionScheme: this.distributedConfig.partitionScheme,
        syncFrequency: this.distributedConfig.syncFrequency,
        synchronizedIterations: this.distributedState.synchronizedIterations,
        lastSyncIteration: this.distributedState.lastSyncIteration,
        failedSynchronizations: this.distributedState.failedSynchronizations,
        syncStrategy: this.distributedConfig.synchronizationStrategy,
        recoveryStrategy: this.distributedConfig.syncRecoveryStrategy,
        activeNodes: this.distributedState.activeNodes.length,
        nodeId: this.distributedState.nodeId,
        lastParameterUpdate: this.distributedState.lastParameterUpdate,
        lastCoherenceCheck: this.distributedState.lastCoherenceCheck,
        hasCheckpoint: !!this.distributedState.checkpoint,
        syncErrors: this.distributedState.syncErrors.slice(0, 3), // Return only the 3 most recent errors
      };
    }

    /**
     * Trains the model for one iteration
     * @param {Array} input - Input data
     * @param {Array} target - Target output
     * @returns {Promise<Object>} - Training results
     */
    async train(input, target) {
      // Increment iteration counter
      this.metrics.iteration++;

      // Train the base model using parent implementation
      const result = await super.train(input, target);

      // Synchronize parameters if needed
      if (this.distributedConfig.enabled && this.distributedState.isInitialized) {
        await this.synchronizeParameters();
      }

      // Perform coherence check periodically
      if (this.distributedConfig.enabled &&
          this.metrics.iteration % (this.distributedConfig.syncFrequency * 5) === 0) {
        await this.performCoherenceCheck();
      }

      // Create checkpoint periodically (every 100 iterations)
      if (this.distributedConfig.enabled &&
          this.metrics.iteration % 100 === 0) {
        this.createCheckpoint();
      }

      return {
        ...result,
        distributed: {
          enabled: this.distributedConfig.enabled,
          synchronized: this.metrics.iteration === this.distributedState.lastSyncIteration
        }
      };
    }
  }

  // Register the model
  Prime.Neural.Distributed.DistributedNeuralModel = DistributedNeuralModel;
})();

// Export the module
module.exports = Prime.Neural.Distributed;