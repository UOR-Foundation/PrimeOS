/**
 * PrimeOS Neural Distributed Module - FIXED Implementation
 *
 * This is a reference implementation of the DistributedNeuralModel with the
 * fixes for proper input size handling and dimension validation.
 */

// Import core modules
const Prime = require("../../core.js");
require("../../neural/index.js");

// Create namespaces
Prime.Neural = Prime.Neural || {};
Prime.Neural.Distributed = Prime.Neural.Distributed || {};

/**
 * Distributed Neural Model - Manages neural network execution across multiple nodes
 *
 * This implementation fixes the input size bug by preserving the original input size
 * and adds robust dimension validation.
 */
class DistributedNeuralModel {
  /**
   * Creates a new distributed neural model
   * @param {Object} config - Configuration object
   */
  constructor(config = {}) {
    // Validate the configuration
    if (Prime.Neural.Distributed.DimensionValidator) {
      Prime.Neural.Distributed.DimensionValidator.validateModelConfig(config);
    }

    // Store and preserve the original input size
    this.originalInputSize = config.inputSize || 10;
    this.inputSize = this.originalInputSize;

    // Initialize layers array
    this.layers = [];

    // Add layers from configuration
    if (Array.isArray(config.layers)) {
      for (const layerConfig of config.layers) {
        this.addLayer(layerConfig);
      }
    }

    // IMPORTANT: Restore original input size after layers are added
    this.inputSize = this.originalInputSize;

    // Configure distributed settings
    this.distributedConfig = {
      enabled: config.distributed?.enabled ?? false,
      partitionScheme: config.distributed?.partitionScheme || "data_parallel",
      syncFrequency: config.distributed?.syncFrequency || 10,
      synchronizationStrategy:
        config.distributed?.synchronizationStrategy || "average",
      syncRecoveryStrategy:
        config.distributed?.syncRecoveryStrategy || "local_fallback",
    };

    // Initialize distributed state
    this.distributedState = {
      isInitialized: false,
      activeNodes: [],
      lastSyncIteration: 0,
      lastParameterUpdate: 0,
      synchronizedIterations: 0,
      failedSynchronizations: 0,
      lastCoherenceCheck: 0,
    };

    // Initialize metrics
    this.metrics = {
      iteration: 0,
      epoch: 0,
      trainingExamples: 0,
      lastLoss: 0,
    };

    // Set up cluster if distributed mode is enabled
    if (this.distributedConfig.enabled) {
      this._initializeCluster();
    }

    // Log layer dimensions if validator is available
    if (Prime.Neural.Distributed.DimensionValidator) {
      Prime.Neural.Distributed.DimensionValidator.logLayerDimensions(
        this.layers,
      );
    }

    // Perform initial coherence check
    this._initialCoherenceCheck();
  }

  /**
   * Adds a layer to the model
   * @param {Object} layerConfig - Layer configuration
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

    // Create the layer based on type
    let layer;

    if (layerOptions.type === "dense" || !layerOptions.type) {
      layer = new Prime.Neural.Layer.Dense(layerOptions);
    } else {
      // Handle other layer types
      throw new Prime.ValidationError(
        `Unsupported layer type: ${layerOptions.type}`,
      );
    }

    // Add layer to the model
    this.layers.push(layer);

    // Update input size for next layer
    this.inputSize = layerOptions.outputSize;

    return this;
  }

  /**
   * Initializes the cluster connection for distributed training
   * @private
   */
  _initializeCluster() {
    if (!Prime.Distributed || !Prime.Distributed.Cluster) {
      throw new Prime.ValidationError("Distributed modules not loaded");
    }

    // Create cluster manager
    this.cluster = new Prime.Distributed.Cluster.Manager({
      partitionScheme: this.distributedConfig.partitionScheme,
    });

    // Register with cluster
    this.distributedState.nodeId = this.cluster.register(this);

    // Get active nodes
    this.distributedState.activeNodes = this.cluster.getActiveNodes();
  }

  /**
   * Performs initial coherence check
   * @private
   */
  _initialCoherenceCheck() {
    if (!this.distributedConfig.enabled) return;

    try {
      // Extract model parameters
      const params = this._extractModelParameters();

      // Verify parameter coherence
      const isCoherent = this._verifyParameterCoherence(params);

      if (!isCoherent) {
        Prime.Logger.warn("Initial model parameters failed coherence check");
      }
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
    return {
      weights: this.layers.map((layer) => layer.weights),
      biases: this.layers.map((layer) => layer.biases),
      layerConfig: this.layers.map((layer) => ({
        inputSize: layer.inputSize,
        outputSize: layer.outputSize,
        type: layer.type,
        activation: layer.activation,
      })),
    };
  }

  /**
   * Applies parameters to the model
   * @param {Object} parameters - Parameters to apply
   * @returns {Boolean} - True if successful
   * @private
   */
  _applyParameters(parameters) {
    if (!parameters || !parameters.weights || !parameters.biases) {
      return false;
    }

    // Verify parameter coherence before applying
    if (!this._verifyParameterCoherence(parameters)) {
      return false;
    }

    try {
      // Apply weights and biases to each layer
      for (
        let i = 0;
        i < this.layers.length && i < parameters.weights.length;
        i++
      ) {
        if (parameters.weights[i]) {
          this.layers[i].weights = parameters.weights[i];
        }

        if (parameters.biases[i]) {
          this.layers[i].biases = parameters.biases[i];
        }
      }

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
    // Use the dimension validator if available
    if (Prime.Neural.Distributed.DimensionValidator) {
      return Prime.Neural.Distributed.DimensionValidator.validateParameterCoherence(
        parameters,
      );
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
   * Averages parameters from multiple nodes
   * @param {Object} localParams - Local parameters
   * @param {Array} remoteParams - Remote parameters from other nodes
   * @returns {Object} - Averaged parameters
   * @private
   */
  _averageParameters(localParams, remoteParams) {
    const strategy = this.distributedConfig.synchronizationStrategy;

    // Use simple averaging as default
    return this._simpleAverageParameters(localParams, remoteParams);
  }

  /**
   * Simple averaging of parameters
   * @param {Object} localParams - Local parameters
   * @param {Array} remoteParams - Remote parameters from other nodes
   * @returns {Object} - Averaged parameters
   * @private
   */
  _simpleAverageParameters(localParams, remoteParams) {
    const avgParams = {
      weights: [],
      biases: [],
    };

    // Process each layer
    for (
      let layerIndex = 0;
      layerIndex < localParams.weights.length;
      layerIndex++
    ) {
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
   * Synchronizes parameters across nodes
   * @returns {Promise<Boolean>} - True if successful
   */
  async _synchronizeParameters() {
    if (!this.distributedConfig.enabled) {
      return true;
    }

    // Check if synchronization is needed
    if (this.metrics.iteration % this.distributedConfig.syncFrequency !== 0) {
      return true;
    }

    try {
      // Get local parameters
      const localParams = this._extractModelParameters();

      // Get remote parameters
      const remoteResults = await this.cluster.manager.getNodeParameters();

      // Average parameters
      const avgParams = this._averageParameters(localParams, remoteResults);

      // Apply averaged parameters
      const success = this._applyParameters(avgParams);

      // Update state
      this.distributedState.synchronizedIterations++;
      this.distributedState.lastSyncIteration = this.metrics.iteration;
      this.distributedState.lastParameterUpdate = Date.now();

      return success;
    } catch (error) {
      this.distributedState.failedSynchronizations++;
      Prime.Logger.error(`Parameter synchronization failed: ${error.message}`);

      // Apply recovery strategy
      return this._handleSynchronizationFailure(error);
    }
  }

  /**
   * Handles synchronization failures
   * @param {Error} error - The error that occurred
   * @returns {Boolean} - True if recovery was successful
   * @private
   */
  _handleSynchronizationFailure(error) {
    const strategy = this.distributedConfig.syncRecoveryStrategy;

    switch (strategy) {
      case "local_fallback":
        // Continue with local parameters
        Prime.Logger.warn("Using local fallback after synchronization failure");
        return true;

      case "retry":
        // Retry is handled at a higher level
        return false;

      case "conservative_merge":
        // Would implement partial merging of available parameters
        Prime.Logger.warn("Conservative merge not yet implemented");
        return false;

      default:
        return false;
    }
  }

  /**
   * Performs distributed coherence check
   * @returns {Promise<Boolean>} - True if coherent
   */
  async _distributedCoherenceCheck() {
    if (!this.distributedConfig.enabled) {
      return true;
    }

    try {
      // Extract current parameters
      const params = this._extractModelParameters();

      // Verify local coherence
      const isLocallyCoherent = this._verifyParameterCoherence(params);

      if (!isLocallyCoherent) {
        Prime.Logger.warn("Local parameters failed coherence check");
        return false;
      }

      // Update state
      this.distributedState.lastCoherenceCheck = this.metrics.iteration;

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
      partitionScheme: this.distributedConfig.partitionScheme,
      syncFrequency: this.distributedConfig.syncFrequency,
      synchronizedIterations: this.distributedState.synchronizedIterations,
      lastSyncIteration: this.distributedState.lastSyncIteration,
      failedSynchronizations: this.distributedState.failedSynchronizations,
      syncStrategy: this.distributedConfig.synchronizationStrategy,
      recoveryStrategy: this.distributedConfig.syncRecoveryStrategy,
      activeNodes: this.distributedState.activeNodes.length,
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

    // Train the base model
    // (Implementation would depend on base NeuralModel class)

    // Synchronize parameters if needed
    await this._synchronizeParameters();

    // Perform coherence check periodically
    if (
      this.metrics.iteration % (this.distributedConfig.syncFrequency * 5) ===
      0
    ) {
      await this._distributedCoherenceCheck();
    }

    return {
      loss: this.metrics.lastLoss,
      iteration: this.metrics.iteration,
    };
  }
}

// Register the model
Prime.Neural.Distributed.DistributedNeuralModel = DistributedNeuralModel;

// Export the module
module.exports = { Neural: Prime.Neural };
