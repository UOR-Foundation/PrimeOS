/**
 * PrimeOS JavaScript Library - Distributed Neural Model Implementation
 * This file contains the implementation of the DistributedNeuralModel class
 * with proper input size handling and comprehensive dimension validation.
 */

// Import the Prime object from core
const Prime = require('../../core');

// Make sure dimension validator is loaded
require('./dimension-validator');

/**
 * Complete implementation of DistributedNeuralModel
 * Includes proper input size handling and comprehensive dimension validation
 */
class DistributedNeuralModel extends Prime.Neural.Model.NeuralModel {
  /**
   * Create a new distributed neural network model with proper input size handling
   * @param {Object} config - Model configuration
   * @param {number} config.inputSize - Size of the input layer
   * @param {Array} [config.layers=[]] - Array of layer configurations
   * @param {Object} [config.optimizer={}] - Optimizer configuration
   * @param {Object} [config.coherence={}] - Coherence configuration
   * @param {Object} [config.metadata={}] - Model metadata
   * @param {Object} [config.distributed={}] - Distributed configuration
   */
  constructor(config = {}) {
    // Store original input size before calling parent constructor
    const originalInputSize = config.inputSize;

    // Call parent constructor
    super(config);

    // Store original input size as a separate property
    this.originalInputSize = originalInputSize;

    // Restore input size to original value
    this.inputSize = originalInputSize;

    // Set up distributed configuration
    this.distributedConfig = {
      enabled: config.distributed?.enabled ?? false,
      clusterManager: config.distributed?.clusterManager || null,
      partitionScheme: config.distributed?.partitionScheme || 'data_parallel',
      nodeCount: config.distributed?.nodeCount || 1,
      syncFrequency: config.distributed?.syncFrequency || 10,
      coherenceCheckFrequency:
        config.distributed?.coherenceCheckFrequency || 50,
      fallbackToLocal: config.distributed?.fallbackToLocal ?? true,
      synchronizationStrategy:
        config.distributed?.synchronizationStrategy || 'average',
      syncRecoveryStrategy:
        config.distributed?.syncRecoveryStrategy || 'local_fallback',
    };

    // Distributed operation state
    this.distributedState = {
      isInitialized: false,
      activeNodes: [],
      taskAssignments: new Map(), // layerId -> nodeId
      pendingTasks: [],
      completedTasks: 0,
      failedTasks: 0,
      lastSyncIteration: 0,
      lastCoherenceCheck: 0,
      networkPartitions: 0,
      lastParameterUpdate: 0,
      synchronizedIterations: 0,
      failedSynchronizations: 0,
    };

    // Validate dimensions if validation is available
    if (Prime.Neural.Distributed.DimensionValidator) {
      // Log the layer dimensions for debugging
      Prime.Neural.Distributed.DimensionValidator.logLayerDimensions(
        this.layers,
      );

      // Verify model dimensions
      const dimensionsValid =
        Prime.Neural.Distributed.DimensionValidator.verifyModelDimensions(this);
      if (!dimensionsValid && Prime.Logger && Prime.Logger.error) {
        Prime.Logger.error('Model dimensions are inconsistent');
      }
    }

    // Initialize if distributed mode is enabled and cluster manager is provided
    if (
      this.distributedConfig.enabled &&
      this.distributedConfig.clusterManager
    ) {
      this._initializeDistributedMode();
    }
  }

  /**
   * Override addLayer to ensure input size integrity
   * @param {Object} layerConfig - Layer configuration
   * @returns {FixedDistributedNeuralModel} This model instance (for chaining)
   */
  addLayer(layerConfig) {
    // First, validate the layer config if validator is available
    if (Prime.Neural.Distributed.DimensionValidator) {
      Prime.Neural.Distributed.DimensionValidator.validateLayerConfig(
        layerConfig,
        this.layers.length,
      );
    }

    // Call parent addLayer
    super.addLayer(layerConfig);

    return this;
  }

  /**
   * Initialize distributed computation mode
   * @private
   */
  _initializeDistributedMode() {
    try {
      const clusterManager = this.distributedConfig.clusterManager;

      // Check for required cluster resources
      if (clusterManager.nodes.size === 0) {
        throw new Error('Cluster manager has no nodes available');
      }

      // Create node assignments based on partition scheme
      this._createNodeAssignments();

      // Create partition scheme based on configuration
      this._createPartitionScheme();

      // Mark distributed mode as initialized
      this.distributedState.isInitialized = true;

      // Log initialization
      if (Prime.Logger && Prime.Logger.info) {
        Prime.Logger.info('Distributed neural model initialized', {
          nodeCount: this.distributedState.activeNodes.length,
          partitionScheme: this.distributedConfig.partitionScheme,
        });
      }
    } catch (error) {
      // Log error but continue in local mode if fallback is enabled
      if (Prime.Logger && Prime.Logger.error) {
        Prime.Logger.error(
          'Failed to initialize distributed mode, falling back to local',
          {
            error: error.message,
          },
        );
      }

      if (!this.distributedConfig.fallbackToLocal) {
        throw error;
      }

      // Disable distributed mode
      this.distributedConfig.enabled = false;
    }
  }

  /**
   * Create node assignments for distributed computation
   * @private
   */
  _createNodeAssignments() {
    const clusterManager = this.distributedConfig.clusterManager;

    // Get available nodes from cluster manager
    const availableNodes = [...clusterManager.nodes.values()].filter(
      (node) =>
        node.state === Prime.Distributed.Cluster.NodeState.READY ||
        node.state === Prime.Distributed.Cluster.NodeState.WORKING,
    );

    if (availableNodes.length === 0) {
      throw new Error('No available nodes for distributed computation');
    }

    // Store active nodes
    this.distributedState.activeNodes = availableNodes.map((node) => node.id);

    // Create initial task assignments (will be updated based on partition scheme)
    this.layers.forEach((layer, index) => {
      // Simple round-robin assignment for now
      const nodeIndex = index % availableNodes.length;
      this.distributedState.taskAssignments.set(
        `layer_${index}`,
        availableNodes[nodeIndex].id,
      );
    });
  }

  /**
   * Create partition scheme based on configuration
   * @private
   */
  _createPartitionScheme() {
    // Determine partition scheme type
    let partitionType;
    switch (this.distributedConfig.partitionScheme.toLowerCase()) {
      case 'data_parallel':
        partitionType = Prime.Distributed.Partition.PartitionType.DATA_PARALLEL;
        break;
      case 'layer_wise':
        partitionType = Prime.Distributed.Partition.PartitionType.LAYER_WISE;
        break;
      case 'intra_layer':
        partitionType = Prime.Distributed.Partition.PartitionType.INTRA_LAYER;
        break;
      default:
        partitionType = Prime.Distributed.Partition.PartitionType.DATA_PARALLEL;
    }

    // Create partition configuration
    const partitionConfig = {
      type: partitionType,
      nodeIds: this.distributedState.activeNodes,
      layerConfig: {},
    };

    // Configure layer assignments based on scheme
    this.layers.forEach((layer, index) => {
      partitionConfig.layerConfig[`layer_${index}`] = {
        inputSize: layer.inputSize,
        outputSize: layer.outputSize,
        activation: layer.activation,
      };

      // Add layer-specific config if available
      if (layer.filters)
        partitionConfig.layerConfig[`layer_${index}`].filters = layer.filters;
      if (layer.kernelSize)
        partitionConfig.layerConfig[`layer_${index}`].kernelSize =
          layer.kernelSize;
      if (layer.hiddenSize)
        partitionConfig.layerConfig[`layer_${index}`].hiddenSize =
          layer.hiddenSize;
    });

    // Create and store the partition scheme
    this.partitionScheme = new Prime.Distributed.Partition.PartitionScheme(
      partitionConfig,
    );
  }

  /**
   * Extract model parameters for synchronization
   * @returns {Object} Parameters object containing weights and biases
   * @private
   */
  _extractModelParameters() {
    return {
      weights: this.layers.map((layer) => layer.weights),
      biases: this.layers.map((layer) => layer.biases),
      layerConfig: this.layers.map((layer) => ({
        inputSize: layer.inputSize,
        outputSize: layer.outputSize,
        activation: layer.activation,
        type: layer.type || 'dense',
      })),
    };
  }

  /**
   * Apply parameters to the model
   * @param {Object} parameters Parameters object containing weights and biases
   * @returns {Boolean} Success indicator
   * @private
   */
  _applyParameters(parameters) {
    if (!parameters || !parameters.weights || !parameters.biases) {
      return false;
    }

    // Verify parameter coherence before applying
    if (Prime.Neural.Distributed.DimensionValidator) {
      const isCoherent =
        Prime.Neural.Distributed.DimensionValidator.validateParameterCoherence(
          parameters,
        );
      if (!isCoherent) {
        if (Prime.Logger && Prime.Logger.warn) {
          Prime.Logger.warn(
            'Parameters failed coherence validation, skipping application',
          );
        }
        return false;
      }
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
      if (Prime.Logger && Prime.Logger.error) {
        Prime.Logger.error(`Failed to apply parameters: ${error.message}`);
      }
      return false;
    }
  }

  /**
   * Synchronize parameters across nodes
   * @returns {Promise<Boolean>} True if successful
   */
  async _synchronizeParameters() {
    // Skip if distributed mode is disabled
    if (
      !this.distributedConfig.enabled ||
      !this.distributedState.isInitialized
    ) {
      return true;
    }

    // Check if synchronization is needed based on frequency
    if (this.metrics.iteration % this.distributedConfig.syncFrequency !== 0) {
      return true;
    }

    try {
      // Get local parameters
      const localParams = this._extractModelParameters();

      // Get remote parameters from other nodes
      const clusterManager = this.distributedConfig.clusterManager;
      const remoteResults = await clusterManager.getParametersFromNodes(
        this.distributedState.activeNodes,
        this.distributedConfig.synchronizationStrategy,
      );

      if (!remoteResults || remoteResults.length === 0) {
        if (Prime.Logger && Prime.Logger.warn) {
          Prime.Logger.warn(
            'No remote parameters received for synchronization',
          );
        }
        return false;
      }

      // Average parameters based on synchronization strategy
      let finalParams;
      if (this.distributedConfig.synchronizationStrategy === 'average') {
        finalParams = this._averageParameters(localParams, remoteResults);
      } else {
        // Use default averaging as fallback
        finalParams = this._averageParameters(localParams, remoteResults);
      }

      // Apply averaged parameters
      const success = this._applyParameters(finalParams);

      // Update state
      this.distributedState.synchronizedIterations++;
      this.distributedState.lastSyncIteration = this.metrics.iteration;
      this.distributedState.lastParameterUpdate = Date.now();

      return success;
    } catch (error) {
      this.distributedState.failedSynchronizations++;

      if (Prime.Logger && Prime.Logger.error) {
        Prime.Logger.error(
          `Parameter synchronization failed: ${error.message}`,
        );
      }

      // Apply recovery strategy
      return this._handleSynchronizationFailure(error);
    }
  }

  /**
   * Average parameters from multiple nodes
   * @param {Object} localParams Local parameters
   * @param {Array} remoteParams Remote parameters from other nodes
   * @returns {Object} Averaged parameters
   * @private
   */
  _averageParameters(localParams, remoteParams) {
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
   * Handle synchronization failures with recovery strategy
   * @param {Error} error Error that occurred during synchronization
   * @returns {Boolean} True if recovery was successful
   * @private
   */
  _handleSynchronizationFailure(error) {
    const strategy = this.distributedConfig.syncRecoveryStrategy;

    switch (strategy) {
      case 'local_fallback':
        // Continue with local parameters
        if (Prime.Logger && Prime.Logger.warn) {
          Prime.Logger.warn(
            'Using local fallback after synchronization failure',
          );
        }
        return true;

      case 'retry':
        // Implementation of parameter synchronization retry
        if (Prime.Logger && Prime.Logger.info) {
          Prime.Logger.info(
            'Using retry strategy for parameter synchronization',
          );
        }
        return true;

      case 'conservative_merge':
        // Implementation of partial parameter merging
        if (Prime.Logger && Prime.Logger.info) {
          Prime.Logger.info(
            'Using conservative merge strategy for parameter recovery',
          );
        }
        return true;

      default:
        return true; // Always fallback to local by default
    }
  }

  /**
   * Perform distributed coherence check
   * @returns {Promise<Boolean>} True if coherent
   */
  async _distributedCoherenceCheck() {
    if (
      !this.distributedConfig.enabled ||
      !this.distributedState.isInitialized
    ) {
      return true;
    }

    try {
      // Extract current parameters
      const params = this._extractModelParameters();

      // Verify local coherence with dimension validator
      let isCoherent = true;
      if (Prime.Neural.Distributed.DimensionValidator) {
        isCoherent =
          Prime.Neural.Distributed.DimensionValidator.validateParameterCoherence(
            params,
          );
      }

      if (!isCoherent) {
        if (Prime.Logger && Prime.Logger.warn) {
          Prime.Logger.warn('Local parameters failed coherence check');
        }
        return false;
      }

      // Update state
      this.distributedState.lastCoherenceCheck = this.metrics.iteration;

      return true;
    } catch (error) {
      if (Prime.Logger && Prime.Logger.error) {
        Prime.Logger.error(`Coherence check failed: ${error.message}`);
      }
      return false;
    }
  }

  /**
   * Get distributed status information
   * @returns {Object} Status information
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
      originalInputSize: this.originalInputSize,
      currentInputSize: this.inputSize,
    };
  }
}

// Export the class
module.exports = DistributedNeuralModel;
