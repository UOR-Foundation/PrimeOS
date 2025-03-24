/**
 * PrimeOS JavaScript Library - Neural Distributed Module (Consolidated)
 *
 * This is the consolidated implementation of the DistributedNeuralModel with:
 * 1. Fixed input size handling and proper dimension validation
 * 2. Advanced synchronization strategies (weighted_average, majority_vote, parameter_server)
 * 3. Comprehensive recovery mechanisms
 * 4. Multiple parallelism models (data, model, hybrid)
 */

// Import core modules with explicit paths
const Prime = require('../../core/prime.js');
require('../../neural/index.js');

// Import validators
require('./dimension-validator');
require('./coherence-validator');

// Ensure namespaces exist
Prime.Neural = Prime.Neural || {};
Prime.Neural.Distributed = Prime.Neural.Distributed || {};

/**
 * Distributed Neural Model
 * Enhances NeuralModel with distributed computation capabilities
 * @extends Prime.Neural.Model.NeuralModel
 */
class DistributedNeuralModel extends Prime.Neural.Model.NeuralModel {
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
    // Validate the configuration if validator is available
    if (Prime.Neural.Distributed.DimensionValidator) {
      Prime.Neural.Distributed.DimensionValidator.validateModelConfig(config);
    }

    // Store original input size before calling parent constructor
    const originalInputSize = config.inputSize || 10;

    // Call parent constructor with validated config
    super(config);

    // Store original input size as a separate property
    this.originalInputSize = originalInputSize;

    // IMPORTANT: Restore original input size after layers are added
    this.inputSize = originalInputSize;

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
      // Enhanced parameter server mode fields
      nodeRole: config.distributed?.nodeRole || 'worker', // 'worker' or 'server'
      lastParameterSource: null, // ID of last node we got parameters from
      lastUpdateType: 'full', // 'full' or 'differential'
      parameterVersion: Date.now(), // Version counter for this node's parameters
      lastSuccessfulParams: null, // Store last successful parameters for differential sync
      computeCapacity: config.distributed?.computeCapacity || 1.0, // Relative compute capacity (higher is better)
      networkLatency: config.distributed?.networkLatency || 100, // Network latency in ms (lower is better)
      serverSelectionHistory: [], // Track server selection history
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
   * Override addLayer to ensure input size integrity
   * @param {Object} layerConfig - Layer configuration
   * @returns {DistributedNeuralModel} - Returns this for chaining
   */
  addLayer(layerConfig) {
    // Create layer configuration with proper input size
    const layerInputSize = this.layers.length > 0
      ? this.layers[this.layers.length - 1].outputSize
      : this.originalInputSize;

    // Merge input size with layer config
    const fullLayerConfig = {
      ...layerConfig,
      inputSize: layerConfig.inputSize || layerInputSize,
    };

    // Create the layer using parent implementation
    super.addLayer(fullLayerConfig);

    // Ensure input size is maintained after layer addition
    this.inputSize = this.originalInputSize;

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
      if (
        !clusterManager ||
        !clusterManager.nodes ||
        clusterManager.nodes.size === 0
      ) {
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

      Prime.Logger.info(
        `Distributed mode initialized with ${this.distributedState.activeNodes.length} active nodes`
      );
      Prime.Logger.info(
        `Using partition scheme: ${this.distributedConfig.partitionScheme}`
      );
      Prime.Logger.info(
        `Using sync strategy: ${this.distributedConfig.synchronizationStrategy}`
      );
    } catch (error) {
      Prime.Logger.error(
        `Failed to initialize distributed mode: ${error.message}`
      );
      this.distributedState.isInitialized = false;
      this.distributedConfig.enabled = false;
    }
  }

  /**
   * Perform initial coherence check
   * @private
   */
  _initialCoherenceCheck() {
    // Skip if validators not available
    if (!Prime.Neural.Distributed.CoherenceValidator) {
      return;
    }

    try {
      // Extract parameters
      const params = this._extractModelParameters();

      // Verify parameter coherence
      const coherenceResult =
        Prime.Neural.Distributed.CoherenceValidator.checkParameterCoherence(
          params,
          true  // detailed report
        );

      if (!coherenceResult.isCoherent) {
        Prime.Logger.warn(
          `Initial parameters failed coherence check: ${coherenceResult.issues.join(', ')}`
        );
      } else {
        Prime.Logger.debug('Initial parameters passed coherence check');
      }

      // Update state
      this.distributedState.lastCoherenceCheck = Date.now();
    } catch (error) {
      Prime.Logger.error(`Failed to perform initial coherence check: ${error.message}`);
    }
  }

  /**
   * Extracts current model parameters for distribution
   * @param {Object} [options={}] - Extraction options
   * @returns {Object} - Model parameters (weights and biases)
   * @private
   */
  _extractModelParameters(options = {}) {
    // Support differential parameter extraction for efficiency in parameter server mode
    const differential = options.differential || false;
    const baseParameters = options.baseParameters || null;
    const diffThreshold = options.diffThreshold || 0.00001;

    // Regular full parameter extraction
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
          layerCount: this.layers.length,
        },
        isPartial: false,
      },
    };

    // If we're doing differential extraction and have base parameters
    if (differential && baseParameters) {
      const diffParams = {
        weights: [],
        biases: [],
        layerConfig: parameters.layerConfig,
        metadata: {
          ...parameters.metadata,
          isPartial: true,
          differentialInfo: {
            baseVersion: baseParameters.metadata?.version || 0,
            baseTimestamp: baseParameters.metadata?.extractionTime || 0,
            diffThreshold,
            diffStats: {},
          },
        }
      };

      let totalDiffCount = 0;

      // For each layer, compute weight differences
      for (let layerIndex = 0; layerIndex < parameters.weights.length; layerIndex++) {
        // Skip if this layer doesn't exist in either set
        if (!parameters.weights[layerIndex] || !baseParameters.weights[layerIndex]) {
          diffParams.weights[layerIndex] = parameters.weights[layerIndex];
          continue;
        }

        diffParams.weights[layerIndex] = [];
        const layerDiffStats = {
          weightDiffs: 0,
          totalWeights: 0,
          biasDiffs: 0,
          totalBiases: 0,
        };

        // Process weights: only include values that differ significantly
        for (let i = 0; i < parameters.weights[layerIndex].length; i++) {
          diffParams.weights[layerIndex][i] = {};  // Use sparse representation

          for (let j = 0; j < parameters.weights[layerIndex][i].length; j++) {
            const currentValue = parameters.weights[layerIndex][i][j];
            const baseValue = baseParameters.weights[layerIndex][i]?.[j];

            // If we have a base value and current differs significantly
            if (baseValue !== undefined && Math.abs(currentValue - baseValue) > diffThreshold) {
              diffParams.weights[layerIndex][i][j] = currentValue;
              layerDiffStats.weightDiffs++;
            }
            layerDiffStats.totalWeights++;
          }
        }

        // Process biases: only include values that differ significantly
        diffParams.biases[layerIndex] = {};  // Use sparse representation

        for (let i = 0; i < parameters.biases[layerIndex].length; i++) {
          const currentValue = parameters.biases[layerIndex][i];
          const baseValue = baseParameters.biases[layerIndex]?.[i];

          // If we have a base value and current differs significantly
          if (baseValue !== undefined && Math.abs(currentValue - baseValue) > diffThreshold) {
            diffParams.biases[layerIndex][i] = currentValue;
            layerDiffStats.biasDiffs++;
          }
          layerDiffStats.totalBiases++;
        }

        // Record layer stats
        diffParams.metadata.differentialInfo.diffStats[`layer_${layerIndex}`] = layerDiffStats;
        totalDiffCount += layerDiffStats.weightDiffs + layerDiffStats.biasDiffs;
      }

      // Add summary statistics
      diffParams.metadata.differentialInfo.totalDiffCount = totalDiffCount;
      diffParams.metadata.differentialInfo.compressionRatio =
        totalDiffCount / (parameters.weights.reduce((sum, layer) =>
          sum + layer.reduce((layerSum, row) => layerSum + row.length, 0), 0) +
          parameters.biases.reduce((sum, layer) => sum + layer.length, 0));

      // If differential extraction yields good compression, use it
      if (diffParams.metadata.differentialInfo.compressionRatio < 0.5) {
        return diffParams;
      }
    }

    // Validate parameters before returning
    if (!this._validateParameterStructure(parameters)) {
      throw new Prime.ValidationError(
        'Parameter extraction produced invalid structure'
      );
    }

    return parameters;
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
      // Check if these are partial (differential) parameters
      const isPartial = parameters.metadata?.isPartial === true;

      // Apply weights and biases to each layer
      for (
        let i = 0;
        i < this.layers.length && i < parameters.weights.length;
        i++
      ) {
        if (parameters.weights[i]) {
          if (isPartial && typeof parameters.weights[i] === 'object' && !Array.isArray(parameters.weights[i])) {
            // Handle sparse differential updates
            for (const row in parameters.weights[i]) {
              if (typeof parameters.weights[i][row] === 'object' && !Array.isArray(parameters.weights[i][row])) {
                // Apply specific value changes only where defined
                for (const col in parameters.weights[i][row]) {
                  this.layers[i].weights[row][col] = parameters.weights[i][row][col];
                }
              } else if (parameters.weights[i][row] !== undefined) {
                // Handle case where entire row is updated
                this.layers[i].weights[row] = parameters.weights[i][row];
              }
            }
          } else {
            // Handle full matrix replacement (regular update)
            this.layers[i].weights = parameters.weights[i];
          }
        }

        if (parameters.biases[i]) {
          if (isPartial && typeof parameters.biases[i] === 'object' && !Array.isArray(parameters.biases[i])) {
            // Handle sparse differential updates for biases
            for (const index in parameters.biases[i]) {
              this.layers[i].biases[index] = parameters.biases[i][index];
            }
          } else {
            // Handle full vector replacement (regular update)
            this.layers[i].biases = parameters.biases[i];
          }
        }
      }

      // Record update time and source
      this.distributedState.lastParameterUpdate = Date.now();
      this.distributedState.lastParameterSource = parameters.metadata?.serverId || 'unknown';
      this.distributedState.lastUpdateType = isPartial ? 'differential' : 'full';

      // Log update metrics for monitoring
      if (Prime.Logger && Prime.Logger.debug && isPartial) {
        Prime.Logger.debug(
          `Applied differential parameters: ${JSON.stringify({
            baseVersion: parameters.metadata?.differentialInfo?.baseVersion,
            diffCount: parameters.metadata?.differentialInfo?.totalDiffCount,
            compressionRatio: parameters.metadata?.differentialInfo?.compressionRatio,
          })}`
        );
      }

      return true;
    } catch (error) {
      Prime.Logger.error(`Failed to apply parameters: ${error.message}`);
      return false;
    }
  }

  /**
   * Validates the structure of extracted parameters
   * @param {Object} parameters - Parameters to validate
   * @returns {Boolean} - True if structure is valid
   * @private
   */
  _validateParameterStructure(parameters) {
    // Basic structure checks
    if (
      !parameters ||
      !Array.isArray(parameters.weights) ||
      !Array.isArray(parameters.biases) ||
      !Array.isArray(parameters.layerConfig)
    ) {
      return false;
    }

    // Check that arrays have expected length
    if (
      parameters.weights.length !== parameters.biases.length ||
      parameters.weights.length !== parameters.layerConfig.length
    ) {
      return false;
    }

    // Check for required properties in metadata
    if (!parameters.metadata || !parameters.metadata.extractionTime) {
      return false;
    }

    return true;
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
      const metrics =
        Prime.Neural.Distributed.CoherenceValidator.checkParameterCoherence(
          parameters
        );

      if (Prime.Logger && Prime.Logger.debug) {
        Prime.Logger.debug(
          `Parameter coherence metrics: ${JSON.stringify(metrics)}`
        );
      }

      return metrics.isCoherent;
    }

    // Fall back to dimension validator
    if (Prime.Neural.Distributed.DimensionValidator) {
      return Prime.Neural.Distributed.DimensionValidator.validateParameterCoherence(
        parameters
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
   * Synchronizes parameters across nodes
   * @returns {Promise<Boolean>} - True if successful
   */
  async synchronizeParameters() {
    if (
      !this.distributedConfig.enabled ||
      !this.distributedState.isInitialized
    ) {
      return true;
    }

    // Check if synchronization is needed based on frequency
    if (
      this.metrics.iteration - this.distributedState.lastSyncIteration <
      this.distributedConfig.syncFrequency
    ) {
      return true;
    }

    try {
      // Reset retry counter for new synchronization attempt
      this.distributedState.syncRetryCount = 0;

      // Determine if we should use differential parameter synchronization
      // Use differential sync for parameter_server mode to reduce network traffic
      const useDifferentialSync =
        this.distributedConfig.synchronizationStrategy === 'parameter_server' &&
        this.distributedState.lastParameterSource !== undefined;

      // Get local parameters, potentially using differential encoding for efficiency
      let localParams;
      if (useDifferentialSync && this.distributedState.lastSuccessfulParams) {
        // Extract only the changes from the last known server state
        localParams = this._extractModelParameters({
          differential: true,
          baseParameters: this.distributedState.lastSuccessfulParams,
          diffThreshold: 0.0001  // Only report significant changes
        });
      } else {
        // Regular full parameter extraction
        localParams = this._extractModelParameters();
      }

      // Add node role and performance metrics
      localParams.metadata = {
        ...localParams.metadata,
        nodeId: this.distributedState.nodeId,
        role: this.distributedState.nodeRole || 'worker',
        isServer: this.distributedState.nodeRole === 'server',
        performance: {
          accuracy: this.metrics.accuracy || 0.5,
          loss: this.metrics.loss || 1.0,
          iterations: this.metrics.iteration || 0,
          computeCapacity: this.distributedState.computeCapacity || 1.0,
          networkLatency: this.distributedState.networkLatency || 100,
          timestamp: Date.now(),
          weight: 1.0,  // Default weight, may be adjusted by server
        },
        version: this.distributedState.parameterVersion || Date.now(),
      };

      // Get remote parameters with timeout
      const syncPromise =
        this.distributedConfig.clusterManager.getNodeParameters({
          requestDifferential: useDifferentialSync,
          baseVersion: this.distributedState.lastSuccessfulParams?.metadata?.version,
        });

      const timeoutPromise = new Promise((_, reject) => {
        setTimeout(
          () => reject(new Error('Synchronization timeout')),
          this.distributedConfig.syncTimeout,
        );
      });

      const remoteResults = await Promise.race([syncPromise, timeoutPromise]);

      // Apply synchronization strategy to combine parameters
      const combinedParams = this._combineParameters(
        localParams,
        remoteResults,
      );

      // Apply combined parameters
      const success = this._applyParameters(combinedParams);

      // Update state
      this.distributedState.synchronizedIterations++;
      this.distributedState.lastSyncIteration = this.metrics.iteration;

      // For parameter server mode, store server parameters for future differential sync
      if (success && this.distributedConfig.synchronizationStrategy === 'parameter_server') {
        // Store the parameters for future differential synchronization
        this.distributedState.lastSuccessfulParams = combinedParams;

        // Update parameter version to track changes
        this.distributedState.parameterVersion = Date.now();

        // Track server selection if available
        if (combinedParams.metadata?.serverSelection) {
          this.distributedState.serverSelectionHistory.unshift({
            timestamp: Date.now(),
            selectedIsLocal: combinedParams.metadata.serverSelection.selectedIsLocal,
            method: combinedParams.metadata.serverSelection.method,
            serverId: combinedParams.metadata.protocol?.serverId || 'unknown'
          });

          // Keep last 5 entries only
          if (this.distributedState.serverSelectionHistory.length > 5) {
            this.distributedState.serverSelectionHistory.pop();
          }
        }
      }

      // Record successful sync in history (keeping last 10 entries)
      this.distributedState.syncHistory.unshift({
        timestamp: Date.now(),
        iteration: this.metrics.iteration,
        nodeCount: remoteResults.length + 1,
        strategy: this.distributedConfig.synchronizationStrategy,
        success: true,
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
        iteration: this.metrics.iteration,
      });

      // Keep only last 10 errors
      if (this.distributedState.syncErrors.length > 10) {
        this.distributedState.syncErrors.pop();
      }

      Prime.Logger.error(
        `Parameter synchronization failed: ${error.message}`
      );

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
        // Enhanced parameter server mode with proper role detection and failover
        return this._parameterServerSynchronization(localParams, remoteParams);

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
        timestamp: Date.now(),
      },
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
   * Parameter server synchronization with enhanced server selection and communication
   * @param {Object} localParams - Local parameters
   * @param {Array} remoteParams - Remote parameters from other nodes
   * @returns {Object} - Synchronized parameters
   * @private
   */
  _parameterServerSynchronization(localParams, remoteParams) {
    const result = {
      weights: [],
      biases: [],
      layerConfig: localParams.layerConfig,
      metadata: {
        combinationStrategy: 'parameter_server',
        nodeCount: remoteParams.length + 1,
        timestamp: Date.now(),
        serverSelection: {},
        parameterDiffStats: {},
      },
    };

    // 1. Determine which node should be the parameter server based on performance metrics
    const candidateServers = [];

    // First check for explicitly marked server nodes
    const explicitServer = remoteParams.find((p) => p.isServer);
    if (explicitServer) {
      candidateServers.push({
        params: explicitServer,
        score: Number.MAX_SAFE_INTEGER, // Highest priority for explicitly marked servers
        isExplicit: true,
        isLocal: false,
      });
    }

    // Then check performance metrics of all nodes (including local)
    const allNodeMetrics = [
      {
        params: localParams,
        isLocal: true,
        metrics: localParams.metadata?.performance || {
          accuracy: 0.5,
          loss: 1.0,
          iterations: 0,
          computeCapacity: 1.0,
          networkLatency: 100,
        },
      },
      ...remoteParams.map(params => ({
        params,
        isLocal: false,
        metrics: params.metadata?.performance || {
          accuracy: 0.5,
          loss: 1.0,
          iterations: 0,
          computeCapacity: 1.0,
          networkLatency: 100,
        },
      })),
    ];

    // Calculate server score for each node based on multiple factors
    for (const node of allNodeMetrics) {
      // Skip nodes with explicit server status as they're already included
      if (node.params === explicitServer) continue;

      const metrics = node.metrics;

      // Calculate the server score - higher is better
      let score = 0;

      // Accuracy component (higher is better)
      if (metrics.accuracy !== undefined) {
        score += metrics.accuracy * 5.0;
      }

      // Loss component (lower is better)
      if (metrics.loss !== undefined) {
        score += (1.0 / (metrics.loss + 0.1)) * 2.0;
      }

      // Training progress component (higher is better)
      if (metrics.iterations !== undefined) {
        score += Math.log(metrics.iterations + 1) * 0.5;
      }

      // Compute capacity component (higher is better)
      if (metrics.computeCapacity !== undefined) {
        score += metrics.computeCapacity * 3.0;
      }

      // Network latency component (lower is better)
      if (metrics.networkLatency !== undefined) {
        score += (1000.0 / (metrics.networkLatency + 10)) * 2.0;
      }

      // Give slight preference to current local node for stability
      if (node.isLocal) {
        score *= 1.05; // 5% boost for local node
      }

      candidateServers.push({
        params: node.params,
        score,
        isExplicit: false,
        isLocal: node.isLocal,
      });
    }

    // Sort candidates by score (highest first)
    candidateServers.sort((a, b) => b.score - a.score);

    // Select the highest scoring server
    const selectedServer = candidateServers.length > 0 ? candidateServers[0] : null;

    // Store server selection metadata for monitoring and debugging
    result.metadata.serverSelection = {
      method: explicitServer ? 'explicit' : 'performance_based',
      candidateCount: candidateServers.length,
      selectedIsLocal: selectedServer?.isLocal || false,
      selectionScore: selectedServer?.score || 0,
    };

    // If no server found (should never happen as we at least have local params)
    if (!selectedServer) {
      Prime.Logger.warn('No suitable parameter server found, using local parameters');
      return localParams;
    }

    // 2. Use selected server's parameters, implementing parameter differencing
    // to identify only the differences that need to be applied
    const serverParams = selectedServer.params;

    // Copy weights and biases structure from server parameters
    for (let layerIndex = 0; layerIndex < serverParams.weights.length; layerIndex++) {
      // Skip if server layer doesn't exist
      if (!serverParams.weights[layerIndex]) {
        result.weights[layerIndex] = localParams.weights[layerIndex];
        result.biases[layerIndex] = localParams.biases[layerIndex];
        continue;
      }

      // Process weights for this layer
      const serverWeights = serverParams.weights[layerIndex];
      result.weights[layerIndex] = [];

      // For weights, calculate differences compared to local for stats
      let diffCount = 0;
      let totalDiff = 0;
      let maxDiff = 0;

      for (let i = 0; i < serverWeights.length; i++) {
        result.weights[layerIndex][i] = [];

        for (let j = 0; j < serverWeights[i].length; j++) {
          const serverValue = serverWeights[i][j];
          result.weights[layerIndex][i][j] = serverValue;

          // Calculate difference metrics if local values exist
          if (localParams.weights[layerIndex]?.[i]?.[j] !== undefined) {
            const localValue = localParams.weights[layerIndex][i][j];
            const diff = Math.abs(serverValue - localValue);

            if (diff > 0.00001) { // Only count non-trivial differences
              diffCount++;
              totalDiff += diff;
              maxDiff = Math.max(maxDiff, diff);
            }
          }
        }
      }

      // Process biases for this layer
      const serverBiases = serverParams.biases[layerIndex];
      result.biases[layerIndex] = [];

      for (let i = 0; i < serverBiases.length; i++) {
        result.biases[layerIndex][i] = serverBiases[i];
      }

      // Track difference statistics for this layer
      result.metadata.parameterDiffStats[`layer_${layerIndex}`] = {
        diffCount,
        diffPercentage: diffCount / (serverWeights.length * serverWeights[0].length) * 100,
        avgDiff: diffCount > 0 ? totalDiff / diffCount : 0,
        maxDiff,
      };
    }

    // 3. Add protocol information for advanced server-client synchronization
    result.metadata.protocol = {
      version: '1.0',
      timestamp: Date.now(),
      serverId: selectedServer.params.metadata?.nodeId || 'unknown',
      serverVersion: selectedServer.params.metadata?.version || 0,
      coherenceVerified: this._verifyParameterCoherence(serverParams),
      partialUpdate: false, // Currently only full updates are supported
    };

    // 4. Add optimistic locking for future updates
    result.metadata.optimisticLock = {
      version: Date.now(),
      serverId: selectedServer.params.metadata?.nodeId || 'unknown',
    };

    // Log info about parameter server sync
    if (Prime.Logger && Prime.Logger.debug) {
      Prime.Logger.debug(
        `Parameter server sync: ${JSON.stringify({
          serverType: selectedServer.isExplicit ? 'explicit' : 'selected',
          isLocal: selectedServer.isLocal,
          parameterDiffs: Object.keys(result.metadata.parameterDiffStats).length,
        })}`
      );
    }

    return result;
  }

  /**
   * Implements weighted average parameter synchronization with adaptive weighting
   * @param {Object} localParams - Local parameters
   * @param {Array} remoteParams - Remote parameters
   * @returns {Object} - Combined parameters with weights based on performance metrics
   * @private
   */
  _weightedAverageParameters(localParams, remoteParams) {
    // Enhanced weight calculation with performance metrics

    // Initialize base weights (all nodes start with equal weight)

    // Get performance metrics for all nodes
    const allPerformanceMetrics = [
      { isLocal: true, metrics: localParams.metadata?.performance || { weight: 1.0, accuracy: 1.0, loss: 0.0 } },
      ...remoteParams.map(params => ({
        isLocal: false,
        metrics: params.metadata?.performance || { weight: 1.0, accuracy: 1.0, loss: 0.0 }
      }))
    ];

    // Calculate age-based decay for each node's metrics
    const currentTime = Date.now();
    const allNodeWeights = allPerformanceMetrics.map(node => {
      // Start with base weight from performance metrics
      let weight = node.metrics.weight || 1.0;

      // Apply decay factor based on age if timestamp is available
      if (node.metrics.timestamp) {
        const ageMs = currentTime - node.metrics.timestamp;
        const ageMinutes = ageMs / (60 * 1000);
        // Exponential decay: weight diminishes with age (half-life of ~10 minutes)
        const decayFactor = Math.exp(-ageMinutes / 10);
        weight *= decayFactor;
      }

      // Adjust weight based on performance metrics if available
      if (node.metrics.accuracy !== undefined) {
        // Accuracy-based adjustment: higher accuracy = higher weight
        weight *= (0.5 + 0.5 * node.metrics.accuracy);
      }

      if (node.metrics.loss !== undefined) {
        // Loss-based adjustment: lower loss = higher weight
        // Using a sigmoid to normalize loss impact
        const normalizedLoss = 1.0 / (1.0 + Math.exp(node.metrics.loss - 1.0));
        weight *= (0.5 + 0.5 * normalizedLoss);
      }

      // Stability-based adjustment if variance data is available
      if (node.metrics.parameterVariance !== undefined) {
        // Lower variance = higher weight (more stable parameters)
        const varianceFactor = 1.0 / (1.0 + node.metrics.parameterVariance * 10.0);
        weight *= (0.8 + 0.2 * varianceFactor);
      }

      // Record original node index for potential outlier filtering
      return {
        weight,
        isLocal: node.isLocal,
        metrics: node.metrics
      };
    });

    // Detect outliers to exclude problematic nodes
    const weights = allNodeWeights.map(n => n.weight);
    const meanWeight = weights.reduce((sum, w) => sum + w, 0) / weights.length;
    const squaredDiffs = weights.map(w => (w - meanWeight) ** 2);
    const variance = squaredDiffs.reduce((sum, d) => sum + d, 0) / weights.length;
    const stdDev = Math.sqrt(variance);

    // Identify outliers (nodes with weight more than 2 standard deviations from mean)
    // but always keep local node
    const outlierThreshold = 2.0 * stdDev;
    const inlierNodes = allNodeWeights.filter(node =>
      node.isLocal || Math.abs(node.weight - meanWeight) <= outlierThreshold
    );

    // Count outliers for logging
    const outlierCount = allNodeWeights.length - inlierNodes.length;

    // Get final weights array (excluding outliers)
    const finalWeights = inlierNodes.map(node => node.weight);

    // Calculate total weight for normalization
    const totalWeight = finalWeights.reduce((sum, w) => sum + w, 0);

    // Normalize weights to sum to 1.0
    const normalizedWeights = finalWeights.map(w => w / totalWeight);

    // Map indices to easily identify local vs remote nodes after filtering
    const nodeTypes = inlierNodes.map(node => node.isLocal ? 'local' : 'remote');

    // Initialize result structure with enhanced metadata
    const result = {
      weights: [],
      biases: [],
      layerConfig: localParams.layerConfig,
      metadata: {
        combinationStrategy: 'weighted_average',
        nodeCount: inlierNodes.length,
        outlierNodesExcluded: outlierCount,
        nodesIncluded: inlierNodes.length,
        weights: normalizedWeights,
        nodeTypes: nodeTypes,
        timestamp: Date.now(),
        performanceMetricsUsed: true,
        decayFactorsApplied: true,
        outlierDetectionApplied: outlierCount > 0
      },
    };

    // Extract parameters from filtered nodes
    const includedParams = inlierNodes.map((node, index) => {
      if (node.isLocal) {
        return localParams;
      } else {
        // Find the original index in remoteParams
        const remoteIndex = allNodeWeights.findIndex(n =>
          !n.isLocal && n.metrics === node.metrics
        ) - 1; // Subtract 1 because local node is at index 0 in allNodeWeights

        return remoteParams[remoteIndex];
      }
    });

    // Process each layer with the filtered nodes and normalized weights
    for (
      let layerIndex = 0;
      layerIndex < localParams.weights.length;
      layerIndex++
    ) {
      // Skip if local layer doesn't exist
      if (!localParams.weights[layerIndex]) continue;

      result.weights[layerIndex] = [];
      result.biases[layerIndex] = [];

      // Get reference dimensions from local layer
      const localWeights = localParams.weights[layerIndex];
      const localBiases = localParams.biases[layerIndex];

      // Process weights with variance-based weighting for stability
      for (let i = 0; i < localWeights.length; i++) {
        result.weights[layerIndex][i] = [];

        for (let j = 0; j < localWeights[i].length; j++) {
          // Calculate parameter-specific variance across nodes
          const paramValues = [];
          const paramWeights = [];

          // Collect values and weights for this parameter from all included nodes
          for (let nodeIdx = 0; nodeIdx < includedParams.length; nodeIdx++) {
            const params = includedParams[nodeIdx];
            if (
              params.weights &&
              params.weights[layerIndex] &&
              params.weights[layerIndex][i] &&
              params.weights[layerIndex][i][j] !== undefined
            ) {
              paramValues.push(params.weights[layerIndex][i][j]);
              paramWeights.push(normalizedWeights[nodeIdx]);
            }
          }

          // Compute weighted average for this parameter
          if (paramValues.length > 0) {
            let weightedSum = 0;
            let totalWeight = 0;

            for (let v = 0; v < paramValues.length; v++) {
              weightedSum += paramValues[v] * paramWeights[v];
              totalWeight += paramWeights[v];
            }

            // Normalize by total weight
            result.weights[layerIndex][i][j] = weightedSum / totalWeight;
          } else {
            // Fallback to local value if no valid parameters available
            result.weights[layerIndex][i][j] = localWeights[i][j];
          }
        }
      }

      // Process biases
      result.biases[layerIndex] = [];

      for (let i = 0; i < localBiases.length; i++) {
        // Calculate parameter-specific variance across nodes
        const paramValues = [];
        const paramWeights = [];

        // Collect values and weights for this parameter from all included nodes
        for (let nodeIdx = 0; nodeIdx < includedParams.length; nodeIdx++) {
          const params = includedParams[nodeIdx];
          if (
            params.biases &&
            params.biases[layerIndex] &&
            params.biases[layerIndex][i] !== undefined
          ) {
            paramValues.push(params.biases[layerIndex][i]);
            paramWeights.push(normalizedWeights[nodeIdx]);
          }
        }

        // Compute weighted average for this parameter
        if (paramValues.length > 0) {
          let weightedSum = 0;
          let totalWeight = 0;

          for (let v = 0; v < paramValues.length; v++) {
            weightedSum += paramValues[v] * paramWeights[v];
            totalWeight += paramWeights[v];
          }

          // Normalize by total weight
          result.biases[layerIndex][i] = weightedSum / totalWeight;
        } else {
          // Fallback to local value if no valid parameters available
          result.biases[layerIndex][i] = localBiases[i];
        }
      }
    }

    return result;
  }

  /**
   * Implements majority vote parameter synchronization
   * @param {Object} localParams - Local parameters
   * @param {Array} remoteParams - Remote parameters
   * @returns {Object} - Combined parameters based on majority vote
   * @private
   */
  _majorityVoteParameters(localParams, remoteParams) {
    // Add local params to the voting pool
    const allParams = [localParams, ...remoteParams];

    // Track voting statistics for metadata
    const votingStats = {
      totalParameters: 0,
      clusteredParameters: 0,
      medianFallbacks: 0,
      discreteVotes: 0,
      continuousVotes: 0,
      layerStats: {}
    };

    const result = {
      weights: [],
      biases: [],
      layerConfig: localParams.layerConfig,
      metadata: {
        combinationStrategy: 'majority_vote',
        nodeCount: allParams.length,
        timestamp: Date.now(),
        clusteringApplied: true,
        perLayerVotingEnabled: true
      },
    };

    // Process each layer independently with per-layer voting
    for (
      let layerIndex = 0;
      layerIndex < localParams.weights.length;
      layerIndex++
    ) {
      // Skip if local layer doesn't exist
      if (!localParams.weights[layerIndex]) continue;

      // Initialize layer statistics
      votingStats.layerStats[layerIndex] = {
        totalParameters: 0,
        clusteredParameters: 0,
        discreteVotes: 0,
        continuousVotes: 0
      };

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

          // Increment parameter counter
          votingStats.totalParameters++;
          votingStats.layerStats[layerIndex].totalParameters++;

          // Apply enhanced voting strategy based on the parameter values
          if (values.length === 0) {
            // No values available, use 0 as default
            result.weights[layerIndex][i][j] = 0;
          } else if (values.length === 1) {
            // Only one value available, use it directly
            result.weights[layerIndex][i][j] = values[0];
          } else {
            // First check if values appear to be discrete or continuous
            // Count unique values with a small epsilon for floating point comparison
            const epsilon = 1e-10;
            const uniqueValues = new Map();

            for (const value of values) {
              let isUnique = true;
              for (const [existingValue, count] of uniqueValues.entries()) {
                if (Math.abs(existingValue - value) < epsilon) {
                  uniqueValues.set(existingValue, count + 1);
                  isUnique = false;
                  break;
                }
              }
              if (isUnique) {
                uniqueValues.set(value, 1);
              }
            }

            // If there are few unique values relative to total values, treat as discrete
            const uniqueRatio = uniqueValues.size / values.length;

            if (uniqueRatio < 0.5 && uniqueValues.size <= 5) {
              // Discrete-like voting: find the most common value
              let maxCount = 0;
              let mostCommonValue = null;

              for (const [value, count] of uniqueValues.entries()) {
                if (count > maxCount) {
                  maxCount = count;
                  mostCommonValue = value;
                }
              }

              result.weights[layerIndex][i][j] = mostCommonValue;
              votingStats.discreteVotes++;
              votingStats.layerStats[layerIndex].discreteVotes++;
            } else {
              // Continuous values - use clustering approach
              try {
                // Apply k-means clustering to identify natural groupings
                // Determine number of clusters based on data variance
                const mean = values.reduce((sum, v) => sum + v, 0) / values.length;
                const variance = values.reduce((sum, v) => sum + (v - mean) ** 2, 0) / values.length;
                const stdDev = Math.sqrt(variance);

                // Use data variance to determine optimal cluster count
                // More variance suggests more clusters needed
                const minClusters = 2;
                const maxClusters = Math.min(5, Math.floor(values.length / 2));
                let numClusters = minClusters;

                if (stdDev > 0.5) {
                  numClusters = Math.min(maxClusters,
                    Math.max(minClusters, Math.ceil(stdDev * 2)));
                }

                // Simple k-means clustering
                // Initialize centroids with equally spaced values from min to max
                const minVal = Math.min(...values);
                const maxVal = Math.max(...values);
                const step = (maxVal - minVal) / (numClusters <= 1 ? 1 : numClusters - 1);

                const centroids = Array(numClusters).fill(0).map((_, i) => minVal + i * step);
                let clusters = Array(numClusters).fill(0).map(() => []);
                let iterations = 0;
                const maxIterations = 10;

                while (iterations < maxIterations) {
                  // Reset clusters
                  clusters = Array(numClusters).fill(0).map(() => []);

                  // Assign points to clusters
                  for (let vi = 0; vi < values.length; vi++) {
                    const value = values[vi];
                    let nearestCentroidIdx = 0;
                    let minDistance = Math.abs(value - centroids[0]);

                    for (let ci = 1; ci < centroids.length; ci++) {
                      const distance = Math.abs(value - centroids[ci]);
                      if (distance < minDistance) {
                        minDistance = distance;
                        nearestCentroidIdx = ci;
                      }
                    }

                    clusters[nearestCentroidIdx].push(value);
                  }

                  // Recalculate centroids
                  let changed = false;
                  for (let ci = 0; ci < numClusters; ci++) {
                    if (clusters[ci].length > 0) {
                      const newCentroid = clusters[ci].reduce((sum, v) => sum + v, 0) / clusters[ci].length;
                      if (Math.abs(newCentroid - centroids[ci]) > epsilon) {
                        changed = true;
                        centroids[ci] = newCentroid;
                      }
                    }
                  }

                  // If centroids didn't change, we've converged
                  if (!changed) break;

                  iterations++;
                }

                // Find the cluster with most values (the majority)
                let maxClusterSize = 0;
                let majorityClusterIdx = 0;

                for (let ci = 0; ci < clusters.length; ci++) {
                  if (clusters[ci].length > maxClusterSize) {
                    maxClusterSize = clusters[ci].length;
                    majorityClusterIdx = ci;
                  }
                }

                // Use the centroid of the majority cluster
                if (maxClusterSize > 0) {
                  result.weights[layerIndex][i][j] = centroids[majorityClusterIdx];
                  votingStats.clusteredParameters++;
                  votingStats.layerStats[layerIndex].clusteredParameters++;
                } else {
                  // Fallback to median if clustering failed
                  const sortedValues = [...values].sort((a, b) => a - b);
                  const medianIndex = Math.floor(sortedValues.length / 2);
                  result.weights[layerIndex][i][j] = sortedValues[medianIndex];
                  votingStats.medianFallbacks++;
                }

                votingStats.continuousVotes++;
                votingStats.layerStats[layerIndex].continuousVotes++;
              } catch (error) {
                // Fallback to median if error in clustering
                const sortedValues = [...values].sort((a, b) => a - b);
                const medianIndex = Math.floor(sortedValues.length / 2);
                result.weights[layerIndex][i][j] = sortedValues[medianIndex];
                votingStats.medianFallbacks++;
              }
            }
          }
        }
      }

      // Process biases with same approach
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

        // Similar logic as for weights
        if (values.length === 0) {
          result.biases[layerIndex][i] = 0;
        } else if (values.length === 1) {
          result.biases[layerIndex][i] = values[0];
        } else {
          // Use simple majority for biases (typically fewer values)
          const sortedValues = [...values].sort((a, b) => a - b);
          const medianIndex = Math.floor(sortedValues.length / 2);
          result.biases[layerIndex][i] = sortedValues[medianIndex];
        }
      }
    }

    // Add voting statistics to result metadata
    result.metadata.votingStats = {
      totalParameters: votingStats.totalParameters,
      discreteVoteCount: votingStats.discreteVotes,
      continuousVoteCount: votingStats.continuousVotes,
      clusteringSuccessRate: votingStats.totalParameters > 0 ?
        votingStats.clusteredParameters / votingStats.continuousVotes : 0,
      medianFallbacks: votingStats.medianFallbacks
    };

    return result;
  }

  /**
   * Handles synchronization failures with progressive retry and recovery
   * @param {Error} error - The error that caused synchronization failure
   * @returns {Boolean} - True if recovery succeeded
   * @private
   */
  _handleSynchronizationFailure(error) {
    const strategy = this.distributedConfig.syncRecoveryStrategy;
    const errorMessage = error.message || 'Unknown error';
    const retryCount = this.distributedState.syncRetryCount;
    const maxRetries = this.distributedConfig.maxSyncRetries;

    // Log with appropriate severity based on retry count
    const logSeverity = retryCount >= maxRetries ? 'error' :
      (retryCount > maxRetries / 2 ? 'warn' : 'info');

    Prime.Logger[logSeverity](
      `Sync failure (${retryCount}/${maxRetries}): ${errorMessage}`
    );

    // Initialize retry stats if they don't exist
    if (!this.distributedState.retryStats) {
      this.distributedState.retryStats = {
        totalRetries: 0,
        successfulRetries: 0,
        failedRetries: 0,
        lastRetryTime: 0,
        consecutiveFailures: 0,
        averageRetryDelay: 0,
      };
    }

    // Update retry statistics
    this.distributedState.retryStats.totalRetries++;
    this.distributedState.retryStats.failedRetries++;
    this.distributedState.retryStats.consecutiveFailures++;
    this.distributedState.retryStats.lastRetryTime = Date.now();

    // Apply recovery strategy based on configuration
    switch (strategy) {
      case 'local_fallback':
        // Continue with local parameters
        Prime.Logger.warn('Using local fallback after synchronization failure');
        return true;

      case 'conservative_merge':
        // Try to merge with any available parameters
        return this._attemptConservativeMerge();

      case 'checkpoint_rollback':
        // Roll back to last known good state
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
   * Enhanced with confidence metrics, divergence detection, and validation
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
        Prime.Logger.warn(
          'No cached parameters available for conservative merge'
        );
        return true; // Continue with local parameters
      }

      // Check if cached parameters are too old
      const timeSinceLastSync = Date.now() - (this.distributedState.lastSuccessfulSyncTime || 0);
      const maxCachedAgeMs = 5 * 60 * 1000; // 5 minutes maximum age

      if (timeSinceLastSync > maxCachedAgeMs) {
        Prime.Logger.warn(
          `Cached parameters are too old (${Math.round(timeSinceLastSync/1000)}s), using local parameters only`
        );
        return true; // Continue with local parameters
      }

      // Get adaptive blending weights based on time since last sync
      // The older the cached params, the less weight they get
      const ageFactor = Math.min(1.0, timeSinceLastSync / maxCachedAgeMs);

      // Use configuration values if available, otherwise use defaults
      const baseLocalWeight = this.distributedConfig.mergeLocalWeight || 0.8;
      const baseCachedWeight = this.distributedConfig.mergeCachedWeight || 0.2;

      // Adjust weights based on age - older cached params get less weight
      const localWeight = baseLocalWeight + (baseCachedWeight * ageFactor * 0.5);
      const cachedWeight = baseCachedWeight * (1 - ageFactor * 0.5);

      // Normalize weights to sum to 1.0
      const totalWeight = localWeight + cachedWeight;
      const normalizedLocalWeight = localWeight / totalWeight;
      const normalizedCachedWeight = cachedWeight / totalWeight;

      // Simple interpolation between local and last known good state
      const mergedParams = {
        weights: [],
        biases: [],
        layerConfig: localParams.layerConfig,
        metadata: {
          mergeStrategy: 'conservative_merge',
          localWeight: normalizedLocalWeight,
          cachedWeight: normalizedCachedWeight,
          timeSinceLastSync,
          mergeTime: Date.now(),
          divergenceDetected: false,
          extremeDivergenceCount: 0,
        },
      };

      // For tracking parameter divergence statistics
      let totalParameters = 0;
      let divergentParameters = 0;
      let extremeDivergenceCount = 0;

      // For confidence metrics
      const confidenceMetrics = {
        totalElements: 0,
        confidenceSum: 0,
        layerConfidence: [],
      };

      // Process each layer
      for (
        let layerIndex = 0;
        layerIndex < localParams.weights.length;
        layerIndex++
      ) {
        // Skip if local or cached layer doesn't exist
        if (
          !localParams.weights[layerIndex] ||
          !cachedParams.weights[layerIndex]
        ) {
          mergedParams.weights[layerIndex] = localParams.weights[layerIndex];
          mergedParams.biases[layerIndex] = localParams.biases[layerIndex];

          // Track confidence for this layer - use 1.0 for local-only values
          confidenceMetrics.layerConfidence[layerIndex] = 1.0;
          continue;
        }

        // Blend weights with divergence detection
        mergedParams.weights[layerIndex] = [];
        let layerTotalParams = 0;
        let layerConfidenceSum = 0;

        for (let i = 0; i < localParams.weights[layerIndex].length; i++) {
          mergedParams.weights[layerIndex][i] = [];

          for (let j = 0; j < localParams.weights[layerIndex][i].length; j++) {
            const localValue = localParams.weights[layerIndex][i][j];

            // Check if we have a corresponding cached value
            let cachedValue = null;
            if (
              cachedParams.weights[layerIndex] &&
              cachedParams.weights[layerIndex][i] &&
              cachedParams.weights[layerIndex][i][j] !== undefined
            ) {
              cachedValue = cachedParams.weights[layerIndex][i][j];
            }

            // Increment parameter counters
            totalParameters++;
            layerTotalParams++;

            if (cachedValue === null) {
              // Use local value if no cached value exists
              mergedParams.weights[layerIndex][i][j] = localValue;
              layerConfidenceSum += 1.0; // Full confidence in local value
            } else {
              // Calculate divergence
              const divergence = Math.abs(localValue - cachedValue);
              const relativeDivergence = localValue !== 0 ?
                divergence / Math.abs(localValue) : divergence;

              // Define divergence thresholds
              const moderateDivergenceThreshold = 0.1; // 10% relative change
              const extremeDivergenceThreshold = 0.5; // 50% relative change

              let paramConfidence = 1.0;

              if (relativeDivergence > extremeDivergenceThreshold) {
                // Extreme divergence - mostly trust local value
                mergedParams.weights[layerIndex][i][j] =
                  localValue * 0.9 + cachedValue * 0.1;
                paramConfidence = 0.5;
                divergentParameters++;
                extremeDivergenceCount++;
              } else if (relativeDivergence > moderateDivergenceThreshold) {
                // Moderate divergence - blend with bias toward local
                mergedParams.weights[layerIndex][i][j] =
                  localValue * normalizedLocalWeight + cachedValue * normalizedCachedWeight;
                paramConfidence = 0.8;
                divergentParameters++;
              } else {
                // Low divergence - use weighted blend
                mergedParams.weights[layerIndex][i][j] =
                  localValue * normalizedLocalWeight + cachedValue * normalizedCachedWeight;
                paramConfidence = 1.0;
              }

              layerConfidenceSum += paramConfidence;
            }
          }
        }

        // Blend biases
        mergedParams.biases[layerIndex] = [];

        for (let i = 0; i < localParams.biases[layerIndex].length; i++) {
          const localValue = localParams.biases[layerIndex][i];

          // Check if we have a corresponding cached value
          let cachedValue = null;
          if (
            cachedParams.biases[layerIndex] &&
            cachedParams.biases[layerIndex][i] !== undefined
          ) {
            cachedValue = cachedParams.biases[layerIndex][i];
          }

          // Increment parameter counters
          totalParameters++;
          layerTotalParams++;

          if (cachedValue === null) {
            // Use local value if no cached value exists
            mergedParams.biases[layerIndex][i] = localValue;
            layerConfidenceSum += 1.0; // Full confidence in local value
          } else {
            // Simple weighted blend for biases (less prone to divergence)
            mergedParams.biases[layerIndex][i] =
              localValue * normalizedLocalWeight + cachedValue * normalizedCachedWeight;
            layerConfidenceSum += 1.0;
          }
        }

        // Calculate confidence for this layer
        const layerConfidence = layerTotalParams > 0 ?
          layerConfidenceSum / layerTotalParams : 1.0;
        confidenceMetrics.layerConfidence[layerIndex] = layerConfidence;
        confidenceMetrics.confidenceSum += layerConfidenceSum;
        confidenceMetrics.totalElements += layerTotalParams;
      }

      // Update divergence detection in metadata
      if (totalParameters > 0) {
        const divergenceRatio = divergentParameters / totalParameters;
        mergedParams.metadata.divergenceDetected = divergenceRatio > 0.05; // Over 5% parameters divergent
        mergedParams.metadata.divergentRatio = divergenceRatio;
        mergedParams.metadata.extremeDivergenceCount = extremeDivergenceCount;

        // Calculate overall confidence
        const overallConfidence = confidenceMetrics.totalElements > 0 ?
          confidenceMetrics.confidenceSum / confidenceMetrics.totalElements : 1.0;
        mergedParams.metadata.mergeConfidence = overallConfidence;
        mergedParams.metadata.layerConfidence = confidenceMetrics.layerConfidence;

        // Log divergence statistics
        if (mergedParams.metadata.divergenceDetected) {
          Prime.Logger.warn(
            `Parameter divergence detected during conservative merge: ${divergentParameters}/${totalParameters} parameters (${(divergenceRatio * 100).toFixed(2)}%)`
          );
        }
      }

      // Verify coherence of merged parameters
      if (!this._verifyParameterCoherence(mergedParams)) {
        // If merged parameters fail coherence check, return just local parameters
        Prime.Logger.error(
          'Merged parameters failed coherence check, falling back to local parameters only'
        );
        return true; // Continue with local parameters
      }

      // Apply the merged parameters
      const success = this._applyParameters(mergedParams);

      // Store merge statistics for monitoring
      if (!this.distributedState.mergeStats) {
        this.distributedState.mergeStats = {
          totalMerges: 0,
          successfulMerges: 0,
          divergentMerges: 0,
          lastMergeTime: 0,
        };
      }

      this.distributedState.mergeStats.totalMerges++;
      if (success) {
        this.distributedState.mergeStats.successfulMerges++;
        if (mergedParams.metadata.divergenceDetected) {
          this.distributedState.mergeStats.divergentMerges++;
        }
      }
      this.distributedState.mergeStats.lastMergeTime = Date.now();

      return success;
    } catch (error) {
      Prime.Logger.error(
        `Failed to perform conservative merge: ${error.message}`
      );
      return true; // Continue with local parameters
    }
  }

  /**
   * Rolls back to a checkpoint with advanced validation and selection
   * Enhanced with checkpoint validation, rotation, and verification
   * @param {number} [index=0] - Index of checkpoint to roll back to (0 = most recent)
   * @returns {Boolean} - True if successful
   * @private
   */
  _rollbackToCheckpoint(index = 0) {
    try {
      // Initialize checkpoints array if it doesn't exist
      if (!this.distributedState.checkpoints) {
        this.distributedState.checkpoints = [];
      }

      // Check if we have checkpoints
      if (this.distributedState.checkpoints.length === 0) {
        // Fall back to legacy checkpoint property if available
        if (this.distributedState.checkpoint) {
          Prime.Logger.info('Using legacy checkpoint for rollback');
          const success = this._applyParameters(this.distributedState.checkpoint);

          if (success) {
            Prime.Logger.info('Rolled back to legacy checkpoint successfully');
          }
          return success;
        }

        Prime.Logger.warn('No checkpoints available for rollback');
        return true; // Continue with current parameters
      }

      // Validate index
      if (index < 0 || index >= this.distributedState.checkpoints.length) {
        Prime.Logger.warn(`Invalid checkpoint index ${index}, using most recent checkpoint`);
        index = 0;
      }

      // Get the specified checkpoint
      const checkpoint = this.distributedState.checkpoints[index];

      // Verify checkpoint coherence before applying
      if (!this._verifyParameterCoherence(checkpoint)) {
        // If requested checkpoint fails coherence check, try to find a valid one
        Prime.Logger.warn(
          `Checkpoint at index ${index} failed coherence check, searching for valid checkpoint`
        );

        // Try to find the most recent valid checkpoint
        let validCheckpointIndex = -1;
        for (let i = 0; i < this.distributedState.checkpoints.length; i++) {
          if (this._verifyParameterCoherence(this.distributedState.checkpoints[i])) {
            validCheckpointIndex = i;
            break;
          }
        }

        // If we found a valid checkpoint, use it
        if (validCheckpointIndex >= 0) {
          Prime.Logger.info(`Found valid checkpoint at index ${validCheckpointIndex}`);
          const validCheckpoint = this.distributedState.checkpoints[validCheckpointIndex];
          const success = this._applyParameters(validCheckpoint);

          if (success) {
            const checkpointAge = this.metrics.iteration -
              (validCheckpoint.metadata?.iteration || 0);
            Prime.Logger.info(
              `Rolled back to valid checkpoint from iteration ${validCheckpoint.metadata?.iteration} (${checkpointAge} iterations ago)`
            );
          }

          return success;
        } else {
          // No valid checkpoints, continue with current parameters
          Prime.Logger.warn('No valid checkpoints found, continuing with current parameters');
          return true;
        }
      }

      // Apply selected checkpoint parameters
      const success = this._applyParameters(checkpoint);

      if (success) {
        const checkpointAge = this.metrics.iteration - (checkpoint.metadata?.iteration || 0);

        Prime.Logger.info(
          `Rolled back to checkpoint from iteration ${checkpoint.metadata?.iteration} (${checkpointAge} iterations ago)`
        );

        // Store success metric
        if (!this.distributedState.rollbackStats) {
          this.distributedState.rollbackStats = {
            totalRollbacks: 0,
            successfulRollbacks: 0,
            failedRollbacks: 0,
            averageRollbackAge: 0,
          };
        }

        this.distributedState.rollbackStats.totalRollbacks++;
        this.distributedState.rollbackStats.successfulRollbacks++;

        // Calculate running average of rollback age
        const totalSuccessful = this.distributedState.rollbackStats.successfulRollbacks;
        const currentAvgAge = this.distributedState.rollbackStats.averageRollbackAge || 0;
        this.distributedState.rollbackStats.averageRollbackAge =
          (currentAvgAge * (totalSuccessful - 1) + checkpointAge) / totalSuccessful;

        // Record last rollback info
        this.distributedState.rollbackStats.lastRollbackTime = Date.now();
        this.distributedState.rollbackStats.lastRollbackIteration = checkpoint.metadata?.iteration;
        this.distributedState.rollbackStats.lastRollbackAge = checkpointAge;
      } else {
        // Track failed rollback
        if (this.distributedState.rollbackStats) {
          this.distributedState.rollbackStats.totalRollbacks++;
          this.distributedState.rollbackStats.failedRollbacks++;
        }

        Prime.Logger.error(`Failed to roll back to checkpoint at index ${index}`);
      }

      return success;
    } catch (error) {
      Prime.Logger.error(`Error during checkpoint rollback: ${error.message}`);
      return false;
    }
  }

  /**
   * Creates a checkpoint of the current model state
   * @param {Object} [options={}] - Checkpoint options
   * @returns {Boolean} - True if checkpoint was successfully created
   */
  createCheckpoint(options = {}) {
    try {
      // Extract current parameters
      const params = this._extractModelParameters();

      // Add checkpoint-specific metadata
      params.metadata.checkpointTime = Date.now();
      params.metadata.iteration = this.metrics.iteration;
      params.metadata.loss = this.metrics.loss;
      params.metadata.accuracy = this.metrics.accuracy;
      params.metadata.isCheckpoint = true;
      params.metadata.checkpointLabel = options.label || `checkpoint-${this.metrics.iteration}`;

      // Initialize checkpoints array if it doesn't exist
      if (!this.distributedState.checkpoints) {
        this.distributedState.checkpoints = [];
      }

      // Add the checkpoint to the beginning of the array (most recent first)
      this.distributedState.checkpoints.unshift(params);

      // Keep only the most recent N checkpoints to save memory
      const maxCheckpoints = this.distributedConfig.maxCheckpoints || 5;
      if (this.distributedState.checkpoints.length > maxCheckpoints) {
        this.distributedState.checkpoints = this.distributedState.checkpoints.slice(0, maxCheckpoints);
      }

      // Update checkpoint tracking
      this.distributedState.lastCheckpointTime = params.metadata.checkpointTime;
      this.distributedState.lastCheckpointIteration = this.metrics.iteration;

      // Also store in legacy location for backward compatibility
      this.distributedState.checkpoint = params;

      Prime.Logger.debug(
        `Created checkpoint at iteration ${this.metrics.iteration} (total checkpoints: ${this.distributedState.checkpoints.length})`
      );

      return true;
    } catch (error) {
      Prime.Logger.error(`Failed to create checkpoint: ${error.message}`);
      return false;
    }
  }

  /**
   * Validates the data parallel partition scheme configuration
   * @returns {Object} Validation result with isValid status and issues array
   * @private
   */
  _checkDataParallelPartition() {
    // Basic implementation - would be replaced with the full version
    return {
      isValid: true,
      issues: [],
      partitionInfo: {
        scheme: 'data_parallel',
        batchSizePerNode: 0,
        gradientSynchronization: true,
        localBatchSize: this.config?.batchSize || 32,
        totalNodes: this.distributedState.activeNodes.length + 1,
      }
    };
  }

  /**
   * Validates the model parallel partition scheme configuration
   * @returns {Object} Validation result with isValid status and issues array
   * @private
   */
  _checkModelParallelPartition() {
    // Basic implementation - would be replaced with the full version
    return {
      isValid: true,
      issues: [],
      partitionInfo: {
        scheme: 'model_parallel',
        layersPerNode: 0,
        nodeCount: this.distributedState.activeNodes.length + 1,
        communicationPattern: 'sequential',
      }
    };
  }

  /**
   * Creates a model partition plan for model parallel training
   * Basic implementation that would be replaced with the full version
   * @returns {Object} Model partition plan
   */
  createModelPartitionPlan() {
    // Simplified version - full implementation would create partition plan
    Prime.Logger.warn('Model partitioning not fully implemented yet');
    return {
      partitionScheme: 'model_parallel',
      partitions: [],
      nodeCount: this.distributedState.activeNodes.length + 1,
    };
  }

  /**
   * Gets information about the distributed neural model
   * @returns {Object} Model information
   */
  getInfo() {
    return {
      type: 'DistributedNeuralModel',
      inputSize: this.inputSize,
      originalInputSize: this.originalInputSize,
      layerCount: this.layers.length,
      distributed: {
        enabled: this.distributedConfig.enabled,
        initialized: this.distributedState.isInitialized,
        partitionScheme: this.distributedConfig.partitionScheme,
        syncFrequency: this.distributedConfig.syncFrequency,
        synchronizedIterations: this.distributedState.synchronizedIterations,
        failedSynchronizations: this.distributedState.failedSynchronizations,
        syncStrategy: this.distributedConfig.synchronizationStrategy,
        recoveryStrategy: this.distributedConfig.syncRecoveryStrategy,
        activeNodes: this.distributedState.activeNodes.length,
        nodeId: this.distributedState.nodeId,
      },
    };
  }

  /**
   * Trains the model for one iteration with distributed functionality
   * @param {Array} input - Input data
   * @param {Array} target - Target output
   * @returns {Promise<Object>} - Training results
   */
  async train(input, target) {
    // Increment iteration counter
    this.metrics.iteration++;

    // Normal training through parent implementation
    const results = await super.train(input, target);

    // Synchronize parameters if distributed mode is enabled and it's time to sync
    if (
      this.distributedConfig.enabled &&
      this.metrics.iteration % this.distributedConfig.syncFrequency === 0
    ) {
      await this.synchronizeParameters();
    }

    return results;
  }
}

// Register the DistributedNeuralModel in the Prime namespace
Prime.Neural.Distributed.DistributedNeuralModel = DistributedNeuralModel;

// Export the module
module.exports = Prime.Neural.Distributed;