/**
 * PrimeOS JavaScript Library - Neural Distributed Model Factory
 * Factory for creating distributed neural models with cluster integration
 */

// Import the Prime object from core
const Prime = require("../../core");

// Create the Neural Distributed Model Factory using IIFE
(function () {
  // Ensure the Neural and Distributed namespaces exist
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Distributed = Prime.Neural.Distributed || {};

  /**
   * Neural Distributed Model Factory
   * Factory for creating distributed neural models with cluster integration
   */
  class DistributedModelFactory {
    /**
     * Create a new distributed model factory
     * @param {Object} config - Factory configuration
     * @param {Object} [config.clusterManager=null] - Cluster manager instance
     * @param {string} [config.defaultPartitionScheme="data_parallel"] - Default partition scheme
     * @param {Object} [config.coherenceConfig={}] - Default coherence configuration
     */
    constructor(config = {}) {
      this.config = {
        clusterManager: config.clusterManager || null,
        defaultPartitionScheme:
          config.defaultPartitionScheme || "data_parallel",
        coherenceConfig: config.coherenceConfig || {
          enabled: true,
          minThreshold: 0.7,
          autoCorrect: true,
        },
      };
    }

    /**
     * Create a distributed neural model
     * @param {Object} modelConfig - Neural model configuration
     * @param {Object} [distributedConfig={}] - Distributed configuration
     * @returns {Prime.Neural.Distributed.DistributedNeuralModel} Distributed neural model
     */
    createModel(modelConfig = {}, distributedConfig = {}) {
      // Combine base model config with distributed config
      const config = {
        ...modelConfig,
        distributed: {
          enabled: true,
          clusterManager: this.config.clusterManager,
          partitionScheme:
            distributedConfig.partitionScheme ||
            this.config.defaultPartitionScheme,
          nodeCount: distributedConfig.nodeCount,
          syncFrequency: distributedConfig.syncFrequency || 10,
          coherenceCheckFrequency:
            distributedConfig.coherenceCheckFrequency || 50,
          fallbackToLocal: distributedConfig.fallbackToLocal !== false,
        },
        coherence: {
          ...this.config.coherenceConfig,
          ...(modelConfig.coherence || {}),
        },
      };

      // Create distributed model
      return new Prime.Neural.Distributed.DistributedNeuralModel(config);
    }

    /**
     * Create a distributed neural model from an existing local model
     * @param {Prime.Neural.Model.NeuralModel} localModel - Local neural model
     * @param {Object} [distributedConfig={}] - Distributed configuration
     * @returns {Prime.Neural.Distributed.DistributedNeuralModel} Distributed neural model
     */
    fromLocalModel(localModel, distributedConfig = {}) {
      if (!(localModel instanceof Prime.Neural.Model.NeuralModel)) {
        throw new Prime.ValidationError(
          "Local model must be a valid NeuralModel instance",
        );
      }

      // Extract configuration from local model
      const modelConfig = {
        layers: localModel.layers.map((layer) => {
          const config = {};

          // Extract common properties
          if (layer.inputSize !== undefined) config.inputSize = layer.inputSize;
          if (layer.outputSize !== undefined)
            config.outputSize = layer.outputSize;
          if (layer.activation !== undefined)
            config.activation = layer.activation;

          // Layer-specific properties
          if (layer.inputShape !== undefined)
            config.inputShape = layer.inputShape;
          if (layer.outputShape !== undefined)
            config.outputShape = layer.outputShape;
          if (layer.filters !== undefined) config.filters = layer.filters;
          if (layer.kernelSize !== undefined)
            config.kernelSize = layer.kernelSize;
          if (layer.strides !== undefined) config.strides = layer.strides;
          if (layer.padding !== undefined) config.padding = layer.padding;
          if (layer.hiddenSize !== undefined)
            config.hiddenSize = layer.hiddenSize;
          if (layer.cellType !== undefined) config.cellType = layer.cellType;
          if (layer.sequenceLength !== undefined)
            config.sequenceLength = layer.sequenceLength;
          if (layer.returnSequences !== undefined)
            config.returnSequences = layer.returnSequences;

          // Determine layer type
          let type;
          if (layer instanceof Prime.Neural.Layer.NeuralLayer) {
            type = "dense";
          } else if (layer instanceof Prime.Neural.Layer.SelfOptimizingLayer) {
            type = "selfOptimizing";
          } else if (layer instanceof Prime.Neural.Layer.ConvolutionalLayer) {
            type = "convolutional";
          } else if (layer instanceof Prime.Neural.Layer.RecurrentLayer) {
            type = layer.cellType || "recurrent";
          } else {
            type = "custom";
          }

          config.type = type;

          return config;
        }),
        optimizer: {
          type: localModel.optimizer.constructor.name
            .replace("Coherence", "")
            .toLowerCase(),
          learningRate: localModel.optimizer.learningRate,
        },
        coherence: localModel.coherenceConfig,
        metadata: localModel.metadata,
      };

      // Create distributed model with extracted configuration
      const distributedModel = this.createModel(modelConfig, distributedConfig);

      // Copy weights and biases from local model
      localModel.layers.forEach((layer, index) => {
        distributedModel.layers[index].weights = [...layer.weights];
        distributedModel.layers[index].biases = [...layer.biases];
      });

      // Copy compilation state if local model was compiled
      if (localModel.compiled) {
        distributedModel.compile({
          loss: localModel.lossFunction,
          metric: localModel.metric,
        });
      }

      return distributedModel;
    }

    /**
     * Create a cluster for distributed neural computation
     * @param {Object} clusterConfig - Cluster configuration
     * @returns {Prime.Distributed.Cluster.ClusterManager} Cluster manager
     */
    createCluster(clusterConfig = {}) {
      // Create cluster manager
      const clusterManager = new Prime.Distributed.Cluster.ClusterManager(
        clusterConfig,
      );

      // Add to factory configuration
      this.config.clusterManager = clusterManager;

      return clusterManager;
    }

    /**
     * Add a node to the cluster
     * @param {Object} nodeConfig - Node configuration
     * @returns {Prime.Distributed.Cluster.ClusterNode} Cluster node
     */
    addNode(nodeConfig) {
      if (!this.config.clusterManager) {
        this.config.clusterManager = this.createCluster();
      }

      return this.config.clusterManager.addNode(nodeConfig);
    }
  }

  // Add factory to Prime.Neural.Distributed namespace
  Prime.Neural.Distributed.ModelFactory = DistributedModelFactory;
})();

// Export the enhanced Prime object
module.exports = Prime;
