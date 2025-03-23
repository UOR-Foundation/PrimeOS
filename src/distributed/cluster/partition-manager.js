/**
 * PrimeOS JavaScript Library - Distributed Partition Manager Module
 * Manages partitioning strategies for distributed computation
 */

// Import the Prime object from core
const Prime = require("../../core");
const EventBus = require("../event-bus");

/**
 * Partitioning types for distributed computation
 * @enum {string}
 */
const PartitionType = {
  /** Partition data across nodes */
  DATA_PARALLEL: "data-parallel",
  /** Partition model layers across nodes */
  LAYER_WISE: "layer-wise",
  /** Partition within individual layers */
  INTRA_LAYER: "intra-layer",
  /** Partition by computation type */
  FUNCTIONAL: "functional",
};

/**
 * Partitioning strategies for distribution
 * @enum {string}
 */
const PartitionStrategy = {
  /** Equal distribution of work */
  BALANCED: "balanced",
  /** Based on node capabilities */
  CAPABILITY_BASED: "capability-based",
  /** Based on data locality */
  LOCALITY_BASED: "locality-based",
  /** Based on communication cost */
  COMMUNICATION_OPTIMIZED: "communication-optimized",
  /** Dynamic adjustment based on performance */
  ADAPTIVE: "adaptive",
};

/**
 * Base class for partition schemes
 * Provides common functionality for partition management
 */
class PartitionScheme {
  /**
   * Create a new partition scheme
   * @param {Object} config - Partition configuration
   * @param {string} config.type - Partitioning type
   * @param {string} config.strategy - Partitioning strategy
   */
  constructor(config = {}) {
    if (!config.type || !Object.values(PartitionType).includes(config.type)) {
      throw new Prime.ValidationError("Valid partition type is required");
    }

    this.type = config.type;
    this.strategy = config.strategy || PartitionStrategy.BALANCED;
    this.layerConfig = {};

    // Tracking of assignments
    this.nodeAssignments = new Map(); // nodeId -> assigned partitions
    this.layerAssignments = new Map(); // layerId -> assigned nodes

    // Synchronization state
    this.syncStatus = {};

    // Event bus for partition events
    this.eventBus = new EventBus();

    // Metrics
    this.metrics = {
      partitionsCreated: 0,
      reassignments: 0,
      communicationVolume: 0,
      lastPartitionTime: 0,
      averageNodeUtilization: 1.0,
    };
  }

  /**
   * Configure a layer in the partition scheme
   * @param {string} layerId - Layer identifier
   * @param {Object} config - Layer configuration
   * @returns {PartitionScheme} This partition scheme for chaining
   */
  configureLayer(layerId, config) {
    if (!layerId) {
      throw new Prime.ValidationError("Layer ID is required");
    }

    this.layerConfig[layerId] = {
      id: layerId,
      ...config,
    };

    return this;
  }

  /**
   * Assign a layer to nodes
   * @param {string} layerId - Layer identifier
   * @param {Array<string>} nodeIds - Node identifiers
   * @returns {boolean} Whether the assignment was successful
   */
  assignLayerToNodes(layerId, nodeIds) {
    if (!this.layerConfig[layerId]) {
      throw new Prime.ValidationError(
        `Layer ${layerId} not configured in partition scheme`,
      );
    }

    if (!Array.isArray(nodeIds) || nodeIds.length === 0) {
      throw new Prime.ValidationError("At least one node ID is required");
    }

    // Update layer assignments
    this.layerAssignments.set(layerId, [...nodeIds]);

    // Update node assignments
    for (const nodeId of nodeIds) {
      const nodeAssignments = this.nodeAssignments.get(nodeId) || [];
      if (!nodeAssignments.includes(layerId)) {
        nodeAssignments.push(layerId);
        this.nodeAssignments.set(nodeId, nodeAssignments);
      }
    }

    // Emit assignment event
    this.eventBus.emit("partition:layer-assigned", {
      layerId,
      nodeIds,
      timestamp: Date.now(),
    });

    // Track metrics
    this.metrics.partitionsCreated++;
    this.metrics.lastPartitionTime = Date.now();

    return true;
  }

  /**
   * Get nodes assigned to a layer
   * @param {string} layerId - Layer identifier
   * @returns {Array<string>} Assigned node IDs
   */
  getLayerNodes(layerId) {
    return this.layerAssignments.get(layerId) || [];
  }

  /**
   * Get layers assigned to a node
   * @param {string} nodeId - Node identifier
   * @returns {Array<string>} Assigned layer IDs
   */
  getNodeLayers(nodeId) {
    return this.nodeAssignments.get(nodeId) || [];
  }

  /**
   * Update synchronization status for a layer
   * @param {string} layerId - Layer identifier
   * @param {Object} status - Synchronization status
   * @returns {PartitionScheme} This partition scheme for chaining
   */
  updateSyncStatus(layerId, status) {
    if (!this.layerConfig[layerId]) {
      throw new Prime.ValidationError(
        `Layer ${layerId} not configured in partition scheme`,
      );
    }

    this.syncStatus[layerId] = {
      ...this.syncStatus[layerId],
      ...status,
      lastUpdateTimestamp: Date.now(),
    };

    // Emit sync status update event
    this.eventBus.emit("partition:sync-updated", {
      layerId,
      status: this.syncStatus[layerId],
      timestamp: Date.now(),
    });

    return this;
  }

  /**
   * Get communication paths between nodes
   * @returns {Array<Object>} Communication paths
   */
  getCommunicationPaths() {
    const paths = [];

    // Check each layer for connections between nodes
    for (const [layerId, nodeIds] of this.layerAssignments.entries()) {
      if (nodeIds.length > 1) {
        // For layers assigned to multiple nodes, communication is needed
        for (let i = 0; i < nodeIds.length; i++) {
          for (let j = i + 1; j < nodeIds.length; j++) {
            paths.push({
              source: nodeIds[i],
              target: nodeIds[j],
              layerId,
              type: "intra-layer",
            });
          }
        }
      }
    }

    // Check for layer-to-layer connections
    // (simplified: in reality, this depends on the computational graph)
    const allLayers = Array.from(this.layerAssignments.keys());

    for (let i = 0; i < allLayers.length - 1; i++) {
      const currentLayerId = allLayers[i];
      const nextLayerId = allLayers[i + 1];

      const currentNodes = this.getLayerNodes(currentLayerId);
      const nextNodes = this.getLayerNodes(nextLayerId);

      // Connect all nodes from current layer to all nodes in next layer
      for (const sourceNodeId of currentNodes) {
        for (const targetNodeId of nextNodes) {
          if (sourceNodeId !== targetNodeId) {
            paths.push({
              source: sourceNodeId,
              target: targetNodeId,
              sourceLayer: currentLayerId,
              targetLayer: nextLayerId,
              type: "inter-layer",
            });
          }
        }
      }
    }

    return paths;
  }

  /**
   * Get a summary of the partition scheme
   * @returns {Object} Partition summary
   */
  getSummary() {
    // Count totals
    const totalLayers = Object.keys(this.layerConfig).length;
    const totalNodes = this.nodeAssignments.size;

    // Calculate layer distribution stats
    let maxNodesPerLayer = 0;
    let minNodesPerLayer = Infinity;
    let totalNodeAssignments = 0;

    for (const [layerId, nodeIds] of this.layerAssignments.entries()) {
      const nodeCount = nodeIds.length;
      maxNodesPerLayer = Math.max(maxNodesPerLayer, nodeCount);
      minNodesPerLayer = Math.min(minNodesPerLayer, nodeCount);
      totalNodeAssignments += nodeCount;
    }

    // Calculate average assignments
    const avgNodesPerLayer =
      this.layerAssignments.size > 0
        ? totalNodeAssignments / this.layerAssignments.size
        : 0;

    // Calculate node utilization
    let maxLayersPerNode = 0;
    let minLayersPerNode = Infinity;

    for (const [nodeId, layerIds] of this.nodeAssignments.entries()) {
      const layerCount = layerIds.length;
      maxLayersPerNode = Math.max(maxLayersPerNode, layerCount);
      minLayersPerNode = Math.min(minLayersPerNode, layerCount);
    }

    // Calculate average assignments
    const avgLayersPerNode =
      this.nodeAssignments.size > 0
        ? totalNodeAssignments / this.nodeAssignments.size
        : 0;

    // Calculate communication overhead
    const communicationPaths = this.getCommunicationPaths();

    return {
      type: this.type,
      strategy: this.strategy,
      layers: {
        total: totalLayers,
        configured: Object.keys(this.layerConfig).length,
        assigned: this.layerAssignments.size,
      },
      nodes: {
        total: totalNodes,
        distribution: {
          min: minNodesPerLayer === Infinity ? 0 : minNodesPerLayer,
          max: maxNodesPerLayer,
          avg: avgNodesPerLayer,
        },
      },
      utilization: {
        min: minLayersPerNode === Infinity ? 0 : minLayersPerNode,
        max: maxLayersPerNode,
        avg: avgLayersPerNode,
      },
      communication: {
        paths: communicationPaths.length,
        intraLayerPaths: communicationPaths.filter(
          (p) => p.type === "intra-layer",
        ).length,
        interLayerPaths: communicationPaths.filter(
          (p) => p.type === "inter-layer",
        ).length,
      },
      metrics: this.metrics,
    };
  }
}

/**
 * Data-parallel partition scheme
 * Divides data across nodes but replicates model
 */
class DataParallelPartition extends PartitionScheme {
  /**
   * Create a new data-parallel partition scheme
   * @param {Object} config - Partition configuration
   */
  constructor(config = {}) {
    super({
      type: PartitionType.DATA_PARALLEL,
      strategy: config.strategy || PartitionStrategy.BALANCED,
      ...config,
    });

    this.batchSizePerNode = config.batchSizePerNode || 32;
    this.gradientSyncFrequency = config.gradientSyncFrequency || 1;
    this.parameterServer = config.parameterServer || null;
  }

  /**
   * Calculate optimal batch size for nodes
   * @param {number} totalBatchSize - Total batch size
   * @param {number} nodeCount - Number of nodes
   * @returns {Object} Batch size distribution
   */
  calculateBatchSizes(totalBatchSize, nodeCount) {
    if (nodeCount <= 0) {
      throw new Prime.ValidationError("Node count must be positive");
    }

    // Calculate batch size per node
    const baseBatchSize = Math.floor(totalBatchSize / nodeCount);
    const remainder = totalBatchSize % nodeCount;

    // Distribute remainder across nodes
    const batchSizes = Array(nodeCount).fill(baseBatchSize);
    for (let i = 0; i < remainder; i++) {
      batchSizes[i]++;
    }

    return {
      batchSizes,
      totalBatchSize,
      baseBatchSize,
      remainder,
    };
  }

  /**
   * Create a data partition plan
   * @param {Object} config - Partition config
   * @param {number} config.totalBatchSize - Total batch size
   * @param {Array<string>} config.nodeIds - Available node IDs
   * @param {Object} [config.nodeCapabilities={}] - Node capabilities
   * @returns {Object} Partition plan
   */
  createPartitionPlan(config) {
    if (
      !config.totalBatchSize ||
      !config.nodeIds ||
      config.nodeIds.length === 0
    ) {
      throw new Prime.ValidationError(
        "Total batch size and node IDs are required",
      );
    }

    const nodeCount = config.nodeIds.length;
    let batchSizes;

    if (
      this.strategy === PartitionStrategy.CAPABILITY_BASED &&
      config.nodeCapabilities
    ) {
      // Calculate weights based on node capabilities
      const weights = config.nodeIds.map((nodeId) => {
        const capabilities = config.nodeCapabilities[nodeId] || {};
        // Use compute capability as weight, default to 1.0
        return capabilities.compute || 1.0;
      });

      // Normalize weights
      const totalWeight = weights.reduce((sum, w) => sum + w, 0);
      const normalizedWeights = weights.map((w) => w / totalWeight);

      // Calculate batch sizes based on weights
      batchSizes = normalizedWeights.map((w) =>
        Math.max(1, Math.floor(w * config.totalBatchSize)),
      );

      // Adjust for rounding errors
      const currentTotal = batchSizes.reduce((sum, b) => sum + b, 0);
      const diff = config.totalBatchSize - currentTotal;

      if (diff > 0) {
        // Distribute remaining batches to nodes with highest weights
        const indexedWeights = normalizedWeights.map((w, i) => ({
          weight: w,
          index: i,
        }));
        indexedWeights.sort((a, b) => b.weight - a.weight);

        for (let i = 0; i < diff; i++) {
          batchSizes[indexedWeights[i % nodeCount].index]++;
        }
      } else if (diff < 0) {
        // Remove excess batches from nodes with lowest weights
        const indexedWeights = normalizedWeights.map((w, i) => ({
          weight: w,
          index: i,
        }));
        indexedWeights.sort((a, b) => a.weight - b.weight);

        for (let i = 0; i < -diff && i < nodeCount; i++) {
          batchSizes[indexedWeights[i].index] = Math.max(
            1,
            batchSizes[indexedWeights[i].index] - 1,
          );
        }
      }
    } else {
      // Use balanced distribution
      const distribution = this.calculateBatchSizes(
        config.totalBatchSize,
        nodeCount,
      );
      batchSizes = distribution.batchSizes;
    }

    // Create partition assignments
    const partitions = config.nodeIds.map((nodeId, i) => ({
      nodeId,
      batchSize: batchSizes[i],
      startIndex: batchSizes.slice(0, i).reduce((sum, b) => sum + b, 0),
      endIndex: batchSizes.slice(0, i + 1).reduce((sum, b) => sum + b, 0) - 1,
    }));

    return {
      type: this.type,
      strategy: this.strategy,
      totalBatchSize: config.totalBatchSize,
      partitions,
      nodeCount,
      parameterServer: this.parameterServer,
      gradientSyncFrequency: this.gradientSyncFrequency,
    };
  }

  /**
   * Apply partition plan to layers
   * @param {Object} plan - Partition plan
   * @param {Array<string>} layerIds - Layer IDs to partition
   * @returns {boolean} Whether the partitioning was successful
   */
  applyPartitionPlan(plan, layerIds) {
    if (!plan || !plan.partitions || !Array.isArray(layerIds)) {
      throw new Prime.ValidationError(
        "Valid partition plan and layer IDs are required",
      );
    }

    // In data-parallel, all nodes process all layers with different data
    // So we assign all layers to all nodes
    for (const layerId of layerIds) {
      const nodeIds = plan.partitions.map((p) => p.nodeId);
      this.assignLayerToNodes(layerId, nodeIds);

      // Configure layer
      this.configureLayer(layerId, {
        totalBatchSize: plan.totalBatchSize,
        partitioned: true,
        batchDistribution: plan.partitions,
      });
    }

    // Set up sync status tracking
    for (const layerId of layerIds) {
      this.updateSyncStatus(layerId, {
        parameterServer: plan.parameterServer,
        lastSyncTimestamp: Date.now(),
        gradientSyncFrequency: plan.gradientSyncFrequency,
        syncErrors: 0,
      });
    }

    // Emit partition applied event
    this.eventBus.emit("partition:plan-applied", {
      type: this.type,
      strategy: this.strategy,
      layerIds,
      nodeIds: plan.partitions.map((p) => p.nodeId),
      timestamp: Date.now(),
    });

    return true;
  }
}

/**
 * Layer-wise partition scheme
 * Divides model layers across nodes
 */
class LayerWisePartition extends PartitionScheme {
  /**
   * Create a new layer-wise partition scheme
   * @param {Object} config - Partition configuration
   */
  constructor(config = {}) {
    super({
      type: PartitionType.LAYER_WISE,
      strategy: config.strategy || PartitionStrategy.BALANCED,
      ...config,
    });

    this.pipelineDepth = config.pipelineDepth || 1;
    this.activationCaching = config.activationCaching !== false;
  }

  /**
   * Create a layer partition plan
   * @param {Object} config - Partition config
   * @param {Array<Object>} config.layers - Layer configurations
   * @param {Array<string>} config.nodeIds - Available node IDs
   * @param {Object} [config.nodeCapabilities={}] - Node capabilities
   * @returns {Object} Partition plan
   */
  createPartitionPlan(config) {
    if (!config.layers || !config.nodeIds || config.nodeIds.length === 0) {
      throw new Prime.ValidationError("Layers and node IDs are required");
    }

    const nodeCount = config.nodeIds.length;
    const layerCount = config.layers.length;

    // Determine assignment strategy
    let assignments;

    if (
      this.strategy === PartitionStrategy.CAPABILITY_BASED &&
      config.nodeCapabilities
    ) {
      // Calculate scores for each node-layer pair
      const scores = [];

      for (let i = 0; i < nodeCount; i++) {
        const nodeId = config.nodeIds[i];
        const capabilities = config.nodeCapabilities[nodeId] || {};

        for (let j = 0; j < layerCount; j++) {
          const layer = config.layers[j];

          // Calculate score based on layer requirements and node capabilities
          let score = capabilities.compute || 1.0;

          // Adjust score based on layer type
          if (layer.type === "conv" && capabilities.gpu) {
            score *= 1.5; // GPUs are better for convolutional layers
          } else if (layer.type === "recurrent" && capabilities.memory) {
            score *= 1.2; // High memory nodes are better for recurrent layers
          }

          scores.push({
            nodeIndex: i,
            layerIndex: j,
            score,
          });
        }
      }

      // Sort scores in descending order
      scores.sort((a, b) => b.score - a.score);

      // Initialize assignments
      assignments = Array(layerCount).fill(-1);
      const nodeLayerCounts = Array(nodeCount).fill(0);

      // Assign layers to nodes based on scores
      for (const { nodeIndex, layerIndex, score } of scores) {
        // Skip if this layer is already assigned
        if (assignments[layerIndex] !== -1) {
          continue;
        }

        // Check if adding this layer would overload the node
        // (simple heuristic: try to balance layer count)
        const avgLayersPerNode = layerCount / nodeCount;
        if (nodeLayerCounts[nodeIndex] >= Math.ceil(avgLayersPerNode * 1.5)) {
          continue;
        }

        // Assign layer to node
        assignments[layerIndex] = nodeIndex;
        nodeLayerCounts[nodeIndex]++;

        // If all layers are assigned, break
        if (!assignments.includes(-1)) {
          break;
        }
      }

      // Handle any unassigned layers (fallback to round-robin)
      for (let j = 0; j < layerCount; j++) {
        if (assignments[j] === -1) {
          // Find node with fewest layers
          const minNodeIndex = nodeLayerCounts.indexOf(
            Math.min(...nodeLayerCounts),
          );
          assignments[j] = minNodeIndex;
          nodeLayerCounts[minNodeIndex]++;
        }
      }
    } else if (this.strategy === PartitionStrategy.COMMUNICATION_OPTIMIZED) {
      // Group layers to minimize communication
      assignments = this._createCommunicationOptimizedAssignments(
        config.layers,
        nodeCount,
      );
    } else {
      // Use balanced distribution (round-robin)
      assignments = Array(layerCount)
        .fill(0)
        .map((_, i) => i % nodeCount);
    }

    // Create layer-node assignments
    const partitions = config.layers.map((layer, i) => ({
      layerId: layer.id,
      nodeId: config.nodeIds[assignments[i]],
      layerType: layer.type,
      inputSize: layer.inputSize,
      outputSize: layer.outputSize,
    }));

    // Group by node for convenience
    const nodePartitions = {};
    for (const partition of partitions) {
      if (!nodePartitions[partition.nodeId]) {
        nodePartitions[partition.nodeId] = [];
      }
      nodePartitions[partition.nodeId].push(partition);
    }

    return {
      type: this.type,
      strategy: this.strategy,
      partitions,
      nodePartitions,
      nodeCount,
      layerCount,
      pipelineDepth: this.pipelineDepth,
      activationCaching: this.activationCaching,
    };
  }

  /**
   * Apply partition plan to layers
   * @param {Object} plan - Partition plan
   * @returns {boolean} Whether the partitioning was successful
   */
  applyPartitionPlan(plan) {
    if (!plan || !plan.partitions) {
      throw new Prime.ValidationError("Valid partition plan is required");
    }

    // Clear existing assignments
    this.layerAssignments.clear();
    this.nodeAssignments.clear();

    // Apply new assignments
    for (const partition of plan.partitions) {
      // Configure layer
      this.configureLayer(partition.layerId, {
        type: partition.layerType,
        inputSize: partition.inputSize,
        outputSize: partition.outputSize,
        partitioned: true,
      });

      // Assign layer to node
      this.assignLayerToNodes(partition.layerId, [partition.nodeId]);
    }

    // Set up sync status tracking
    for (const partition of plan.partitions) {
      this.updateSyncStatus(partition.layerId, {
        lastSyncTimestamp: Date.now(),
        pipelineDepth: plan.pipelineDepth,
        activationCaching: plan.activationCaching,
        syncErrors: 0,
      });
    }

    // Emit partition applied event
    this.eventBus.emit("partition:plan-applied", {
      type: this.type,
      strategy: this.strategy,
      layerIds: plan.partitions.map((p) => p.layerId),
      nodeIds: [...new Set(plan.partitions.map((p) => p.nodeId))],
      timestamp: Date.now(),
    });

    return true;
  }

  /**
   * Create communication-optimized layer assignments
   * @private
   * @param {Array<Object>} layers - Layer configurations
   * @param {number} nodeCount - Number of available nodes
   * @returns {Array<number>} Node index assignments for each layer
   */
  _createCommunicationOptimizedAssignments(layers, nodeCount) {
    const layerCount = layers.length;

    // Step 1: Build layer dependency graph and connectivity matrix
    const dependencyGraph = this._buildLayerDependencyGraph(layers);

    // Step 2: Create initial computational cost estimate for each layer
    const layerCosts = this._estimateLayerComputationalCosts(layers);

    // Step 3: Calculate communication cost matrix between layers
    const communicationCosts = this._calculateCommunicationCosts(
      layers,
      dependencyGraph,
    );

    // Step 4: Apply graph partitioning algorithm to minimize communication costs
    // while balancing computational load
    return this._partitionLayerGraph(
      dependencyGraph,
      communicationCosts,
      layerCosts,
      nodeCount,
    );
  }

  /**
   * Build layer dependency graph based on network topology
   * @private
   * @param {Array<Object>} layers - Layer configurations
   * @returns {Array<Array<number>>} Adjacency matrix representing layer dependencies
   */
  _buildLayerDependencyGraph(layers) {
    const layerCount = layers.length;
    const dependencyGraph = Array(layerCount)
      .fill()
      .map(() => Array(layerCount).fill(0));

    // Map layer IDs to indices for faster lookups
    const layerIndexMap = new Map();
    layers.forEach((layer, idx) => {
      layerIndexMap.set(layer.id, idx);
    });

    // For each layer, determine its inputs and outputs
    for (let i = 0; i < layerCount; i++) {
      const layer = layers[i];

      // For standard sequential networks, connect adjacent layers
      if (i < layerCount - 1) {
        dependencyGraph[i][i + 1] = 1; // Forward connection
      }

      // Add any explicitly defined connections from layer configuration
      if (layer.inputs && Array.isArray(layer.inputs)) {
        for (const inputId of layer.inputs) {
          const inputIdx = layerIndexMap.get(inputId);
          if (inputIdx !== undefined) {
            dependencyGraph[inputIdx][i] = 1; // Connection from input to current layer
          }
        }
      }

      if (layer.outputs && Array.isArray(layer.outputs)) {
        for (const outputId of layer.outputs) {
          const outputIdx = layerIndexMap.get(outputId);
          if (outputIdx !== undefined) {
            dependencyGraph[i][outputIdx] = 1; // Connection from current layer to output
          }
        }
      }

      // Add residual/skip connections if specified
      if (layer.skipConnections && Array.isArray(layer.skipConnections)) {
        for (const skipId of layer.skipConnections) {
          const skipIdx = layerIndexMap.get(skipId);
          if (skipIdx !== undefined) {
            dependencyGraph[i][skipIdx] = 1; // Skip connection
          }
        }
      }
    }

    return dependencyGraph;
  }

  /**
   * Estimate computational cost for each layer
   * @private
   * @param {Array<Object>} layers - Layer configurations
   * @returns {Array<number>} Estimated computational cost for each layer
   */
  _estimateLayerComputationalCosts(layers) {
    return layers.map((layer) => {
      // Base cost based on input and output sizes
      let cost = (layer.inputSize || 1) * (layer.outputSize || 1);

      // Adjust based on layer type
      switch (layer.type) {
        case "conv":
          // Convolutional layers are more expensive
          const kernelSize = layer.kernelSize || 3;
          const channels = layer.channels || 1;
          cost *= kernelSize * kernelSize * channels;
          break;

        case "recurrent":
          // Recurrent layers have sequential dependencies
          const timeSteps = layer.timeSteps || 1;
          cost *= timeSteps;
          break;

        case "attention":
          // Attention mechanisms are very computation-heavy
          cost *= 3; // Multiple matrix multiplies + softmax
          break;

        case "pooling":
          // Pooling layers are computationally lighter
          cost /= 4;
          break;
      }

      // Adjust for activation function complexity
      if (layer.activation) {
        switch (layer.activation) {
          case "relu":
            // ReLU is computationally simple
            break;
          case "sigmoid":
          case "tanh":
            // These involve exponentials and are more expensive
            cost *= 1.2;
            break;
          case "softmax":
            // Softmax involves exponentials and normalization
            cost *= 1.5;
            break;
        }
      }

      return Math.max(1, cost); // Ensure minimum cost of 1
    });
  }

  /**
   * Calculate communication costs between layers
   * @private
   * @param {Array<Object>} layers - Layer configurations
   * @param {Array<Array<number>>} dependencyGraph - Layer dependency graph
   * @returns {Array<Array<number>>} Communication costs between layers
   */
  _calculateCommunicationCosts(layers, dependencyGraph) {
    const layerCount = layers.length;
    const communicationCosts = Array(layerCount)
      .fill()
      .map(() => Array(layerCount).fill(0));

    for (let i = 0; i < layerCount; i++) {
      for (let j = 0; j < layerCount; j++) {
        if (dependencyGraph[i][j]) {
          // Calculate communication volume based on tensor sizes
          const sourceLayer = layers[i];
          const targetLayer = layers[j];

          // Communication volume is proportional to the connecting dimensions
          // For simplicity, use output size of source layer
          const volume = sourceLayer.outputSize || 1;

          communicationCosts[i][j] = volume;
        }
      }
    }

    return communicationCosts;
  }

  /**
   * Partition layer graph to minimize communication costs while balancing load
   * @private
   * @param {Array<Array<number>>} dependencyGraph - Layer dependency graph
   * @param {Array<Array<number>>} communicationCosts - Communication costs between layers
   * @param {Array<number>} layerCosts - Computational costs for each layer
   * @param {number} nodeCount - Number of available nodes
   * @returns {Array<number>} Node assignments for each layer
   */
  _partitionLayerGraph(
    dependencyGraph,
    communicationCosts,
    layerCosts,
    nodeCount,
  ) {
    const layerCount = layerCosts.length;

    // Initialize with equal distribution of layers across nodes
    const assignments = Array(layerCount).fill(-1);
    const nodeCosts = Array(nodeCount).fill(0);
    const totalCost = layerCosts.reduce((sum, cost) => sum + cost, 0);
    const targetCostPerNode = totalCost / nodeCount;

    // First pass: group strongly connected components
    const components =
      this._identifyStronglyConnectedComponents(dependencyGraph);

    // Sort components by total cost (descending)
    components.sort((a, b) => {
      const costA = a.reduce((sum, layerIdx) => sum + layerCosts[layerIdx], 0);
      const costB = b.reduce((sum, layerIdx) => sum + layerCosts[layerIdx], 0);
      return costB - costA;
    });

    // Assign components to nodes using a bin packing approach
    for (const component of components) {
      // Calculate component cost
      const componentCost = component.reduce(
        (sum, layerIdx) => sum + layerCosts[layerIdx],
        0,
      );

      // Find best node for this component
      let bestNodeIdx = 0;
      let minCost = nodeCosts[0];

      for (let i = 1; i < nodeCount; i++) {
        if (nodeCosts[i] < minCost) {
          minCost = nodeCosts[i];
          bestNodeIdx = i;
        }
      }

      // If this component would make the node too unbalanced, try splitting it
      if (
        nodeCosts[bestNodeIdx] + componentCost > targetCostPerNode * 1.5 &&
        component.length > 1
      ) {
        // Find node with second lowest cost
        let secondBestNodeIdx = bestNodeIdx === 0 ? 1 : 0;
        let secondMinCost = nodeCosts[secondBestNodeIdx];

        for (let i = 0; i < nodeCount; i++) {
          if (i !== bestNodeIdx && nodeCosts[i] < secondMinCost) {
            secondMinCost = nodeCosts[i];
            secondBestNodeIdx = i;
          }
        }

        // Try to split component across these two nodes
        const sortedLayers = [...component].sort(
          (a, b) => layerCosts[b] - layerCosts[a],
        );
        let firstNodeCost = 0;
        let secondNodeCost = 0;

        for (const layerIdx of sortedLayers) {
          const cost = layerCosts[layerIdx];

          // Assign to node with lower current cost
          if (
            nodeCosts[bestNodeIdx] + firstNodeCost <=
            nodeCosts[secondBestNodeIdx] + secondNodeCost
          ) {
            assignments[layerIdx] = bestNodeIdx;
            firstNodeCost += cost;
          } else {
            assignments[layerIdx] = secondBestNodeIdx;
            secondNodeCost += cost;
          }
        }

        // Update node costs
        nodeCosts[bestNodeIdx] += firstNodeCost;
        nodeCosts[secondBestNodeIdx] += secondNodeCost;
      } else {
        // Assign all layers in this component to the same node
        for (const layerIdx of component) {
          assignments[layerIdx] = bestNodeIdx;
        }

        // Update node cost
        nodeCosts[bestNodeIdx] += componentCost;
      }
    }

    // Second pass: optimize communication by moving individual layers
    let improvements = true;
    const maxIterations = Math.min(20, layerCount * 2);

    for (
      let iteration = 0;
      iteration < maxIterations && improvements;
      iteration++
    ) {
      improvements = false;

      // For each layer, consider moving it to another node
      for (let layerIdx = 0; layerIdx < layerCount; layerIdx++) {
        const currentNodeIdx = assignments[layerIdx];
        const layerCost = layerCosts[layerIdx];

        // Calculate current communication cost for this layer
        let currentCommCost = 0;
        for (let otherLayer = 0; otherLayer < layerCount; otherLayer++) {
          if (otherLayer !== layerIdx) {
            const otherNodeIdx = assignments[otherLayer];
            if (currentNodeIdx !== otherNodeIdx) {
              // Add communication cost if layers are connected and on different nodes
              if (communicationCosts[layerIdx][otherLayer] > 0) {
                currentCommCost += communicationCosts[layerIdx][otherLayer];
              }
              if (communicationCosts[otherLayer][layerIdx] > 0) {
                currentCommCost += communicationCosts[otherLayer][layerIdx];
              }
            }
          }
        }

        // Try moving to each other node
        for (
          let targetNodeIdx = 0;
          targetNodeIdx < nodeCount;
          targetNodeIdx++
        ) {
          if (targetNodeIdx === currentNodeIdx) continue;

          // Calculate new communication cost if moved to this node
          let newCommCost = 0;
          for (let otherLayer = 0; otherLayer < layerCount; otherLayer++) {
            if (otherLayer !== layerIdx) {
              const otherNodeIdx = assignments[otherLayer];
              if (targetNodeIdx !== otherNodeIdx) {
                // Add communication cost if layers are connected and would be on different nodes
                if (communicationCosts[layerIdx][otherLayer] > 0) {
                  newCommCost += communicationCosts[layerIdx][otherLayer];
                }
                if (communicationCosts[otherLayer][layerIdx] > 0) {
                  newCommCost += communicationCosts[otherLayer][layerIdx];
                }
              }
            }
          }

          // Consider load balancing factor
          const currentNodeNewCost = nodeCosts[currentNodeIdx] - layerCost;
          const targetNodeNewCost = nodeCosts[targetNodeIdx] + layerCost;

          // Move if it improves communication cost without severely unbalancing nodes
          const commImprovement = currentCommCost - newCommCost;
          const balanceEffect = Math.abs(
            targetNodeNewCost - currentNodeNewCost,
          );

          if (commImprovement > 0 && balanceEffect < targetCostPerNode * 0.5) {
            // Move layer to target node
            assignments[layerIdx] = targetNodeIdx;
            nodeCosts[currentNodeIdx] -= layerCost;
            nodeCosts[targetNodeIdx] += layerCost;
            improvements = true;
            break;
          }
        }
      }
    }

    // Ensure all layers are assigned
    for (let i = 0; i < layerCount; i++) {
      if (assignments[i] === -1) {
        // Find node with minimum load
        let minLoadNodeIdx = 0;
        let minLoad = nodeCosts[0];

        for (let j = 1; j < nodeCount; j++) {
          if (nodeCosts[j] < minLoad) {
            minLoad = nodeCosts[j];
            minLoadNodeIdx = j;
          }
        }

        // Assign to least loaded node
        assignments[i] = minLoadNodeIdx;
        nodeCosts[minLoadNodeIdx] += layerCosts[i];
      }
    }

    return assignments;
  }

  /**
   * Identify strongly connected components in the layer graph
   * @private
   * @param {Array<Array<number>>} graph - Layer dependency graph
   * @returns {Array<Array<number>>} Strongly connected components
   */
  _identifyStronglyConnectedComponents(graph) {
    const n = graph.length;
    const visited = Array(n).fill(false);
    const stack = [];
    const components = [];

    // First DFS to fill the stack
    for (let i = 0; i < n; i++) {
      if (!visited[i]) {
        this._fillStack(i, graph, visited, stack);
      }
    }

    // Create transposed graph
    const transposedGraph = Array(n)
      .fill()
      .map(() => Array(n).fill(0));

    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        if (graph[i][j] === 1) {
          transposedGraph[j][i] = 1;
        }
      }
    }

    // Reset visited array
    for (let i = 0; i < n; i++) {
      visited[i] = false;
    }

    // Second DFS to find components
    while (stack.length > 0) {
      const v = stack.pop();

      if (!visited[v]) {
        const component = [];
        this._collectComponent(v, transposedGraph, visited, component);
        components.push(component);
      }
    }

    return components;
  }

  /**
   * Fill stack in DFS order for strongly connected components algorithm
   * @private
   * @param {number} vertex - Current vertex
   * @param {Array<Array<number>>} graph - Dependency graph
   * @param {Array<boolean>} visited - Visited vertices
   * @param {Array<number>} stack - Vertex stack
   */
  _fillStack(vertex, graph, visited, stack) {
    visited[vertex] = true;

    for (let i = 0; i < graph.length; i++) {
      if (graph[vertex][i] === 1 && !visited[i]) {
        this._fillStack(i, graph, visited, stack);
      }
    }

    stack.push(vertex);
  }

  /**
   * Collect vertices in a strongly connected component
   * @private
   * @param {number} vertex - Current vertex
   * @param {Array<Array<number>>} graph - Dependency graph
   * @param {Array<boolean>} visited - Visited vertices
   * @param {Array<number>} component - Component being built
   */
  _collectComponent(vertex, graph, visited, component) {
    visited[vertex] = true;
    component.push(vertex);

    for (let i = 0; i < graph.length; i++) {
      if (graph[vertex][i] === 1 && !visited[i]) {
        this._collectComponent(i, graph, visited, component);
      }
    }
  }
}

/**
 * Intra-layer partition scheme
 * Divides individual layers across nodes
 */
class IntraLayerPartition extends PartitionScheme {
  /**
   * Create a new intra-layer partition scheme
   * @param {Object} config - Partition configuration
   */
  constructor(config = {}) {
    super({
      type: PartitionType.INTRA_LAYER,
      strategy: config.strategy || PartitionStrategy.BALANCED,
      ...config,
    });

    this.splitDimension = config.splitDimension || "output";
    this.replicationFactor = config.replicationFactor || 1;
  }

  /**
   * Create an intra-layer partition plan
   * @param {Object} config - Partition config
   * @param {Array<Object>} config.layers - Layer configurations
   * @param {Array<string>} config.nodeIds - Available node IDs
   * @param {Object} [config.nodeCapabilities={}] - Node capabilities
   * @returns {Object} Partition plan
   */
  createPartitionPlan(config) {
    if (!config.layers || !config.nodeIds || config.nodeIds.length === 0) {
      throw new Prime.ValidationError("Layers and node IDs are required");
    }

    const nodeCount = config.nodeIds.length;
    const partitions = [];

    // Process each layer
    for (const layer of config.layers) {
      // Determine how to partition this layer
      const splitPoints = this._calculateSplitPoints(layer, nodeCount);

      // Create partitions for this layer
      const layerPartitions = splitPoints.map((split, i) => ({
        layerId: layer.id,
        nodeId: config.nodeIds[i % nodeCount],
        layerType: layer.type,
        splitDimension: this.splitDimension,
        inputSize: layer.inputSize,
        outputSize: layer.outputSize,
        start: split.start,
        end: split.end,
        size: split.end - split.start + 1,
      }));

      partitions.push(...layerPartitions);
    }

    // Group by layer for convenience
    const layerPartitions = {};
    for (const partition of partitions) {
      if (!layerPartitions[partition.layerId]) {
        layerPartitions[partition.layerId] = [];
      }
      layerPartitions[partition.layerId].push(partition);
    }

    return {
      type: this.type,
      strategy: this.strategy,
      splitDimension: this.splitDimension,
      partitions,
      layerPartitions,
      nodeCount,
      layerCount: config.layers.length,
      replicationFactor: this.replicationFactor,
    };
  }

  /**
   * Apply partition plan to layers
   * @param {Object} plan - Partition plan
   * @returns {boolean} Whether the partitioning was successful
   */
  applyPartitionPlan(plan) {
    if (!plan || !plan.partitions || !plan.layerPartitions) {
      throw new Prime.ValidationError("Valid partition plan is required");
    }

    // Clear existing assignments
    this.layerAssignments.clear();
    this.nodeAssignments.clear();

    // Apply new assignments for each layer
    for (const [layerId, partitions] of Object.entries(plan.layerPartitions)) {
      // Get node IDs for this layer
      const nodeIds = partitions.map((p) => p.nodeId);

      // Configure layer
      this.configureLayer(layerId, {
        type: partitions[0].layerType,
        inputSize: partitions[0].inputSize,
        outputSize: partitions[0].outputSize,
        partitioned: true,
        splitDimension: plan.splitDimension,
        partitions: partitions.map((p) => ({
          nodeId: p.nodeId,
          start: p.start,
          end: p.end,
          size: p.size,
        })),
      });

      // Assign layer to nodes
      this.assignLayerToNodes(layerId, nodeIds);
    }

    // Set up sync status tracking
    for (const [layerId, partitions] of Object.entries(plan.layerPartitions)) {
      this.updateSyncStatus(layerId, {
        lastSyncTimestamp: Date.now(),
        replicationFactor: plan.replicationFactor,
        syncErrors: 0,
      });
    }

    // Emit partition applied event
    this.eventBus.emit("partition:plan-applied", {
      type: this.type,
      strategy: this.strategy,
      layerIds: Object.keys(plan.layerPartitions),
      nodeIds: [...new Set(plan.partitions.map((p) => p.nodeId))],
      timestamp: Date.now(),
    });

    return true;
  }

  /**
   * Calculate split points for a layer
   * @private
   * @param {Object} layer - Layer configuration
   * @param {number} nodeCount - Number of available nodes
   * @returns {Array<Object>} Split points
   */
  _calculateSplitPoints(layer, nodeCount) {
    // Determine dimension to split on
    const dimensionSize =
      this.splitDimension === "output" ? layer.outputSize : layer.inputSize;

    const splits = [];
    const baseSize = Math.floor(dimensionSize / nodeCount);
    const remainder = dimensionSize % nodeCount;

    let start = 0;
    for (let i = 0; i < nodeCount; i++) {
      // Calculate size for this partition (distribute remainder)
      const size = baseSize + (i < remainder ? 1 : 0);
      const end = start + size - 1;

      // Only create a partition if there's something to compute
      if (size > 0) {
        splits.push({ start, end });
      }

      start = end + 1;
    }

    return splits;
  }
}

/**
 * Partition manager for creating and managing partition schemes
 */
class PartitionManager {
  /**
   * Create a new partition manager
   */
  constructor() {
    this.schemes = new Map(); // schemeId -> scheme
    this.eventBus = new EventBus();
  }

  /**
   * Create a new partition scheme
   * @param {string} schemeId - Scheme identifier
   * @param {Object} config - Scheme configuration
   * @returns {PartitionScheme} Created partition scheme
   */
  createScheme(schemeId, config) {
    if (!schemeId) {
      throw new Prime.ValidationError("Scheme ID is required");
    }

    if (this.schemes.has(schemeId)) {
      throw new Prime.ValidationError(`Scheme ${schemeId} already exists`);
    }

    // Determine scheme type and create appropriate instance
    let scheme;

    if (config.type === PartitionType.DATA_PARALLEL) {
      scheme = new DataParallelPartition(config);
    } else if (config.type === PartitionType.LAYER_WISE) {
      scheme = new LayerWisePartition(config);
    } else if (config.type === PartitionType.INTRA_LAYER) {
      scheme = new IntraLayerPartition(config);
    } else if (config.type === PartitionType.FUNCTIONAL) {
      scheme = new FunctionalPartition(config);
    } else {
      throw new Prime.ValidationError(
        `Unsupported partition type: ${config.type}`,
      );
    }

    // Register scheme
    this.schemes.set(schemeId, scheme);

    // Emit event
    this.eventBus.emit("partition:scheme-created", {
      schemeId,
      type: scheme.type,
      strategy: scheme.strategy,
      timestamp: Date.now(),
    });

    return scheme;
  }

  /**
   * Get a partition scheme
   * @param {string} schemeId - Scheme identifier
   * @returns {PartitionScheme} Partition scheme
   */
  getScheme(schemeId) {
    return this.schemes.get(schemeId);
  }

  /**
   * Delete a partition scheme
   * @param {string} schemeId - Scheme identifier
   * @returns {boolean} Whether the deletion was successful
   */
  deleteScheme(schemeId) {
    if (!this.schemes.has(schemeId)) {
      return false;
    }

    // Delete scheme
    this.schemes.delete(schemeId);

    // Emit event
    this.eventBus.emit("partition:scheme-deleted", {
      schemeId,
      timestamp: Date.now(),
    });

    return true;
  }

  /**
   * Get all partition schemes
   * @returns {Array<PartitionScheme>} All partition schemes
   */
  getAllSchemes() {
    return Array.from(this.schemes.values());
  }
}

/**
 * Functional partition scheme
 * Partitions network based on functional components and computational patterns
 */
class FunctionalPartition extends PartitionScheme {
  /**
   * Create a new functional partition scheme
   * @param {Object} config - Partition configuration
   */
  constructor(config = {}) {
    super({
      type: PartitionType.FUNCTIONAL,
      strategy: config.strategy || PartitionStrategy.BALANCED,
      ...config,
    });

    this.specializationMap = config.specializationMap || {};
    this.patternDetection = config.patternDetection !== false;
    this.adaptiveMigration = config.adaptiveMigration !== false;
  }

  /**
   * Create a functional partition plan
   * @param {Object} config - Partition config
   * @param {Array<Object>} config.layers - Layer configurations
   * @param {Array<string>} config.nodeIds - Available node IDs
   * @param {Object} [config.nodeCapabilities={}] - Node capabilities
   * @returns {Object} Partition plan
   */
  createPartitionPlan(config) {
    if (!config.layers || !config.nodeIds || config.nodeIds.length === 0) {
      throw new Prime.ValidationError("Layers and node IDs are required");
    }

    // Detect computational patterns in the network
    const patterns = this._detectComputationalPatterns(config.layers);

    // Group layers by pattern
    const patternGroups = this._groupLayersByPattern(config.layers, patterns);

    // Match patterns to node specializations
    const assignments = this._matchPatternsToNodes(
      patternGroups,
      config.nodeIds,
      config.nodeCapabilities || {},
    );

    // Create layer-node assignments
    const partitions = [];

    for (let i = 0; i < config.layers.length; i++) {
      const layer = config.layers[i];
      const nodeId = config.nodeIds[assignments[i]];

      partitions.push({
        layerId: layer.id,
        nodeId,
        layerType: layer.type,
        pattern: patterns[i],
        inputSize: layer.inputSize,
        outputSize: layer.outputSize,
      });
    }

    // Group by pattern for convenience
    const patternPartitions = {};
    for (const pattern of Object.keys(patternGroups)) {
      patternPartitions[pattern] = partitions.filter(
        (p) => p.pattern === pattern,
      );
    }

    return {
      type: this.type,
      strategy: this.strategy,
      partitions,
      patternPartitions,
      patterns,
      nodeCount: config.nodeIds.length,
      layerCount: config.layers.length,
      adaptiveMigration: this.adaptiveMigration,
    };
  }

  /**
   * Apply partition plan to layers
   * @param {Object} plan - Partition plan
   * @returns {boolean} Whether the partitioning was successful
   */
  applyPartitionPlan(plan) {
    if (!plan || !plan.partitions) {
      throw new Prime.ValidationError("Valid partition plan is required");
    }

    // Clear existing assignments
    this.layerAssignments.clear();
    this.nodeAssignments.clear();

    // Apply new assignments
    for (const partition of plan.partitions) {
      // Configure layer
      this.configureLayer(partition.layerId, {
        type: partition.layerType,
        inputSize: partition.inputSize,
        outputSize: partition.outputSize,
        partitioned: true,
        pattern: partition.pattern,
      });

      // Assign layer to node
      this.assignLayerToNodes(partition.layerId, [partition.nodeId]);
    }

    // Set up sync status tracking
    for (const partition of plan.partitions) {
      this.updateSyncStatus(partition.layerId, {
        lastSyncTimestamp: Date.now(),
        adaptiveMigration: plan.adaptiveMigration,
        syncErrors: 0,
      });
    }

    // Emit partition applied event
    this.eventBus.emit("partition:plan-applied", {
      type: this.type,
      strategy: this.strategy,
      layerIds: plan.partitions.map((p) => p.layerId),
      nodeIds: [...new Set(plan.partitions.map((p) => p.nodeId))],
      timestamp: Date.now(),
    });

    return true;
  }

  /**
   * Detect computational patterns in the network
   * @private
   * @param {Array<Object>} layers - Layer configurations
   * @returns {Array<string>} Detected pattern for each layer
   */
  _detectComputationalPatterns(layers) {
    return layers.map((layer) => {
      // Detect pattern based on layer type and properties
      if (layer.type === "conv") {
        return "convolutional";
      } else if (
        layer.type === "recurrent" ||
        layer.type === "lstm" ||
        layer.type === "gru"
      ) {
        return "recurrent";
      } else if (layer.type === "attention" || layer.type === "transformer") {
        return "attention";
      } else if (
        layer.type === "pooling" ||
        layer.type === "max_pool" ||
        layer.type === "avg_pool"
      ) {
        return "pooling";
      } else if (layer.sparse === true || layer.sparsity > 0.5) {
        return "sparse";
      } else if (layer.activation === "softmax" && layer.outputSize > 1000) {
        return "classification";
      } else if (layer.activation === "sigmoid" && layer.outputSize === 1) {
        return "binary";
      } else if (layer.normalization === true || layer.type === "batchnorm") {
        return "normalization";
      } else {
        // Default to dense pattern
        return "dense";
      }
    });
  }

  /**
   * Group layers by computational pattern
   * @private
   * @param {Array<Object>} layers - Layer configurations
   * @param {Array<string>} patterns - Detected patterns
   * @returns {Object} Grouped layers by pattern
   */
  _groupLayersByPattern(layers, patterns) {
    const groups = {};

    // Initialize groups
    for (let i = 0; i < layers.length; i++) {
      const pattern = patterns[i];
      if (!groups[pattern]) {
        groups[pattern] = [];
      }
      groups[pattern].push(i);
    }

    return groups;
  }

  /**
   * Match computational patterns to node specializations
   * @private
   * @param {Object} patternGroups - Grouped layers by pattern
   * @param {Array<string>} nodeIds - Available node IDs
   * @param {Object} nodeCapabilities - Node capabilities
   * @returns {Array<number>} Node index assignments for each layer
   */
  _matchPatternsToNodes(patternGroups, nodeIds, nodeCapabilities) {
    const layerCount = Object.values(patternGroups).flat().length;
    const assignments = Array(layerCount).fill(-1);
    const nodeCount = nodeIds.length;

    // Calculate node affinities for each pattern
    const nodeAffinities = {};

    for (const pattern of Object.keys(patternGroups)) {
      nodeAffinities[pattern] = Array(nodeCount).fill(1); // Default affinity

      for (let nodeIdx = 0; nodeIdx < nodeCount; nodeIdx++) {
        const nodeId = nodeIds[nodeIdx];
        const capabilities = nodeCapabilities[nodeId] || {};

        // Adjust affinity based on node capabilities and pattern
        switch (pattern) {
          case "convolutional":
            // GPUs are good for convolutional operations
            if (capabilities.gpu) {
              nodeAffinities[pattern][nodeIdx] *= 2.0;
            }
            break;

          case "recurrent":
            // Memory bandwidth is important for recurrent layers
            if (capabilities.memory) {
              nodeAffinities[pattern][nodeIdx] *= 1.5;
            }
            break;

          case "attention":
            // Both compute and memory are critical for attention
            if (capabilities.gpu && capabilities.memory) {
              nodeAffinities[pattern][nodeIdx] *= 2.5;
            } else if (capabilities.gpu || capabilities.memory) {
              nodeAffinities[pattern][nodeIdx] *= 1.3;
            }
            break;

          case "sparse":
            // CPUs can be better for sparse operations
            if (capabilities.cpu && !capabilities.gpu) {
              nodeAffinities[pattern][nodeIdx] *= 1.5;
            }
            break;

          case "dense":
            // General compute capability
            if (capabilities.compute) {
              nodeAffinities[pattern][nodeIdx] *= capabilities.compute;
            }
            break;
        }

        // Consider user-defined specializations
        if (this.specializationMap[pattern] === nodeId) {
          nodeAffinities[pattern][nodeIdx] *= 3.0; // Strong preference
        }
      }
    }

    // Track node loads
    const nodeCosts = Array(nodeCount).fill(0);

    // Assign patterns to nodes based on affinity and load balance
    for (const [pattern, layerIndices] of Object.entries(patternGroups)) {
      // Check if this pattern has a strong specialization
      const affinities = nodeAffinities[pattern];

      // Find the best node for this pattern
      let bestNodeIdx = 0;
      let bestScore = -Infinity;

      for (let nodeIdx = 0; nodeIdx < nodeCount; nodeIdx++) {
        // Score combines affinity and inverse of current load
        const loadFactor = 1 / (1 + nodeCosts[nodeIdx]); // Decreases as load increases
        const score = affinities[nodeIdx] * loadFactor;

        if (score > bestScore) {
          bestScore = score;
          bestNodeIdx = nodeIdx;
        }
      }

      // Assign all layers with this pattern to the best node
      for (const layerIdx of layerIndices) {
        assignments[layerIdx] = bestNodeIdx;
        nodeCosts[bestNodeIdx] += 1;
      }
    }

    return assignments;
  }
}

// Add to Prime namespace
Prime.Distributed = Prime.Distributed || {};
Prime.Distributed.Cluster = Prime.Distributed.Cluster || {};
Prime.Distributed.Cluster.Partition = {
  PartitionType,
  PartitionStrategy,
  PartitionScheme,
  DataParallelPartition,
  LayerWisePartition,
  IntraLayerPartition,
  FunctionalPartition,
  PartitionManager,
};

module.exports = Prime;
