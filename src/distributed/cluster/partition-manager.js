/**
 * PrimeOS JavaScript Library - Distributed Partition Manager Module
 * Manages partitioning strategies for distributed computation
 */

// Import the Prime object from core
const Prime = require('../../core');
const EventBus = require('../event-bus');

/**
 * Partitioning types for distributed computation
 * @enum {string}
 */
const PartitionType = {
  /** Partition data across nodes */
  DATA_PARALLEL: 'data-parallel',
  /** Partition model layers across nodes */
  LAYER_WISE: 'layer-wise',
  /** Partition within individual layers */
  INTRA_LAYER: 'intra-layer',
  /** Partition by computation type */
  FUNCTIONAL: 'functional',
};

/**
 * Partitioning strategies for distribution
 * @enum {string}
 */
const PartitionStrategy = {
  /** Equal distribution of work */
  BALANCED: 'balanced',
  /** Based on node capabilities */
  CAPABILITY_BASED: 'capability-based',
  /** Based on data locality */
  LOCALITY_BASED: 'locality-based',
  /** Based on communication cost */
  COMMUNICATION_OPTIMIZED: 'communication-optimized',
  /** Dynamic adjustment based on performance */
  ADAPTIVE: 'adaptive',
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
      throw new Prime.ValidationError('Valid partition type is required');
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
      throw new Prime.ValidationError('Layer ID is required');
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
      throw new Prime.ValidationError('At least one node ID is required');
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
    this.eventBus.emit('partition:layer-assigned', {
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
    this.eventBus.emit('partition:sync-updated', {
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
              type: 'intra-layer',
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
              type: 'inter-layer',
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
          (p) => p.type === 'intra-layer',
        ).length,
        interLayerPaths: communicationPaths.filter(
          (p) => p.type === 'inter-layer',
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
      throw new Prime.ValidationError('Node count must be positive');
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
        'Total batch size and node IDs are required',
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
        'Valid partition plan and layer IDs are required',
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
    this.eventBus.emit('partition:plan-applied', {
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
      throw new Prime.ValidationError('Layers and node IDs are required');
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
          if (layer.type === 'conv' && capabilities.gpu) {
            score *= 1.5; // GPUs are better for convolutional layers
          } else if (layer.type === 'recurrent' && capabilities.memory) {
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
      throw new Prime.ValidationError('Valid partition plan is required');
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
    this.eventBus.emit('partition:plan-applied', {
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
    const assignments = Array(layerCount).fill(-1);

    // Simplified implementation: group sequential layers together
    // In a real implementation, this would analyze the computational graph
    // and group layers to minimize cross-node communication

    const layersPerNode = Math.ceil(layerCount / nodeCount);

    for (let i = 0; i < layerCount; i++) {
      assignments[i] = Math.floor(i / layersPerNode) % nodeCount;
    }

    return assignments;
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

    this.splitDimension = config.splitDimension || 'output';
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
      throw new Prime.ValidationError('Layers and node IDs are required');
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
      throw new Prime.ValidationError('Valid partition plan is required');
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
    this.eventBus.emit('partition:plan-applied', {
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
      this.splitDimension === 'output' ? layer.outputSize : layer.inputSize;

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
      throw new Prime.ValidationError('Scheme ID is required');
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
    } else {
      throw new Prime.ValidationError(
        `Unsupported partition type: ${config.type}`,
      );
    }

    // Register scheme
    this.schemes.set(schemeId, scheme);

    // Emit event
    this.eventBus.emit('partition:scheme-created', {
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
    this.eventBus.emit('partition:scheme-deleted', {
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
  PartitionManager,
};

module.exports = Prime;
