/**
 * PrimeOS JavaScript Library - Distributed Partition Module
 * Handles distributed neural computation partitioning
 */

// Import the Prime object from core
const Prime = require("../../core");
const EventBus = require("../event-bus");

// Create the Partition module using IIFE
(function () {
  /**
   * Partition types for neural network distribution
   * @enum {string}
   */
  const PartitionType = {
    /** Split network horizontally across layers */
    LAYER_WISE: "layer_wise",
    /** Split individual layers across nodes */
    INTRA_LAYER: "intra_layer",
    /** Split training data across nodes */
    DATA_PARALLEL: "data_parallel",
    /** Split model state for parameter averaging */
    MODEL_PARALLEL: "model_parallel",
    /** Hybrid partitioning based on coherence optimization */
    COHERENCE_ADAPTIVE: "coherence_adaptive",
  };

  /**
   * PartitionScheme defines how to distribute neural computations
   * across a cluster of nodes
   */
  class PartitionScheme {
    /**
     * Create a new partition scheme
     * @param {Object} config - Partition configuration
     * @param {string} config.type - Partition type from PartitionType
     * @param {number} [config.nodeCount=1] - Number of nodes in the cluster
     * @param {Object} [config.layerConfig={}] - Neural network layer configuration
     * @param {boolean} [config.optimizeCoherence=true] - Whether to optimize for coherence
     */
    constructor(config) {
      if (!Prime.Utils.isObject(config)) {
        throw new Prime.ValidationError(
          "Partition configuration must be an object",
        );
      }

      if (!Object.values(PartitionType).includes(config.type)) {
        throw new Prime.ValidationError(
          `Invalid partition type: ${config.type}`,
        );
      }

      this.type = config.type;
      this.nodeCount = config.nodeCount || 1;
      this.layerConfig = config.layerConfig || {};
      this.optimizeCoherence = config.optimizeCoherence !== false;

      // Partition mapping
      this.partitionMap = new Map();
      this.layerAssignments = new Map();

      // Coherence metrics
      this.coherenceScore = 1.0;

      // Generate initial partitioning
      this._generatePartitioning();
    }

    /**
     * Generate the partitioning scheme based on configuration
     * @private
     */
    _generatePartitioning() {
      Prime.Logger.info(
        `Generating ${this.type} partitioning for ${this.nodeCount} nodes`,
      );

      switch (this.type) {
        case PartitionType.LAYER_WISE:
          this._generateLayerWisePartitioning();
          break;
        case PartitionType.INTRA_LAYER:
          this._generateIntraLayerPartitioning();
          break;
        case PartitionType.DATA_PARALLEL:
          this._generateDataParallelPartitioning();
          break;
        case PartitionType.MODEL_PARALLEL:
          this._generateModelParallelPartitioning();
          break;
        case PartitionType.COHERENCE_ADAPTIVE:
          this._generateCoherenceAdaptivePartitioning();
          break;
        default:
          throw new Prime.ValidationError(
            `Unsupported partition type: ${this.type}`,
          );
      }

      // Calculate initial coherence score
      this._calculateCoherenceScore();
    }

    /**
     * Generate layer-wise partitioning
     * @private
     */
    _generateLayerWisePartitioning() {
      // In layer-wise partitioning, each node gets one or more complete layers
      const layerIds = Object.keys(this.layerConfig);

      if (layerIds.length === 0) {
        Prime.Logger.debug(
          "No layers provided for partitioning, creating empty partition structure",
        );

        // Create empty partition structure with one node
        const nodeId = `node_0`;
        this.partitionMap.set(nodeId, {
          layers: [],
          dataIndices: null,
          partialComputation: false,
        });

        return;
      }

      // Distribute layers across nodes
      let currentNode = 0;

      for (let i = 0; i < layerIds.length; i++) {
        const layerId = layerIds[i];
        const nodeId = `node_${currentNode}`;

        // Assign this layer to the current node
        this.layerAssignments.set(layerId, nodeId);

        // Add layer to this node's partition
        if (!this.partitionMap.has(nodeId)) {
          this.partitionMap.set(nodeId, {
            layers: [],
            dataIndices: null,
            partialComputation: false,
          });
        }

        this.partitionMap.get(nodeId).layers.push(layerId);

        // Move to next node (wrap around if needed)
        currentNode = (currentNode + 1) % this.nodeCount;
      }
    }

    /**
     * Generate intra-layer partitioning
     * @private
     */
    _generateIntraLayerPartitioning() {
      // In intra-layer partitioning, individual layers are split across nodes
      const layerIds = Object.keys(this.layerConfig);

      if (layerIds.length === 0) {
        Prime.Logger.debug(
          "No layers provided for intra-layer partitioning, creating empty partition structure",
        );

        // Create empty partition structure with one node
        const nodeId = `node_0`;
        this.partitionMap.set(nodeId, {
          layers: [],
          dataIndices: null,
          partialComputation: true,
        });

        return;
      }

      for (const layerId of layerIds) {
        const layer = this.layerConfig[layerId];

        if (!layer || !layer.inputSize || !layer.outputSize) {
          continue;
        }

        // Split layer across nodes
        const outputsPerNode = Math.ceil(layer.outputSize / this.nodeCount);

        for (let nodeIndex = 0; nodeIndex < this.nodeCount; nodeIndex++) {
          const nodeId = `node_${nodeIndex}`;

          // Calculate this node's output range
          const startOutput = nodeIndex * outputsPerNode;
          const endOutput = Math.min(
            startOutput + outputsPerNode,
            layer.outputSize,
          );

          // Skip if no outputs assigned to this node
          if (startOutput >= layer.outputSize) {
            continue;
          }

          // Create partition configuration
          if (!this.partitionMap.has(nodeId)) {
            this.partitionMap.set(nodeId, {
              layers: [],
              dataIndices: null,
              partialComputation: true,
            });
          }

          // Add layer to node's partition with output range
          this.partitionMap.get(nodeId).layers.push(layerId);

          // Track layer assignment with slice information
          this.layerAssignments.set(`${layerId}_${nodeIndex}`, {
            nodeId,
            outputRange: [startOutput, endOutput],
            inputRange: [0, layer.inputSize], // Full input range for now
          });
        }
      }
    }

    /**
     * Generate data-parallel partitioning
     * @private
     */
    _generateDataParallelPartitioning() {
      // In data-parallel partitioning, each node has a copy of the full model
      // but processes a different subset of the training data

      // Each node gets the full set of layers
      const layerIds = Object.keys(this.layerConfig);

      if (layerIds.length === 0) {
        Prime.Logger.debug(
          "No layers provided for data-parallel partitioning, creating empty partition structure",
        );

        // Determine batch size from configuration or use default
        const batchSize = this.layerConfig.batchSize || 32;

        // Create empty partition structures
        for (let nodeIndex = 0; nodeIndex < this.nodeCount; nodeIndex++) {
          const nodeId = `node_${nodeIndex}`;

          // Calculate this node's data range
          const dataIndicesPerNode = Math.ceil(batchSize / this.nodeCount);
          const startIndex = nodeIndex * dataIndicesPerNode;
          const endIndex = Math.min(startIndex + dataIndicesPerNode, batchSize);

          this.partitionMap.set(nodeId, {
            layers: [],
            dataIndices: {
              start: startIndex,
              end: endIndex,
            },
            partialComputation: false,
          });
        }

        return;
      }

      // Determine batch size from configuration or use default
      const batchSize = this.layerConfig.batchSize || 32;

      // Split batch indices across nodes
      const dataIndicesPerNode = Math.ceil(batchSize / this.nodeCount);

      for (let nodeIndex = 0; nodeIndex < this.nodeCount; nodeIndex++) {
        const nodeId = `node_${nodeIndex}`;

        // Calculate this node's data range
        const startIndex = nodeIndex * dataIndicesPerNode;
        const endIndex = Math.min(startIndex + dataIndicesPerNode, batchSize);

        // Skip if no data assigned to this node
        if (startIndex >= batchSize) {
          continue;
        }

        // Create partition with data indices
        this.partitionMap.set(nodeId, {
          layers: [...layerIds], // Full model
          dataIndices: {
            start: startIndex,
            end: endIndex,
          },
          partialComputation: false,
        });

        // Assign all layers to this node
        for (const layerId of layerIds) {
          this.layerAssignments.set(`${layerId}_${nodeIndex}`, nodeId);
        }
      }
    }

    /**
     * Generate model-parallel partitioning
     * @private
     */
    _generateModelParallelPartitioning() {
      // Model-parallel is similar to layer-wise but with more sophisticated
      // load balancing based on computational requirements
      const layerIds = Object.keys(this.layerConfig);

      if (layerIds.length === 0) {
        Prime.Logger.debug(
          "No layers provided for model-parallel partitioning, creating empty partition structure",
        );

        // Create empty partition structures with balanced distribution
        for (let nodeIndex = 0; nodeIndex < this.nodeCount; nodeIndex++) {
          const nodeId = `node_${nodeIndex}`;

          this.partitionMap.set(nodeId, {
            layers: [],
            dataIndices: null,
            partialComputation: false,
          });
        }

        return;
      }

      // Calculate computational load for each layer
      const layerLoads = new Map();
      let totalLoad = 0;

      for (const layerId of layerIds) {
        const layer = this.layerConfig[layerId];

        if (!layer || !layer.inputSize || !layer.outputSize) {
          layerLoads.set(layerId, 1); // Default weight
          totalLoad += 1;
          continue;
        }

        // Estimate computational load based on matrix multiplication operations
        const forwardOps = layer.inputSize * layer.outputSize;
        const backwardOps = forwardOps * 2;
        const load = forwardOps + backwardOps;

        layerLoads.set(layerId, load);
        totalLoad += load;
      }

      // Target load per node
      const targetLoadPerNode = totalLoad / this.nodeCount;

      // Distribute layers across nodes
      let currentNodeId = `node_0`;
      let currentNodeLoad = 0;

      // Initialize first node
      this.partitionMap.set(currentNodeId, {
        layers: [],
        dataIndices: null,
        partialComputation: false,
      });

      // Sort layers by load (descending)
      const sortedLayers = Array.from(layerLoads.entries()).sort(
        (a, b) => b[1] - a[1],
      );

      for (const [layerId, load] of sortedLayers) {
        // If adding this layer would exceed target load by too much,
        // move to next node (unless this is the last node)
        if (
          currentNodeLoad + load > targetLoadPerNode * 1.5 &&
          currentNodeId !== `node_${this.nodeCount - 1}`
        ) {
          // Create new node
          const nodeIndex = parseInt(currentNodeId.split("_")[1]) + 1;
          if (nodeIndex >= this.nodeCount) {
            break;
          }

          currentNodeId = `node_${nodeIndex}`;
          currentNodeLoad = 0;

          this.partitionMap.set(currentNodeId, {
            layers: [],
            dataIndices: null,
            partialComputation: false,
          });
        }

        // Assign layer to current node
        this.partitionMap.get(currentNodeId).layers.push(layerId);
        this.layerAssignments.set(layerId, currentNodeId);

        // Update load
        currentNodeLoad += load;
      }
    }

    /**
     * Generate coherence-adaptive partitioning
     * @private
     */
    _generateCoherenceAdaptivePartitioning() {
      // This is a more advanced partitioning that adapts based on coherence measures
      // For this implementation, we'll start with model-parallel and refine it

      // Start with model-parallel as a baseline
      this._generateModelParallelPartitioning();

      // Apply coherence-based refinements if requested
      if (this.optimizeCoherence) {
        this._refinePartitioningForCoherence();
      }
    }

    /**
     * Refine partitioning to optimize coherence
     * @private
     */
    _refinePartitioningForCoherence() {
      // Comprehensive coherence-based partitioning optimization
      // This implementation analyzes layer dependencies, data flow patterns,
      // computational load, and communication overhead to create a coherence-optimized partition

      const layerIds = Object.keys(this.layerConfig);
      const layerDependencies = this._analyzeDependencies(layerIds);

      // Calculate computational load for each layer
      const layerLoads = this._calculateLayerComputationalLoads(layerIds);

      // Calculate initial communication costs
      const initialCommCosts = this._calculateCommunicationCosts();
      Prime.Logger.debug(
        `Initial communication cost: ${initialCommCosts.total.toFixed(4)}`,
      );

      // Phase 1: Identify strongly connected components (clusters of layers)
      const layerClusters = this._identifyLayerClusters(layerDependencies);

      // Phase 2: Initial assignment of clusters to nodes based on load balancing
      this._assignClustersToNodes(layerClusters, layerLoads);

      // Phase 3: Iterative refinement using simulated annealing
      const iterations = Math.min(50, layerIds.length * 2); // Limit iterations based on layer count
      const initialTemp = 1.0;
      const finalTemp = 0.01;

      for (let i = 0; i < iterations; i++) {
        // Calculate temperature (exponential cooling schedule)
        const t =
          initialTemp * Math.pow(finalTemp / initialTemp, i / iterations);

        // Attempt a refinement move
        this._refinementStep(t, layerDependencies, layerLoads);

        // Recalculate coherence score
        this._calculateCoherenceScore();

        // Log progress for significant iterations
        if (i % 10 === 0 || i === iterations - 1) {
          Prime.Logger.debug(
            `Refinement iteration ${i}, coherence: ${this.coherenceScore.toFixed(4)}`,
          );
        }
      }

      // Phase 4: Final local optimization
      this._localOptimization(layerDependencies);

      // Calculate final communication costs for comparison
      const finalCommCosts = this._calculateCommunicationCosts();
      Prime.Logger.info(
        `Partition refinement complete: communication cost reduced from ${initialCommCosts.total.toFixed(4)} to ${finalCommCosts.total.toFixed(4)}`,
      );
    }

    /**
     * Calculate computational loads for all layers
     * @private
     * @param {Array<string>} layerIds - Layer IDs
     * @returns {Map<string, number>} Map of layer ID to computational load
     */
    _calculateLayerComputationalLoads(layerIds) {
      const layerLoads = new Map();

      for (const layerId of layerIds) {
        const layer = this.layerConfig[layerId];

        if (!layer || !layer.inputSize || !layer.outputSize) {
          // Default weight for layers without size information
          layerLoads.set(layerId, 1);
          continue;
        }

        // Calculate computational complexity based on operation type
        let complexity = layer.inputSize * layer.outputSize; // Base matrix multiply

        // Adjust complexity based on layer type
        if (layer.type === "conv") {
          // Convolutional layers are more expensive
          const kernelSize = layer.kernelSize || 3;
          const channels = layer.channels || 1;
          complexity *= kernelSize * kernelSize * channels;
        } else if (layer.type === "attention") {
          // Attention mechanisms are very computation-heavy
          complexity *= 3; // Multiple matrix multiplies + softmax
        } else if (layer.type === "recurrent") {
          // Recurrent layers have sequential dependencies
          const timeSteps = layer.timeSteps || 1;
          complexity *= timeSteps;
        }

        // Memory access patterns also affect performance
        const memoryFactor = layer.sparseConnections ? 0.7 : 1.0;

        // Activation function complexity
        const activationFactor =
          layer.activation === "relu"
            ? 1.0
            : layer.activation === "sigmoid"
              ? 1.2
              : layer.activation === "tanh"
                ? 1.3
                : 1.0;

        // Final load calculation
        const load = complexity * memoryFactor * activationFactor;
        layerLoads.set(layerId, load);
      }

      return layerLoads;
    }

    /**
     * Calculate communication costs between nodes in current partitioning
     * @private
     * @returns {Object} Communication costs
     */
    _calculateCommunicationCosts() {
      const costs = {
        nodeToNode: new Map(), // Node-to-node communication volume
        total: 0, // Total communication cost
        maxLink: 0, // Maximum link load
        crossLayerCount: 0, // Count of cross-node layer dependencies
      };

      // Initialize node-to-node map
      for (const nodeA of this.partitionMap.keys()) {
        costs.nodeToNode.set(nodeA, new Map());
        for (const nodeB of this.partitionMap.keys()) {
          if (nodeA !== nodeB) {
            costs.nodeToNode.get(nodeA).set(nodeB, 0);
          }
        }
      }

      // Calculate costs based on layer dependencies that span nodes
      const layerIds = Object.keys(this.layerConfig);
      for (let i = 0; i < layerIds.length - 1; i++) {
        const currentLayerId = layerIds[i];
        const nextLayerId = layerIds[i + 1];

        const currentNodeId = this.layerAssignments.get(currentLayerId);
        const nextNodeId = this.layerAssignments.get(nextLayerId);

        if (!currentNodeId || !nextNodeId) continue;

        // If layers are on different nodes, add communication cost
        if (currentNodeId !== nextNodeId) {
          // Get layer sizes for communication volume calculation
          const currentLayer = this.layerConfig[currentLayerId];
          const nextLayer = this.layerConfig[nextLayerId];

          // Communication volume is proportional to the connecting dimensions
          const commVolume =
            currentLayer && currentLayer.outputSize
              ? currentLayer.outputSize
              : 1;

          // Update node-to-node communication
          const currentNodeMap = costs.nodeToNode.get(currentNodeId);
          if (currentNodeMap) {
            const existingVolume = currentNodeMap.get(nextNodeId) || 0;
            currentNodeMap.set(nextNodeId, existingVolume + commVolume);

            // Update max link if this is now the highest
            const newLinkLoad = existingVolume + commVolume;
            costs.maxLink = Math.max(costs.maxLink, newLinkLoad);
          }

          // Add to total communication cost
          costs.total += commVolume;
          costs.crossLayerCount++;
        }
      }

      return costs;
    }

    /**
     * Identify clusters of strongly connected layers
     * @private
     * @param {Map<string, Map<string, number>>} layerDependencies - Layer dependency scores
     * @returns {Array<Array<string>>} Clusters of layer IDs
     */
    _identifyLayerClusters(layerDependencies) {
      // Use a hierarchical clustering approach to identify layer clusters
      const clusters = [];
      const threshold = 0.6; // Dependency threshold for clustering
      const assignedLayers = new Set();

      // Start with each layer in its own cluster
      const layerIds = Array.from(layerDependencies.keys());

      // First pass: identify strongly connected components
      for (const layerId of layerIds) {
        if (assignedLayers.has(layerId)) continue;

        // Start a new cluster with this layer
        const cluster = [layerId];
        assignedLayers.add(layerId);

        // Find strongly connected layers
        let added = true;
        while (added) {
          added = false;

          for (const clusteredId of [...cluster]) {
            const dependencies = layerDependencies.get(clusteredId);
            if (!dependencies) continue;

            for (const [dependentId, score] of dependencies.entries()) {
              if (score >= threshold && !assignedLayers.has(dependentId)) {
                cluster.push(dependentId);
                assignedLayers.add(dependentId);
                added = true;
              }
            }
          }
        }

        clusters.push(cluster);
      }

      // Second pass: merge small clusters to avoid fragmentation
      const mergedClusters = [];
      const minClusterSize = 2;

      for (const cluster of clusters) {
        if (cluster.length >= minClusterSize) {
          // Keep large clusters as-is
          mergedClusters.push(cluster);
        } else {
          // For small clusters, find best merge target
          let bestTargetIndex = -1;
          let bestConnectionStrength = -1;

          for (let i = 0; i < mergedClusters.length; i++) {
            const targetCluster = mergedClusters[i];
            let connectionStrength = 0;

            // Calculate connection strength between clusters
            for (const sourceId of cluster) {
              const dependencies = layerDependencies.get(sourceId);
              if (!dependencies) continue;

              for (const targetId of targetCluster) {
                connectionStrength += dependencies.get(targetId) || 0;
              }
            }

            if (connectionStrength > bestConnectionStrength) {
              bestConnectionStrength = connectionStrength;
              bestTargetIndex = i;
            }
          }

          if (bestTargetIndex >= 0 && bestConnectionStrength > 0) {
            // Merge with best target
            mergedClusters[bestTargetIndex].push(...cluster);
          } else {
            // No good merge target, keep as separate cluster
            mergedClusters.push(cluster);
          }
        }
      }

      return mergedClusters;
    }

    /**
     * Assign clusters of layers to nodes based on load balancing
     * @private
     * @param {Array<Array<string>>} clusters - Clusters of layer IDs
     * @param {Map<string, number>} layerLoads - Computational load per layer
     */
    _assignClustersToNodes(clusters, layerLoads) {
      // Calculate load for each cluster
      const clusterLoads = clusters.map((cluster) => {
        let totalLoad = 0;
        for (const layerId of cluster) {
          totalLoad += layerLoads.get(layerId) || 1;
        }
        return totalLoad;
      });

      // Sort clusters by load (descending)
      const sortedIndices = clusterLoads
        .map((load, index) => ({ load, index }))
        .sort((a, b) => b.load - a.load)
        .map((item) => item.index);

      // Initialize node loads
      const nodeLoads = new Map();
      for (let i = 0; i < this.nodeCount; i++) {
        nodeLoads.set(`node_${i}`, 0);
      }

      // Reset partition mapping
      this.partitionMap.clear();
      this.layerAssignments.clear();

      // Initialize empty nodes
      for (let i = 0; i < this.nodeCount; i++) {
        const nodeId = `node_${i}`;
        this.partitionMap.set(nodeId, {
          layers: [],
          dataIndices: null,
          partialComputation: false,
        });
      }

      // Assign clusters to nodes using a greedy bin packing approach
      for (const clusterIndex of sortedIndices) {
        const cluster = clusters[clusterIndex];
        const clusterLoad = clusterLoads[clusterIndex];

        // Find node with minimum load
        let minLoadNodeId = null;
        let minLoad = Infinity;

        for (const [nodeId, load] of nodeLoads.entries()) {
          if (load < minLoad) {
            minLoad = load;
            minLoadNodeId = nodeId;
          }
        }

        // Assign all layers in this cluster to the selected node
        for (const layerId of cluster) {
          // Update assignments
          this.layerAssignments.set(layerId, minLoadNodeId);
          this.partitionMap.get(minLoadNodeId).layers.push(layerId);
        }

        // Update node load
        nodeLoads.set(minLoadNodeId, minLoad + clusterLoad);
      }
    }

    /**
     * Perform a single refinement step using simulated annealing
     * @private
     * @param {number} temperature - Current temperature for annealing
     * @param {Map<string, Map<string, number>>} dependencies - Layer dependencies
     * @param {Map<string, number>} layerLoads - Layer computational loads
     */
    _refinementStep(temperature, dependencies, layerLoads) {
      // Calculate current state metrics
      const currentCommCost = this._calculateCommunicationCosts().total;
      const currentLoadBalance = this._calculateLoadBalanceScore();
      const currentScore =
        0.6 * currentLoadBalance - 0.4 * (currentCommCost / 100);

      // Randomly select a layer to move
      const layerIds = Array.from(this.layerAssignments.keys());
      const randomLayerIndex = Math.floor(Math.random() * layerIds.length);
      const layerId = layerIds[randomLayerIndex];
      const currentNodeId = this.layerAssignments.get(layerId);

      if (!currentNodeId) return;

      // Select a random target node different from current
      const nodeIds = Array.from(this.partitionMap.keys()).filter(
        (id) => id !== currentNodeId,
      );

      if (nodeIds.length === 0) return;

      const randomNodeIndex = Math.floor(Math.random() * nodeIds.length);
      const targetNodeId = nodeIds[randomNodeIndex];

      // Temporarily move the layer
      this._moveLayerToNode(layerId, targetNodeId);

      // Calculate new state metrics
      const newCommCost = this._calculateCommunicationCosts().total;
      const newLoadBalance = this._calculateLoadBalanceScore();
      const newScore = 0.6 * newLoadBalance - 0.4 * (newCommCost / 100);

      // Decide whether to keep the change
      const scoreDelta = newScore - currentScore;
      const acceptProbability =
        scoreDelta > 0 ? 1.0 : Math.exp(scoreDelta / temperature);

      if (Math.random() > acceptProbability) {
        // Revert the move
        this._moveLayerToNode(layerId, currentNodeId);
      }
    }

    /**
     * Perform local optimization to finalize partitioning
     * @private
     * @param {Map<string, Map<string, number>>} layerDependencies - Layer dependencies
     */
    _localOptimization(layerDependencies) {
      // This phase does a final pass to optimize specific local patterns
      // Focus on critical paths and communication bottlenecks
      const layerIds = Array.from(this.layerAssignments.keys());

      // First, identify communication bottlenecks
      const commCosts = this._calculateCommunicationCosts();
      const bottleneckLinks = [];

      for (const [sourceNodeId, targets] of commCosts.nodeToNode.entries()) {
        for (const [targetNodeId, volume] of targets.entries()) {
          if (volume > 0.7 * commCosts.maxLink) {
            bottleneckLinks.push({
              source: sourceNodeId,
              target: targetNodeId,
              volume,
            });
          }
        }
      }

      // Sort bottlenecks by volume (descending)
      bottleneckLinks.sort((a, b) => b.volume - a.volume);

      // For each bottleneck, try to move layers to reduce communication
      for (const link of bottleneckLinks) {
        // Find layers that communicate across this link
        const crossLinkLayers = [];

        for (let i = 0; i < layerIds.length - 1; i++) {
          const layerId = layerIds[i];
          const nextLayerId = layerIds[i + 1];

          const nodeId = this.layerAssignments.get(layerId);
          const nextNodeId = this.layerAssignments.get(nextLayerId);

          if (nodeId === link.source && nextNodeId === link.target) {
            crossLinkLayers.push({
              layerId,
              nextLayerId,
              direction: "forward",
            });
          } else if (nodeId === link.target && nextNodeId === link.source) {
            crossLinkLayers.push({
              layerId: nextLayerId,
              nextLayerId: layerId,
              direction: "backward",
            });
          }
        }

        if (crossLinkLayers.length === 0) continue;

        // Attempt to reduce bottleneck by moving layers
        // Strategy: Move smaller layers across the link to reduce communication
        for (const { layerId, nextLayerId, direction } of crossLinkLayers) {
          const layer = this.layerConfig[layerId];
          const nextLayer = this.layerConfig[nextLayerId];

          // Skip if layer info is missing
          if (!layer || !nextLayer) continue;

          // Determine which layer is smaller (in terms of parameters)
          const layerSize = (layer.inputSize || 1) * (layer.outputSize || 1);
          const nextLayerSize =
            (nextLayer.inputSize || 1) * (nextLayer.outputSize || 1);

          if (layerSize <= nextLayerSize) {
            // Move the smaller layer to join the larger one
            const targetNodeId = this.layerAssignments.get(nextLayerId);
            if (targetNodeId) {
              this._moveLayerToNode(layerId, targetNodeId);
            }
          } else {
            // Move the next layer to join this one
            const targetNodeId = this.layerAssignments.get(layerId);
            if (targetNodeId) {
              this._moveLayerToNode(nextLayerId, targetNodeId);
            }
          }

          // Recalculate costs after each move
          const newCosts = this._calculateCommunicationCosts();
          if (newCosts.total < commCosts.total * 0.95) {
            // If we've significantly improved, stop optimizing this bottleneck
            break;
          }
        }
      }
    }

    /**
     * Analyze layer dependencies based on network architecture and data flow
     * @private
     * @param {Array<string>} layerIds - Layer IDs to analyze
     * @returns {Map<string, Map<string, number>>} Dependency scores
     */
    _analyzeDependencies(layerIds) {
      // Create a map for each layer's dependencies
      const dependencies = new Map();

      // Initialize dependency maps for each layer
      for (const layerId of layerIds) {
        dependencies.set(layerId, new Map());
      }

      // Get layer configuration from the model
      const layers = layerIds.map(id => this.layerConfig[id] || {});
      
      // Step 1: Identify direct connections based on layer topology
      this._analyzeTopologyDependencies(layerIds, layers, dependencies);
      
      // Step 2: Analyze computational dependencies (shared weights, attention mechanisms)
      this._analyzeComputationalDependencies(layerIds, layers, dependencies);
      
      // Step 3: Analyze gradient flow dependencies for backpropagation
      this._analyzeGradientDependencies(layerIds, layers, dependencies);
      
      // Step 4: Consider skip connections and residual paths
      this._analyzeSkipConnections(layerIds, layers, dependencies);
      
      // Log dependency analysis results
      Prime.Logger.info(`Completed layer dependency analysis for ${layerIds.length} layers`);
      
      return dependencies;
    }
    
    /**
     * Analyze direct topology dependencies between layers
     * @private
     * @param {Array<string>} layerIds - Layer IDs to analyze
     * @param {Array<Object>} layers - Layer configurations
     * @param {Map<string, Map<string, number>>} dependencies - Dependency map to update
     */
    _analyzeTopologyDependencies(layerIds, layers, dependencies) {
      // For each layer, check its inputs and outputs
      for (let i = 0; i < layerIds.length; i++) {
        const currentId = layerIds[i];
        const currentLayer = layers[i];
        
        // Check for explicit connections defined in the layer config
        const connections = currentLayer.connections || [];
        const explicitOutputs = currentLayer.outputs || [];
        
        if (connections.length > 0) {
          // If explicit connections are defined, use them
          for (const connection of connections) {
            if (connection.to && layerIds.includes(connection.to)) {
              // Add forward dependency with specified strength or default to strong (0.9)
              const strength = connection.strength || 0.9;
              dependencies.get(currentId).set(connection.to, strength);
              
              // Add corresponding backward dependency
              const backwardStrength = connection.bidirectional ? strength : strength * 0.7;
              dependencies.get(connection.to).set(currentId, backwardStrength);
            }
          }
        } else if (explicitOutputs.length > 0) {
          // If explicit outputs are defined, use them
          for (const outputId of explicitOutputs) {
            if (layerIds.includes(outputId)) {
              dependencies.get(currentId).set(outputId, 0.9);
              dependencies.get(outputId).set(currentId, 0.7);
            }
          }
        } else if (i < layerIds.length - 1) {
          // Default sequential connection to next layer
          const nextId = layerIds[i + 1];
          
          // Strong forward dependency
          dependencies.get(currentId).set(nextId, 0.95);
          
          // Moderate backward dependency
          dependencies.get(nextId).set(currentId, 0.75);
        }
      }
    }
    
    /**
     * Analyze computational dependencies like shared weights or attention mechanisms
     * @private
     * @param {Array<string>} layerIds - Layer IDs to analyze
     * @param {Array<Object>} layers - Layer configurations
     * @param {Map<string, Map<string, number>>} dependencies - Dependency map to update
     */
    _analyzeComputationalDependencies(layerIds, layers, dependencies) {
      // Find layers with shared weights or parameters
      const sharedParams = new Map();
      
      // Group layers by shared parameter groups
      for (let i = 0; i < layerIds.length; i++) {
        const layer = layers[i];
        const layerId = layerIds[i];
        
        // Check if this layer has a shared parameter group
        if (layer.sharedParams) {
          if (!sharedParams.has(layer.sharedParams)) {
            sharedParams.set(layer.sharedParams, []);
          }
          sharedParams.get(layer.sharedParams).push(layerId);
        }
        
        // Handle special layer types with computational dependencies
        if (layer.type === 'attention' && layer.attendsTo) {
          // Attention mechanisms create dependencies with attended layers
          const attendedLayers = Array.isArray(layer.attendsTo) ? 
            layer.attendsTo : [layer.attendsTo];
            
          for (const attendedId of attendedLayers) {
            if (layerIds.includes(attendedId)) {
              // Add strong bidirectional dependency for attention mechanisms
              dependencies.get(layerId).set(attendedId, 0.85);
              dependencies.get(attendedId).set(layerId, 0.85);
            }
          }
        }
      }
      
      // Create strong dependencies between layers that share parameters
      for (const [group, memberIds] of sharedParams.entries()) {
        if (memberIds.length > 1) {
          // Create a fully connected graph between these layers
          for (let i = 0; i < memberIds.length; i++) {
            for (let j = i + 1; j < memberIds.length; j++) {
              // Very strong bidirectional dependency for shared parameters
              dependencies.get(memberIds[i]).set(memberIds[j], 0.95); 
              dependencies.get(memberIds[j]).set(memberIds[i], 0.95);
            }
          }
        }
      }
    }
    
    /**
     * Analyze gradient flow dependencies for backpropagation
     * @private
     * @param {Array<string>} layerIds - Layer IDs to analyze
     * @param {Array<Object>} layers - Layer configurations
     * @param {Map<string, Map<string, number>>} dependencies - Dependency map to update
     */
    _analyzeGradientDependencies(layerIds, layers, dependencies) {
      // Layers closer to the loss function have gradient dependencies
      // with earlier layers that affect their inputs
      
      // Find output layers (typically those without outgoing connections)
      const outputLayerIndices = [];
      
      for (let i = 0; i < layerIds.length; i++) {
        const layerId = layerIds[i];
        let hasOutgoing = false;
        
        // Check if this layer has outgoing connections
        for (let j = 0; j < layerIds.length; j++) {
          if (i !== j && dependencies.get(layerId).has(layerIds[j])) {
            hasOutgoing = true;
            break;
          }
        }
        
        if (!hasOutgoing || layers[i].isOutput) {
          outputLayerIndices.push(i);
        }
      }
      
      // If no output layers identified, assume the last layer is output
      if (outputLayerIndices.length === 0 && layerIds.length > 0) {
        outputLayerIndices.push(layerIds.length - 1);
      }
      
      // For each output layer, add gradient dependencies with earlier layers
      for (const outputIndex of outputLayerIndices) {
        const outputId = layerIds[outputIndex];
        
        // Gradient strength diminishes with layer distance
        for (let i = outputIndex - 1; i >= 0; i--) {
          const earlierId = layerIds[i];
          const distance = outputIndex - i;
          
          // Gradient dependency strength diminishes with distance
          // but is still significant for optimization
          const gradientStrength = Math.max(0.5, 0.9 - (distance * 0.1));
          
          // Add or update backward dependency for gradient flow
          const currentDep = dependencies.get(outputId).get(earlierId) || 0;
          dependencies.get(outputId).set(earlierId, Math.max(currentDep, gradientStrength));
        }
      }
    }
    
    /**
     * Analyze skip connections and residual paths
     * @private
     * @param {Array<string>} layerIds - Layer IDs to analyze
     * @param {Array<Object>} layers - Layer configurations
     * @param {Map<string, Map<string, number>>} dependencies - Dependency map to update
     */
    _analyzeSkipConnections(layerIds, layers, dependencies) {
      // Check for skip connections or residual connections
      for (let i = 0; i < layerIds.length; i++) {
        const layer = layers[i];
        const layerId = layerIds[i];
        
        // Look for skip connections specified in the layer config
        if (layer.skipConnections) {
          for (const skip of layer.skipConnections) {
            // Skip connections can be specified by layer ID or relative position
            let skipLayerId;
            
            if (typeof skip === 'string') {
              // Direct layer ID reference
              skipLayerId = skip;
            } else if (typeof skip === 'number') {
              // Relative position (negative for previous layers)
              const skipIndex = i + skip;
              if (skipIndex >= 0 && skipIndex < layerIds.length) {
                skipLayerId = layerIds[skipIndex];
              }
            }
            
            if (skipLayerId && layerIds.includes(skipLayerId)) {
              // Add strong direct dependency for skip connection
              dependencies.get(skipLayerId).set(layerId, 0.9);
              dependencies.get(layerId).set(skipLayerId, 0.8);
            }
          }
        }
        
        // Handle residual connections (often used in ResNet-like architectures)
        if (layer.residualConnection) {
          // Residual connections typically span a few layers
          const span = layer.residualSpan || 2;
          const targetIndex = i + span;
          
          if (targetIndex < layerIds.length) {
            const targetId = layerIds[targetIndex];
            
            // Create strong bidirectional dependency for residual connection
            dependencies.get(layerId).set(targetId, 0.9);
            dependencies.get(targetId).set(layerId, 0.9);
          }
        }
      }
    }

    /**
     * Choose target node for consolidation with load balancing
     * @private
     * @param {string} nodeA - First node ID
     * @param {string} nodeB - Second node ID
     * @returns {string} Target node ID
     */
    _chooseTargetNode(nodeA, nodeB) {
      // Calculate computational load for each node
      const nodeALoad = this._calculateNodeLoad(nodeA);
      const nodeBLoad = this._calculateNodeLoad(nodeB);
      
      // Get layer counts for each node
      const layersOnA = this.partitionMap.get(nodeA).layers.length;
      const layersOnB = this.partitionMap.get(nodeB).layers.length;
      
      // Get node capabilities and capacity if available
      const nodeACapacity = this._getNodeCapacity(nodeA);
      const nodeBCapacity = this._getNodeCapacity(nodeB);
      
      // Calculate load relative to capacity
      const nodeARelativeLoad = nodeACapacity > 0 ? nodeALoad / nodeACapacity : nodeALoad;
      const nodeBRelativeLoad = nodeBCapacity > 0 ? nodeBLoad / nodeBCapacity : nodeBLoad;
      
      // Calculate communication impact for both choices
      const commImpactIfA = this._estimateConsolidationCommImpact(nodeA);
      const commImpactIfB = this._estimateConsolidationCommImpact(nodeB);
      
      // Create a weighted score for each node considering multiple factors
      // - Load balance: Prefer less loaded nodes
      // - Capacity: Consider available capacity
      // - Communication: Consider communication efficiency
      // - Coherence: Consider effect on overall coherence
      
      const nodeAScore = (
        // Load balance factor - lower is better
        (1 - nodeARelativeLoad) * 0.4 +
        // Communication impact factor - lower is better
        (1 - commImpactIfA / Math.max(commImpactIfA, commImpactIfB, 1)) * 0.3 +
        // Layer balance factor - choose node with fewer layers when possible
        (layersOnB > layersOnA ? 0.2 : 0) +
        // Capacity utilization - prefer higher capacity nodes
        (nodeACapacity / Math.max(nodeACapacity, nodeBCapacity, 1)) * 0.1
      );
      
      const nodeBScore = (
        // Load balance factor - lower is better
        (1 - nodeBRelativeLoad) * 0.4 +
        // Communication impact factor - lower is better
        (1 - commImpactIfB / Math.max(commImpactIfA, commImpactIfB, 1)) * 0.3 +
        // Layer balance factor - choose node with fewer layers when possible
        (layersOnA > layersOnB ? 0.2 : 0) +
        // Capacity utilization - prefer higher capacity nodes
        (nodeBCapacity / Math.max(nodeACapacity, nodeBCapacity, 1)) * 0.1
      );
      
      // Choose the node with the better score
      Prime.Logger.debug(`Node consolidation scores: ${nodeA}=${nodeAScore.toFixed(3)}, ${nodeB}=${nodeBScore.toFixed(3)}`);
      
      return nodeAScore >= nodeBScore ? nodeA : nodeB;
    }
    
    /**
     * Calculate the computational load of a node
     * @private
     * @param {string} nodeId - Node ID
     * @returns {number} Computational load
     */
    _calculateNodeLoad(nodeId) {
      const node = this.partitionMap.get(nodeId);
      if (!node) return 0;
      
      let totalLoad = 0;
      
      // Calculate load based on all layers assigned to this node
      for (const layerId of node.layers) {
        const layer = this.layerConfig[layerId];
        
        if (!layer || !layer.inputSize || !layer.outputSize) {
          totalLoad += 1; // Default minimal load
          continue;
        }
        
        // Calculate layer load based on computational complexity
        let layerLoad = layer.inputSize * layer.outputSize;
        
        // Adjust based on layer type
        if (layer.type === 'conv') {
          const kernelSize = layer.kernelSize || 3;
          const channels = layer.channels || 1;
          layerLoad *= kernelSize * kernelSize * channels;
        } else if (layer.type === 'attention') {
          layerLoad *= 3; // Attention is computationally expensive
        } else if (layer.type === 'recurrent') {
          const timeSteps = layer.timeSteps || 1;
          layerLoad *= timeSteps;
        }
        
        // Consider memory requirements
        if (layer.memoryIntensive) {
          layerLoad *= 1.5;
        }
        
        totalLoad += layerLoad;
      }
      
      return totalLoad;
    }
    
    /**
     * Get the capacity of a node based on its capabilities
     * @private
     * @param {string} nodeId - Node ID
     * @returns {number} Node capacity
     */
    _getNodeCapacity(nodeId) {
      // In a production environment, this would retrieve actual node
      // capabilities from the cluster manager or hardware metrics
      
      // Default capacity if not explicitly defined
      let capacity = 100;
      
      // Check if we have capacity information in the configuration
      if (this.clusterConfig && this.clusterConfig.nodes) {
        const nodeConfig = this.clusterConfig.nodes[nodeId];
        
        if (nodeConfig && nodeConfig.capacity) {
          capacity = nodeConfig.capacity;
        } else if (nodeConfig && nodeConfig.capabilities) {
          // Calculate capacity based on hardware capabilities
          const cores = nodeConfig.capabilities.cores || 1;
          const memory = nodeConfig.capabilities.memory || 1;
          const gpu = nodeConfig.capabilities.gpu ? 5 : 1;
          
          capacity = cores * memory * gpu * 10;
        }
      }
      
      return capacity;
    }
    
    /**
     * Estimate the communication impact of consolidating to a node
     * @private
     * @param {string} targetNodeId - Target node ID
     * @returns {number} Estimated communication impact
     */
    _estimateConsolidationCommImpact(targetNodeId) {
      let impact = 0;
      const targetNode = this.partitionMap.get(targetNodeId);
      
      if (!targetNode) return 0;
      
      // For each layer on the target node, calculate comm cost with other nodes
      for (const layerId of targetNode.layers) {
        for (const [otherNodeId, otherNode] of this.partitionMap.entries()) {
          if (otherNodeId === targetNodeId) continue;
          
          for (const otherLayerId of otherNode.layers) {
            // Check if these layers have a dependency
            const layerDeps = this._getLayerDependency(layerId, otherLayerId);
            
            if (layerDeps > 0) {
              // Communication impact is higher for stronger dependencies
              // and for layers with more data to transfer
              const layer = this.layerConfig[layerId];
              const otherLayer = this.layerConfig[otherLayerId];
              
              const transferSize = layer && layer.outputSize ? layer.outputSize : 1;
              impact += layerDeps * transferSize;
            }
          }
        }
      }
      
      return impact;
    }
    
    /**
     * Get dependency strength between two layers
     * @private
     * @param {string} layerId1 - First layer ID
     * @param {string} layerId2 - Second layer ID
     * @returns {number} Dependency strength (0-1)
     */
    _getLayerDependency(layerId1, layerId2) {
      // Check for cached dependency analysis results
      if (this._layerDependencies) {
        const deps1 = this._layerDependencies.get(layerId1);
        if (deps1 && deps1.has(layerId2)) {
          return deps1.get(layerId2);
        }
        
        const deps2 = this._layerDependencies.get(layerId2);
        if (deps2 && deps2.has(layerId1)) {
          return deps2.get(layerId1);
        }
      }
      
      // If no cached results, estimate based on layer configurations
      const layer1 = this.layerConfig[layerId1];
      const layer2 = this.layerConfig[layerId2];
      
      if (!layer1 || !layer2) return 0;
      
      // Check if sequential (direct connection)
      const layerIds = Object.keys(this.layerConfig);
      const index1 = layerIds.indexOf(layerId1);
      const index2 = layerIds.indexOf(layerId2);
      
      if (index1 >= 0 && index2 >= 0) {
        // Direct sequential connection
        if (Math.abs(index1 - index2) === 1) {
          return 0.9;
        }
        
        // Indirect connection (skip connection)
        if (Math.abs(index1 - index2) <= 3) {
          return 0.5;
        }
      }
      
      // Check for explicit connections in layer config
      if (layer1.connections && layer1.connections.some(c => c.to === layerId2)) {
        return 0.8;
      }
      
      if (layer2.connections && layer2.connections.some(c => c.to === layerId1)) {
        return 0.8;
      }
      
      // Low default dependency for unrelated layers
      return 0.1;
    }

    /**
     * Move a layer from its current node to a target node
     * @private
     * @param {string} layerId - Layer ID to move
     * @param {string} targetNodeId - Target node ID
     */
    _moveLayerToNode(layerId, targetNodeId) {
      const currentNodeId = this.layerAssignments.get(layerId);

      if (!currentNodeId || currentNodeId === targetNodeId) {
        return;
      }

      // Remove from current node
      const currentNode = this.partitionMap.get(currentNodeId);
      currentNode.layers = currentNode.layers.filter((id) => id !== layerId);

      // Add to target node
      const targetNode = this.partitionMap.get(targetNodeId);
      targetNode.layers.push(layerId);

      // Update assignment
      this.layerAssignments.set(layerId, targetNodeId);

      Prime.Logger.info(
        `Moved layer ${layerId} from ${currentNodeId} to ${targetNodeId} for coherence optimization`,
      );
    }

    /**
     * Calculate comprehensive coherence score for this partitioning
     * @private
     */
    _calculateCoherenceScore() {
      // Coherence score is a combination of multiple metrics:
      // 1. Load balance: How evenly distributed is computation
      // 2. Layer grouping: How well are related layers grouped together
      // 3. Communication efficiency: How optimized is inter-node communication
      // 4. Tensor dimension alignment: How well aligned are layer dimensions across nodes
      // 5. Gradient flow efficiency: How efficiently gradients can flow during backprop
      
      // Calculate all component scores
      const loadBalanceScore = this._calculateLoadBalanceScore();
      const layerGroupingScore = this._calculateLayerGroupingScore();
      const communicationScore = this._calculateCommunicationScore();
      const dimensionAlignmentScore = this._calculateDimensionAlignmentScore();
      const gradientFlowScore = this._calculateGradientFlowScore();
      
      // Calculate weighted coherence score with most important factors weighted higher
      this.coherenceScore = (
        loadBalanceScore * 0.25 +          // Load balance is critical for performance
        communicationScore * 0.25 +         // Communication overhead significantly affects distributed performance
        layerGroupingScore * 0.2 +          // Layer grouping affects locality and caching
        gradientFlowScore * 0.2 +           // Gradient flow affects training stability
        dimensionAlignmentScore * 0.1       // Dimension alignment affects tensor operations
      );
      
      // Calculate detailed coherence metrics for diagnostics
      this.coherenceMetrics = {
        loadBalance: loadBalanceScore,
        layerGrouping: layerGroupingScore,
        communication: communicationScore,
        dimensionAlignment: dimensionAlignmentScore,
        gradientFlow: gradientFlowScore
      };
      
      Prime.Logger.info(
        `Partitioning coherence score: ${this.coherenceScore.toFixed(4)}`,
        {
          loadBalance: loadBalanceScore.toFixed(4),
          layerGrouping: layerGroupingScore.toFixed(4),
          communication: communicationScore.toFixed(4),
          dimensionAlignment: dimensionAlignmentScore.toFixed(4),
          gradientFlow: gradientFlowScore.toFixed(4)
        },
      );
    }
    
    /**
     * Calculate communication efficiency score
     * @private
     * @returns {number} Score between 0 and 1
     */
    _calculateCommunicationScore() {
      // Calculate communication costs
      const commCosts = this._calculateCommunicationCosts();
      
      // If there are no cross-node dependencies, perfect score
      if (commCosts.crossLayerCount === 0) {
        return 1.0;
      }
      
      // Get layer dependency information for normalization
      const layerIds = Object.keys(this.layerConfig);
      const totalPossibleCrossings = layerIds.length - 1;
      
      if (totalPossibleCrossings <= 0) {
        return 1.0;
      }
      
      // Calculate normalized crossing ratio (how many layers cross node boundaries)
      const crossingRatio = commCosts.crossLayerCount / totalPossibleCrossings;
      
      // Calculate bandwidth utilization score
      // Lower is better - normalized to 0-1 range
      const bandwidthScore = Math.max(0, 1 - (commCosts.total / (totalPossibleCrossings * 100)));
      
      // Calculate link contention score
      // Measure how evenly distributed communication is across links
      const linkCount = commCosts.nodeToNode.size;
      const linkValues = Array.from(commCosts.nodeToNode.values())
        .flatMap(targetMap => Array.from(targetMap.values()))
        .filter(val => val > 0);
      
      // Calculate coefficient of variation for link loads (lower is better)
      let linkContention = 0;
      if (linkValues.length > 1) {
        const mean = linkValues.reduce((sum, val) => sum + val, 0) / linkValues.length;
        const variance = linkValues.reduce((sum, val) => sum + Math.pow(val - mean, 2), 0) / linkValues.length;
        const stdDev = Math.sqrt(variance);
        const cv = mean > 0 ? stdDev / mean : 0;
        
        // Convert to 0-1 score (lower CV is better)
        linkContention = Math.max(0, 1 - cv);
      } else {
        // If only one link or no links, no contention
        linkContention = 1.0;
      }
      
      // Combine scores with appropriate weights
      return (
        (1 - crossingRatio) * 0.4 +  // Fewer crossings is better
        bandwidthScore * 0.3 +       // Lower bandwidth usage is better
        linkContention * 0.3         // More even link distribution is better
      );
    }
    
    /**
     * Calculate tensor dimension alignment score
     * @private
     * @returns {number} Score between 0 and 1
     */
    _calculateDimensionAlignmentScore() {
      const layerIds = Object.keys(this.layerConfig);
      let alignmentScore = 1.0;
      let edgeCount = 0;
      
      // For each pair of connected layers that span nodes, check dimension alignment
      for (let i = 0; i < layerIds.length - 1; i++) {
        const currentLayerId = layerIds[i];
        const nextLayerId = layerIds[i + 1];
        
        const currentNodeId = this.layerAssignments.get(currentLayerId);
        const nextNodeId = this.layerAssignments.get(nextLayerId);
        
        // Skip if not crossing node boundaries
        if (!currentNodeId || !nextNodeId || currentNodeId === nextNodeId) {
          continue;
        }
        
        // Get layer configurations
        const currentLayer = this.layerConfig[currentLayerId];
        const nextLayer = this.layerConfig[nextLayerId];
        
        if (!currentLayer || !nextLayer) {
          continue;
        }
        
        // Check dimension alignment at the boundary
        // For neural nets, output of one layer should match input of the next
        const outputSize = currentLayer.outputSize || 0;
        const inputSize = nextLayer.inputSize || 0;
        
        // Perfect alignment is when output size matches input size exactly
        if (outputSize > 0 && inputSize > 0) {
          const alignmentRatio = Math.min(outputSize, inputSize) / Math.max(outputSize, inputSize);
          alignmentScore -= (1 - alignmentRatio) * 0.1; // Penalize misalignment
          edgeCount++;
        }
        
        // Check for special case alignment issues
        if (currentLayer.type === 'conv' && nextLayer.type !== 'conv' && 
            nextLayer.type !== 'pooling' && !nextLayer.acceptsConvInput) {
          // Penalize conv to non-conv transitions across nodes (often require reshape)
          alignmentScore -= 0.1;
        }
      }
      
      // Normalize score to ensure it stays in 0-1 range
      return Math.max(0, Math.min(1, alignmentScore));
    }
    
    /**
     * Calculate gradient flow efficiency score
     * @private
     * @returns {number} Score between 0 and 1
     */
    _calculateGradientFlowScore() {
      const layerIds = Object.keys(this.layerConfig);
      
      // 1. Find output layers (for gradient source)
      const outputLayerIndices = [];
      
      for (let i = 0; i < layerIds.length; i++) {
        const layer = this.layerConfig[layerIds[i]];
        if (layer && (layer.isOutput || (i === layerIds.length - 1))) {
          outputLayerIndices.push(i);
        }
      }
      
      if (outputLayerIndices.length === 0 && layerIds.length > 0) {
        outputLayerIndices.push(layerIds.length - 1); // Default to last layer
      }
      
      if (outputLayerIndices.length === 0) {
        return 1.0; // No layers to evaluate
      }
      
      // 2. Calculate gradient chain depth for each node
      const nodeGradientChains = new Map();
      
      // Initialize gradient chain lengths
      for (const [nodeId, partition] of this.partitionMap.entries()) {
        nodeGradientChains.set(nodeId, {
          longestChain: 0,
          layerIndices: []
        });
        
        // Find all layers on this node
        for (let i = 0; i < layerIds.length; i++) {
          if (partition.layers.includes(layerIds[i])) {
            nodeGradientChains.get(nodeId).layerIndices.push(i);
          }
        }
      }
      
      // 3. For each output layer, trace backward gradient flow
      for (const outputIndex of outputLayerIndices) {
        const outputNodeId = this.layerAssignments.get(layerIds[outputIndex]);
        
        if (!outputNodeId) continue;
        
        // Track the current gradient chain
        let currentChain = 1;
        let currentNodeId = outputNodeId;
        
        // Trace backward through the network
        for (let i = outputIndex - 1; i >= 0; i--) {
          const layerId = layerIds[i];
          const nodeId = this.layerAssignments.get(layerId);
          
          if (!nodeId) continue;
          
          // If crossing node boundary, reset chain
          if (nodeId !== currentNodeId) {
            // Update longest chain for the previous node
            const nodeChainsData = nodeGradientChains.get(currentNodeId);
            if (nodeChainsData) {
              nodeChainsData.longestChain = Math.max(
                nodeChainsData.longestChain, 
                currentChain
              );
            }
            
            // Start new chain at the new node
            currentChain = 1;
            currentNodeId = nodeId;
          } else {
            // Continue chain within same node
            currentChain++;
          }
        }
        
        // Update final node chain
        const nodeChainsData = nodeGradientChains.get(currentNodeId);
        if (nodeChainsData) {
          nodeChainsData.longestChain = Math.max(
            nodeChainsData.longestChain, 
            currentChain
          );
        }
      }
      
      // 4. Calculate node gradient chain coherence
      let totalLayers = 0;
      let totalChainLength = 0;
      
      for (const [nodeId, chainsData] of nodeGradientChains.entries()) {
        // Longer continuous chains are better for gradient flow
        totalChainLength += chainsData.longestChain;
        totalLayers += chainsData.layerIndices.length;
      }
      
      // Perfect gradient flow would have all layers in a single chain
      const perfectChainLength = layerIds.length;
      
      // Calculate gradient flow efficiency
      if (totalLayers === 0) {
        return 1.0;
      }
      
      const chainRatio = totalChainLength / totalLayers;
      const nodeTransitionCount = totalLayers - totalChainLength;
      
      // Combine factors for final score
      return (
        chainRatio * 0.7 +                               // Longer chains are better
        (1 - nodeTransitionCount / layerIds.length) * 0.3  // Fewer node transitions are better
      );
    }

    /**
     * Calculate load balance score
     * @private
     * @returns {number} Score between 0 and 1
     */
    _calculateLoadBalanceScore() {
      // Calculate computational load per node
      const nodeLoads = new Map();
      let totalLoad = 0;

      for (const [nodeId, partition] of this.partitionMap.entries()) {
        let nodeLoad = 0;

        for (const layerId of partition.layers) {
          const layer = this.layerConfig[layerId];

          if (!layer || !layer.inputSize || !layer.outputSize) {
            nodeLoad += 1; // Default weight
            continue;
          }

          // Simple computational load estimate
          const load = layer.inputSize * layer.outputSize;
          nodeLoad += load;
        }

        nodeLoads.set(nodeId, nodeLoad);
        totalLoad += nodeLoad;
      }

      // Perfect load would be equal distribution
      const perfectLoadPerNode = totalLoad / this.nodeCount;

      // Calculate variance from perfect load
      let totalVariance = 0;

      for (const [nodeId, load] of nodeLoads.entries()) {
        const variance = Math.pow(load - perfectLoadPerNode, 2);
        totalVariance += variance;
      }

      // Normalize variance and convert to score (0-1)
      if (totalLoad === 0) {
        return 1.0; // No load, perfect balance
      }

      const normalizedVariance = Math.sqrt(totalVariance) / perfectLoadPerNode;
      return Math.max(0, 1 - normalizedVariance);
    }

    /**
     * Calculate layer grouping score
     * @private
     * @returns {number} Score between 0 and 1
     */
    _calculateLayerGroupingScore() {
      // For sequential networks, we want adjacent layers on the same node
      // to minimize communication overhead
      const layerIds = Object.keys(this.layerConfig);
      let adjacentLayersOnSameNode = 0;
      const totalAdjacentPairs = layerIds.length - 1;

      if (totalAdjacentPairs <= 0) {
        return 1.0; // No adjacent pairs to evaluate
      }

      for (let i = 0; i < layerIds.length - 1; i++) {
        const currentLayerId = layerIds[i];
        const nextLayerId = layerIds[i + 1];

        const currentNodeId = this.layerAssignments.get(currentLayerId);
        const nextNodeId = this.layerAssignments.get(nextLayerId);

        if (currentNodeId && nextNodeId && currentNodeId === nextNodeId) {
          adjacentLayersOnSameNode++;
        }
      }

      return adjacentLayersOnSameNode / totalAdjacentPairs;
    }

    /**
     * Get the node ID assigned to a specific layer
     * @param {string} layerId - Layer ID to look up
     * @returns {string|null} Assigned node ID or null if not found
     */
    getLayerAssignment(layerId) {
      return this.layerAssignments.get(layerId) || null;
    }

    /**
     * Get all layers assigned to a specific node
     * @param {string} nodeId - Node ID to lookup
     * @returns {Array<string>} Array of layer IDs
     */
    getNodeLayers(nodeId) {
      const partition = this.partitionMap.get(nodeId);
      return partition ? [...partition.layers] : [];
    }

    /**
     * Get data partitioning for a specific node
     * @param {string} nodeId - Node ID to lookup
     * @returns {Object|null} Data partition information
     */
    getNodeDataPartition(nodeId) {
      const partition = this.partitionMap.get(nodeId);
      return partition ? partition.dataIndices : null;
    }

    /**
     * Check if a node is performing partial computations
     * @param {string} nodeId - Node ID to check
     * @returns {boolean} Whether node does partial computations
     */
    isPartialComputation(nodeId) {
      const partition = this.partitionMap.get(nodeId);
      return partition ? !!partition.partialComputation : false;
    }

    /**
     * Get a summary of this partitioning
     * @returns {Object} Partitioning summary
     */
    getSummary() {
      return {
        type: this.type,
        nodeCount: this.nodeCount,
        coherenceScore: this.coherenceScore,
        nodeLayers: Array.from(this.partitionMap.entries()).map(
          ([nodeId, partition]) => ({
            nodeId,
            layerCount: partition.layers.length,
            layers: partition.layers,
            dataPartition: partition.dataIndices,
            partialComputation: partition.partialComputation,
          }),
        ),
      };
    }

    /**
     * Export this partitioning as a configuration object
     * @returns {Object} Serialized partition configuration
     */
    export() {
      return {
        type: this.type,
        nodeCount: this.nodeCount,
        layerAssignments: Array.from(this.layerAssignments.entries()),
        nodePartitions: Array.from(this.partitionMap.entries()),
        coherenceScore: this.coherenceScore,
      };
    }

    /**
     * Create a partition scheme from exported configuration
     * @param {Object} exportedConfig - Exported configuration
     * @returns {PartitionScheme} New partition scheme
     */
    static import(exportedConfig) {
      if (!exportedConfig || !exportedConfig.type) {
        throw new Prime.ValidationError("Invalid exported configuration");
      }

      // Create new scheme with minimal config
      const scheme = new PartitionScheme({
        type: exportedConfig.type,
        nodeCount: exportedConfig.nodeCount || 1,
      });

      // Override automatic partitioning with imported data
      scheme.layerAssignments = new Map(exportedConfig.layerAssignments || []);
      scheme.partitionMap = new Map(exportedConfig.nodePartitions || []);
      scheme.coherenceScore = exportedConfig.coherenceScore || 1.0;

      return scheme;
    }
  }

  /**
   * Distributed layer that implements a sharded neural network layer
   * across multiple computation nodes
   */
  class DistributedLayer {
    /**
     * Create a new distributed layer
     * @param {Object} config - Layer configuration
     * @param {string} config.id - Unique layer identifier
     * @param {Object} config.layerConfig - Base neural layer configuration
     * @param {Array<string>} config.nodeIds - Node IDs for computation
     * @param {Object} [config.partitionScheme] - Partition scheme or null for auto
     */
    constructor(config) {
      if (!Prime.Utils.isObject(config)) {
        throw new Prime.ValidationError(
          "Distributed layer configuration must be an object",
        );
      }

      if (!config.id) {
        throw new Prime.ValidationError("Layer ID is required");
      }

      if (!Prime.Utils.isObject(config.layerConfig)) {
        throw new Prime.ValidationError("Layer configuration is required");
      }

      if (!Array.isArray(config.nodeIds) || config.nodeIds.length === 0) {
        throw new Prime.ValidationError("At least one node ID is required");
      }

      this.id = config.id;
      this.layerConfig = { ...config.layerConfig };
      this.nodeIds = [...config.nodeIds];

      // Create or use partition scheme
      if (config.partitionScheme) {
        this.partitionScheme = config.partitionScheme;
      } else {
        this.partitionScheme = new PartitionScheme({
          type: PartitionType.INTRA_LAYER,
          nodeCount: this.nodeIds.length,
          layerConfig: { [this.id]: this.layerConfig },
        });
      }

      // Task tracking for distributed operations
      this.pendingTasks = new Map();
      this.nextTaskId = 1;

      // Performance metrics
      this.metrics = {
        forwardTime: 0,
        backwardTime: 0,
        completedForwardPasses: 0,
        completedBackwardPasses: 0,
        communicationOverhead: 0,
        coherenceScore: 1.0,
      };

      // Event bus for layer events
      this.eventBus = new EventBus();

      Prime.Logger.info(
        `Created distributed layer ${this.id} across ${this.nodeIds.length} nodes`,
      );
    }

    /**
     * Distribute a forward pass across nodes
     * @param {Array} input - Input data
     * @param {Object} [options={}] - Forward pass options
     * @returns {Promise<Object>} Forward pass result
     */
    async forward(input, options = {}) {
      if (!Array.isArray(input)) {
        throw new Prime.ValidationError("Input must be an array");
      }

      const startTime = performance.now();

      // Create task ID for this forward pass
      const taskId = `forward_${this.id}_${this.nextTaskId++}`;

      try {
        // Determine partitioning strategy
        let result;

        if (this.partitionScheme.type === PartitionType.DATA_PARALLEL) {
          result = await this._forwardDataParallel(input, taskId);
        } else if (this.partitionScheme.type === PartitionType.INTRA_LAYER) {
          result = await this._forwardIntraLayer(input, taskId);
        } else {
          result = await this._forwardLayerWise(input, taskId);
        }

        // Update metrics
        const endTime = performance.now();
        this.metrics.forwardTime =
          0.9 * this.metrics.forwardTime + 0.1 * (endTime - startTime);
        this.metrics.completedForwardPasses++;

        return result;
      } catch (error) {
        Prime.Logger.error(
          `Error in distributed forward pass for layer ${this.id}`,
          error,
        );
        throw error;
      }
    }

    /**
     * Perform forward pass with data parallelism
     * @private
     * @param {Array} input - Input data
     * @param {string} taskId - Task identifier
     * @returns {Promise<Object>} Forward pass result
     */
    async _forwardDataParallel(input, taskId) {
      // Create tasks for each node
      const nodeTasks = [];

      for (let i = 0; i < this.nodeIds.length; i++) {
        const nodeId = this.nodeIds[i];
        const dataPartition = this.partitionScheme.getNodeDataPartition(nodeId);

        // Skip nodes without a data partition
        if (!dataPartition) {
          continue;
        }

        // Create subset of input based on data partition
        const nodeInput = Array.isArray(input[0])
          ? input.slice(dataPartition.start, dataPartition.end)
          : [input.slice(dataPartition.start, dataPartition.end)];

        // Prepare forward task
        const nodeTask = {
          id: `${taskId}_node${i}`,
          type: "forward_pass",
          data: {
            layerConfig: this.layerConfig,
            input: nodeInput,
          },
        };

        // Queue or execute task
        nodeTasks.push(this._executeTask(nodeId, nodeTask));
      }

      // Wait for all nodes to complete
      const nodeResults = await Promise.all(nodeTasks);

      // Combine results
      let combinedActivation = [];
      const combinedCache = { input, z: [] };

      for (const result of nodeResults) {
        if (!result || !result.activation) {
          continue;
        }

        // For data parallel, concatenate activations
        combinedActivation = combinedActivation.concat(result.activation);

        // Combining cache requires special handling
        if (result.cache && result.cache.z) {
          combinedCache.z = combinedCache.z.concat(result.cache.z);
        }
      }

      return {
        activation: combinedActivation,
        cache: combinedCache,
      };
    }

    /**
     * Perform forward pass with intra-layer parallelism
     * @private
     * @param {Array} input - Input data
     * @param {string} taskId - Task identifier
     * @returns {Promise<Object>} Forward pass result
     */
    async _forwardIntraLayer(input, taskId) {
      // Create tasks for each node
      const nodeTasks = [];

      for (let i = 0; i < this.nodeIds.length; i++) {
        const nodeId = this.nodeIds[i];
        const layerAssignment = this.partitionScheme.getLayerAssignment(
          `${this.id}_${i}`,
        );

        // Skip nodes without an assignment
        if (!layerAssignment) {
          continue;
        }

        // Get output range for this node
        let outputRange = [0, this.layerConfig.outputSize];

        // Check for slicing information
        if (
          typeof layerAssignment === "object" &&
          layerAssignment.outputRange
        ) {
          outputRange = layerAssignment.outputRange;
        }

        // Create partial layer config with reduced outputs
        const nodeConfig = { ...this.layerConfig };
        nodeConfig.originalOutputSize = this.layerConfig.outputSize;
        nodeConfig.outputSize = outputRange[1] - outputRange[0];
        nodeConfig.outputOffset = outputRange[0];

        // Prepare forward task
        const nodeTask = {
          id: `${taskId}_node${i}`,
          type: "forward_pass",
          data: {
            layerConfig: nodeConfig,
            input,
            outputRange,
          },
        };

        // Queue or execute task
        nodeTasks.push(this._executeTask(nodeId, nodeTask));
      }

      // Wait for all nodes to complete
      const nodeResults = await Promise.all(nodeTasks);

      // Combine results
      const combinedActivation = new Array(this.layerConfig.outputSize).fill(0);
      const combinedCache = {
        input,
        z: new Array(this.layerConfig.outputSize).fill(0),
      };

      for (const result of nodeResults) {
        if (!result || !result.activation) {
          continue;
        }

        // Determine where to place this node's outputs
        let outputOffset = 0;

        if (result.outputRange) {
          outputOffset = result.outputRange[0];
        }

        // Copy activations to the right place
        for (let i = 0; i < result.activation.length; i++) {
          combinedActivation[outputOffset + i] = result.activation[i];
        }

        // Copy cache data
        if (result.cache && result.cache.z) {
          for (let i = 0; i < result.cache.z.length; i++) {
            combinedCache.z[outputOffset + i] = result.cache.z[i];
          }
        }
      }

      return {
        activation: combinedActivation,
        cache: combinedCache,
      };
    }

    /**
     * Perform forward pass with layer-wise parallelism
     * @private
     * @param {Array} input - Input data
     * @param {string} taskId - Task identifier
     * @returns {Promise<Object>} Forward pass result
     */
    async _forwardLayerWise(input, taskId) {
      // Find node for this layer
      const nodeId = this.partitionScheme.getLayerAssignment(this.id);

      if (!nodeId) {
        throw new Prime.ValidationError(
          `No node assigned for layer ${this.id}`,
        );
      }

      // Prepare forward task
      const nodeTask = {
        id: taskId,
        type: "forward_pass",
        data: {
          layerConfig: this.layerConfig,
          input,
        },
      };

      // Execute task on single node
      const result = await this._executeTask(nodeId, nodeTask);

      return {
        activation: result.activation,
        cache: result.cache,
      };
    }

    /**
     * Distribute a backward pass across nodes
     * @param {Array} gradOutput - Gradient of loss with respect to output
     * @param {Object} cache - Cache from forward pass
     * @param {Object} [options={}] - Backward pass options
     * @returns {Promise<Object>} Backward pass result with gradients
     */
    async backward(gradOutput, cache, options = {}) {
      if (!Array.isArray(gradOutput)) {
        throw new Prime.ValidationError("Gradient output must be an array");
      }

      if (!Prime.Utils.isObject(cache)) {
        throw new Prime.ValidationError("Cache must be an object");
      }

      const startTime = performance.now();

      // Create task ID for this backward pass
      const taskId = `backward_${this.id}_${this.nextTaskId++}`;

      try {
        // Determine partitioning strategy
        let result;

        if (this.partitionScheme.type === PartitionType.DATA_PARALLEL) {
          result = await this._backwardDataParallel(gradOutput, cache, taskId);
        } else if (this.partitionScheme.type === PartitionType.INTRA_LAYER) {
          result = await this._backwardIntraLayer(gradOutput, cache, taskId);
        } else {
          result = await this._backwardLayerWise(gradOutput, cache, taskId);
        }

        // Update metrics
        const endTime = performance.now();
        this.metrics.backwardTime =
          0.9 * this.metrics.backwardTime + 0.1 * (endTime - startTime);
        this.metrics.completedBackwardPasses++;

        return result;
      } catch (error) {
        Prime.Logger.error(
          `Error in distributed backward pass for layer ${this.id}`,
          error,
        );
        throw error;
      }
    }

    /**
     * Perform backward pass with data parallelism
     * @private
     * @param {Array} gradOutput - Gradient of loss with respect to output
     * @param {Object} cache - Cache from forward pass
     * @param {string} taskId - Task identifier
     * @returns {Promise<Object>} Backward pass result
     */
    async _backwardDataParallel(gradOutput, cache, taskId) {
      // Create tasks for each node
      const nodeTasks = [];

      for (let i = 0; i < this.nodeIds.length; i++) {
        const nodeId = this.nodeIds[i];
        const dataPartition = this.partitionScheme.getNodeDataPartition(nodeId);

        // Skip nodes without a data partition
        if (!dataPartition) {
          continue;
        }

        // Create subset of gradients and cache based on data partition
        const nodeGradOutput = Array.isArray(gradOutput[0])
          ? gradOutput.slice(dataPartition.start, dataPartition.end)
          : [gradOutput.slice(dataPartition.start, dataPartition.end)];

        const nodeCache = {
          input: Array.isArray(cache.input[0])
            ? cache.input.slice(dataPartition.start, dataPartition.end)
            : [cache.input.slice(dataPartition.start, dataPartition.end)],
          z: Array.isArray(cache.z[0])
            ? cache.z.slice(dataPartition.start, dataPartition.end)
            : [cache.z.slice(dataPartition.start, dataPartition.end)],
        };

        // Prepare backward task
        const nodeTask = {
          id: `${taskId}_node${i}`,
          type: "backward_pass",
          data: {
            layerConfig: this.layerConfig,
            gradOutput: nodeGradOutput,
            cache: nodeCache,
          },
        };

        // Queue or execute task
        nodeTasks.push(this._executeTask(nodeId, nodeTask));
      }

      // Wait for all nodes to complete
      const nodeResults = await Promise.all(nodeTasks);

      // Aggregate gradients (average across nodes)
      const dW = Array.isArray(this.layerConfig.weights)
        ? JSON.parse(JSON.stringify(this.layerConfig.weights))
        : Array.from({ length: this.layerConfig.outputSize }, () =>
            Array(this.layerConfig.inputSize).fill(0),
          );

      const dB = new Array(this.layerConfig.outputSize).fill(0);
      const dX = new Array(this.layerConfig.inputSize).fill(0);

      // Helper functions for numerical stability
      const isStable = (value) =>
        Number.isFinite(value) && !Number.isNaN(value);

      const clipValue = (value, maxAbs = 1e6) => {
        if (!isStable(value)) return 0;
        return Math.max(-maxAbs, Math.min(maxAbs, value));
      };

      // Compensation arrays for Kahan summation to reduce floating point error
      const dWCompensation = Array.from({ length: dW.length }, () =>
        new Array(dW[0].length).fill(0),
      );
      const dBCompensation = new Array(dB.length).fill(0);
      const dXCompensation = new Array(dX.length).fill(0);

      // Scale factor for averaging
      const scaleFactor = 1 / Math.max(1, nodeResults.length);

      // Combine gradients from all nodes with numerical stability enhancements
      for (const result of nodeResults) {
        if (!result || !result.gradients) {
          continue;
        }

        // Add weight gradients with Kahan summation for better precision
        if (result.gradients.dW && Array.isArray(result.gradients.dW)) {
          for (
            let i = 0;
            i < dW.length && i < result.gradients.dW.length;
            i++
          ) {
            if (Array.isArray(result.gradients.dW[i])) {
              for (
                let j = 0;
                j < dW[i].length && j < result.gradients.dW[i].length;
                j++
              ) {
                // Clip value for numerical stability
                const value =
                  clipValue(result.gradients.dW[i][j]) * scaleFactor;

                // Kahan summation to reduce floating point error
                const y = value - dWCompensation[i][j];
                const t = dW[i][j] + y;
                dWCompensation[i][j] = t - dW[i][j] - y;
                dW[i][j] = t;
              }
            }
          }
        }

        // Add bias gradients with stability checks
        if (result.gradients.dB && Array.isArray(result.gradients.dB)) {
          for (
            let i = 0;
            i < dB.length && i < result.gradients.dB.length;
            i++
          ) {
            // Clip value for numerical stability
            const value = clipValue(result.gradients.dB[i]) * scaleFactor;

            // Kahan summation to reduce floating point error
            const y = value - dBCompensation[i];
            const t = dB[i] + y;
            dBCompensation[i] = t - dB[i] - y;
            dB[i] = t;
          }
        }

        // Add input gradients with stability checks
        if (result.gradients.dX && Array.isArray(result.gradients.dX)) {
          for (
            let i = 0;
            i < dX.length && i < result.gradients.dX.length;
            i++
          ) {
            // Clip value for numerical stability
            const value = clipValue(result.gradients.dX[i]) * scaleFactor;

            // Kahan summation to reduce floating point error
            const y = value - dXCompensation[i];
            const t = dX[i] + y;
            dXCompensation[i] = t - dX[i] - y;
            dX[i] = t;
          }
        }
      }

      return { dW, dB, dX };
    }

    /**
     * Perform backward pass with intra-layer parallelism
     * @private
     * @param {Array} gradOutput - Gradient of loss with respect to output
     * @param {Object} cache - Cache from forward pass
     * @param {string} taskId - Task identifier
     * @returns {Promise<Object>} Backward pass result
     */
    async _backwardIntraLayer(gradOutput, cache, taskId) {
      // Create tasks for each node
      const nodeTasks = [];

      for (let i = 0; i < this.nodeIds.length; i++) {
        const nodeId = this.nodeIds[i];
        const layerAssignment = this.partitionScheme.getLayerAssignment(
          `${this.id}_${i}`,
        );

        // Skip nodes without an assignment
        if (!layerAssignment) {
          continue;
        }

        // Get output range for this node
        let outputRange = [0, this.layerConfig.outputSize];

        // Check for slicing information
        if (
          typeof layerAssignment === "object" &&
          layerAssignment.outputRange
        ) {
          outputRange = layerAssignment.outputRange;
        }

        // Create partial layer config with reduced outputs
        const nodeConfig = { ...this.layerConfig };
        nodeConfig.originalOutputSize = this.layerConfig.outputSize;
        nodeConfig.outputSize = outputRange[1] - outputRange[0];
        nodeConfig.outputOffset = outputRange[0];

        // Slice gradOutput for this node
        const nodeGradOutput = gradOutput.slice(outputRange[0], outputRange[1]);

        // Slice cache z for this node
        const nodeCache = { ...cache };
        nodeCache.z = cache.z.slice(outputRange[0], outputRange[1]);

        // Prepare backward task
        const nodeTask = {
          id: `${taskId}_node${i}`,
          type: "backward_pass",
          data: {
            layerConfig: nodeConfig,
            gradOutput: nodeGradOutput,
            cache: nodeCache,
            outputRange,
          },
        };

        // Queue or execute task
        nodeTasks.push(this._executeTask(nodeId, nodeTask));
      }

      // Wait for all nodes to complete
      const nodeResults = await Promise.all(nodeTasks);

      // Initialize combined gradients
      const dW = Array.from({ length: this.layerConfig.outputSize }, () =>
        Array(this.layerConfig.inputSize).fill(0),
      );
      const dB = new Array(this.layerConfig.outputSize).fill(0);
      const dX = new Array(this.layerConfig.inputSize).fill(0);

      // Helper functions for numerical stability
      const isStable = (value) =>
        Number.isFinite(value) && !Number.isNaN(value);

      const clipValue = (value, maxAbs = 1e6) => {
        if (!isStable(value)) return 0;
        return Math.max(-maxAbs, Math.min(maxAbs, value));
      };

      // Compensation arrays for Kahan summation to reduce floating point error
      const dXCompensation = new Array(dX.length).fill(0);

      // Combine results from all nodes with numerical stability checks
      for (const result of nodeResults) {
        if (!result || !result.gradients) {
          continue;
        }

        // Determine where to place this node's gradients
        let outputOffset = 0;

        if (result.outputRange) {
          outputOffset = result.outputRange[0];
        }

        // Copy weight gradients to the right place with stability checks
        if (result.gradients.dW && Array.isArray(result.gradients.dW)) {
          for (let i = 0; i < result.gradients.dW.length; i++) {
            if (Array.isArray(result.gradients.dW[i])) {
              for (let j = 0; j < result.gradients.dW[i].length; j++) {
                if (
                  outputOffset + i < dW.length &&
                  j < dW[outputOffset + i].length
                ) {
                  dW[outputOffset + i][j] = clipValue(
                    result.gradients.dW[i][j],
                  );
                }
              }
            }
          }
        }

        // Copy bias gradients with stability checks
        if (result.gradients.dB && Array.isArray(result.gradients.dB)) {
          for (let i = 0; i < result.gradients.dB.length; i++) {
            if (outputOffset + i < dB.length) {
              dB[outputOffset + i] = clipValue(result.gradients.dB[i]);
            }
          }
        }

        // Add input gradients (all nodes contribute to full dX) with Kahan summation
        if (result.gradients.dX && Array.isArray(result.gradients.dX)) {
          for (
            let i = 0;
            i < dX.length && i < result.gradients.dX.length;
            i++
          ) {
            // Use Kahan summation algorithm for better numerical stability
            const value = clipValue(result.gradients.dX[i]);
            const y = value - dXCompensation[i];
            const t = dX[i] + y;
            dXCompensation[i] = t - dX[i] - y;
            dX[i] = t;
          }
        }
      }

      return { dW, dB, dX };
    }

    /**
     * Perform backward pass with layer-wise parallelism
     * @private
     * @param {Array} gradOutput - Gradient of loss with respect to output
     * @param {Object} cache - Cache from forward pass
     * @param {string} taskId - Task identifier
     * @returns {Promise<Object>} Backward pass result
     */
    async _backwardLayerWise(gradOutput, cache, taskId) {
      // Find node for this layer
      const nodeId = this.partitionScheme.getLayerAssignment(this.id);

      if (!nodeId) {
        throw new Prime.ValidationError(
          `No node assigned for layer ${this.id}`,
        );
      }

      // Prepare backward task
      const nodeTask = {
        id: taskId,
        type: "backward_pass",
        data: {
          layerConfig: this.layerConfig,
          gradOutput,
          cache,
        },
      };

      // Execute task on single node
      const result = await this._executeTask(nodeId, nodeTask);

      // Ensure numerical stability in result gradients
      if (result && result.gradients) {
        // Helper functions for numerical stability
        const isStable = (value) =>
          Number.isFinite(value) && !Number.isNaN(value);

        const clipValue = (value, maxAbs = 1e6) => {
          if (!isStable(value)) return 0;
          return Math.max(-maxAbs, Math.min(maxAbs, value));
        };

        // Apply numerical stability to weight gradients
        if (result.gradients.dW && Array.isArray(result.gradients.dW)) {
          for (let i = 0; i < result.gradients.dW.length; i++) {
            if (Array.isArray(result.gradients.dW[i])) {
              for (let j = 0; j < result.gradients.dW[i].length; j++) {
                result.gradients.dW[i][j] = clipValue(
                  result.gradients.dW[i][j],
                );
              }
            }
          }
        }

        // Apply numerical stability to bias gradients
        if (result.gradients.dB && Array.isArray(result.gradients.dB)) {
          for (let i = 0; i < result.gradients.dB.length; i++) {
            result.gradients.dB[i] = clipValue(result.gradients.dB[i]);
          }
        }

        // Apply numerical stability to input gradients
        if (result.gradients.dX && Array.isArray(result.gradients.dX)) {
          for (let i = 0; i < result.gradients.dX.length; i++) {
            result.gradients.dX[i] = clipValue(result.gradients.dX[i]);
          }
        }
      }

      return {
        dW: result.gradients.dW,
        dB: result.gradients.dB,
        dX: result.gradients.dX,
      };
    }

    /**
     * Update layer parameters across all nodes
     * @param {Object} gradients - Weight and bias gradients
     * @param {number} learningRate - Learning rate for update
     * @returns {Promise<void>} Promise that resolves when update is complete
     */
    async update(gradients, learningRate) {
      // Create task ID for this update
      const taskId = `update_${this.id}_${this.nextTaskId++}`;

      try {
        if (this.partitionScheme.type === PartitionType.DATA_PARALLEL) {
          // For data parallel, we need to update all nodes with the same gradients
          const updateTasks = [];

          for (const nodeId of this.nodeIds) {
            const updateTask = {
              id: `${taskId}_${nodeId}`,
              type: "weight_update",
              data: {
                layerConfig: this.layerConfig,
                gradients,
                learningRate,
              },
            };

            updateTasks.push(this._executeTask(nodeId, updateTask));
          }

          // Wait for all updates to complete
          await Promise.all(updateTasks);
        } else if (this.partitionScheme.type === PartitionType.INTRA_LAYER) {
          // For intra-layer, we need to update each node with its part of the gradients
          const updateTasks = [];

          for (let i = 0; i < this.nodeIds.length; i++) {
            const nodeId = this.nodeIds[i];
            const layerAssignment = this.partitionScheme.getLayerAssignment(
              `${this.id}_${i}`,
            );

            // Skip nodes without an assignment
            if (!layerAssignment) {
              continue;
            }

            // Get output range for this node
            let outputRange = [0, this.layerConfig.outputSize];

            // Check for slicing information
            if (
              typeof layerAssignment === "object" &&
              layerAssignment.outputRange
            ) {
              outputRange = layerAssignment.outputRange;
            }

            // Slice gradients for this node
            const nodeGradients = {
              dW: gradients.dW.slice(outputRange[0], outputRange[1]),
              dB: gradients.dB.slice(outputRange[0], outputRange[1]),
            };

            // Create partial layer config
            const nodeConfig = { ...this.layerConfig };
            nodeConfig.originalOutputSize = this.layerConfig.outputSize;
            nodeConfig.outputSize = outputRange[1] - outputRange[0];
            nodeConfig.outputOffset = outputRange[0];

            const updateTask = {
              id: `${taskId}_${nodeId}`,
              type: "weight_update",
              data: {
                layerConfig: nodeConfig,
                gradients: nodeGradients,
                learningRate,
                outputRange,
              },
            };

            updateTasks.push(this._executeTask(nodeId, updateTask));
          }

          // Wait for all updates to complete
          await Promise.all(updateTasks);
        } else {
          // For layer-wise, we only need to update the node assigned to this layer
          const nodeId = this.partitionScheme.getLayerAssignment(this.id);

          if (!nodeId) {
            throw new Prime.ValidationError(
              `No node assigned for layer ${this.id}`,
            );
          }

          const updateTask = {
            id: taskId,
            type: "weight_update",
            data: {
              layerConfig: this.layerConfig,
              gradients,
              learningRate,
            },
          };

          await this._executeTask(nodeId, updateTask);
        }

        // After update, synchronize state across nodes
        await this._synchronizeState();
      } catch (error) {
        Prime.Logger.error(
          `Error updating distributed layer ${this.id}`,
          error,
        );
        throw error;
      }
    }

    /**
     * Synchronize layer state across all nodes
     * @private
     * @returns {Promise<void>} Promise that resolves when sync is complete
     */
    async _synchronizeState() {
      // Skip synchronization for single-node layers
      if (this.nodeIds.length <= 1) {
        return;
      }

      // Use the first node as source of truth
      const sourceNodeId = this.nodeIds[0];

      // Create a coherence check task
      const checkTask = {
        id: `coherence_check_${this.id}_${Date.now()}`,
        type: "coherence_check",
        data: {
          layerConfig: this.layerConfig,
          parameters: {
            weights: this.layerConfig.weights,
            biases: this.layerConfig.biases,
          },
        },
      };

      // Check coherence on source node
      try {
        const coherenceResult = await this._executeTask(
          sourceNodeId,
          checkTask,
        );

        if (coherenceResult && typeof coherenceResult.score === "number") {
          this.metrics.coherenceScore = coherenceResult.score;

          // Only synchronize if coherence is poor
          if (coherenceResult.score < 0.8) {
            await this._forceSynchronize(sourceNodeId);
          }
        }
      } catch (error) {
        Prime.Logger.warn(`Coherence check failed for layer ${this.id}`, error);
        // Continue without synchronization
      }
    }

    /**
     * Force synchronization from a source node to all others
     * @private
     * @param {string} sourceNodeId - Source node ID
     * @returns {Promise<void>} Promise that resolves when sync is complete
     */
    async _forceSynchronize(sourceNodeId) {
      // Skip if source node is not valid
      if (!this.nodeIds.includes(sourceNodeId)) {
        return;
      }

      Prime.Logger.info(
        `Force synchronizing layer ${this.id} from node ${sourceNodeId}`,
      );

      // Get the state snapshot from source node
      const stateSnapshotTask = {
        id: `state_snapshot_${this.id}_${Date.now()}`,
        type: "state_snapshot",
        data: {
          layerId: this.id,
          layerConfig: this.layerConfig,
        },
      };

      let stateSnapshot;
      try {
        stateSnapshot = await this._executeTask(
          sourceNodeId,
          stateSnapshotTask,
        );
      } catch (error) {
        Prime.Logger.error(
          `Failed to get state snapshot from node ${sourceNodeId}`,
          error,
        );
        return;
      }

      if (!stateSnapshot || !stateSnapshot.params) {
        Prime.Logger.error(`Invalid state snapshot from node ${sourceNodeId}`);
        return;
      }

      // Create sync tasks for all other nodes
      const syncTasks = [];

      for (const nodeId of this.nodeIds) {
        // Skip the source node
        if (nodeId === sourceNodeId) {
          continue;
        }

        const syncTask = {
          id: `sync_${this.id}_${nodeId}_${Date.now()}`,
          type: "state_sync",
          data: {
            layerId: this.id,
            params: stateSnapshot.params,
            metadata: {
              sourceNodeId,
              timestamp: Date.now(),
              version: stateSnapshot.version || 1,
              coherenceScore: stateSnapshot.coherenceScore || 1.0,
              syncReason: "forced_sync",
            },
          },
        };

        syncTasks.push(this._executeTask(nodeId, syncTask));
      }

      // Wait for all syncs to complete
      try {
        const results = await Promise.all(syncTasks);

        // Analyze sync results
        let successCount = 0;
        for (const result of results) {
          if (result && result.success) {
            successCount++;
          }
        }

        // Calculate sync rate
        const syncRate = successCount / syncTasks.length;
        Prime.Logger.info(
          `Layer ${this.id} synchronized across ${successCount}/${syncTasks.length} nodes (${(syncRate * 100).toFixed(1)}%)`,
        );

        // Update metrics
        this.metrics.communicationOverhead +=
          (this.nodeIds.length - 1) *
          (stateSnapshot.params ? Object.keys(stateSnapshot.params).length : 1);

        // If we had any failures, update coherence score
        if (syncRate < 1.0) {
          this.metrics.coherenceScore *= syncRate;
        }

        // Check for sync conflicts and resolve if needed
        const conflicts = results.filter((r) => r && r.conflict);
        if (conflicts.length > 0) {
          await this._resolveStateConflicts(conflicts, stateSnapshot);
        }
      } catch (error) {
        Prime.Logger.error(`Error during state synchronization`, error);
        this.metrics.coherenceScore *= 0.8; // Reduce coherence score on error
      }
    }

    /**
     * Resolve state conflicts after synchronization
     * @private
     * @param {Array<Object>} conflicts - List of sync conflicts
     * @param {Object} masterSnapshot - Master state snapshot
     * @returns {Promise<void>} Promise that resolves when conflicts are resolved
     */
    async _resolveStateConflicts(conflicts, masterSnapshot) {
      if (!conflicts || conflicts.length === 0 || !masterSnapshot) {
        return;
      }

      Prime.Logger.warn(
        `Resolving ${conflicts.length} state conflicts for layer ${this.id}`,
      );

      // For each conflict, decide how to resolve
      for (const conflict of conflicts) {
        if (!conflict.nodeId || !conflict.localVersion) {
          continue;
        }

        // Simple resolution strategy: newer version wins
        const masterVersion = masterSnapshot.version || 1;
        const localVersion = conflict.localVersion;

        if (localVersion > masterVersion) {
          // Local version is newer, pull its state and propagate
          Prime.Logger.info(
            `Node ${conflict.nodeId} has newer state (${localVersion} > ${masterVersion}), pulling its state`,
          );

          // This would be a recursive call in full implementation
          // Simplified to avoid complexity
          this.metrics.coherenceScore *= 0.9;
        } else {
          // Master version should win, force sync again
          const resolveTask = {
            id: `resolve_conflict_${this.id}_${conflict.nodeId}_${Date.now()}`,
            type: "force_sync",
            data: {
              layerId: this.id,
              params: masterSnapshot.params,
              overrideLocal: true,
              metadata: {
                resolution: "master_override",
                timestamp: Date.now(),
                version: masterSnapshot.version,
              },
            },
          };

          try {
            await this._executeTask(conflict.nodeId, resolveTask);
            Prime.Logger.debug(`Resolved conflict on node ${conflict.nodeId}`);
          } catch (error) {
            Prime.Logger.error(
              `Failed to resolve conflict on node ${conflict.nodeId}`,
              error,
            );
          }
        }
      }
    }

    /**
     * Execute a task on a specific node using cluster communication
     * @private
     * @param {string} nodeId - Node ID to execute on
     * @param {Object} task - Task to execute
     * @returns {Promise<Object>} Task result
     */
    async _executeTask(nodeId, task) {
      // Use the cluster manager and communication modules to execute the task on the target node
      
      // Create message router if not already created
      if (!this.messageRouter) {
        // Get a unique ID for this partition scheme instance
        const routerId = `partition_${Date.now().toString(36)}_${Math.random().toString(36).substring(2, 7)}`;
        
        // Create message router for communications
        this.messageRouter = new Prime.Distributed.Communication.MessageRouter({
          nodeId: routerId
        });
        
        Prime.Logger.info(`Created message router for partition scheme with ID ${routerId}`);
      }
      
      // Store pending task with promise controls
      return new Promise((resolve, reject) => {
        // Store task in pending map for tracking
        this.pendingTasks.set(task.id, {
          task,
          nodeId,
          startTime: Date.now(),
          resolve,
          reject,
        });
        
        // Task timeout handler
        const timeoutId = setTimeout(() => {
          // Handle timeout if task takes too long
          if (this.pendingTasks.has(task.id)) {
            const pendingTask = this.pendingTasks.get(task.id);
            this.pendingTasks.delete(task.id);
            
            reject(new Prime.TimeoutError(`Task ${task.id} timed out after ${Date.now() - pendingTask.startTime}ms`));
          }
        }, this.taskTimeout || 30000); // Default 30 second timeout
        
        // Send task via message router
        this._sendTaskToNode(nodeId, task).then(result => {
          clearTimeout(timeoutId);
          
          // If task is still pending, resolve it
          if (this.pendingTasks.has(task.id)) {
            this.pendingTasks.delete(task.id);
            resolve(result);
          }
        }).catch(error => {
          clearTimeout(timeoutId);
          
          // If task is still pending, reject it
          if (this.pendingTasks.has(task.id)) {
            this.pendingTasks.delete(task.id);
            reject(error);
          }
        });
      });
    }
    
    /**
     * Send a task to a node using the message router
     * @private
     * @param {string} nodeId - Target node ID
     * @param {Object} task - Task to execute
     * @returns {Promise<Object>} Task result
     */
    async _sendTaskToNode(nodeId, task) {
      try {
        // Check if the node is reachable
        const isAvailable = await this._checkNodeAvailability(nodeId);
        
        if (!isAvailable) {
          throw new Prime.CommunicationError(`Node ${nodeId} is not available for task execution`);
        }
        
        // Create task message based on task type
        const taskMessage = {
          taskId: task.id,
          type: task.type,
          layerId: task.layerId,
          payload: task.data || {},
          timestamp: Date.now(),
          origin: this.messageRouter.nodeId,
          requiresResponse: true
        };
        
        // Send task via communication channel
        const response = await this.messageRouter.request(
          nodeId,
          `task_${task.type}`, // e.g., task_compute, task_sync
          taskMessage,
          {
            timeout: this.taskTimeout || 30000,
            retry: true
          }
        );
        
        // Process response
        if (!response || !response.data) {
          throw new Prime.CommunicationError('Invalid response from node');
        }
        
        return response.data;
      } catch (error) {
        // Handle communication errors
        Prime.Logger.error(`Error sending task to node ${nodeId}`, {
          taskId: task.id,
          taskType: task.type,
          error: error.message
        });
        
        // Determine if we should retry based on error type
        if (error instanceof Prime.CommunicationError) {
          // Retry communication errors if within retry limit
          if (task._retryCount < (this.maxRetries || 3)) {
            Prime.Logger.info(`Retrying task ${task.id} on node ${nodeId} (attempt ${task._retryCount + 1})`);
            
            // Clone task with retry count
            const retryTask = {
              ...task,
              _retryCount: (task._retryCount || 0) + 1
            };
            
            // Use exponential backoff for retries
            const backoffMs = Math.min(100 * Math.pow(2, retryTask._retryCount), 2000);
            await new Promise(resolve => setTimeout(resolve, backoffMs));
            
            // Retry task execution
            return this._sendTaskToNode(nodeId, retryTask);
          }
        }
        
        // If no retry or retry exhausted, throw the error
        throw error;
      }
    }
    
    /**
     * Check if a node is available for communication
     * @private
     * @param {string} nodeId - Node ID to check
     * @returns {Promise<boolean>} Whether the node is available
     */
    async _checkNodeAvailability(nodeId) {
      try {
        // Try to send a lightweight heartbeat message
        const heartbeatResult = await this.messageRouter.route(
          nodeId,
          Prime.Distributed.Communication.MessageType.HEARTBEAT,
          { timestamp: Date.now() },
          { timeout: 5000 }
        );
        
        return heartbeatResult && heartbeatResult.success;
      } catch (error) {
        Prime.Logger.warn(`Node ${nodeId} is not available: ${error.message}`);
        return false;
      }
    }

    /**
     * Simulate execution of a task on a node
     * @private
     * @param {string} nodeId - Node ID
     * @param {Object} task - Task to simulate
     * @returns {Object} Simulated result
     */
    _simulateTaskExecution(nodeId, task) {
      // This method simulates what would happen on a real compute node
      switch (task.type) {
        case "forward_pass":
          return this._simulateForwardPass(task.data);
        case "backward_pass":
          return this._simulateBackwardPass(task.data);
        case "weight_update":
          return this._simulateWeightUpdate(task.data);
        case "coherence_check":
          return this._simulateCoherenceCheck(task.data);
        case "state_snapshot":
          return this._getStateSnapshot(nodeId, task.data);
        case "state_sync":
          return this._syncStateWithNode(nodeId, task.data);
        case "force_sync":
          return this._forceSyncWithNode(nodeId, task.data);
        default:
          throw new Error(`Unknown task type: ${task.type}`);
      }
    }

    /**
     * Get a state snapshot from a node
     * @private
     * @param {string} nodeId - Node ID
     * @param {Object} data - Task data
     * @returns {Promise<Object>} State snapshot
     */
    async _getStateSnapshot(nodeId, data) {
      // Request the actual state from the specific node
      const { layerId, layerConfig } = data;

      
      try {
        // Create request for layer state
        const snapshotRequest = {
          layerId,
          requestId: `snapshot_${Date.now()}_${Math.random().toString(36).substring(2, 7)}`,
          format: 'full',  // Request full state
          includeMetadata: true,
          timestamp: Date.now()
        };
        
        // Send request through message router
        const response = await this.messageRouter.request(
          nodeId,
          'layer_state_request',
          snapshotRequest,
          { timeout: 10000 }
        );
        
        // Validate response
        if (!response || !response.data || !response.data.state) {
          throw new Prime.CommunicationError('Invalid state snapshot response');
        }
        
        return response.data;
      } catch (error) {
        Prime.Logger.error(`Error getting state snapshot from node ${nodeId} for layer ${layerId}`, {
          error: error.message
        });
        
        // Fall back to local layer state if available
        if (this.layerStates && this.layerStates.has(layerId)) {
          Prime.Logger.warn(`Using cached layer state for ${layerId} due to snapshot failure`);
          return this.layerStates.get(layerId);
        }
        
        // Create minimal state based on layer config as last resort
        return this._createMinimalStateFromConfig(layerId, layerConfig);
      }
    }
    
    /**
     * Create a minimal state object from layer configuration
     * @private
     * @param {string} layerId - Layer ID
     * @param {Object} layerConfig - Layer configuration
     * @returns {Object} Minimal state object
     */
    _createMinimalStateFromConfig(layerId, layerConfig) {
      let weights = null;
      let biases = null;
      
      // Initialize weights based on layer dimensions
      if (layerConfig.inputSize && layerConfig.outputSize) {
        // Create weights with proper initialization based on layer type
        const stdDev = this._calculateWeightInitStdDev(layerConfig);
        
        weights = Array.from({ length: layerConfig.outputSize }, () =>
          Array.from(
            { length: layerConfig.inputSize },
            () => this._generateNormalizedRandom(stdDev)
          )
        );
        
        // Create biases initialized to small values or zeros based on layer type
        const biasInitValue = layerConfig.type === 'conv' ? 0.01 : 0;
        biases = Array.from(
          { length: layerConfig.outputSize },
          () => biasInitValue
        );
      }
      
      // Return the minimal state object
      return {
        layerId,
        state: {
          weights,
          biases,
          activations: null,
          gradients: null
        },
        metadata: {
          version: 1,
          lastUpdateTimestamp: Date.now(),
          isMinimalState: true
        }
      };
    }
    
    /**
     * Calculate standard deviation for weight initialization
     * @private
     * @param {Object} layerConfig - Layer configuration
     * @returns {number} Standard deviation for weight initialization
     */
    _calculateWeightInitStdDev(layerConfig) {
      // Use appropriate initialization method based on layer type and activation
      const fanIn = layerConfig.inputSize || 1;
      const fanOut = layerConfig.outputSize || 1;
      
      if (layerConfig.type === 'conv') {
        // He initialization for conv layers with ReLU
        return Math.sqrt(2 / fanIn);
      } else if (layerConfig.activation === 'relu' || layerConfig.activation === 'leaky_relu') {
        // He initialization for ReLU activation
        return Math.sqrt(2 / fanIn);
      } else if (layerConfig.activation === 'tanh' || layerConfig.activation === 'sigmoid') {
        // Xavier/Glorot initialization for tanh/sigmoid
        return Math.sqrt(6 / (fanIn + fanOut));
      } else {
        // Default to Xavier/Glorot
        return Math.sqrt(2 / (fanIn + fanOut));
      }
    }
    
    /**
     * Generate a random number from a normal distribution
     * @private
     * @param {number} stdDev - Standard deviation
     * @returns {number} Random value
     */
    _generateNormalizedRandom(stdDev) {
      // Box-Muller transform for normal distribution
      const u1 = Math.random();
      const u2 = Math.random();
      
      const z0 = Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math.PI * u2);
      return z0 * stdDev;
    }

    /**
     * Synchronize state with a node
     * @private
     * @param {string} nodeId - Node ID
     * @param {Object} data - Task data
     * @returns {Promise<Object>} Sync result
     */
    async _syncStateWithNode(nodeId, data) {
      // Apply the state to the specific node and return success/failure
      const { layerId, params, metadata } = data;

      // Simulate occasional sync failures or conflicts
      const randomFactor = Math.random();

      // 90% success rate in simulation
      if (randomFactor < 0.9) {
        // Successful sync
        return {
          success: true,
          nodeId,
          layerId,
          syncTimestamp: Date.now(),
          appliedVersion: metadata ? metadata.version : 1,
        };
      } else if (randomFactor < 0.95) {
        // Sync failure
        return {
          success: false,
          nodeId,
          layerId,
          error: "Simulated sync failure",
          errorCode: "SYNC_FAILURE",
        };
      } else {
        // Version conflict
        return {
          success: false,
          nodeId,
          layerId,
          conflict: true,
          localVersion:
            (metadata ? metadata.version : 1) +
            1 +
            Math.floor(Math.random() * 3),
          error: "Version conflict detected",
          errorCode: "VERSION_CONFLICT",
        };
      }
    }

    /**
     * Simulate forced sync on a node
     * @private
     * @param {string} nodeId - Node ID
     * @param {Object} data - Task data
     * @returns {Object} Force sync result
     */
    async _forceSyncWithNode(nodeId, data) {
      // Forcibly apply the state regardless of local version (with safety checks)
      const { layerId, params, overrideLocal, metadata } = data;
      
      try {
        // Create force synchronization message with override flags
        const forceSyncMessage = {
          layerId,
          state: params,
          metadata: {
            ...metadata,
            syncTimestamp: Date.now(),
            sourceNodeId: this.messageRouter.nodeId,
            forcedSync: true
          },
          options: {
            forceUpdate: true,
            overrideVersionCheck: true,
            validateCoherence: overrideLocal !== true, // Skip coherence check if overrideLocal is true
            broadcastChanges: true
          }
        };
        
        // Send force sync message to target node with higher timeout
        const response = await this.messageRouter.request(
          nodeId,
          'layer_state_force_sync',
          forceSyncMessage,
          {
            timeout: 20000, // Longer timeout for force sync
            retry: true
          }
        );
        
        // Process response
        if (!response || !response.data) {
          throw new Prime.CommunicationError('Invalid force sync response from node');
        }
        
        // Handle successful force sync
        if (response.data.success) {
          // Store sync in state history
          this._recordStateUpdate(layerId, nodeId, {
            ...response.data,
            forced: true
          });
          
          // Return force sync result to caller
          return {
            success: true,
            nodeId,
            layerId,
            forcedSync: true,
            overrodeLocal: !!overrideLocal,
            syncTimestamp: response.data.syncTimestamp || Date.now(),
            appliedVersion: response.data.version || (metadata ? metadata.version : 1)
          };
        } else {
          // Handle critical sync failure
          Prime.Logger.error(`Critical failure during forced sync for layer ${layerId} on node ${nodeId}`, {
            errorCode: response.data.errorCode,
            error: response.data.error
          });
          
          return {
            success: false,
            nodeId,
            layerId,
            forcedSync: true,
            error: response.data.error || "Critical error during forced sync",
            errorCode: response.data.errorCode || "CRITICAL_SYNC_FAILURE"
          };
        }
      } catch (error) {
        // Handle communication errors
        Prime.Logger.error(`Error during forced sync with node ${nodeId} for layer ${layerId}`, {
          error: error.message
        });
        
        return {
          success: false,
          nodeId,
          layerId,
          forcedSync: true,
          error: error.message,
          errorCode: error instanceof Prime.CommunicationError ? 
                     "COMMUNICATION_ERROR" : "CRITICAL_SYNC_FAILURE"
        };
      }
    }

    /**
     * Simulate forward pass on a node
     * @private
     * @param {Object} data - Task data
     * @returns {Object} Simulated result
     */
    _simulateForwardPass(data) {
      const { layerConfig, input, outputRange } = data;

      // Ensure Neural module is loaded before use
      if (
        !Prime.Neural ||
        !Prime.Neural.Layer ||
        !Prime.Neural.Layer.NeuralLayer
      ) {
        // This is a critical dependency - ensure proper dependency loading order
        // First load the base layer module
        require("../../neural/layer/index");

        // Then load the main neural module which ties everything together
        require("../../neural/index");

        // After loading, verify again
        if (
          !Prime.Neural ||
          !Prime.Neural.Layer ||
          !Prime.Neural.Layer.NeuralLayer
        ) {
          throw new Error(
            "Neural module not loaded or NeuralLayer not available",
          );
        }
      }

      // Create neural layer instance
      const layer = new Prime.Neural.Layer.NeuralLayer(layerConfig);

      // Perform forward pass
      const result = layer.forward(input);

      // Add output range to result if provided
      if (outputRange) {
        result.outputRange = outputRange;
      }

      return result;
    }

    /**
     * Simulate backward pass on a node
     * @private
     * @param {Object} data - Task data
     * @returns {Object} Simulated result
     */
    _simulateBackwardPass(data) {
      const { layerConfig, gradOutput, cache, outputRange } = data;

      // Ensure Neural module is loaded before use
      if (
        !Prime.Neural ||
        !Prime.Neural.Layer ||
        !Prime.Neural.Layer.NeuralLayer
      ) {
        // This is a critical dependency - we should have proper module loading
        // Try to load the module if not already loaded
        require("../../neural/layer/index");

        // After loading, verify again
        if (
          !Prime.Neural ||
          !Prime.Neural.Layer ||
          !Prime.Neural.Layer.NeuralLayer
        ) {
          throw new Error(
            "Neural module not loaded or NeuralLayer not available",
          );
        }
      }

      // Create neural layer instance
      const layer = new Prime.Neural.Layer.NeuralLayer(layerConfig);

      // Perform backward pass
      const gradients = layer.backward(gradOutput, cache);

      // Add output range to result if provided
      const result = { gradients };
      if (outputRange) {
        result.outputRange = outputRange;
      }

      return result;
    }

    /**
     * Simulate weight update on a node
     * @private
     * @param {Object} data - Task data
     * @returns {Object} Simulated result
     */
    _simulateWeightUpdate(data) {
      const { layerConfig, gradients, learningRate, outputRange } = data;

      // Ensure Neural module is loaded before use
      if (
        !Prime.Neural ||
        !Prime.Neural.Layer ||
        !Prime.Neural.Layer.NeuralLayer
      ) {
        // This is a critical dependency - we should have proper module loading
        // Try to load the module if not already loaded
        require("../../neural/layer/index");

        // After loading, verify again
        if (
          !Prime.Neural ||
          !Prime.Neural.Layer ||
          !Prime.Neural.Layer.NeuralLayer
        ) {
          throw new Error(
            "Neural module not loaded or NeuralLayer not available",
          );
        }
      }

      // Create neural layer instance
      const layer = new Prime.Neural.Layer.NeuralLayer(layerConfig);

      // Apply weight update
      layer.update(gradients, learningRate);

      // Return updated weights and biases
      const result = {
        updatedWeights: layer.weights,
        updatedBiases: layer.biases,
        coherenceScore: layer.getCoherenceScore
          ? layer.getCoherenceScore()
          : 0.9,
      };

      // Add output range to result if provided
      if (outputRange) {
        result.outputRange = outputRange;
      }

      return result;
    }

    /**
     * Simulate coherence check on a node
     * @private
     * @param {Object} data - Task data
     * @returns {Object} Simulated result
     */
    _simulateCoherenceCheck(data) {
      // Ensure Coherence module is loaded before use
      if (
        !Prime.Distributed ||
        !Prime.Distributed.Coherence ||
        !Prime.Distributed.Coherence.DistributedCoherenceManager
      ) {
        // This is a critical dependency - we should have proper module loading
        // Try to load the module if not already loaded
        require("../coherence-core");

        // After loading, verify again
        if (
          !Prime.Distributed ||
          !Prime.Distributed.Coherence ||
          !Prime.Distributed.Coherence.DistributedCoherenceManager
        ) {
          throw new Error(
            "Coherence module not loaded or DistributedCoherenceManager not available",
          );
        }
      }

      // Use the proper coherence checker implementation
      const coherenceManager =
        new Prime.Distributed.Coherence.DistributedCoherenceManager();

      // Extract layer data from task
      const { layer, globalParams } = data;

      // Perform coherence check
      return coherenceManager.checkLayerCoherence(layer, {
        isDistributed: true,
        globalParams,
      });
    }

    /**
     * Get layer metrics
     * @returns {Object} Current metrics
     */
    getMetrics() {
      return { ...this.metrics };
    }

    /**
     * Get the partition scheme for this layer
     * @returns {PartitionScheme} Current partition scheme
     */
    getPartitionScheme() {
      return this.partitionScheme;
    }
  }

  // Add classes to Prime.Distributed namespace
  Prime.Distributed.Partition = {
    PartitionType,
    PartitionScheme,
    DistributedLayer,
  };
})();

// Export the enhanced Prime object
module.exports = Prime;
