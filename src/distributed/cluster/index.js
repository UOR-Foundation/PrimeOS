/**
 * PrimeOS JavaScript Library - Distributed Cluster Module
 * Main entry point for distributed computation functionality
 */

// Import the Prime object from core
const Prime = require("../../core");

// Ensure namespace exists
Prime.Distributed = Prime.Distributed || {};
Prime.Distributed.Cluster = Prime.Distributed.Cluster || {};

// Import cluster components
require("./cluster-nodes");
require("./task-distribution");
require("./partition-manager");

// Make sure the cluster module components are accessible at the correct paths
// ClusterNode
if (
  Prime.Distributed.Cluster.Nodes &&
  Prime.Distributed.Cluster.Nodes.ClusterNode
) {
  Prime.Distributed.Cluster.ClusterNode =
    Prime.Distributed.Cluster.Nodes.ClusterNode;
}

// NodeType and NodeState
if (
  Prime.Distributed.Cluster.Nodes &&
  Prime.Distributed.Cluster.Nodes.NodeType
) {
  Prime.Distributed.Cluster.NodeType = Prime.Distributed.Cluster.Nodes.NodeType;
}

if (
  Prime.Distributed.Cluster.Nodes &&
  Prime.Distributed.Cluster.Nodes.NodeState
) {
  Prime.Distributed.Cluster.NodeState =
    Prime.Distributed.Cluster.Nodes.NodeState;
}

// NodeRegistry (for backward compatibility)
if (
  Prime.Distributed.Cluster.Nodes &&
  Prime.Distributed.Cluster.Nodes.NodeRegistry
) {
  Prime.Distributed.Cluster.NodeRegistry =
    Prime.Distributed.Cluster.Nodes.NodeRegistry;
}

// Tasks module components
if (Prime.Distributed.Cluster.Tasks) {
  // TaskQueue
  if (Prime.Distributed.Cluster.Tasks.TaskQueue) {
    Prime.Distributed.Cluster.TaskQueue =
      Prime.Distributed.Cluster.Tasks.TaskQueue;
  }

  // TaskScheduler
  if (Prime.Distributed.Cluster.Tasks.TaskScheduler) {
    Prime.Distributed.Cluster.TaskScheduler =
      Prime.Distributed.Cluster.Tasks.TaskScheduler;
  }

  // TaskPriority
  if (Prime.Distributed.Cluster.Tasks.TaskPriority) {
    Prime.Distributed.Cluster.TaskPriority =
      Prime.Distributed.Cluster.Tasks.TaskPriority;
  }

  // DistributedTask
  if (Prime.Distributed.Cluster.Tasks.DistributedTask) {
    Prime.Distributed.Cluster.DistributedTask =
      Prime.Distributed.Cluster.Tasks.DistributedTask;
  }
}

// Partition module components
if (Prime.Distributed.Cluster.Partition) {
  // PartitionManager
  if (Prime.Distributed.Cluster.Partition.PartitionManager) {
    Prime.Distributed.Cluster.PartitionManager =
      Prime.Distributed.Cluster.Partition.PartitionManager;
  }

  // PartitionScheme
  if (Prime.Distributed.Cluster.Partition.PartitionScheme) {
    Prime.Distributed.Cluster.PartitionScheme =
      Prime.Distributed.Cluster.Partition.PartitionScheme;
  }

  // PartitionType
  if (Prime.Distributed.Cluster.Partition.PartitionType) {
    Prime.Distributed.Cluster.PartitionType =
      Prime.Distributed.Cluster.Partition.PartitionType;
  }
}

/**
 * Cluster manager for distributed computation
 * Manages nodes, tasks, and partitioning in the distributed system
 */
class ClusterManager {
  /**
   * Create a new cluster manager
   * @param {Object} config - Cluster configuration
   */
  constructor(config = {}) {
    // Create node registry
    this.nodeRegistry = new Prime.Distributed.Cluster.Nodes.NodeRegistry();

    // Create task queue and scheduler
    this.taskQueue = new Prime.Distributed.Cluster.Tasks.TaskQueue();
    this.taskScheduler = new Prime.Distributed.Cluster.Tasks.TaskScheduler({
      taskQueue: this.taskQueue,
      nodeRegistry: this.nodeRegistry,
      schedulingInterval: config.schedulingInterval || 1000,
      maxTasksPerNode: config.maxTasksPerNode || 10,
    });

    // Create partition manager
    this.partitionManager =
      new Prime.Distributed.Cluster.Partition.PartitionManager();

    // Cluster configuration
    this.config = {
      name: config.name || "PrimeOS Cluster",
      coordinatorId: config.coordinatorId || null,
      maxNodes: config.maxNodes || 100,
      autoStart: config.autoStart !== false,
      ...config,
    };

    // Cluster status
    this.status = {
      running: false,
      startedAt: null,
      nodesJoined: 0,
      tasksProcessed: 0,
      lastStatusUpdate: Date.now(),
    };

    // Direct nodes map for tests
    this.nodes = new Map();

    // Initialize if auto-start is enabled
    if (this.config.autoStart) {
      this.start();
    }
  }

  /**
   * Start the cluster manager
   * @returns {boolean} Whether the cluster was started
   */
  start() {
    if (this.status.running) {
      return false;
    }

    // Start task scheduler
    this.taskScheduler.start();

    // Update status
    this.status.running = true;
    this.status.startedAt = Date.now();

    // Log start
    if (Prime.Logger && typeof Prime.Logger.info === "function") {
      Prime.Logger.info(`Cluster manager started: ${this.config.name}`, {
        coordinatorId: this.config.coordinatorId,
        maxNodes: this.config.maxNodes,
      });
    } else {
      console.log(`Cluster manager started: ${this.config.name}`);
    }

    return true;
  }

  /**
   * Stop the cluster manager
   * @returns {boolean} Whether the cluster was stopped
   */
  stop() {
    if (!this.status.running) {
      return false;
    }

    // Stop task scheduler
    this.taskScheduler.stop();

    // Update status
    this.status.running = false;

    // Log stop
    if (Prime.Logger && typeof Prime.Logger.info === "function") {
      Prime.Logger.info(`Cluster manager stopped: ${this.config.name}`, {
        uptime: Date.now() - this.status.startedAt,
        tasksProcessed: this.status.tasksProcessed,
      });
    } else {
      console.log(`Cluster manager stopped: ${this.config.name}`);
    }

    return true;
  }

  /**
   * Register a node with the cluster
   * @param {Object} nodeConfig - Node configuration
   * @returns {Object} Registered node
   */
  registerNode(nodeConfig) {
    // Check max nodes limit
    if (this.nodeRegistry.getAllNodes().length >= this.config.maxNodes) {
      throw new Prime.InvalidOperationError("Maximum number of nodes reached");
    }

    // Register with node registry
    const node = this.nodeRegistry.registerNode(nodeConfig);

    // Update status
    this.status.nodesJoined++;
    this.status.lastStatusUpdate = Date.now();

    // Log registration
    if (Prime.Logger && typeof Prime.Logger.info === "function") {
      Prime.Logger.info(`Node registered: ${node.id}`, {
        type: node.type,
        address: node.address,
        port: node.port,
      });
    } else {
      console.log(`Node registered: ${node.id}`);
    }

    return node;
  }

  /**
   * Unregister a node from the cluster
   * @param {string} nodeId - Node ID
   * @returns {boolean} Whether the node was unregistered
   */
  unregisterNode(nodeId) {
    // Unregister from node registry
    const result = this.nodeRegistry.unregisterNode(nodeId);

    if (result) {
      // Update status
      this.status.lastStatusUpdate = Date.now();

      // Log unregistration
      if (Prime.Logger && typeof Prime.Logger.info === "function") {
        Prime.Logger.info(`Node unregistered: ${nodeId}`);
      } else {
        console.log(`Node unregistered: ${nodeId}`);
      }
    }

    return result;
  }

  /**
   * Submit a task to the cluster
   * @param {Object} taskConfig - Task configuration
   * @returns {Promise<Object>} Promise that resolves to the task result
   */
  submitTask(taskConfig) {
    // Check if cluster is running
    if (!this.status.running) {
      throw new Prime.InvalidOperationError("Cluster manager is not running");
    }

    // Submit task to scheduler
    const task = this.taskScheduler.submitTask(taskConfig);

    // Update status
    this.status.lastStatusUpdate = Date.now();

    // Log submission
    if (Prime.Logger && typeof Prime.Logger.info === "function") {
      Prime.Logger.info(`Task submitted: ${task.id}`, {
        type: task.type,
        priority: task.priority,
      });
    } else {
      console.log(`Task submitted: ${task.id}`);
    }

    // Return a promise that resolves when the task is completed
    return new Promise((resolve, reject) => {
      // Create a timeout to prevent indefinite waiting
      const timeout = taskConfig.timeout || 30000; // Default timeout: 30 seconds
      let timeoutId = null;
      
      // Set up the timeout
      timeoutId = setTimeout(() => {
        // Remove task listener to prevent memory leaks
        this.taskScheduler.taskQueue.eventBus.off(`task:completed:${task.id}`, handleCompletion);
        this.taskScheduler.taskQueue.eventBus.off(`task:failed:${task.id}`, handleFailure);
        
        // Reject the promise with timeout error
        reject(new Prime.CommunicationError(`Task ${task.id} timed out after ${timeout}ms`));
      }, timeout);
      
      // Handle task completion
      const handleCompletion = (eventData) => {
        // Clear timeout
        if (timeoutId) {
          clearTimeout(timeoutId);
          timeoutId = null;
        }
        
        // Update cluster stats
        this.status.tasksProcessed++;
        
        // Resolve with task result
        resolve({
          taskId: task.id,
          result: {
            success: true,
            data: eventData.result || {
              output: null,
              processingTime: Date.now() - task.createdAt,
              processingNode: eventData.nodeId || task.assignedNodeId,
              completed: true
            }
          }
        });
      };
      
      // Handle task failure
      const handleFailure = (eventData) => {
        // Clear timeout
        if (timeoutId) {
          clearTimeout(timeoutId);
          timeoutId = null;
        }
        
        // Resolve with error result (we still resolve, not reject, to maintain API compatibility)
        resolve({
          taskId: task.id,
          result: {
            success: false,
            error: eventData.error || "Task execution failed",
            data: {
              processingTime: Date.now() - task.createdAt,
              processingNode: eventData.nodeId || task.assignedNodeId,
              completed: false
            }
          }
        });
      };
      
      // If task is already completed, resolve immediately
      if (task.state === Prime.Distributed.Cluster.Tasks.TaskState.COMPLETED) {
        handleCompletion({
          taskId: task.id,
          result: task.result,
          nodeId: task.assignedNodeId
        });
        return;
      }
      
      // If task has already failed, resolve with error immediately
      if (task.state === Prime.Distributed.Cluster.Tasks.TaskState.FAILED) {
        handleFailure({
          taskId: task.id,
          error: task.error ? task.error.message : "Task execution failed",
          nodeId: task.assignedNodeId
        });
        return;
      }
      
      // Register event listeners for task completion and failure
      this.taskScheduler.taskQueue.eventBus.on(`task:completed:${task.id}`, handleCompletion);
      this.taskScheduler.taskQueue.eventBus.on(`task:failed:${task.id}`, handleFailure);
    });
  }

  /**
   * Create a partition scheme
   * @param {string} schemeId - Scheme ID
   * @param {Object} schemeConfig - Scheme configuration
   * @returns {Object} Created partition scheme
   */
  createPartitionScheme(schemeId, schemeConfig) {
    // Create scheme with partition manager
    const scheme = this.partitionManager.createScheme(schemeId, schemeConfig);

    // Update status
    this.status.lastStatusUpdate = Date.now();

    // Log creation
    if (Prime.Logger && typeof Prime.Logger.info === "function") {
      Prime.Logger.info(`Partition scheme created: ${schemeId}`, {
        type: scheme.type,
        strategy: scheme.strategy,
      });
    } else {
      console.log(`Partition scheme created: ${schemeId}`);
    }

    return scheme;
  }

  /**
   * Add a node to the cluster
   * @param {Object} nodeConfig - Node configuration
   * @returns {ClusterNode} Created node
   */
  addNode(nodeConfig) {
    // Check if we've reached the max nodes limit
    if (this.nodes.size >= this.config.maxNodes) {
      throw new Prime.InvalidOperationError(
        `Maximum number of nodes reached (${this.config.maxNodes})`
      );
    }

    // Create the node with reference to this cluster manager
    const node = new Prime.Distributed.Cluster.ClusterNode({
      ...nodeConfig,
      clusterManager: this
    });

    // Add to the nodes map
    this.nodes.set(node.id, node);

    // Also register with the registry for compatibility
    this.registerNode(nodeConfig);

    // Return the node
    return node;
  }

  /**
   * Get cluster status
   * @returns {Object} Cluster status
   */
  getStatus() {
    return {
      name: this.config.name,
      running: this.status.running,
      startedAt: this.status.startedAt,
      uptime: this.status.startedAt ? Date.now() - this.status.startedAt : 0,
      nodes: {
        total: this.nodeRegistry.getAllNodes().length,
        joined: this.status.nodesJoined,
        ...this.nodeRegistry.getSummary(),
      },
      tasks: this.taskQueue.getSummary(),
      scheduling: this.taskScheduler.getStatus(),
      partitioning: {
        schemes: this.partitionManager.getAllSchemes().length,
      },
      lastUpdate: Date.now(),
    };
  }

  /**
   * Get metrics for the cluster manager
   * @returns {Object} Cluster metrics
   */
  getMetrics() {
    return {
      totalNodes: this.nodes.size, // Changed to totalNodes for test compatibility
      activeNodes: this.nodes.size,
      tasksInProgress: Array.from(this.nodes.values()).reduce((sum, node) => {
        return sum + (node.currentTasks ? node.currentTasks.size : 0);
      }, 0),
      tasksCompleted: Array.from(this.nodes.values()).reduce((sum, node) => {
        return sum + (node.metrics ? node.metrics.tasksProcessed : 0);
      }, 0),
      lastUpdated: Date.now(),
    };
  }
}

// Add ClusterManager to the Prime namespace directly
Prime.Distributed.Cluster.Manager = ClusterManager;

// Also add as ClusterManager for backward compatibility and clear naming
Prime.Distributed.Cluster.ClusterManager = ClusterManager;

// Ensure backward compatibility through the legacy namespace
if (Prime.distributed && Prime.distributed.cluster) {
  Prime.distributed.cluster.Manager = ClusterManager;
  Prime.distributed.cluster.ClusterManager = ClusterManager;
}

module.exports = Prime;
