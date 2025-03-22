/**
 * PrimeOS JavaScript Library - Distributed Cluster Module
 * Main entry point for distributed computation functionality
 */

// Import the Prime object from core
const Prime = require("../../core");

// Import cluster components
require("./cluster-nodes");
require("./task-distribution");
require("./partition-manager");

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
      maxTasksPerNode: config.maxTasksPerNode || 10
    });
    
    // Create partition manager
    this.partitionManager = new Prime.Distributed.Cluster.Partition.PartitionManager();
    
    // Cluster configuration
    this.config = {
      name: config.name || "PrimeOS Cluster",
      coordinatorId: config.coordinatorId || null,
      maxNodes: config.maxNodes || 100,
      autoStart: config.autoStart !== false,
      ...config
    };
    
    // Cluster status
    this.status = {
      running: false,
      startedAt: null,
      nodesJoined: 0,
      tasksProcessed: 0,
      lastStatusUpdate: Date.now()
    };
    
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
    Prime.Logger.info(`Cluster manager started: ${this.config.name}`, {
      coordinatorId: this.config.coordinatorId,
      maxNodes: this.config.maxNodes
    });
    
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
    Prime.Logger.info(`Cluster manager stopped: ${this.config.name}`, {
      uptime: Date.now() - this.status.startedAt,
      tasksProcessed: this.status.tasksProcessed
    });
    
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
    Prime.Logger.info(`Node registered: ${node.id}`, {
      type: node.type,
      address: node.address,
      port: node.port
    });
    
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
      Prime.Logger.info(`Node unregistered: ${nodeId}`);
    }
    
    return result;
  }

  /**
   * Submit a task to the cluster
   * @param {Object} taskConfig - Task configuration
   * @returns {Object} Submitted task
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
    Prime.Logger.info(`Task submitted: ${task.id}`, {
      type: task.type,
      priority: task.priority
    });
    
    return task;
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
    Prime.Logger.info(`Partition scheme created: ${schemeId}`, {
      type: scheme.type,
      strategy: scheme.strategy
    });
    
    return scheme;
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
        ...this.nodeRegistry.getSummary()
      },
      tasks: this.taskQueue.getSummary(),
      scheduling: this.taskScheduler.getStatus(),
      partitioning: {
        schemes: this.partitionManager.getAllSchemes().length
      },
      lastUpdate: Date.now()
    };
  }
}

// Add to Prime namespace
Prime.Distributed = Prime.Distributed || {};
Prime.Distributed.Cluster = Prime.Distributed.Cluster || {};
Prime.Distributed.Cluster.Manager = ClusterManager;

module.exports = Prime;