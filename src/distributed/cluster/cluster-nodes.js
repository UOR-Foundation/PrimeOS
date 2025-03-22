/**
 * PrimeOS JavaScript Library - Distributed Cluster Nodes Module
 * Manages individual nodes in the distributed computation system
 */

// Import the Prime object from core
const Prime = require("../../core");
const EventBus = require("../event-bus");

/**
 * Node types for distributed computation
 * @enum {string}
 */
const NodeType = {
  /** Coordinates the cluster and distributes work */
  COORDINATOR: "coordinator",
  /** Processes distributed neural computations */
  WORKER: "worker",
  /** Both coordinates and processes computations */
  HYBRID: "hybrid",
};

/**
 * Node states for distributed computation
 * @enum {string}
 */
const NodeState = {
  /** Node is being initialized */
  INITIALIZING: "initializing",
  /** Node is ready to accept work */
  READY: "ready",
  /** Node is actively processing work */
  WORKING: "working",
  /** Node encountered an error */
  ERROR: "error",
  /** Node is shutting down */
  TERMINATING: "terminating",
};

/**
 * Cluster node for distributed computation
 * Represents a single computational node in the distributed system
 */
class ClusterNode {
  /**
   * Create a new cluster node
   * @param {Object} config - Node configuration
   * @param {string} config.id - Unique identifier for this node
   * @param {string} config.type - Type of node (from NodeType enum)
   * @param {string} [config.address='localhost'] - Network address for this node
   * @param {number} [config.port=0] - Port number (0 for auto-assign)
   * @param {Object} [config.capabilities={}] - Special capabilities of this node
   * @param {number} [config.maxConcurrency=1] - Max concurrent tasks
   */
  constructor(config) {
    if (!Prime.Utils.isObject(config)) {
      throw new Prime.ValidationError("Node configuration must be an object");
    }

    if (!config.id) {
      throw new Prime.ValidationError("Node ID is required");
    }

    if (!Object.values(NodeType).includes(config.type)) {
      throw new Prime.ValidationError("Invalid node type");
    }

    this.id = config.id;
    this.type = config.type;
    this.address = config.address || "localhost";
    this.port = config.port || 0;
    this.capabilities = config.capabilities || {};
    this.maxConcurrency = config.maxConcurrency || 1;

    // Current state
    this.state = NodeState.INITIALIZING;
    this.currentTasks = new Map(); // taskId -> task
    this.metrics = {
      tasksProcessed: 0,
      totalProcessingTime: 0,
      errors: 0,
      lastHeartbeat: Date.now(),
      coherenceViolations: 0,
    };

    // Create a unique event bus for this node
    this.eventBus = new EventBus();

    // Initialize node-specific resources
    this._initialize();
  }

  /**
   * Initialize node-specific resources
   * @private
   */
  _initialize() {
    try {
      // Set up event listeners
      this.eventBus.on("task:completed", this._handleTaskCompleted.bind(this));
      this.eventBus.on("task:error", this._handleTaskError.bind(this));
      
      // Update state to ready
      this.state = NodeState.READY;
      
      // Log successful initialization
      Prime.Logger.info(`Node ${this.id} initialized successfully`, {
        type: this.type,
        address: this.address,
        port: this.port
      });
    } catch (error) {
      this.state = NodeState.ERROR;
      Prime.Logger.error(`Failed to initialize node ${this.id}`, {
        error: error.message,
        stack: error.stack
      });
    }
  }

  /**
   * Check if this node can accept a new task
   * @param {Object} task - Task to check
   * @returns {boolean} Whether the node can accept the task
   */
  canAcceptTask(task) {
    // Check if node is in a state to accept work
    if (this.state !== NodeState.READY && this.state !== NodeState.WORKING) {
      return false;
    }
    
    // Check if node has capacity for another task
    if (this.currentTasks.size >= this.maxConcurrency) {
      return false;
    }
    
    // Check if node has the required capabilities for the task
    if (task.requiredCapabilities) {
      for (const [capability, minValue] of Object.entries(task.requiredCapabilities)) {
        if (!this.capabilities[capability] || this.capabilities[capability] < minValue) {
          return false;
        }
      }
    }
    
    return true;
  }

  /**
   * Assign a task to this node
   * @param {Object} task - Task to assign
   * @returns {boolean} Whether the task was successfully assigned
   */
  assignTask(task) {
    if (!this.canAcceptTask(task)) {
      return false;
    }
    
    // Add task to current tasks
    this.currentTasks.set(task.id, {
      ...task,
      assignedAt: Date.now()
    });
    
    // Update node state
    if (this.state === NodeState.READY) {
      this.state = NodeState.WORKING;
    }
    
    // Log task assignment
    Prime.Logger.info(`Task ${task.id} assigned to node ${this.id}`, {
      taskType: task.type,
      nodeType: this.type
    });
    
    // Emit event
    this.eventBus.emit("task:assigned", { taskId: task.id, nodeId: this.id });
    
    return true;
  }

  /**
   * Complete a task on this node
   * @param {string} taskId - ID of the task that was completed
   * @param {Object} result - Task result
   */
  completeTask(taskId, result) {
    const task = this.currentTasks.get(taskId);
    if (!task) {
      Prime.Logger.warn(`Attempting to complete unknown task ${taskId} on node ${this.id}`);
      return false;
    }
    
    // Calculate processing time
    const processingTime = Date.now() - task.assignedAt;
    
    // Update metrics
    this.metrics.tasksProcessed++;
    this.metrics.totalProcessingTime += processingTime;
    
    // Remove task from current tasks
    this.currentTasks.delete(taskId);
    
    // Update node state if no more tasks
    if (this.currentTasks.size === 0) {
      this.state = NodeState.READY;
    }
    
    // Emit completion event
    this.eventBus.emit("task:completed", {
      taskId,
      nodeId: this.id,
      result,
      processingTime
    });
    
    return true;
  }

  /**
   * Report an error for a task on this node
   * @param {string} taskId - ID of the task with error
   * @param {Error} error - Error that occurred
   */
  reportTaskError(taskId, error) {
    const task = this.currentTasks.get(taskId);
    if (!task) {
      Prime.Logger.warn(`Reporting error for unknown task ${taskId} on node ${this.id}`);
      return false;
    }
    
    // Update metrics
    this.metrics.errors++;
    
    // Remove task from current tasks
    this.currentTasks.delete(taskId);
    
    // Update node state if no more tasks
    if (this.currentTasks.size === 0) {
      this.state = NodeState.READY;
    }
    
    // Emit error event
    this.eventBus.emit("task:error", {
      taskId,
      nodeId: this.id,
      error: error.message,
      stack: error.stack
    });
    
    return true;
  }

  /**
   * Report a coherence violation on this node
   * @param {Object} violation - Coherence violation details
   */
  reportCoherenceViolation(violation) {
    // Update metrics
    this.metrics.coherenceViolations++;
    
    // Emit violation event
    this.eventBus.emit("coherence:violation", {
      nodeId: this.id,
      violation,
      timestamp: Date.now()
    });
    
    // Log violation
    Prime.Logger.warn(`Coherence violation on node ${this.id}`, {
      type: violation.type,
      severity: violation.severity,
      details: violation.details || {}
    });
    
    // For numerical stability violations, attempt automatic recovery
    if (violation.type === 'numerical' && 
        Prime.Distributed && 
        Prime.Distributed.Coherence && 
        Prime.Distributed.Coherence.DistributedCoherenceManager) {
      
      this._attemptAutomaticRecovery(violation);
    }
    
    return true;
  }
  
  /**
   * Attempt automatic recovery from coherence violations
   * @private
   * @param {Object} violation - The violation to recover from
   */
  _attemptAutomaticRecovery(violation) {
    try {
      // Find the affected task based on violation
      let affectedTaskId = null;
      if (violation.details && violation.details.taskId) {
        affectedTaskId = violation.details.taskId;
      } else if (violation.context && violation.context.taskId) {
        affectedTaskId = violation.context.taskId;
      }
      
      if (!affectedTaskId) {
        // Can't determine which task was affected
        return;
      }
      
      const task = this.currentTasks.get(affectedTaskId);
      if (!task) {
        // Task not found or already completed
        return;
      }
      
      // Create a coherence manager for recovery
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager({
        strictChecking: true,
        thresholds: {
          numerical: 1e-8,
          gradient: 1.0,
          synchronization: 0.01
        }
      });
      
      // Apply corrections based on violation type
      if (violation.type === 'numerical') {
        // For numerical stability issues, apply corrections to task data
        if (task.data && task.data.parameters) {
          // Apply numerical stability fixes to parameters
          const corrections = coherenceManager.applyCoherenceCorrection(
            task.data.parameters, 
            [violation]
          );
          
          if (corrections.applied) {
            Prime.Logger.info(`Applied automatic numerical stability corrections to task ${affectedTaskId}`, {
              corrections: corrections.corrections,
              taskType: task.type,
              nodeId: this.id
            });
          }
        }
        
        if (task.data && task.data.gradients) {
          // Apply gradient clipping for extreme values
          const clippedGradients = this._applyGradientClipping(task.data.gradients);
          task.data.gradients = clippedGradients;
          
          Prime.Logger.info(`Applied gradient clipping to task ${affectedTaskId}`, {
            taskType: task.type,
            nodeId: this.id
          });
        }
      }
    } catch (error) {
      Prime.Logger.error(`Error during automatic recovery attempt`, {
        error: error.message,
        stack: error.stack,
        nodeId: this.id,
        violationType: violation.type
      });
    }
  }
  
  /**
   * Apply gradient clipping to prevent numerical instability
   * @private
   * @param {Object} gradients - Gradients to clip
   * @param {number} maxValue - Maximum absolute value (default: 1000.0)
   * @returns {Object} Clipped gradients
   */
  _applyGradientClipping(gradients, maxValue = 1000.0) {
    if (!gradients || typeof gradients !== 'object') {
      return gradients;
    }
    
    const clipped = JSON.parse(JSON.stringify(gradients));
    
    // Helper function to clip a single value
    const clipValue = (value) => {
      if (!Number.isFinite(value)) {
        return 0; // Replace NaN or Infinity with 0
      }
      return Math.max(-maxValue, Math.min(maxValue, value));
    };
    
    // Process all gradient values recursively
    const processObject = (obj) => {
      if (!obj || typeof obj !== 'object') {
        return;
      }
      
      // Handle arrays (including matrices)
      if (Array.isArray(obj)) {
        for (let i = 0; i < obj.length; i++) {
          if (Array.isArray(obj[i])) {
            processObject(obj[i]); // Process nested arrays
          } else if (typeof obj[i] === 'number') {
            obj[i] = clipValue(obj[i]); // Clip numeric values
          }
        }
      }
      // Handle plain objects
      else {
        for (const key in obj) {
          if (obj.hasOwnProperty(key)) {
            if (obj[key] && typeof obj[key] === 'object') {
              processObject(obj[key]); // Process nested objects
            } else if (typeof obj[key] === 'number') {
              obj[key] = clipValue(obj[key]); // Clip numeric values
            }
          }
        }
      }
    };
    
    // Process the gradients
    processObject(clipped);
    
    return clipped;
  }

  /**
   * Update the heartbeat timestamp for this node
   */
  heartbeat() {
    this.metrics.lastHeartbeat = Date.now();
    return this.metrics.lastHeartbeat;
  }

  /**
   * Get the current status of this node
   * @returns {Object} Node status
   */
  getStatus() {
    return {
      id: this.id,
      type: this.type,
      state: this.state,
      address: this.address,
      port: this.port,
      activeTasks: this.currentTasks.size,
      metrics: {
        ...this.metrics,
        averageProcessingTime: this.metrics.tasksProcessed > 0 
          ? this.metrics.totalProcessingTime / this.metrics.tasksProcessed 
          : 0,
        lastHeartbeatAge: Date.now() - this.metrics.lastHeartbeat
      },
      capabilities: this.capabilities
    };
  }

  /**
   * Terminate this node
   */
  terminate() {
    // Set state to terminating
    this.state = NodeState.TERMINATING;
    
    // Log termination
    Prime.Logger.info(`Node ${this.id} terminating`, {
      activeTasks: this.currentTasks.size
    });
    
    // Clean up resources
    this.eventBus.removeAllListeners();
    
    // Emit termination event
    this.eventBus.emit("node:terminated", {
      nodeId: this.id,
      timestamp: Date.now()
    });
    
    return true;
  }

  /**
   * Handle task completion event
   * @private
   * @param {Object} eventData - Event data
   */
  _handleTaskCompleted(eventData) {
    // Additional handling can be added here
  }

  /**
   * Handle task error event
   * @private
   * @param {Object} eventData - Event data
   */
  _handleTaskError(eventData) {
    // Additional handling can be added here
  }
  
  /**
   * Get node metrics
   * @returns {Object} Node metrics
   */
  getMetrics() {
    return this.metrics;
  }
}

/**
 * Node registry for managing cluster nodes
 */
class NodeRegistry {
  /**
   * Create a new node registry
   */
  constructor() {
    this.nodes = new Map(); // nodeId -> node
    this.eventBus = new EventBus();
  }

  /**
   * Register a new node
   * @param {ClusterNode|Object} node - Node or node configuration
   * @returns {ClusterNode} Registered node
   */
  registerNode(node) {
    // Convert configuration object to node if needed
    const clusterNode = node instanceof ClusterNode 
      ? node 
      : new ClusterNode(node);
    
    // Check if node already exists
    if (this.nodes.has(clusterNode.id)) {
      throw new Prime.ValidationError(`Node with ID ${clusterNode.id} already exists`);
    }
    
    // Add node to registry
    this.nodes.set(clusterNode.id, clusterNode);
    
    // Emit event
    this.eventBus.emit("node:registered", {
      nodeId: clusterNode.id,
      timestamp: Date.now()
    });
    
    return clusterNode;
  }

  /**
   * Unregister a node
   * @param {string} nodeId - Node ID
   * @returns {boolean} Whether the node was successfully unregistered
   */
  unregisterNode(nodeId) {
    const node = this.nodes.get(nodeId);
    if (!node) {
      return false;
    }
    
    // Terminate node
    node.terminate();
    
    // Remove from registry
    this.nodes.delete(nodeId);
    
    // Emit event
    this.eventBus.emit("node:unregistered", {
      nodeId,
      timestamp: Date.now()
    });
    
    return true;
  }

  /**
   * Get a node by ID
   * @param {string} nodeId - Node ID
   * @returns {ClusterNode} Node
   */
  getNode(nodeId) {
    return this.nodes.get(nodeId);
  }

  /**
   * Find nodes matching criteria
   * @param {Object} criteria - Search criteria
   * @returns {Array<ClusterNode>} Matching nodes
   */
  findNodes(criteria = {}) {
    // Convert to array and filter
    return Array.from(this.nodes.values()).filter(node => {
      // Match criteria
      for (const [key, value] of Object.entries(criteria)) {
        if (key === 'capabilities') {
          // Check capabilities
          for (const [capability, minValue] of Object.entries(value)) {
            if (!node.capabilities[capability] || node.capabilities[capability] < minValue) {
              return false;
            }
          }
        } else if (node[key] !== value) {
          return false;
        }
      }
      return true;
    });
  }

  /**
   * Find the best node for a task
   * @param {Object} task - Task to assign
   * @returns {ClusterNode} Best node for the task
   */
  findBestNodeForTask(task) {
    // Get all nodes that can accept the task
    const eligibleNodes = Array.from(this.nodes.values())
      .filter(node => node.canAcceptTask(task));
    
    if (eligibleNodes.length === 0) {
      return null;
    }
    
    // Sort by load (number of current tasks) and processing capacity
    eligibleNodes.sort((a, b) => {
      // First priority: current load ratio
      const aLoadRatio = a.currentTasks.size / a.maxConcurrency;
      const bLoadRatio = b.currentTasks.size / b.maxConcurrency;
      
      if (aLoadRatio !== bLoadRatio) {
        return aLoadRatio - bLoadRatio; // Lower load ratio is better
      }
      
      // Second priority: maximizing capabilities match
      let aCapabilityScore = 0;
      let bCapabilityScore = 0;
      
      if (task.requiredCapabilities) {
        for (const [capability, minValue] of Object.entries(task.requiredCapabilities)) {
          if (a.capabilities[capability]) {
            aCapabilityScore += (a.capabilities[capability] - minValue) / minValue;
          }
          if (b.capabilities[capability]) {
            bCapabilityScore += (b.capabilities[capability] - minValue) / minValue;
          }
        }
      }
      
      if (aCapabilityScore !== bCapabilityScore) {
        return bCapabilityScore - aCapabilityScore; // Higher capability score is better
      }
      
      // Third priority: historical processing performance
      const aAvgTime = a.metrics.tasksProcessed > 0 
        ? a.metrics.totalProcessingTime / a.metrics.tasksProcessed 
        : Infinity;
      const bAvgTime = b.metrics.tasksProcessed > 0 
        ? b.metrics.totalProcessingTime / b.metrics.tasksProcessed 
        : Infinity;
      
      return aAvgTime - bAvgTime; // Lower average processing time is better
    });
    
    // Return the best node
    return eligibleNodes[0];
  }

  /**
   * Get all nodes
   * @returns {Array<ClusterNode>} All nodes
   */
  getAllNodes() {
    return Array.from(this.nodes.values());
  }

  /**
   * Get a summary of the node registry
   * @returns {Object} Registry summary
   */
  getSummary() {
    const allNodes = this.getAllNodes();
    
    // Count nodes by type
    const nodesByType = {};
    for (const type of Object.values(NodeType)) {
      nodesByType[type] = allNodes.filter(node => node.type === type).length;
    }
    
    // Count nodes by state
    const nodesByState = {};
    for (const state of Object.values(NodeState)) {
      nodesByState[state] = allNodes.filter(node => node.state === state).length;
    }
    
    // Calculate task statistics
    let totalTasks = 0;
    let totalProcessedTasks = 0;
    let totalErrors = 0;
    
    for (const node of allNodes) {
      totalTasks += node.currentTasks.size;
      totalProcessedTasks += node.metrics.tasksProcessed;
      totalErrors += node.metrics.errors;
    }
    
    return {
      totalNodes: allNodes.length,
      nodesByType,
      nodesByState,
      taskStats: {
        currentTasks: totalTasks,
        processedTasks: totalProcessedTasks,
        errors: totalErrors,
        successRate: totalProcessedTasks > 0 ? 
          (totalProcessedTasks - totalErrors) / totalProcessedTasks : 0
      }
    };
  }
}

// Add to Prime namespace
Prime.Distributed = Prime.Distributed || {};
Prime.Distributed.Cluster = Prime.Distributed.Cluster || {};
Prime.Distributed.Cluster.Nodes = {
  NodeType,
  NodeState,
  ClusterNode,
  NodeRegistry
};

module.exports = Prime;