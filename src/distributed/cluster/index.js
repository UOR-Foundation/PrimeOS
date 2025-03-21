/**
 * PrimeOS JavaScript Library - Distributed Cluster Module
 * Manages distributed computation nodes and their coordination
 */

// Import the Prime object from core
const Prime = require("../../core");
const EventBus = require("../event-bus");

// Create the Cluster module using IIFE
(function () {
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
      Prime.Logger.info(
        `Initializing cluster node ${this.id} as ${this.type}`,
        {
          address: this.address,
          port: this.port,
        },
      );

      // Set up event listeners
      this.eventBus.on("task:complete", this._onTaskComplete.bind(this));
      this.eventBus.on("task:error", this._onTaskError.bind(this));
      this.eventBus.on(
        "coherence:violation",
        this._onCoherenceViolation.bind(this),
      );

      // Transition to ready state
      this.state = NodeState.READY;

      // Emit ready event
      this.eventBus.emit("node:ready", { nodeId: this.id });
    }

    /**
     * Submit a task to this node for processing
     * @param {Object} task - The task to be processed
     * @param {string} task.id - Unique identifier for this task
     * @param {string} task.type - Type of computation to perform
     * @param {Object} task.data - Input data for the task
     * @param {Function} [callback] - Optional callback for task completion
     * @returns {Promise<Object>} Promise that resolves with task result
     */
    submitTask(task, callback) {
      if (!Prime.Utils.isObject(task) || !task.id || !task.type) {
        throw new Prime.ValidationError("Invalid task format");
      }

      if (this.state !== NodeState.READY && this.state !== NodeState.WORKING) {
        throw new Prime.OperationError(
          `Node ${this.id} not ready (${this.state})`,
        );
      }

      if (this.currentTasks.size >= this.maxConcurrency) {
        throw new Prime.OperationError(`Node ${this.id} at max capacity`);
      }

      // Create a promise for task completion
      const taskPromise = new Promise((resolve, reject) => {
        // Store the task with its resolution callbacks
        this.currentTasks.set(task.id, {
          task,
          resolve,
          reject,
          startTime: Date.now(),
        });
      });

      // Register optional callback if provided
      if (callback && typeof callback === "function") {
        taskPromise.then(callback).catch(callback);
      }

      // Update state if this is the first task
      if (this.currentTasks.size === 1 && this.state === NodeState.READY) {
        this.state = NodeState.WORKING;
      }

      // Process the task asynchronously
      this._processTask(task);

      return taskPromise;
    }

    /**
     * Process a task asynchronously
     * @private
     * @param {Object} task - The task to process
     */
    async _processTask(task) {
      Prime.Logger.info(`Processing task ${task.id} on node ${this.id}`, {
        taskType: task.type,
      });

      try {
        // Simulate task execution with appropriate task handler
        let result;

        switch (task.type) {
          case "forward_pass":
            result = await this._handleForwardPass(task.data);
            break;
          case "backward_pass":
            result = await this._handleBackwardPass(task.data);
            break;
          case "weight_update":
            result = await this._handleWeightUpdate(task.data);
            break;
          case "coherence_check":
            result = await this._handleCoherenceCheck(task.data);
            break;
          default:
            throw new Error(`Unknown task type: ${task.type}`);
        }

        // Task completed successfully
        this.eventBus.emit("task:complete", {
          taskId: task.id,
          result,
        });
      } catch (error) {
        // Task failed
        this.eventBus.emit("task:error", {
          taskId: task.id,
          error: error.message,
        });
      }
    }

    /**
     * Handle task completion event
     * @private
     * @param {Object} event - Task completion event data
     */
    _onTaskComplete(event) {
      const { taskId, result } = event;
      const taskInfo = this.currentTasks.get(taskId);

      if (taskInfo) {
        // Calculate processing time
        const processingTime = Date.now() - taskInfo.startTime;

        // Update metrics
        this.metrics.tasksProcessed++;
        this.metrics.totalProcessingTime += processingTime;

        // Resolve the task promise
        taskInfo.resolve(result);

        // Remove from current tasks
        this.currentTasks.delete(taskId);

        // Update state if no more tasks
        if (this.currentTasks.size === 0 && this.state === NodeState.WORKING) {
          this.state = NodeState.READY;
        }
      }
    }

    /**
     * Handle task error event
     * @private
     * @param {Object} event - Task error event data
     */
    _onTaskError(event) {
      const { taskId, error } = event;
      const taskInfo = this.currentTasks.get(taskId);

      if (taskInfo) {
        // Update metrics
        this.metrics.errors++;

        // Reject the task promise
        taskInfo.reject(new Error(error));

        // Remove from current tasks
        this.currentTasks.delete(taskId);

        // Update state if no more tasks
        if (this.currentTasks.size === 0 && this.state === NodeState.WORKING) {
          this.state = NodeState.READY;
        }
      }
    }

    /**
     * Handle coherence violation event
     * @private
     * @param {Object} event - Coherence violation event data
     */
    _onCoherenceViolation(event) {
      this.metrics.coherenceViolations++;

      Prime.Logger.warn(`Coherence violation detected on node ${this.id}`, {
        taskId: event.taskId,
        violationType: event.type,
        severity: event.severity,
      });
    }

    /**
     * Forward pass task handler
     * @private
     * @param {Object} data - Task input data
     * @returns {Promise<Object>} Task result
     */
    async _handleForwardPass(data) {
      // Extract layer and input information
      const { layerConfig, input } = data;

      if (!layerConfig || !Array.isArray(input)) {
        throw new Error("Invalid forward pass task data");
      }

      // Create temporary layer for computation
      const layer = new Prime.Neural.Layer.NeuralLayer(layerConfig);

      // Verify coherence before processing
      this._verifyCoherence(layerConfig);

      // Perform forward pass
      const result = layer.forward(input);

      return {
        activation: result.activation,
        coherenceScore: this._calculateCoherenceScore(
          result.activation,
          layerConfig,
        ),
      };
    }

    /**
     * Backward pass task handler
     * @private
     * @param {Object} data - Task input data
     * @returns {Promise<Object>} Task result
     */
    async _handleBackwardPass(data) {
      // Extract necessary information
      const { layerConfig, gradOutput, cache } = data;

      if (!layerConfig || !Array.isArray(gradOutput) || !cache) {
        throw new Error("Invalid backward pass task data");
      }

      // Create temporary layer for computation
      const layer = new Prime.Neural.Layer.NeuralLayer(layerConfig);

      // Verify coherence before processing
      this._verifyCoherence(layerConfig);

      // Perform backward pass
      const gradients = layer.backward(gradOutput, cache);

      return {
        gradients,
        coherenceScore: this._calculateCoherenceScore(
          gradients.dW,
          layerConfig,
        ),
      };
    }

    /**
     * Weight update task handler
     * @private
     * @param {Object} data - Task input data
     * @returns {Promise<Object>} Task result
     */
    async _handleWeightUpdate(data) {
      // Extract necessary information
      const { layerConfig, gradients, learningRate } = data;

      if (!layerConfig || !gradients || typeof learningRate !== "number") {
        throw new Error("Invalid weight update task data");
      }

      // Create temporary layer for computation
      const layer = new Prime.Neural.Layer.NeuralLayer(layerConfig);

      // Apply weight update
      layer.update(gradients, learningRate);

      // Check coherence after update
      const coherenceScore = this._calculateCoherenceScore(
        layer.weights,
        layerConfig,
      );

      // If coherence violation detected, apply correction
      if (coherenceScore < 0.5) {
        this._applyCoherenceCorrection(layer, coherenceScore);

        // Emit coherence violation event
        this.eventBus.emit("coherence:violation", {
          taskId: data.taskId,
          type: "weight_update",
          severity: "medium",
          score: coherenceScore,
        });
      }

      return {
        updatedWeights: layer.weights,
        updatedBiases: layer.biases,
        coherenceScore,
      };
    }

    /**
     * Coherence check task handler
     * @private
     * @param {Object} data - Task input data
     * @returns {Promise<Object>} Task result
     */
    async _handleCoherenceCheck(data) {
      // Extract layer information
      const { layerConfig, parameters } = data;

      if (!layerConfig || !parameters) {
        throw new Error("Invalid coherence check task data");
      }

      // Calculate coherence score
      const coherenceScore = this._calculateCoherenceScore(
        parameters.weights,
        layerConfig,
      );

      // Prepare detailed coherence analysis
      const analysis = {
        score: coherenceScore,
        weightNorm: this._calculateL2Norm(parameters.weights),
        gradientAlignment: Math.random(), // Placeholder for actual calculation
        activationDistribution:
          this._simulateActivationDistribution(layerConfig),
        recommendations: [],
      };

      // Add recommendations based on coherence score
      if (coherenceScore < 0.3) {
        analysis.recommendations.push("Reset weights to improve stability");
      } else if (coherenceScore < 0.7) {
        analysis.recommendations.push(
          "Apply regularization to improve coherence",
        );
      }

      return analysis;
    }

    /**
     * Calculate coherence score for a parameter set
     * @private
     * @param {Array|Matrix} parameters - Parameters to check
     * @param {Object} config - Layer configuration
     * @returns {number} Coherence score between 0 and 1
     */
    _calculateCoherenceScore(parameters, config) {
      // Simple coherence score calculation (placeholder)
      // In a real implementation, this would be a more sophisticated
      // calculation based on mathematical principles

      if (Array.isArray(parameters) && Array.isArray(parameters[0])) {
        // For weight matrices
        const norm = this._calculateL2Norm(parameters);
        const size = Math.sqrt(config.inputSize * config.outputSize);
        return Math.exp(-Math.abs(norm - size) / size);
      } else if (Array.isArray(parameters)) {
        // For activation vectors or bias vectors
        const mean =
          parameters.reduce((sum, val) => sum + val, 0) / parameters.length;
        const variance =
          parameters.reduce((sum, val) => sum + Math.pow(val - mean, 2), 0) /
          parameters.length;
        return Math.min(1, 1 / (1 + variance));
      }

      return 0.8; // Default fallback
    }

    /**
     * Calculate L2 norm of a matrix
     * @private
     * @param {Array<Array<number>>} matrix - Matrix to calculate norm for
     * @returns {number} L2 norm
     */
    _calculateL2Norm(matrix) {
      let sumSquared = 0;

      for (let i = 0; i < matrix.length; i++) {
        for (let j = 0; j < matrix[i].length; j++) {
          sumSquared += Math.pow(matrix[i][j], 2);
        }
      }

      return Math.sqrt(sumSquared);
    }

    /**
     * Simulate activation distribution for coherence checking
     * @private
     * @param {Object} config - Layer configuration
     * @returns {Array} Distribution statistics
     */
    _simulateActivationDistribution(config) {
      // Simulate activation distribution statistics
      return {
        mean: Math.random() * 0.5,
        variance: Math.random() * 0.2,
        sparsity: Math.random() * 0.8,
      };
    }

    /**
     * Verify coherence of layer configuration
     * @private
     * @param {Object} config - Layer configuration to verify
     * @throws {Error} If coherence check fails
     */
    _verifyCoherence(config) {
      // Simple validation of configuration
      if (!config.inputSize || !config.outputSize) {
        this.eventBus.emit("coherence:violation", {
          type: "configuration",
          severity: "high",
          message: "Invalid layer dimensions",
        });
        throw new Error("Invalid layer dimensions");
      }

      // Could include more sophisticated coherence checks here
    }

    /**
     * Apply coherence correction to a layer
     * @private
     * @param {Object} layer - Layer to correct
     * @param {number} currentScore - Current coherence score
     */
    _applyCoherenceCorrection(layer, currentScore) {
      // Simple correction strategy - scale weights to improve coherence
      // This is a simplified version of what would be a more sophisticated
      // mathematical correction in a real implementation

      const scaleFactor = Math.min(1, 1 / (2 * (1 - currentScore)));

      for (let i = 0; i < layer.weights.length; i++) {
        for (let j = 0; j < layer.weights[i].length; j++) {
          layer.weights[i][j] *= scaleFactor;
        }
      }
    }

    /**
     * Get current node metrics
     * @returns {Object} Current node metrics
     */
    getMetrics() {
      // Update heartbeat timestamp
      this.metrics.lastHeartbeat = Date.now();

      return { ...this.metrics };
    }

    /**
     * Terminate this node
     * @returns {Promise<void>} Promise that resolves when node is terminated
     */
    async terminate() {
      // Only allow termination if not processing tasks
      if (this.state === NodeState.WORKING && this.currentTasks.size > 0) {
        throw new Prime.OperationError(
          `Cannot terminate node ${this.id} with ${this.currentTasks.size} active tasks`,
        );
      }

      this.state = NodeState.TERMINATING;

      Prime.Logger.info(`Terminating cluster node ${this.id}`);

      // Clean up resources
      this.eventBus.removeAllListeners();

      // In a real implementation, would close network connections, etc.

      this.state = null; // Mark node as terminated

      return Promise.resolve();
    }
  }

  /**
   * Cluster manager for distributed computation
   * Coordinates multiple computation nodes
   */
  class ClusterManager {
    /**
     * Create a new cluster manager
     * @param {Object} config - Cluster configuration
     * @param {number} [config.maxNodes=10] - Maximum number of nodes
     * @param {string} [config.discoveryMethod='local'] - Node discovery method
     * @param {Object} [config.coherencePolicy={}] - Coherence policy settings
     */
    constructor(config = {}) {
      this.config = {
        maxNodes: config.maxNodes || 10,
        discoveryMethod: config.discoveryMethod || "local",
        coherencePolicy: config.coherencePolicy || {
          enforceGlobalCoherence: true,
          minCoherenceThreshold: 0.6,
          recoveryStrategy: "rollback",
        },
      };

      // Node registry
      this.nodes = new Map(); // nodeId -> node

      // Task tracking
      this.taskRegistry = new Map(); // taskId -> task info
      this.taskAssignments = new Map(); // taskId -> nodeId

      // Performance tracking
      this.metrics = {
        totalTasks: 0,
        completedTasks: 0,
        failedTasks: 0,
        averageProcessingTime: 0,
        globalCoherenceScore: 1.0,
      };

      // Create cluster event bus
      this.eventBus = new EventBus();

      // Set up event listeners
      this._setupEventListeners();

      Prime.Logger.info(
        `Created cluster manager with max ${this.config.maxNodes} nodes`,
      );
    }

    /**
     * Set up cluster event listeners
     * @private
     */
    _setupEventListeners() {
      // Global error handler
      this.eventBus.on("error", this._handleError.bind(this));

      // Node events
      this.eventBus.on("node:added", this._onNodeAdded.bind(this));
      this.eventBus.on("node:removed", this._onNodeRemoved.bind(this));

      // Task events
      this.eventBus.on("task:submitted", this._onTaskSubmitted.bind(this));
      this.eventBus.on("task:completed", this._onTaskCompleted.bind(this));
      this.eventBus.on("task:failed", this._onTaskFailed.bind(this));

      // Coherence events
      this.eventBus.on("coherence:check", this._onCoherenceCheck.bind(this));
      this.eventBus.on(
        "coherence:violation",
        this._onCoherenceViolation.bind(this),
      );
    }

    /**
     * Add a new node to the cluster
     * @param {Object} nodeConfig - Node configuration
     * @returns {ClusterNode} The newly created node
     * @throws {Error} If maximum node limit is reached
     */
    addNode(nodeConfig) {
      if (this.nodes.size >= this.config.maxNodes) {
        throw new Prime.OperationError(
          `Maximum node limit (${this.config.maxNodes}) reached`,
        );
      }

      // Create new node instance
      const node = new ClusterNode(nodeConfig);

      // Add to node registry
      this.nodes.set(node.id, node);

      // Forward node events to cluster event bus
      this._forwardNodeEvents(node);

      // Emit node added event
      this.eventBus.emit("node:added", { nodeId: node.id, type: node.type });

      return node;
    }

    /**
     * Forward node events to cluster event bus
     * @private
     * @param {ClusterNode} node - Node to forward events from
     */
    _forwardNodeEvents(node) {
      // Forward task completion events
      node.eventBus.on("task:complete", (event) => {
        this.eventBus.emit("task:completed", {
          nodeId: node.id,
          taskId: event.taskId,
          result: event.result,
        });
      });

      // Forward task error events
      node.eventBus.on("task:error", (event) => {
        this.eventBus.emit("task:failed", {
          nodeId: node.id,
          taskId: event.taskId,
          error: event.error,
        });
      });

      // Forward coherence violation events
      node.eventBus.on("coherence:violation", (event) => {
        this.eventBus.emit("coherence:violation", {
          nodeId: node.id,
          ...event,
        });
      });
    }

    /**
     * Remove a node from the cluster
     * @param {string} nodeId - ID of node to remove
     * @returns {Promise<boolean>} Success status
     */
    async removeNode(nodeId) {
      const node = this.nodes.get(nodeId);

      if (!node) {
        return false;
      }

      try {
        // Terminate the node
        await node.terminate();

        // Remove from registry
        this.nodes.delete(nodeId);

        // Emit node removed event
        this.eventBus.emit("node:removed", { nodeId });

        Prime.Logger.info(`Node ${nodeId} removed from cluster`);

        return true;
      } catch (error) {
        Prime.Logger.error(`Failed to remove node ${nodeId}`, error);
        return false;
      }
    }

    /**
     * Submit a task to the cluster for distributed processing
     * @param {Object} task - Task to submit
     * @param {string} task.id - Unique task identifier
     * @param {string} task.type - Type of task
     * @param {Object} task.data - Task input data
     * @param {Array<string>} [preferredNodes] - List of preferred node IDs
     * @returns {Promise<Object>} Promise resolving to task result
     */
    submitTask(task, preferredNodes = []) {
      if (!task.id || !task.type) {
        throw new Prime.ValidationError("Invalid task format");
      }

      // Create task tracking promise
      return new Promise((resolve, reject) => {
        // Register task in task registry
        this.taskRegistry.set(task.id, {
          task,
          submitTime: Date.now(),
          resolve,
          reject,
          attempts: 0,
          preferredNodes,
        });

        // Update metrics
        this.metrics.totalTasks++;

        // Emit task submitted event
        this.eventBus.emit("task:submitted", {
          taskId: task.id,
          taskType: task.type,
        });

        // Find suitable node and assign task
        this._assignTask(task.id);
      });
    }

    /**
     * Assign a task to a suitable node
     * @private
     * @param {string} taskId - ID of task to assign
     */
    _assignTask(taskId) {
      const taskInfo = this.taskRegistry.get(taskId);

      if (!taskInfo) {
        return;
      }

      // Find best node for this task
      const nodeId = this._findSuitableNode(
        taskInfo.task,
        taskInfo.preferredNodes,
      );

      if (!nodeId) {
        // No suitable node found, queue task for later
        setTimeout(() => this._assignTask(taskId), 100);
        return;
      }

      const node = this.nodes.get(nodeId);

      try {
        // Submit task to selected node
        node
          .submitTask(taskInfo.task)
          .then((result) => {
            // Task completed on this node
            this.taskAssignments.set(taskId, nodeId);

            // Store completion time for metrics
            taskInfo.completeTime = Date.now();
          })
          .catch((error) => {
            // Task failed on this node, try to reassign
            Prime.Logger.warn(
              `Task ${taskId} failed on node ${nodeId}, reassigning`,
              {
                error: error.message,
              },
            );

            // Increment attempt counter
            taskInfo.attempts++;

            if (taskInfo.attempts < 3) {
              // Retry on a different node
              setTimeout(() => this._assignTask(taskId), 100);
            } else {
              // Too many attempts, fail the task
              this.eventBus.emit("task:failed", {
                taskId,
                error: `Failed after ${taskInfo.attempts} attempts: ${error.message}`,
              });
            }
          });
      } catch (error) {
        // Could not submit task to node
        Prime.Logger.error(
          `Failed to submit task ${taskId} to node ${nodeId}`,
          error,
        );

        // Try to reassign
        setTimeout(() => this._assignTask(taskId), 100);
      }
    }

    /**
     * Find the most suitable node for a given task
     * @private
     * @param {Object} task - Task to assign
     * @param {Array<string>} preferredNodes - List of preferred nodes
     * @returns {string|null} ID of selected node, or null if none available
     */
    _findSuitableNode(task, preferredNodes) {
      // First try preferred nodes
      for (const nodeId of preferredNodes) {
        const node = this.nodes.get(nodeId);

        if (node && node.state === NodeState.READY) {
          return nodeId;
        }
      }

      // Filter available nodes
      const availableNodes = [...this.nodes.values()].filter((node) => {
        return (
          node.state === NodeState.READY ||
          (node.state === NodeState.WORKING &&
            node.currentTasks.size < node.maxConcurrency)
        );
      });

      if (availableNodes.length === 0) {
        return null;
      }

      // Sort by current load
      availableNodes.sort((a, b) => {
        return a.currentTasks.size - b.currentTasks.size;
      });

      // Return the least loaded node
      return availableNodes[0].id;
    }

    /**
     * Handle global error event
     * @private
     * @param {Object} event - Error event data
     */
    _handleError(event) {
      Prime.Logger.error("Cluster error occurred", {
        source: event.source,
        message: event.message,
      });
    }

    /**
     * Handle node added event
     * @private
     * @param {Object} event - Node added event data
     */
    _onNodeAdded(event) {
      Prime.Logger.info(`Node ${event.nodeId} added to cluster`);

      // Check for pending tasks that could be assigned to this node
      this._reassignPendingTasks();
    }

    /**
     * Handle node removed event
     * @private
     * @param {Object} event - Node removed event data
     */
    _onNodeRemoved(event) {
      Prime.Logger.info(`Node ${event.nodeId} removed from cluster`);

      // Reassign tasks from this node
      this._reassignTasksFromNode(event.nodeId);
    }

    /**
     * Handle task submitted event
     * @private
     * @param {Object} event - Task submitted event data
     */
    _onTaskSubmitted(event) {
      Prime.Logger.info(`Task ${event.taskId} submitted to cluster`);
    }

    /**
     * Handle task completed event
     * @private
     * @param {Object} event - Task completed event data
     */
    _onTaskCompleted(event) {
      const { nodeId, taskId, result } = event;
      const taskInfo = this.taskRegistry.get(taskId);

      if (taskInfo) {
        // Calculate processing time
        const processingTime = Date.now() - taskInfo.submitTime;

        // Update metrics
        this.metrics.completedTasks++;
        this.metrics.averageProcessingTime =
          0.9 * this.metrics.averageProcessingTime + 0.1 * processingTime;

        // Update global coherence if result includes a coherence score
        if (result && typeof result.coherenceScore === "number") {
          this.metrics.globalCoherenceScore =
            0.95 * this.metrics.globalCoherenceScore +
            0.05 * result.coherenceScore;
        }

        // Resolve the task promise
        taskInfo.resolve(result);

        // Clean up task registry
        this.taskRegistry.delete(taskId);
        this.taskAssignments.delete(taskId);

        Prime.Logger.info(`Task ${taskId} completed on node ${nodeId}`, {
          processingTime,
        });
      }
    }

    /**
     * Handle task failed event
     * @private
     * @param {Object} event - Task failed event data
     */
    _onTaskFailed(event) {
      const { taskId, error } = event;
      const taskInfo = this.taskRegistry.get(taskId);

      if (taskInfo) {
        // Update metrics
        this.metrics.failedTasks++;

        // Reject the task promise
        taskInfo.reject(new Error(error));

        // Clean up task registry
        this.taskRegistry.delete(taskId);
        this.taskAssignments.delete(taskId);

        Prime.Logger.error(`Task ${taskId} failed`, { error });
      }
    }

    /**
     * Handle coherence check event
     * @private
     * @param {Object} event - Coherence check event data
     */
    _onCoherenceCheck(event) {
      Prime.Logger.info("Performing cluster-wide coherence check");

      // Schedule a coherence check across all nodes
      this._performClusterCoherenceCheck();
    }

    /**
     * Handle coherence violation event
     * @private
     * @param {Object} event - Coherence violation event data
     */
    _onCoherenceViolation(event) {
      Prime.Logger.warn(`Coherence violation on node ${event.nodeId}`, {
        taskId: event.taskId,
        type: event.type,
        severity: event.severity,
      });

      // Update global coherence score
      this.metrics.globalCoherenceScore *= 0.9;

      // If global coherence too low, trigger recovery
      if (
        this.metrics.globalCoherenceScore <
        this.config.coherencePolicy.minCoherenceThreshold
      ) {
        this._triggerCoherenceRecovery();
      }
    }

    /**
     * Perform a cluster-wide coherence check
     * @private
     */
    async _performClusterCoherenceCheck() {
      // Collect coherence reports from all nodes
      const coherencePromises = [];

      for (const [nodeId, node] of this.nodes.entries()) {
        // Create a coherence check task for each node
        const task = {
          id: `coherence_check_${nodeId}_${Date.now()}`,
          type: "coherence_check",
          data: {
            checkType: "full",
            timestamp: Date.now(),
          },
        };

        coherencePromises.push(
          this.submitTask(task, [nodeId]).catch((error) => {
            Prime.Logger.error(
              `Coherence check failed on node ${nodeId}`,
              error,
            );
            return { score: 0 };
          }),
        );
      }

      // Wait for all coherence checks to complete
      const results = await Promise.all(coherencePromises);

      // Calculate average coherence score
      let totalScore = 0;
      for (const result of results) {
        totalScore += result.score || 0;
      }

      const averageScore = results.length > 0 ? totalScore / results.length : 0;

      // Update global coherence score
      this.metrics.globalCoherenceScore = averageScore;

      Prime.Logger.info(`Cluster coherence check complete`, {
        score: averageScore,
        nodeCount: results.length,
      });

      // If coherence is too low, trigger recovery
      if (averageScore < this.config.coherencePolicy.minCoherenceThreshold) {
        this._triggerCoherenceRecovery();
      }
    }

    /**
     * Trigger coherence recovery procedure
     * @private
     */
    _triggerCoherenceRecovery() {
      Prime.Logger.warn(`Triggering coherence recovery`, {
        strategy: this.config.coherencePolicy.recoveryStrategy,
        currentScore: this.metrics.globalCoherenceScore,
      });

      // Implement recovery strategy based on configuration
      switch (this.config.coherencePolicy.recoveryStrategy) {
        case "rollback":
          // Would implement rollback to last known good state
          // Simplified version just logs the action
          Prime.Logger.info("Rolling back to last known coherent state");
          this.metrics.globalCoherenceScore = Math.max(
            0.7,
            this.metrics.globalCoherenceScore,
          );
          break;

        case "rebalance":
          // Would implement task rebalancing
          // Simplified version reassigns all pending tasks
          this._reassignPendingTasks();
          Prime.Logger.info("Rebalancing tasks across cluster nodes");
          break;

        case "restart":
          // Would implement node restart
          // Simplified version just logs the action
          Prime.Logger.info(
            "Restarting affected nodes would occur in a real implementation",
          );
          break;

        default:
          Prime.Logger.warn(
            `Unknown recovery strategy: ${this.config.coherencePolicy.recoveryStrategy}`,
          );
      }
    }

    /**
     * Reassign pending tasks in the task registry
     * @private
     */
    _reassignPendingTasks() {
      for (const [taskId, taskInfo] of this.taskRegistry.entries()) {
        if (!this.taskAssignments.has(taskId)) {
          // Task not assigned, try to assign it
          this._assignTask(taskId);
        }
      }
    }

    /**
     * Reassign tasks from a specific node
     * @private
     * @param {string} nodeId - ID of node whose tasks need reassignment
     */
    _reassignTasksFromNode(nodeId) {
      // Find tasks assigned to this node
      for (const [taskId, assignedNodeId] of this.taskAssignments.entries()) {
        if (assignedNodeId === nodeId) {
          // Remove assignment
          this.taskAssignments.delete(taskId);

          // Try to reassign
          this._assignTask(taskId);
        }
      }
    }

    /**
     * Get cluster metrics
     * @returns {Object} Current cluster metrics
     */
    getMetrics() {
      const metrics = { ...this.metrics };

      // Add node count statistics
      metrics.totalNodes = this.nodes.size;
      metrics.readyNodes = [...this.nodes.values()].filter(
        (node) => node.state === NodeState.READY,
      ).length;
      metrics.workingNodes = [...this.nodes.values()].filter(
        (node) => node.state === NodeState.WORKING,
      ).length;

      // Add task statistics
      metrics.pendingTasks = this.taskRegistry.size;

      return metrics;
    }

    /**
     * Shut down the cluster
     * @returns {Promise<void>} Promise that resolves when shutdown is complete
     */
    async shutdown() {
      Prime.Logger.info("Shutting down cluster manager");

      // Terminate all nodes
      const terminationPromises = [];

      for (const [nodeId, node] of this.nodes.entries()) {
        terminationPromises.push(
          node.terminate().catch((error) => {
            Prime.Logger.error(`Failed to terminate node ${nodeId}`, error);
          }),
        );
      }

      // Wait for all nodes to terminate
      await Promise.all(terminationPromises);

      // Clear all registries
      this.nodes.clear();
      this.taskRegistry.clear();
      this.taskAssignments.clear();

      // Remove all event listeners
      this.eventBus.removeAllListeners();

      Prime.Logger.info("Cluster manager shutdown complete");
    }
  }

  // Add classes to Prime.Distributed namespace
  Prime.Distributed.Cluster = {
    NodeType,
    NodeState,
    ClusterNode,
    ClusterManager,
  };
})();

// Export the enhanced Prime object
module.exports = Prime;
