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

      // Use enhanced coherence module if available
      if (Prime.Distributed && Prime.Distributed.Coherence) {
        try {
          // Create layer object from parameters
          const layer = {
            id: data.layerId || 'coherence_check_layer',
            config: layerConfig,
            weights: parameters.weights,
            biases: parameters.biases
          };
          
          // Create context object with additional information
          const context = {
            isDistributed: true,
            nodeId: this.id,
            nodeType: this.type,
            checkTime: Date.now()
          };
          
          // Add global parameters if provided
          if (data.globalParams) {
            context.globalParams = data.globalParams;
          }
          
          // Add gradients if provided
          if (data.gradients) {
            context.gradients = data.gradients;
          }
          
          // Create coherence manager
          const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
          
          // Perform comprehensive coherence check
          const result = coherenceManager.checkLayerCoherence(layer, context);
          
          // If coherence violations detected, emit event
          if (!result.isCoherent) {
            for (const violation of result.violations) {
              this.eventBus.emit('coherence:violation', {
                taskId: data.taskId,
                type: violation.type,
                severity: violation.severity,
                score: violation.score,
                message: violation.message
              });
            }
            
            // If automatic correction is requested, apply corrections
            if (data.autoCorrect) {
              const correctionResult = coherenceManager.applyCoherenceCorrection(
                layer, 
                result.violations,
                context
              );
              
              // Return corrected parameters if corrections were applied
              if (correctionResult.applied) {
                result.correctionApplied = true;
                result.correctedParameters = {
                  weights: layer.weights,
                  biases: layer.biases
                };
              }
            }
          }
          
          return result;
        } catch (e) {
          // Fallback to legacy implementation if error occurs
          Prime.Logger.warn('Error using enhanced coherence check, falling back to legacy implementation', {
            error: e.message
          });
          return this._legacyHandleCoherenceCheck(data);
        }
      } else {
        // Use legacy implementation if coherence module not available
        return this._legacyHandleCoherenceCheck(data);
      }
    }
    
    /**
     * Legacy coherence check task handler
     * @private
     * @param {Object} data - Task input data
     * @returns {Promise<Object>} Task result
     */
    async _legacyHandleCoherenceCheck(data) {
      // Extract layer information
      const { layerConfig, parameters } = data;

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
      // Use the dedicated coherence manager if available
      if (Prime.Distributed && Prime.Distributed.Coherence) {
        try {
          // Create temporary layer structure
          const layer = {
            id: 'temp_layer',
            config: config,
            weights: Array.isArray(parameters) && Array.isArray(parameters[0]) ? parameters : null,
            biases: Array.isArray(parameters) && !Array.isArray(parameters[0]) ? parameters : null
          };
          
          // If parameters doesn't match expected types, use default implementation
          if (!layer.weights && !layer.biases) {
            return this._legacyCalculateCoherence(parameters, config);
          }
          
          // Create a temporary coherence manager
          const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
          
          // Check coherence
          const result = coherenceManager.checkLayerCoherence(layer);
          
          return result.coherenceScore;
        } catch (e) {
          // Fallback to legacy implementation if error occurs
          Prime.Logger.warn('Error using enhanced coherence check, falling back to legacy implementation', {
            error: e.message
          });
          return this._legacyCalculateCoherence(parameters, config);
        }
      } else {
        // Fallback to legacy implementation if coherence module not available
        return this._legacyCalculateCoherence(parameters, config);
      }
    }
    
    /**
     * Legacy coherence calculation method
     * @private
     * @param {Array|Matrix} parameters - Parameters to check
     * @param {Object} config - Layer configuration
     * @returns {number} Coherence score between 0 and 1
     */
    _legacyCalculateCoherence(parameters, config) {
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
     * @param {Object} [config.networkPartitionDetection={}] - Network partition detection settings
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
        networkPartitionDetection: config.networkPartitionDetection || {
          enabled: true,
          heartbeatInterval: 5000,
          heartbeatTimeout: 15000,
          consensusThreshold: 0.6,
          minPartitionSize: 2,
          autoRecovery: true
        }
      };

      // Node registry
      this.nodes = new Map(); // nodeId -> node

      // Task tracking
      this.taskRegistry = new Map(); // taskId -> task info
      this.taskAssignments = new Map(); // taskId -> nodeId

      // Network partition tracking
      this.partitionRegistry = new Map(); // partitionId -> partition info
      this.nodePartitions = new Map(); // nodeId -> partitionId
      this.heartbeatTimestamps = new Map(); // nodeId -> last heartbeat timestamp
      this.nodeConnectivity = new Map(); // nodeId -> Set of connected nodeIds

      // Performance tracking
      this.metrics = {
        totalTasks: 0,
        completedTasks: 0,
        failedTasks: 0,
        averageProcessingTime: 0,
        globalCoherenceScore: 1.0,
        networkPartitions: 0,
        partitionRecoveries: 0,
        currentPartitionCount: 0,
      };

      // Create cluster event bus
      this.eventBus = new EventBus();

      // Set up event listeners
      this._setupEventListeners();

      // Start network partition detection if enabled
      if (this.config.networkPartitionDetection.enabled) {
        this._startPartitionDetection();
      }

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

      // Check if this is a network-related coherence violation
      if (event.type === Prime.Distributed.Coherence.CoherenceViolationType.NETWORK) {
        // Network partitions should trigger network partition detection
        this._checkForNetworkPartition(event.nodeId);
      }

      // If global coherence too low, trigger recovery
      if (
        this.metrics.globalCoherenceScore <
        this.config.coherencePolicy.minCoherenceThreshold
      ) {
        this._triggerCoherenceRecovery();
      }
    }
    
    /**
     * Start network partition detection
     * @private
     */
    _startPartitionDetection() {
      // Set up heartbeat monitoring
      this._heartbeatInterval = setInterval(() => {
        this._monitorHeartbeats();
      }, this.config.networkPartitionDetection.heartbeatInterval);
      
      // Set up connectivity graph update
      this._connectivityInterval = setInterval(() => {
        this._updateConnectivityGraph();
      }, this.config.networkPartitionDetection.heartbeatInterval * 2);
      
      // Register for heartbeat events
      this.eventBus.on('node:heartbeat', this._onNodeHeartbeat.bind(this));
      
      Prime.Logger.info('Network partition detection started', {
        heartbeatInterval: this.config.networkPartitionDetection.heartbeatInterval,
        heartbeatTimeout: this.config.networkPartitionDetection.heartbeatTimeout
      });
    }
    
    /**
     * Handle node heartbeat
     * @private
     * @param {Object} event - Heartbeat event data
     */
    _onNodeHeartbeat(event) {
      const nodeId = event.nodeId;
      
      // Update last heartbeat timestamp
      this.heartbeatTimestamps.set(nodeId, Date.now());
      
      // If the node was previously suspected as partitioned, check if it's back
      if (this.nodePartitions.has(nodeId)) {
        const partitionId = this.nodePartitions.get(nodeId);
        const partition = this.partitionRegistry.get(partitionId);
        
        // If this node can communicate with the main partition now, it may be healed
        if (partition && partition.isMinority) {
          this._checkPartitionHealing(nodeId, partition);
        }
      }
      
      // Update node's visible peers if provided
      if (event.visiblePeers && Array.isArray(event.visiblePeers)) {
        if (!this.nodeConnectivity.has(nodeId)) {
          this.nodeConnectivity.set(nodeId, new Set());
        }
        
        const connectivity = this.nodeConnectivity.get(nodeId);
        event.visiblePeers.forEach(peerId => connectivity.add(peerId));
      }
    }
    
    /**
     * Monitor node heartbeats to detect potential partitions
     * @private
     */
    _monitorHeartbeats() {
      const now = Date.now();
      const timeout = this.config.networkPartitionDetection.heartbeatTimeout;
      const timeoutNodes = [];
      
      // Check for nodes that have timed out
      for (const [nodeId, lastHeartbeat] of this.heartbeatTimestamps.entries()) {
        if (now - lastHeartbeat > timeout) {
          timeoutNodes.push(nodeId);
        }
      }
      
      // If any nodes timed out, check for network partition
      if (timeoutNodes.length > 0) {
        Prime.Logger.warn(`Heartbeat timeout detected for ${timeoutNodes.length} nodes`, {
          nodes: timeoutNodes
        });
        
        // Trigger network partition detection for each timed out node
        for (const nodeId of timeoutNodes) {
          this._checkForNetworkPartition(nodeId);
        }
      }
    }
    
    /**
     * Update the connectivity graph between nodes
     * @private
     */
    _updateConnectivityGraph() {
      // Skip if we don't have enough nodes
      if (this.nodes.size < 3) {
        return;
      }
      
      // Analyze connectivity data to identify partitions
      const partitions = this._detectPartitionsFromConnectivity();
      
      if (partitions.length > 1) {
        Prime.Logger.warn(`Detected ${partitions.length} network partitions based on connectivity graph`);
        
        // Process detected partitions
        this._handleDetectedPartitions(partitions);
      }
    }
    
    /**
     * Check if a specific node might be in a network partition
     * @private
     * @param {string} suspectNodeId - ID of node to check
     */
    _checkForNetworkPartition(suspectNodeId) {
      // Skip if the node doesn't exist
      if (!this.nodes.has(suspectNodeId)) {
        return;
      }
      
      // Get the suspect node's connectivity
      const suspectConnectivity = this.nodeConnectivity.get(suspectNodeId) || new Set();
      
      // Count how many other nodes can see this node
      let visibleToCount = 0;
      for (const [nodeId, connectivity] of this.nodeConnectivity.entries()) {
        if (nodeId !== suspectNodeId && connectivity.has(suspectNodeId)) {
          visibleToCount++;
        }
      }
      
      // Calculate how many nodes this node can see
      const canSeeCount = suspectConnectivity.size;
      
      // Calculate visibility ratios
      const visibilityRatio = visibleToCount / (this.nodes.size - 1);
      const canSeeRatio = canSeeCount / (this.nodes.size - 1);
      
      // If the node can see less than threshold % of nodes and is seen by less than threshold % of nodes
      const threshold = this.config.networkPartitionDetection.consensusThreshold;
      if (visibilityRatio < threshold && canSeeRatio < threshold) {
        Prime.Logger.warn(`Potential network partition detected for node ${suspectNodeId}`, {
          visibilityRatio,
          canSeeRatio,
          threshold
        });
        
        // Create a partition for this node if it's not already in one
        if (!this.nodePartitions.has(suspectNodeId)) {
          this._createPartition([suspectNodeId]);
        }
      }
    }
    
    /**
     * Detect network partitions from connectivity data
     * @private
     * @returns {Array<Array<string>>} Detected partitions (arrays of node IDs)
     */
    _detectPartitionsFromConnectivity() {
      // Skip if we don't have enough nodes
      if (this.nodes.size < 2) {
        return [[...this.nodes.keys()]];
      }
      
      // Build an undirected graph based on bidirectional connections
      const graph = {};
      for (const nodeId of this.nodes.keys()) {
        graph[nodeId] = [];
      }
      
      // Populate graph with bidirectional connections
      for (const [nodeId1, connections] of this.nodeConnectivity.entries()) {
        for (const nodeId2 of connections) {
          if (this.nodeConnectivity.has(nodeId2) && 
              this.nodeConnectivity.get(nodeId2).has(nodeId1)) {
            if (!graph[nodeId1]) graph[nodeId1] = [];
            if (!graph[nodeId2]) graph[nodeId2] = [];
            graph[nodeId1].push(nodeId2);
            graph[nodeId2].push(nodeId1);
          }
        }
      }
      
      // Use DFS to identify connected components (partitions)
      const visited = {};
      const partitions = [];
      
      for (const nodeId of Object.keys(graph)) {
        if (!visited[nodeId]) {
          const partition = [];
          this._dfs(graph, nodeId, visited, partition);
          if (partition.length > 0) {
            partitions.push(partition);
          }
        }
      }
      
      return partitions;
    }
    
    /**
     * Depth-first search for connected components
     * @private
     * @param {Object} graph - Connectivity graph
     * @param {string} nodeId - Current node ID
     * @param {Object} visited - Visited nodes tracking
     * @param {Array<string>} partition - Current partition being built
     */
    _dfs(graph, nodeId, visited, partition) {
      visited[nodeId] = true;
      partition.push(nodeId);
      
      if (graph[nodeId]) {
        for (const neighbor of graph[nodeId]) {
          if (!visited[neighbor]) {
            this._dfs(graph, neighbor, visited, partition);
          }
        }
      }
    }
    
    /**
     * Handle detected network partitions
     * @private
     * @param {Array<Array<string>>} partitions - Detected partitions
     */
    _handleDetectedPartitions(partitions) {
      // Find the largest partition
      let largestPartition = partitions[0];
      for (const partition of partitions) {
        if (partition.length > largestPartition.length) {
          largestPartition = partition;
        }
      }
      
      // Create partition entries for all partitions except the largest
      for (const partition of partitions) {
        if (partition !== largestPartition && 
            partition.length >= this.config.networkPartitionDetection.minPartitionSize) {
          this._createPartition(partition);
        }
      }
      
      // Register largest partition if it's not already registered
      const largestPartitionId = this._findPartitionContainingNodes(largestPartition);
      if (!largestPartitionId) {
        this._createPartition(largestPartition, false); // Not a minority partition
      }
      
      // Update metrics
      this.metrics.currentPartitionCount = this.partitionRegistry.size;
      
      // Emit event
      this.eventBus.emit('network:partitioned', {
        partitions: partitions.length,
        largestSize: largestPartition.length,
        timestamp: Date.now()
      });
      
      // If auto recovery is enabled, trigger recovery
      if (this.config.networkPartitionDetection.autoRecovery) {
        this._triggerPartitionRecovery();
      }
    }
    
    /**
     * Find if a partition containing specific nodes already exists
     * @private
     * @param {Array<string>} nodeIds - Node IDs to check
     * @returns {string|null} Partition ID if found, null otherwise
     */
    _findPartitionContainingNodes(nodeIds) {
      // Check if all nodes are in the same partition
      const partitionIds = new Set();
      
      for (const nodeId of nodeIds) {
        if (this.nodePartitions.has(nodeId)) {
          partitionIds.add(this.nodePartitions.get(nodeId));
        }
      }
      
      // If all nodes are in exactly one partition, return that partition ID
      if (partitionIds.size === 1) {
        return [...partitionIds][0];
      }
      
      return null;
    }
    
    /**
     * Create a new network partition record
     * @private
     * @param {Array<string>} nodeIds - Node IDs in the partition
     * @param {boolean} [isMinority=true] - Whether this is a minority partition
     * @returns {string} Created partition ID
     */
    _createPartition(nodeIds, isMinority = true) {
      // Generate a unique partition ID
      const partitionId = `partition_${Date.now()}_${this.metrics.networkPartitions}`;
      
      // Create partition record
      const partition = {
        id: partitionId,
        nodeIds: [...nodeIds],
        detectedAt: Date.now(),
        isMinority,
        recoveryAttempts: 0,
        state: 'detected'
      };
      
      // Register partition
      this.partitionRegistry.set(partitionId, partition);
      
      // Associate nodes with this partition
      for (const nodeId of nodeIds) {
        this.nodePartitions.set(nodeId, partitionId);
      }
      
      // Update metrics
      this.metrics.networkPartitions++;
      this.metrics.currentPartitionCount = this.partitionRegistry.size;
      
      // Emit partition event
      this.eventBus.emit('network:partition:created', {
        partitionId,
        nodeCount: nodeIds.length,
        isMinority,
        timestamp: Date.now()
      });
      
      Prime.Logger.warn(`Created network partition ${partitionId} with ${nodeIds.length} nodes`, {
        nodeIds,
        isMinority
      });
      
      return partitionId;
    }
    
    /**
     * Check if a partition is healing
     * @private
     * @param {string} nodeId - Node ID that might have recovered
     * @param {Object} partition - Partition information
     */
    _checkPartitionHealing(nodeId, partition) {
      // Get the main partition
      const mainPartitionId = this._findMainPartition();
      if (!mainPartitionId) return;
      
      // Check if this node can now see nodes in the main partition
      let canSeeMainPartition = false;
      const nodePeers = this.nodeConnectivity.get(nodeId) || new Set();
      
      for (const mainNodeId of this.partitionRegistry.get(mainPartitionId).nodeIds) {
        if (nodePeers.has(mainNodeId)) {
          canSeeMainPartition = true;
          break;
        }
      }
      
      if (canSeeMainPartition) {
        // This node seems to have connectivity to the main partition again
        Prime.Logger.info(`Node ${nodeId} appears to have reconnected to the main partition`);
        
        // Check if all nodes in this partition can see the main partition
        let allNodesRecovered = true;
        for (const peerNodeId of partition.nodeIds) {
          if (peerNodeId === nodeId) continue;
          
          const peerConnectivity = this.nodeConnectivity.get(peerNodeId) || new Set();
          let peerCanSeeMain = false;
          
          for (const mainNodeId of this.partitionRegistry.get(mainPartitionId).nodeIds) {
            if (peerConnectivity.has(mainNodeId)) {
              peerCanSeeMain = true;
              break;
            }
          }
          
          if (!peerCanSeeMain) {
            allNodesRecovered = false;
            break;
          }
        }
        
        if (allNodesRecovered) {
          // All nodes in this partition appear to have healed
          this._healPartition(partition.id);
        } else {
          // Only this node has healed, move it to the main partition
          this._moveNodeToPartition(nodeId, mainPartitionId);
        }
      }
    }
    
    /**
     * Find the main (largest) partition
     * @private
     * @returns {string|null} Main partition ID or null if none found
     */
    _findMainPartition() {
      let mainPartitionId = null;
      let maxSize = 0;
      
      for (const [partitionId, partition] of this.partitionRegistry.entries()) {
        if (!partition.isMinority && partition.nodeIds.length > maxSize) {
          mainPartitionId = partitionId;
          maxSize = partition.nodeIds.length;
        }
      }
      
      return mainPartitionId;
    }
    
    /**
     * Move a node to a different partition
     * @private
     * @param {string} nodeId - Node ID to move
     * @param {string} targetPartitionId - Target partition ID
     */
    _moveNodeToPartition(nodeId, targetPartitionId) {
      // Check if node is in a partition
      if (!this.nodePartitions.has(nodeId)) return;
      
      const sourcePartitionId = this.nodePartitions.get(nodeId);
      const sourcePartition = this.partitionRegistry.get(sourcePartitionId);
      const targetPartition = this.partitionRegistry.get(targetPartitionId);
      
      if (!sourcePartition || !targetPartition) return;
      
      // Remove from source partition
      sourcePartition.nodeIds = sourcePartition.nodeIds.filter(id => id !== nodeId);
      
      // Add to target partition
      targetPartition.nodeIds.push(nodeId);
      
      // Update node partition mapping
      this.nodePartitions.set(nodeId, targetPartitionId);
      
      // If source partition is now empty, remove it
      if (sourcePartition.nodeIds.length === 0) {
        this.partitionRegistry.delete(sourcePartitionId);
        this.metrics.currentPartitionCount = this.partitionRegistry.size;
      }
      
      Prime.Logger.info(`Moved node ${nodeId} from partition ${sourcePartitionId} to ${targetPartitionId}`);
      
      // Emit move event
      this.eventBus.emit('network:partition:node:moved', {
        nodeId,
        sourcePartitionId,
        targetPartitionId,
        timestamp: Date.now()
      });
    }
    
    /**
     * Heal a network partition
     * @private
     * @param {string} partitionId - Partition ID to heal
     */
    _healPartition(partitionId) {
      const partition = this.partitionRegistry.get(partitionId);
      if (!partition) return;
      
      const mainPartitionId = this._findMainPartition();
      if (!mainPartitionId) return;
      
      // Move all nodes to the main partition
      for (const nodeId of partition.nodeIds) {
        this._moveNodeToPartition(nodeId, mainPartitionId);
      }
      
      // Delete the healed partition
      this.partitionRegistry.delete(partitionId);
      
      // Update metrics
      this.metrics.partitionRecoveries++;
      this.metrics.currentPartitionCount = this.partitionRegistry.size;
      
      Prime.Logger.info(`Healed network partition ${partitionId}`);
      
      // Emit heal event
      this.eventBus.emit('network:partition:healed', {
        partitionId,
        mainPartitionId,
        timestamp: Date.now()
      });
    }
    
    /**
     * Trigger recovery for all partitions
     * @private
     */
    _triggerPartitionRecovery() {
      // For each minority partition, try to recover
      for (const [partitionId, partition] of this.partitionRegistry.entries()) {
        if (partition.isMinority) {
          // Update partition state
          partition.state = 'recovering';
          partition.recoveryAttempts++;
          
          Prime.Logger.info(`Attempting recovery for partition ${partitionId} (attempt ${partition.recoveryAttempts})`);
          
          // Emit recovery attempt event
          this.eventBus.emit('network:partition:recovery:attempt', {
            partitionId,
            attempt: partition.recoveryAttempts,
            timestamp: Date.now()
          });
          
          // Trigger coherence violations for all nodes in this partition
          for (const nodeId of partition.nodeIds) {
            if (this.nodes.has(nodeId)) {
              this.eventBus.emit('coherence:violation', {
                nodeId,
                type: Prime.Distributed.Coherence.CoherenceViolationType.NETWORK,
                severity: Prime.Distributed.Coherence.ViolationSeverity.HIGH,
                message: `Node is in network partition ${partitionId}`,
              });
            }
          }
        }
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

      // Stop network partition detection
      if (this._heartbeatInterval) {
        clearInterval(this._heartbeatInterval);
      }
      
      if (this._connectivityInterval) {
        clearInterval(this._connectivityInterval);
      }

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
      this.partitionRegistry.clear();
      this.nodePartitions.clear();
      this.heartbeatTimestamps.clear();
      this.nodeConnectivity.clear();

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
