/**
 * PrimeOS JavaScript Library - Distributed Task Distribution Module
 * Handles distribution and execution of tasks across cluster nodes
 */

// Import the Prime object from core
const Prime = require("../../core");
const EventBus = require("../event-bus");

/**
 * Task states for distributed computation
 * @enum {string}
 */
const TaskState = {
  /** Task is created but not yet assigned */
  PENDING: "pending",
  /** Task is assigned to a node */
  ASSIGNED: "assigned",
  /** Task is currently executing */
  EXECUTING: "executing",
  /** Task has completed successfully */
  COMPLETED: "completed",
  /** Task has failed */
  FAILED: "failed",
  /** Task was canceled */
  CANCELED: "canceled"
};

/**
 * Task priorities for scheduling
 * @enum {number}
 */
const TaskPriority = {
  /** Low priority tasks */
  LOW: 0,
  /** Normal priority tasks */
  NORMAL: 5,
  /** High priority tasks */
  HIGH: 10,
  /** Critical priority tasks */
  CRITICAL: 15
};

/**
 * Distributed task for cluster computation
 * Represents a unit of work that can be distributed to nodes
 */
class DistributedTask {
  /**
   * Create a new distributed task
   * @param {Object} config - Task configuration
   * @param {string} config.id - Unique identifier for this task
   * @param {string} config.type - Type of task
   * @param {Object} config.data - Task input data
   * @param {Object} [config.requiredCapabilities={}] - Capabilities required to execute this task
   * @param {number} [config.priority=TaskPriority.NORMAL] - Task priority
   * @param {number} [config.timeout=30000] - Task execution timeout in ms
   */
  constructor(config) {
    if (!Prime.Utils.isObject(config)) {
      throw new Prime.ValidationError("Task configuration must be an object");
    }

    if (!config.id) {
      throw new Prime.ValidationError("Task ID is required");
    }

    if (!config.type) {
      throw new Prime.ValidationError("Task type is required");
    }

    this.id = config.id;
    this.type = config.type;
    this.data = config.data || {};
    this.requiredCapabilities = config.requiredCapabilities || {};
    this.priority = config.priority !== undefined ? config.priority : TaskPriority.NORMAL;
    this.timeout = config.timeout || 30000;

    // Task state tracking
    this.state = TaskState.PENDING;
    this.createdAt = Date.now();
    this.assignedAt = null;
    this.executionStartedAt = null;
    this.completedAt = null;
    this.assignedNodeId = null;
    this.result = null;
    this.error = null;
    
    // Retry tracking
    this.retryCount = 0;
    this.maxRetries = config.maxRetries || 3;
    this.lastError = null;
  }

  /**
   * Assign this task to a node
   * @param {string} nodeId - ID of the node to assign to
   * @returns {boolean} Whether the assignment was successful
   */
  assign(nodeId) {
    if (this.state !== TaskState.PENDING && this.state !== TaskState.FAILED) {
      return false;
    }
    
    this.state = TaskState.ASSIGNED;
    this.assignedAt = Date.now();
    this.assignedNodeId = nodeId;
    
    return true;
  }

  /**
   * Mark this task as executing
   * @returns {boolean} Whether the update was successful
   */
  markExecuting() {
    if (this.state !== TaskState.ASSIGNED) {
      return false;
    }
    
    this.state = TaskState.EXECUTING;
    this.executionStartedAt = Date.now();
    
    return true;
  }

  /**
   * Complete this task with a result
   * @param {*} result - Task result
   * @returns {boolean} Whether the update was successful
   */
  complete(result) {
    if (this.state !== TaskState.EXECUTING && this.state !== TaskState.ASSIGNED) {
      return false;
    }
    
    this.state = TaskState.COMPLETED;
    this.completedAt = Date.now();
    this.result = result;
    
    return true;
  }

  /**
   * Mark this task as failed
   * @param {Error} error - Error that caused the failure
   * @returns {boolean} Whether the update was successful
   */
  fail(error) {
    if (this.state !== TaskState.EXECUTING && this.state !== TaskState.ASSIGNED) {
      return false;
    }
    
    // Track error
    this.lastError = {
      message: error.message,
      stack: error.stack,
      timestamp: Date.now()
    };
    
    // Increment retry count
    this.retryCount++;
    
    // If we haven't exceeded max retries, reset to pending
    if (this.retryCount <= this.maxRetries) {
      this.state = TaskState.PENDING;
      this.assignedNodeId = null;
      this.assignedAt = null;
      this.executionStartedAt = null;
      return true;
    }
    
    // Otherwise, mark as failed
    this.state = TaskState.FAILED;
    this.completedAt = Date.now();
    this.error = this.lastError;
    
    return true;
  }

  /**
   * Cancel this task
   * @returns {boolean} Whether the cancellation was successful
   */
  cancel() {
    if (this.state === TaskState.COMPLETED || this.state === TaskState.FAILED || this.state === TaskState.CANCELED) {
      return false;
    }
    
    this.state = TaskState.CANCELED;
    this.completedAt = Date.now();
    
    return true;
  }

  /**
   * Check if this task has timed out
   * @returns {boolean} Whether the task has timed out
   */
  hasTimedOut() {
    if (this.state !== TaskState.EXECUTING && this.state !== TaskState.ASSIGNED) {
      return false;
    }
    
    const executionTime = Date.now() - (this.executionStartedAt || this.assignedAt);
    return executionTime > this.timeout;
  }

  /**
   * Get the execution time of this task
   * @returns {number} Execution time in milliseconds
   */
  getExecutionTime() {
    if (!this.assignedAt) {
      return 0;
    }
    
    const end = this.completedAt || Date.now();
    return end - this.assignedAt;
  }

  /**
   * Get the current status of this task
   * @returns {Object} Task status
   */
  getStatus() {
    return {
      id: this.id,
      type: this.type,
      state: this.state,
      priority: this.priority,
      createdAt: this.createdAt,
      assignedAt: this.assignedAt,
      executionStartedAt: this.executionStartedAt,
      completedAt: this.completedAt,
      assignedNodeId: this.assignedNodeId,
      executionTime: this.getExecutionTime(),
      retryCount: this.retryCount,
      maxRetries: this.maxRetries,
      timeout: this.timeout,
      hasTimedOut: this.hasTimedOut()
    };
  }
}

/**
 * Task queue for managing distributed tasks
 */
class TaskQueue {
  /**
   * Create a new task queue
   * @param {Object} [config={}] - Queue configuration
   */
  constructor(config = {}) {
    this.config = {
      maxQueueSize: config.maxQueueSize || 1000,
      ...config
    };
    
    this.tasks = new Map(); // taskId -> task
    this.pendingTasks = []; // Tasks waiting for assignment
    this.eventBus = new EventBus();
  }

  /**
   * Add a task to the queue
   * @param {DistributedTask|Object} task - Task or task configuration
   * @returns {DistributedTask} Added task
   */
  addTask(task) {
    // Check queue size limit
    if (this.tasks.size >= this.config.maxQueueSize) {
      throw new Prime.InvalidOperationError("Task queue is full");
    }
    
    // Convert configuration object to task if needed
    const distributedTask = task instanceof DistributedTask 
      ? task 
      : new DistributedTask(task);
    
    // Check if task already exists
    if (this.tasks.has(distributedTask.id)) {
      throw new Prime.ValidationError(`Task with ID ${distributedTask.id} already exists`);
    }
    
    // Add task to maps
    this.tasks.set(distributedTask.id, distributedTask);
    this.pendingTasks.push(distributedTask);
    
    // Sort pending tasks by priority
    this._sortPendingTasks();
    
    // Emit event
    this.eventBus.emit("task:added", {
      taskId: distributedTask.id,
      timestamp: Date.now()
    });
    
    return distributedTask;
  }

  /**
   * Get the next pending task
   * @param {Object} [criteria={}] - Criteria for task selection
   * @returns {DistributedTask} Next pending task
   */
  getNextPendingTask(criteria = {}) {
    // Filter pending tasks by criteria
    const eligible = this.pendingTasks.filter(task => {
      // Match criteria
      for (const [key, value] of Object.entries(criteria)) {
        if (key === 'requiredCapabilities') {
          // Check capabilities
          for (const [capability, minValue] of Object.entries(value)) {
            if (!task.requiredCapabilities[capability] || 
                task.requiredCapabilities[capability] < minValue) {
              return false;
            }
          }
        } else if (task[key] !== value) {
          return false;
        }
      }
      return true;
    });
    
    // Return highest priority eligible task
    return eligible.length > 0 ? eligible[0] : null;
  }

  /**
   * Get a task by ID
   * @param {string} taskId - Task ID
   * @returns {DistributedTask} Task
   */
  getTask(taskId) {
    return this.tasks.get(taskId);
  }

  /**
   * Assign a task to a node
   * @param {string} taskId - Task ID
   * @param {string} nodeId - Node ID
   * @returns {boolean} Whether the assignment was successful
   */
  assignTask(taskId, nodeId) {
    const task = this.tasks.get(taskId);
    if (!task) {
      return false;
    }
    
    // Assign task
    const success = task.assign(nodeId);
    
    if (success) {
      // Remove from pending tasks
      this.pendingTasks = this.pendingTasks.filter(t => t.id !== taskId);
      
      // Emit event
      this.eventBus.emit("task:assigned", {
        taskId,
        nodeId,
        timestamp: Date.now()
      });
    }
    
    return success;
  }

  /**
   * Mark a task as executing
   * @param {string} taskId - Task ID
   * @returns {boolean} Whether the update was successful
   */
  markTaskExecuting(taskId) {
    const task = this.tasks.get(taskId);
    if (!task) {
      return false;
    }
    
    // Mark task as executing
    const success = task.markExecuting();
    
    if (success) {
      // Emit event
      this.eventBus.emit("task:executing", {
        taskId,
        nodeId: task.assignedNodeId,
        timestamp: Date.now()
      });
    }
    
    return success;
  }

  /**
   * Complete a task
   * @param {string} taskId - Task ID
   * @param {*} result - Task result
   * @returns {boolean} Whether the update was successful
   */
  completeTask(taskId, result) {
    const task = this.tasks.get(taskId);
    if (!task) {
      return false;
    }
    
    // Complete task
    const success = task.complete(result);
    
    if (success) {
      // Emit event
      this.eventBus.emit("task:completed", {
        taskId,
        nodeId: task.assignedNodeId,
        result,
        timestamp: Date.now()
      });
    }
    
    return success;
  }

  /**
   * Mark a task as failed
   * @param {string} taskId - Task ID
   * @param {Error} error - Error that caused the failure
   * @returns {boolean} Whether the update was successful
   */
  failTask(taskId, error) {
    const task = this.tasks.get(taskId);
    if (!task) {
      return false;
    }
    
    // Fail task
    const success = task.fail(error);
    
    if (success) {
      // If task went back to pending, add it back to pending tasks
      if (task.state === TaskState.PENDING) {
        this.pendingTasks.push(task);
        this._sortPendingTasks();
        
        // Emit retry event
        this.eventBus.emit("task:retry", {
          taskId,
          retryCount: task.retryCount,
          error: error.message,
          timestamp: Date.now()
        });
      } else {
        // Emit failure event
        this.eventBus.emit("task:failed", {
          taskId,
          nodeId: task.assignedNodeId,
          error: error.message,
          retries: task.retryCount,
          timestamp: Date.now()
        });
      }
    }
    
    return success;
  }

  /**
   * Cancel a task
   * @param {string} taskId - Task ID
   * @returns {boolean} Whether the cancellation was successful
   */
  cancelTask(taskId) {
    const task = this.tasks.get(taskId);
    if (!task) {
      return false;
    }
    
    // Cancel task
    const success = task.cancel();
    
    if (success) {
      // Remove from pending tasks if present
      this.pendingTasks = this.pendingTasks.filter(t => t.id !== taskId);
      
      // Emit event
      this.eventBus.emit("task:canceled", {
        taskId,
        nodeId: task.assignedNodeId,
        timestamp: Date.now()
      });
    }
    
    return success;
  }

  /**
   * Remove a task from the queue
   * @param {string} taskId - Task ID
   * @returns {boolean} Whether the removal was successful
   */
  removeTask(taskId) {
    const task = this.tasks.get(taskId);
    if (!task) {
      return false;
    }
    
    // Remove task
    this.tasks.delete(taskId);
    this.pendingTasks = this.pendingTasks.filter(t => t.id !== taskId);
    
    // Emit event
    this.eventBus.emit("task:removed", {
      taskId,
      timestamp: Date.now()
    });
    
    return true;
  }

  /**
   * Check for timed out tasks
   * @returns {Array<string>} IDs of timed out tasks
   */
  checkTimeouts() {
    const timedOutTasks = [];
    
    for (const [taskId, task] of this.tasks.entries()) {
      if (task.hasTimedOut()) {
        timedOutTasks.push(taskId);
        
        // Emit timeout event
        this.eventBus.emit("task:timeout", {
          taskId,
          nodeId: task.assignedNodeId,
          assignedAt: task.assignedAt,
          executionStartedAt: task.executionStartedAt,
          timeout: task.timeout,
          timestamp: Date.now()
        });
      }
    }
    
    return timedOutTasks;
  }

  /**
   * Get all tasks
   * @param {Object} [filter={}] - Filter criteria
   * @returns {Array<DistributedTask>} Tasks
   */
  getAllTasks(filter = {}) {
    return Array.from(this.tasks.values()).filter(task => {
      // Match filter criteria
      for (const [key, value] of Object.entries(filter)) {
        if (task[key] !== value) {
          return false;
        }
      }
      return true;
    });
  }

  /**
   * Get a summary of the task queue
   * @returns {Object} Queue summary
   */
  getSummary() {
    const allTasks = Array.from(this.tasks.values());
    
    // Count tasks by state
    const tasksByState = {};
    for (const state of Object.values(TaskState)) {
      tasksByState[state] = allTasks.filter(task => task.state === state).length;
    }
    
    // Count tasks by type
    const tasksByType = {};
    for (const task of allTasks) {
      tasksByType[task.type] = (tasksByType[task.type] || 0) + 1;
    }
    
    // Calculate average execution time for completed tasks
    const completedTasks = allTasks.filter(task => task.state === TaskState.COMPLETED);
    let avgExecutionTime = 0;
    
    if (completedTasks.length > 0) {
      const totalExecutionTime = completedTasks.reduce(
        (sum, task) => sum + task.getExecutionTime(), 0
      );
      avgExecutionTime = totalExecutionTime / completedTasks.length;
    }
    
    return {
      totalTasks: allTasks.length,
      pendingTasks: this.pendingTasks.length,
      tasksByState,
      tasksByType,
      executionStats: {
        completedTasks: completedTasks.length,
        avgExecutionTime,
        failedTasks: allTasks.filter(task => task.state === TaskState.FAILED).length,
        canceledTasks: allTasks.filter(task => task.state === TaskState.CANCELED).length
      }
    };
  }

  /**
   * Sort pending tasks by priority
   * @private
   */
  _sortPendingTasks() {
    this.pendingTasks.sort((a, b) => {
      // First by priority (higher first)
      const priorityDiff = b.priority - a.priority;
      if (priorityDiff !== 0) {
        return priorityDiff;
      }
      
      // Then by creation time (older first)
      return a.createdAt - b.createdAt;
    });
  }
}

/**
 * Task scheduler for distributing tasks to nodes
 */
class TaskScheduler {
  /**
   * Create a new task scheduler
   * @param {Object} config - Scheduler configuration
   * @param {TaskQueue} config.taskQueue - Task queue
   * @param {NodeRegistry} config.nodeRegistry - Node registry
   */
  constructor(config) {
    if (!config || !config.taskQueue || !config.nodeRegistry) {
      throw new Prime.ValidationError("Task scheduler requires taskQueue and nodeRegistry");
    }
    
    this.taskQueue = config.taskQueue;
    this.nodeRegistry = config.nodeRegistry;
    this.eventBus = new EventBus();
    
    this.config = {
      schedulingInterval: config.schedulingInterval || 1000, // ms
      maxTasksPerNode: config.maxTasksPerNode || 10,
      maxConcurrentAssignments: config.maxConcurrentAssignments || 10,
      ...config
    };
    
    // Scheduling state
    this.isScheduling = false;
    this.schedulingInterval = null;
    this.metrics = {
      schedulingRuns: 0,
      tasksAssigned: 0,
      assignmentFailures: 0,
      lastSchedulingRun: null
    };
  }

  /**
   * Start the scheduler
   * @returns {boolean} Whether the scheduler was started
   */
  start() {
    if (this.isScheduling) {
      return false;
    }
    
    this.isScheduling = true;
    
    // Schedule immediate run
    this._scheduleRun();
    
    // Start interval
    this.schedulingInterval = setInterval(() => {
      this._scheduleRun();
    }, this.config.schedulingInterval);
    
    // Log start
    Prime.Logger.info("Task scheduler started", {
      interval: this.config.schedulingInterval,
      maxTasksPerNode: this.config.maxTasksPerNode
    });
    
    return true;
  }

  /**
   * Stop the scheduler
   * @returns {boolean} Whether the scheduler was stopped
   */
  stop() {
    if (!this.isScheduling) {
      return false;
    }
    
    this.isScheduling = false;
    
    // Clear interval
    if (this.schedulingInterval) {
      clearInterval(this.schedulingInterval);
      this.schedulingInterval = null;
    }
    
    // Log stop
    Prime.Logger.info("Task scheduler stopped", {
      metrics: this.metrics
    });
    
    return true;
  }

  /**
   * Manually trigger a scheduling run
   * @returns {Promise<number>} Number of tasks assigned
   */
  async triggerScheduling() {
    if (!this.isScheduling) {
      return 0;
    }
    
    return this._runScheduling();
  }

  /**
   * Submit a task for execution
   * @param {Object} taskConfig - Task configuration
   * @returns {DistributedTask} Submitted task
   */
  submitTask(taskConfig) {
    // Generate ID if not provided
    if (!taskConfig.id) {
      taskConfig.id = `task_${Date.now()}_${Math.floor(Math.random() * 10000)}`;
    }
    
    // Add task to queue
    const task = this.taskQueue.addTask(taskConfig);
    
    // Trigger scheduling if running
    if (this.isScheduling) {
      this._scheduleRun();
    }
    
    return task;
  }

  /**
   * Schedule a run of the scheduler
   * @private
   */
  _scheduleRun() {
    // Run scheduling asynchronously
    Promise.resolve().then(() => this._runScheduling());
  }

  /**
   * Run the scheduling algorithm
   * @private
   * @returns {Promise<number>} Number of tasks assigned
   */
  async _runScheduling() {
    // Update metrics
    this.metrics.schedulingRuns++;
    this.metrics.lastSchedulingRun = Date.now();
    
    // Check timeouts
    const timedOutTasks = this.taskQueue.checkTimeouts();
    for (const taskId of timedOutTasks) {
      const task = this.taskQueue.getTask(taskId);
      if (task) {
        this.taskQueue.failTask(taskId, new Error("Task timed out"));
      }
    }
    
    // Get available nodes
    const availableNodes = this.nodeRegistry.findNodes({
      state: "ready"
    }).concat(this.nodeRegistry.findNodes({
      state: "working"
    }));
    
    // If no available nodes, nothing to do
    if (availableNodes.length === 0) {
      return 0;
    }
    
    let assignedCount = 0;
    let pendingTask = this.taskQueue.getNextPendingTask();
    
    // Assign tasks until we run out of tasks or hit concurrency limit
    while (pendingTask && assignedCount < this.config.maxConcurrentAssignments) {
      // Find best node for task
      const bestNode = this.nodeRegistry.findBestNodeForTask(pendingTask);
      
      if (bestNode) {
        // Assign task to node
        const taskAssigned = this.taskQueue.assignTask(pendingTask.id, bestNode.id);
        const nodeAccepted = bestNode.assignTask(pendingTask);
        
        if (taskAssigned && nodeAccepted) {
          assignedCount++;
          this.metrics.tasksAssigned++;
          
          // Mark as executing
          this.taskQueue.markTaskExecuting(pendingTask.id);
          
          // Emit event
          this.eventBus.emit("task:scheduled", {
            taskId: pendingTask.id,
            nodeId: bestNode.id,
            timestamp: Date.now()
          });
        } else {
          // Assignment failed
          this.metrics.assignmentFailures++;
          
          // If task was assigned but node didn't accept, fail task
          if (taskAssigned && !nodeAccepted) {
            this.taskQueue.failTask(pendingTask.id, new Error("Node rejected task assignment"));
          }
        }
      } else {
        // No suitable node found, leave task in queue
        this.metrics.assignmentFailures++;
        
        // Log warning
        Prime.Logger.warn(`No suitable node found for task ${pendingTask.id}`, {
          taskType: pendingTask.type,
          requiredCapabilities: pendingTask.requiredCapabilities
        });
        
        break; // No point checking more tasks if no nodes are available
      }
      
      // Get next pending task
      pendingTask = this.taskQueue.getNextPendingTask();
    }
    
    return assignedCount;
  }

  /**
   * Get scheduling status
   * @returns {Object} Scheduler status
   */
  getStatus() {
    return {
      isScheduling: this.isScheduling,
      metrics: {
        ...this.metrics,
        timeSinceLastRun: this.metrics.lastSchedulingRun ? 
          Date.now() - this.metrics.lastSchedulingRun : null
      },
      taskQueueSummary: this.taskQueue.getSummary(),
      nodeRegistrySummary: this.nodeRegistry.getSummary()
    };
  }
}

// Add to Prime namespace
Prime.Distributed = Prime.Distributed || {};
Prime.Distributed.Cluster = Prime.Distributed.Cluster || {};
Prime.Distributed.Cluster.Tasks = {
  TaskState,
  TaskPriority,
  DistributedTask,
  TaskQueue,
  TaskScheduler
};

module.exports = Prime;