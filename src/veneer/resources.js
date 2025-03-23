/**
 * PrimeOS Veneer - Resource Access Facade
 * Provides simplified access to PrimeOS resources
 */

const Prime = require('../core');
const { PrimeError } = require('../core/error');

/**
 * Resource error class
 */
class ResourceError extends PrimeError {
  constructor(message, details = {}, code = 'RESOURCE_ERROR') {
    super(message, details, code);
    this.name = 'ResourceError';
  }
}

/**
 * Base Resource class
 * Base class for all resource types
 */
class Resource {
  /**
   * Create a new resource
   * @param {string} type - Resource type
   * @param {string} id - Resource ID
   * @param {Object} options - Resource options
   */
  constructor(type, id, options = {}) {
    this.type = type;
    this.id = id;
    this.options = options;
    this.allocated = false;
    this.usage = 0;
    this.createdAt = Date.now();
  }
  
  /**
   * Initialize the resource
   * @returns {Promise<void>}
   */
  async init() {
    this.allocated = true;
    Prime.Logger.debug(`Resource initialized: ${this.type}/${this.id}`);
  }
  
  /**
   * Release the resource
   * @returns {Promise<void>}
   */
  async release() {
    this.allocated = false;
    Prime.Logger.debug(`Resource released: ${this.type}/${this.id}`);
  }
  
  /**
   * Get resource usage statistics
   * @returns {Object} - Usage statistics
   */
  getUsage() {
    return {
      type: this.type,
      id: this.id,
      allocated: this.allocated,
      usage: this.usage,
      createdAt: this.createdAt
    };
  }
}

/**
 * Storage Resource
 * Provides access to storage capabilities
 */
class StorageResource extends Resource {
  /**
   * Create a new storage resource
   * @param {string} id - Resource ID
   * @param {Object} options - Storage options
   */
  constructor(id, options = {}) {
    super('storage', id, {
      persistent: options.persistent || false,
      quota: options.quota || '10MB',
      prefix: options.prefix || id,
      ...options
    });
    
    this.storageManager = null;
    this.keyPrefix = this.options.prefix;
  }
  
  /**
   * Initialize the storage resource
   * @returns {Promise<void>}
   */
  async init() {
    await super.init();
    
    // Get storage manager from Prime
    this.storageManager = Prime.Storage.createManager({
      provider: this.options.provider || 'auto'
    });
    
    await this.storageManager.init();
    
    Prime.Logger.info(`Storage resource initialized: ${this.id}`, {
      persistent: this.options.persistent,
      quota: this.options.quota
    });
  }
  
  /**
   * Store data with the given key
   * @param {*} data - Data to store
   * @param {string} key - Storage key
   * @returns {Promise<string>} - Storage ID
   */
  async store(data, key) {
    if (!this.allocated) {
      throw new ResourceError('Storage resource not allocated', {
        resourceId: this.id
      }, 'RESOURCE_NOT_ALLOCATED');
    }
    
    const prefixedKey = `${this.keyPrefix}:${key}`;
    const id = await this.storageManager.store(data, prefixedKey);
    
    // Update usage statistics
    this._updateUsage();
    
    return id;
  }
  
  /**
   * Load data with the given key
   * @param {string} key - Storage key
   * @returns {Promise<*>} - Loaded data
   */
  async load(key) {
    if (!this.allocated) {
      throw new ResourceError('Storage resource not allocated', {
        resourceId: this.id
      }, 'RESOURCE_NOT_ALLOCATED');
    }
    
    const prefixedKey = `${this.keyPrefix}:${key}`;
    return this.storageManager.load(prefixedKey);
  }
  
  /**
   * Delete data with the given key
   * @param {string} key - Storage key
   * @returns {Promise<boolean>} - True if successfully deleted
   */
  async delete(key) {
    if (!this.allocated) {
      throw new ResourceError('Storage resource not allocated', {
        resourceId: this.id
      }, 'RESOURCE_NOT_ALLOCATED');
    }
    
    const prefixedKey = `${this.keyPrefix}:${key}`;
    const result = await this.storageManager.delete(prefixedKey);
    
    // Update usage statistics
    this._updateUsage();
    
    return result;
  }
  
  /**
   * List all keys with the prefix
   * @returns {Promise<string[]>} - Array of keys
   */
  async listKeys() {
    if (!this.allocated) {
      throw new ResourceError('Storage resource not allocated', {
        resourceId: this.id
      }, 'RESOURCE_NOT_ALLOCATED');
    }
    
    const allKeys = await this.storageManager.getAllKeys();
    
    // Filter keys with our prefix
    return allKeys.filter(key => key.startsWith(`${this.keyPrefix}:`))
      .map(key => key.substring(this.keyPrefix.length + 1));
  }
  
  /**
   * Clear all data with the prefix
   * @returns {Promise<void>}
   */
  async clear() {
    if (!this.allocated) {
      throw new ResourceError('Storage resource not allocated', {
        resourceId: this.id
      }, 'RESOURCE_NOT_ALLOCATED');
    }
    
    const keys = await this.listKeys();
    
    // Delete each key
    for (const key of keys) {
      await this.delete(key);
    }
    
    // Update usage statistics
    this._updateUsage();
  }
  
  /**
   * Release the storage resource
   * @returns {Promise<void>}
   */
  async release() {
    if (!this.allocated) {
      return;
    }
    
    // If not persistent, clear all data
    if (!this.options.persistent) {
      await this.clear();
    }
    
    // Release the storage manager
    if (this.storageManager) {
      // In a real implementation, we would release the storage manager
      // but for now we'll just log it
      Prime.Logger.info(`Storage manager would be released: ${this.id}`);
    }
    
    await super.release();
  }
  
  /**
   * Update usage statistics
   * @private
   */
  async _updateUsage() {
    try {
      // Get storage info
      const storageInfo = await this.storageManager.getStorageInfo();
      this.usage = storageInfo.used || 0;
    } catch (error) {
      Prime.Logger.warn('Failed to update storage usage statistics', {
        resourceId: this.id,
        error
      });
    }
  }
}

/**
 * Compute Resource
 * Provides access to computation capabilities
 */
class ComputeResource extends Resource {
  /**
   * Create a new compute resource
   * @param {string} id - Resource ID
   * @param {Object} options - Compute options
   */
  constructor(id, options = {}) {
    super('compute', id, {
      priority: options.priority || 'normal',
      background: options.background !== false,
      concurrency: options.concurrency || 1,
      ...options
    });
    
    this.tasks = new Map();
    this.runningTasks = 0;
    this.maxConcurrency = this.options.concurrency;
  }
  
  /**
   * Initialize the compute resource
   * @returns {Promise<void>}
   */
  async init() {
    await super.init();
    
    Prime.Logger.info(`Compute resource initialized: ${this.id}`, {
      priority: this.options.priority,
      background: this.options.background,
      concurrency: this.maxConcurrency
    });
  }
  
  /**
   * Execute a task
   * @param {Function} taskFn - Task function to execute
   * @param {Object} options - Task options
   * @returns {Promise<*>} - Task result
   */
  async execute(taskFn, options = {}) {
    if (!this.allocated) {
      throw new ResourceError('Compute resource not allocated', {
        resourceId: this.id
      }, 'RESOURCE_NOT_ALLOCATED');
    }
    
    if (typeof taskFn !== 'function') {
      throw new ResourceError('Task must be a function', {
        resourceId: this.id,
        taskType: typeof taskFn
      }, 'INVALID_TASK');
    }
    
    // Check if we can execute more tasks
    if (this.runningTasks >= this.maxConcurrency) {
      throw new ResourceError('Maximum concurrency reached', {
        resourceId: this.id,
        runningTasks: this.runningTasks,
        maxConcurrency: this.maxConcurrency
      }, 'MAX_CONCURRENCY_REACHED');
    }
    
    // Create task ID
    const taskId = `task_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
    
    // Track task
    this.tasks.set(taskId, {
      id: taskId,
      status: 'running',
      startedAt: Date.now(),
      options
    });
    
    this.runningTasks++;
    
    try {
      // Execute the task
      const result = await taskFn();
      
      // Update task status
      this.tasks.set(taskId, {
        ...this.tasks.get(taskId),
        status: 'completed',
        completedAt: Date.now(),
        result
      });
      
      this.runningTasks--;
      
      // Update usage statistics
      this._updateUsage();
      
      return result;
    } catch (error) {
      // Update task status
      this.tasks.set(taskId, {
        ...this.tasks.get(taskId),
        status: 'failed',
        completedAt: Date.now(),
        error
      });
      
      this.runningTasks--;
      
      // Update usage statistics
      this._updateUsage();
      
      throw error;
    }
  }
  
  /**
   * Get task status
   * @param {string} taskId - Task ID
   * @returns {Object|null} - Task status or null if not found
   */
  getTaskStatus(taskId) {
    return this.tasks.has(taskId) ? { ...this.tasks.get(taskId) } : null;
  }
  
  /**
   * Get all tasks
   * @returns {Array<Object>} - Array of task statuses
   */
  getAllTasks() {
    return Array.from(this.tasks.values()).map(task => ({ ...task }));
  }
  
  /**
   * Release the compute resource
   * @returns {Promise<void>}
   */
  async release() {
    if (!this.allocated) {
      return;
    }
    
    // Cancel any running tasks
    // In a real implementation, we would cancel tasks
    // but for now we'll just log it
    if (this.runningTasks > 0) {
      Prime.Logger.warn(`Releasing compute resource with ${this.runningTasks} running tasks`, {
        resourceId: this.id
      });
    }
    
    this.tasks.clear();
    this.runningTasks = 0;
    
    await super.release();
  }
  
  /**
   * Update usage statistics
   * @private
   */
  _updateUsage() {
    this.usage = this.runningTasks / this.maxConcurrency;
  }
}

/**
 * Memory Resource
 * Provides access to memory management capabilities
 */
class MemoryResource extends Resource {
  /**
   * Create a new memory resource
   * @param {string} id - Resource ID
   * @param {Object} options - Memory options
   */
  constructor(id, options = {}) {
    super('memory', id, {
      max: options.max || '10MB',
      swappable: options.swappable !== false,
      ...options
    });
    
    this.memoryLimit = this._parseMemorySize(this.options.max);
    this.usedMemory = 0;
    this.objects = new Map();
  }
  
  /**
   * Initialize the memory resource
   * @returns {Promise<void>}
   */
  async init() {
    await super.init();
    
    Prime.Logger.info(`Memory resource initialized: ${this.id}`, {
      max: this.options.max,
      swappable: this.options.swappable
    });
  }
  
  /**
   * Allocate memory for an object
   * @param {*} data - Data to store
   * @param {string} key - Object key
   * @returns {Promise<string>} - Memory allocation ID
   */
  async allocate(data, key) {
    if (!this.allocated) {
      throw new ResourceError('Memory resource not allocated', {
        resourceId: this.id
      }, 'RESOURCE_NOT_ALLOCATED');
    }
    
    // Estimate data size
    const estimatedSize = this._estimateSize(data);
    
    // Check memory limit
    if (this.usedMemory + estimatedSize > this.memoryLimit) {
      throw new ResourceError('Memory limit exceeded', {
        resourceId: this.id,
        usedMemory: this.usedMemory,
        requestedSize: estimatedSize,
        memoryLimit: this.memoryLimit
      }, 'MEMORY_LIMIT_EXCEEDED');
    }
    
    // Create allocation ID
    const allocationId = key || `mem_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
    
    // Store object
    this.objects.set(allocationId, {
      id: allocationId,
      data,
      size: estimatedSize,
      allocatedAt: Date.now()
    });
    
    // Update used memory
    this.usedMemory += estimatedSize;
    this.usage = this.usedMemory / this.memoryLimit;
    
    return allocationId;
  }
  
  /**
   * Get an allocated object
   * @param {string} key - Object key
   * @returns {*} - Allocated object or null if not found
   */
  get(key) {
    if (!this.allocated) {
      throw new ResourceError('Memory resource not allocated', {
        resourceId: this.id
      }, 'RESOURCE_NOT_ALLOCATED');
    }
    
    return this.objects.has(key) ? this.objects.get(key).data : null;
  }
  
  /**
   * Free an allocated object
   * @param {string} key - Object key
   * @returns {boolean} - True if successfully freed
   */
  free(key) {
    if (!this.allocated) {
      throw new ResourceError('Memory resource not allocated', {
        resourceId: this.id
      }, 'RESOURCE_NOT_ALLOCATED');
    }
    
    if (!this.objects.has(key)) {
      return false;
    }
    
    // Get object size
    const { size } = this.objects.get(key);
    
    // Free object
    this.objects.delete(key);
    
    // Update used memory
    this.usedMemory -= size;
    this.usage = this.usedMemory / this.memoryLimit;
    
    return true;
  }
  
  /**
   * Release the memory resource
   * @returns {Promise<void>}
   */
  async release() {
    if (!this.allocated) {
      return;
    }
    
    // Free all objects
    this.objects.clear();
    this.usedMemory = 0;
    this.usage = 0;
    
    await super.release();
  }
  
  /**
   * Parse memory size string to bytes
   * @private
   * @param {string} sizeStr - Memory size string (e.g., "10MB")
   * @returns {number} - Size in bytes
   */
  _parseMemorySize(sizeStr) {
    if (typeof sizeStr === 'number') {
      return sizeStr;
    }
    
    const units = {
      B: 1,
      KB: 1024,
      MB: 1024 * 1024,
      GB: 1024 * 1024 * 1024
    };
    
    const match = /^(\d+(?:\.\d+)?)\s*([KMGT]?B)$/i.exec(sizeStr);
    
    if (!match) {
      return 10 * 1024 * 1024; // Default to 10MB
    }
    
    const size = parseFloat(match[1]);
    const unit = match[2].toUpperCase();
    
    return size * (units[unit] || units.B);
  }
  
  /**
   * Estimate the size of data in bytes
   * @private
   * @param {*} data - Data to estimate
   * @returns {number} - Estimated size in bytes
   */
  _estimateSize(data) {
    // Simple size estimation
    if (data === null || data === undefined) {
      return 0;
    }
    
    if (typeof data === 'boolean') {
      return 4;
    }
    
    if (typeof data === 'number') {
      return 8;
    }
    
    if (typeof data === 'string') {
      return data.length * 2;
    }
    
    if (typeof data === 'object') {
      if (Array.isArray(data)) {
        return data.reduce((size, item) => size + this._estimateSize(item), 0);
      }
      
      // Handle Buffer or TypedArray
      if (ArrayBuffer.isView(data)) {
        return data.byteLength;
      }
      
      // Handle objects
      let size = 0;
      for (const key in data) {
        if (Object.prototype.hasOwnProperty.call(data, key)) {
          size += key.length * 2; // Key size
          size += this._estimateSize(data[key]); // Value size
        }
      }
      
      return size;
    }
    
    // Default size for unknown types
    return 16;
  }
}

/**
 * Resource Manager
 * Factory for creating and managing resources
 */
class ResourceManager {
  /**
   * Create a new resource of the specified type
   * @param {string} type - Resource type (storage, compute, memory)
   * @param {string} id - Resource ID
   * @param {Object} options - Resource options
   * @returns {Resource} - Resource instance
   */
  static createResource(type, id, options = {}) {
    switch (type) {
      case 'storage':
        return new StorageResource(id, options);
      case 'compute':
        return new ComputeResource(id, options);
      case 'memory':
        return new MemoryResource(id, options);
      default:
        throw new ResourceError(`Unknown resource type: ${type}`, {
          type, id, options
        }, 'UNKNOWN_RESOURCE_TYPE');
    }
  }
}

// Add to Prime namespace
Prime.Veneer = Prime.Veneer || {};
Prime.Veneer.ResourceManager = ResourceManager;
Prime.Veneer.Resource = Resource;
Prime.Veneer.StorageResource = StorageResource;
Prime.Veneer.ComputeResource = ComputeResource;
Prime.Veneer.MemoryResource = MemoryResource;
Prime.Veneer.ResourceError = ResourceError;

module.exports = {
  ResourceManager,
  Resource,
  StorageResource,
  ComputeResource,
  MemoryResource,
  ResourceError
};