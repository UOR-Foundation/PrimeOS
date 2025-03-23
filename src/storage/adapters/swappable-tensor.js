/**
 * PrimeOS JavaScript Library - Swappable Tensor
 * Tensor implementation that swaps data to storage as needed
 */

// Use the direct core modules instead of the main core export
// This helps avoid circular dependencies
const Prime = require('../../core/prime');
const SwappableMatrix = require('./swappable-matrix');

// Define an error class that doesn't rely on circular imports
class TensorError extends Error {
  constructor(message, details = {}, code = 'TENSOR_ERROR') {
    super(message);
    this.name = 'TensorError';
    this.details = details;
    this.code = code;
    
    // Capture stack trace
    if (Error.captureStackTrace) {
      Error.captureStackTrace(this, this.constructor);
    }
  }
}

/**
 * Tensor implementation that keeps part of the data in memory
 * and swaps to storage as needed - extends SwappableMatrix for n-dimensional tensors
 */
class SwappableTensor {
  /**
   * Creates a new swappable tensor
   * @param {StorageManager} storageManager - Storage manager to use
   * @param {string} id - ID of the stored tensor
   * @param {Object} tensor - Original tensor
   * @param {SwappableTensorOptions} [options] - Tensor options
   */
  constructor(storageManager, id, tensor, options = {}) {
    this.storageManager = storageManager;
    this.id = id;
    
    // Determine tensor shape
    this.shape = this._determineShape(tensor);
    
    // Set up dimension names for clarity
    this.dimensions = this.shape.length;
    
    this.options = {
      blockSize: options.blockSize || 16,
      maxCachedBlocks: options.maxCachedBlocks || 10,
      evictionPolicy: options.evictionPolicy || 'lru',
      ...options
    };
    
    // Calculate number of blocks per dimension
    this.blockCounts = this.shape.map(dim => 
      Math.ceil(dim / this.options.blockSize)
    );
    
    // Calculate total number of blocks
    this.totalBlocks = this.blockCounts.reduce((total, count) => total * count, 1);
    
    // Initialize block cache
    this.blockCache = new Map();
    this.accessOrder = []; // For LRU eviction
    
    // If tensor is small enough, keep it fully in memory
    const totalElements = this.shape.reduce((prod, dim) => prod * dim, 1);
    this.fullTensor = totalElements <= this.options.blockSize * this.options.maxCachedBlocks ? 
      tensor : null;
      
    // This property tracks whether we've split and stored the tensor
    this.initialized = false;
    
    // For cache statistics
    this.cacheHits = 0;
    this.cacheMisses = 0;
    this.cacheEvictions = 0;
  }
  
  /**
   * Determines the shape of a tensor
   * @private
   * @param {Array} tensor - The tensor to analyze
   * @returns {Array<number>} Shape array
   */
  _determineShape(tensor) {
    if (!Array.isArray(tensor)) {
      return [];
    }
    
    const shape = [tensor.length];
    
    if (tensor.length > 0 && Array.isArray(tensor[0])) {
      // Recursively get shape of first element
      const subShape = this._determineShape(tensor[0]);
      shape.push(...subShape);
    }
    
    // Validate that all elements have the same shape
    this._validateUniformShape(tensor, shape);
    
    return shape;
  }
  
  /**
   * Validates that all elements in a tensor have the same shape
   * @private
   * @param {Array} tensor - The tensor to validate
   * @param {Array<number>} expectedShape - Expected shape of nested elements
   */
  _validateUniformShape(tensor, expectedShape) {
    if (!Array.isArray(tensor) || expectedShape.length === 1) {
      return;
    }
    
    for (let i = 0; i < tensor.length; i++) {
      if (!Array.isArray(tensor[i])) {
        throw new TensorError(
          'Non-uniform tensor shape detected',
          { index: i, expectedShape },
          'STORAGE_NON_UNIFORM_TENSOR'
        );
      }
      
      if (tensor[i].length !== expectedShape[1]) {
        throw new TensorError(
          'Non-uniform tensor shape detected',
          { 
            index: i, 
            elementLength: tensor[i].length, 
            expectedLength: expectedShape[1] 
          },
          'STORAGE_NON_UNIFORM_TENSOR'
        );
      }
      
      // Recursively validate nested shapes
      if (expectedShape.length > 2) {
        this._validateUniformShape(tensor[i], expectedShape.slice(1));
      }
    }
  }
  
  /**
   * Ensures the tensor is initialized
   * @private
   */
  async _ensureInitialized() {
    if (this.initialized) {
      return;
    }
    
    if (!this.fullTensor && this.originalTensor) {
      // Split and store the tensor
      await this._splitAndStoreBlocks(this.originalTensor);
    }
    
    this.initialized = true;
  }

  /**
   * Splits a tensor into blocks and stores them
   * @private
   * @param {Object} tensor - Tensor to split
   */
  async _splitAndStoreBlocks(tensor) {
    // For each block, extract data and store it
    const storePromises = [];
    
    // Generate all possible block indices combinations
    const blockIndices = this._generateBlockIndices(this.blockCounts);
    
    for (const indices of blockIndices) {
      const blockId = this._getBlockId(indices);
      const blockData = this._extractBlock(tensor, indices);
      
      // Store block data
      storePromises.push(
        this.storageManager.store(blockData, `${this.id}_block_${blockId}`)
      );
    }
    
    await Promise.all(storePromises);
  }
  
  /**
   * Generates all possible block indices combinations
   * @private
   * @param {Array<number>} blockCounts - Array of block counts per dimension
   * @returns {Array<Array<number>>} Array of block indices combinations
   */
  _generateBlockIndices(blockCounts) {
    const result = [];
    
    const generateHelper = (current, dimension) => {
      if (dimension === blockCounts.length) {
        result.push([...current]);
        return;
      }
      
      for (let i = 0; i < blockCounts[dimension]; i++) {
        current.push(i);
        generateHelper(current, dimension + 1);
        current.pop();
      }
    };
    
    generateHelper([], 0);
    return result;
  }

  /**
   * Extracts a block from a tensor
   * @private
   * @param {Object} tensor - Tensor to extract from
   * @param {Array<number>} blockIndices - Block indices
   * @returns {Array} Block data
   */
  _extractBlock(tensor, blockIndices) {
    // Calculate the start and end indices for each dimension
    const startIndices = blockIndices.map((blockIdx, dim) => 
      blockIdx * this.options.blockSize
    );
    
    const endIndices = blockIndices.map((blockIdx, dim) => 
      Math.min((blockIdx + 1) * this.options.blockSize, this.shape[dim])
    );
    
    // Create a block structure based on block dimensions
    const blockShape = endIndices.map((end, i) => end - startIndices[i]);
    const blockData = this._createNestedArray(blockShape);
    
    // Fill the block with data using recursive function
    this._fillBlockData(tensor, blockData, startIndices, endIndices, 0, []);
    
    return blockData;
  }
  
  /**
   * Creates a nested array with given shape
   * @private
   * @param {Array<number>} shape - Shape of the array to create
   * @returns {Array} Nested array
   */
  _createNestedArray(shape) {
    if (shape.length === 0) {
      return undefined;
    }
    
    if (shape.length === 1) {
      return new Array(shape[0]);
    }
    
    const result = new Array(shape[0]);
    const remainingShape = shape.slice(1);
    
    for (let i = 0; i < shape[0]; i++) {
      result[i] = this._createNestedArray(remainingShape);
    }
    
    return result;
  }
  
  /**
   * Recursively fills block data from tensor
   * @private
   * @param {Array} tensor - Source tensor
   * @param {Array} block - Target block
   * @param {Array<number>} start - Start indices
   * @param {Array<number>} end - End indices
   * @param {number} dimension - Current dimension
   * @param {Array<number>} currentIndices - Current indices
   */
  _fillBlockData(tensor, block, start, end, dimension, currentIndices) {
    if (dimension === start.length) {
      // Base case: assign the value from the tensor to the block
      let source = tensor;
      let target = block;
      
      for (let i = 0; i < currentIndices.length - 1; i++) {
        source = source[currentIndices[i]];
        target = target[currentIndices[i] - start[i]];
      }
      
      const lastIdx = currentIndices[currentIndices.length - 1];
      const lastBlockIdx = lastIdx - start[start.length - 1];
      target[lastBlockIdx] = source[lastIdx];
      return;
    }
    
    // Recursive case: iterate over the current dimension
    for (let i = start[dimension]; i < end[dimension]; i++) {
      currentIndices.push(i);
      this._fillBlockData(tensor, block, start, end, dimension + 1, currentIndices);
      currentIndices.pop();
    }
  }

  /**
   * Gets the block ID for a set of block indices
   * @private
   * @param {Array<number>} blockIndices - Block indices
   * @returns {string} Block ID
   */
  _getBlockId(blockIndices) {
    // Convert multi-dimensional block indices to a unique string ID
    return blockIndices.join('_');
  }

  /**
   * Gets the block indices for a tensor position
   * @private
   * @param {Array<number>} indices - Tensor indices
   * @returns {Object} Block information
   */
  _getBlockIndices(indices) {
    // Calculate block indices and indices within block
    const blockIndices = indices.map(idx => Math.floor(idx / this.options.blockSize));
    const indicesInBlock = indices.map((idx, dim) => idx % this.options.blockSize);
    const blockId = this._getBlockId(blockIndices);
    
    return {
      blockIndices,
      indicesInBlock,
      blockId
    };
  }

  /**
   * Loads a block into memory
   * @private
   * @param {string} blockId - Block ID
   * @returns {Promise<Array>} Block data
   */
  async _loadBlock(blockId) {
    // If block is in cache, update access order and return it
    if (this.blockCache.has(blockId)) {
      this._updateAccessOrder(blockId);
      this.cacheHits++;
      return this.blockCache.get(blockId);
    }
    
    // Record cache miss
    this.cacheMisses++;
    
    // Load block from storage
    const blockData = await this.storageManager.load(`${this.id}_block_${blockId}`);
    
    // Evict blocks if cache is full
    if (this.blockCache.size >= this.options.maxCachedBlocks) {
      this._evictBlock();
    }
    
    // Add block to cache
    this.blockCache.set(blockId, blockData);
    this._updateAccessOrder(blockId);
    
    return blockData;
  }

  /**
   * Updates the access order for LRU eviction
   * @private
   * @param {string} blockId - Block ID
   */
  _updateAccessOrder(blockId) {
    // Remove from current position
    const index = this.accessOrder.indexOf(blockId);
    if (index !== -1) {
      this.accessOrder.splice(index, 1);
    }
    
    // Add to the end (most recently used)
    this.accessOrder.push(blockId);
  }

  /**
   * Evicts a block from the cache
   * @private
   */
  _evictBlock() {
    if (this.blockCache.size === 0) {
      return;
    }
    
    let blockToEvict;
    
    switch (this.options.evictionPolicy) {
      case 'lru':
        // Least Recently Used - evict first in access order
        blockToEvict = this.accessOrder.shift();
        break;
      case 'fifo':
        // First In, First Out - evict oldest added block
        blockToEvict = Array.from(this.blockCache.keys())[0];
        break;
      case 'random':
        // Random - evict a random block
        const keys = Array.from(this.blockCache.keys());
        blockToEvict = keys[Math.floor(Math.random() * keys.length)];
        break;
      default:
        // Default to LRU
        blockToEvict = this.accessOrder.shift();
    }
    
    // Remove from cache
    this.blockCache.delete(blockToEvict);
    
    // Track eviction
    this.cacheEvictions++;
  }

  /**
   * Gets a value from the tensor
   * @param {...number} indices - Tensor indices
   * @returns {Promise<number>} Tensor value
   */
  async get(...indices) {
    // Handle edge cases
    if (indices.length === 0) {
      throw new TensorError(
        'No indices provided',
        {},
        'STORAGE_INVALID_INDICES'
      );
    }
    
    // If indices is an array (passed as [x,y,z] instead of x,y,z)
    if (indices.length === 1 && Array.isArray(indices[0])) {
      indices = indices[0];
    }
    
    this._validateIndices(indices);
    
    // Ensure initialization
    await this._ensureInitialized();
    
    // If we have the full tensor in memory, use it directly
    if (this.fullTensor) {
      return this._getFromFullTensor(this.fullTensor, indices);
    }
    
    // Get block indices
    const { blockId, indicesInBlock } = this._getBlockIndices(indices);
    
    // Load block
    const blockData = await this._loadBlock(blockId);
    
    // Get value from block
    return this._getFromBlock(blockData, indicesInBlock);
  }
  
  /**
   * Gets a value from a full tensor
   * @private
   * @param {Array} tensor - Tensor to get value from
   * @param {Array<number>} indices - Indices
   * @returns {number} Tensor value
   */
  _getFromFullTensor(tensor, indices) {
    let current = tensor;
    
    for (let i = 0; i < indices.length; i++) {
      if (!Array.isArray(current)) {
        throw new TensorError(
          'Invalid tensor indices',
          { indices },
          'STORAGE_INVALID_INDICES'
        );
      }
      
      current = current[indices[i]];
    }
    
    return current;
  }
  
  /**
   * Gets a value from a block
   * @private
   * @param {Array} block - Block to get value from
   * @param {Array<number>} indices - Indices within block
   * @returns {number} Tensor value
   */
  _getFromBlock(block, indices) {
    let current = block;
    
    for (const idx of indices) {
      if (!Array.isArray(current)) {
        throw new TensorError(
          'Invalid block structure',
          { indices },
          'STORAGE_INVALID_BLOCK'
        );
      }
      
      current = current[idx];
    }
    
    return current;
  }

  /**
   * Sets a value in the tensor
   * @param {Array<number>} indices - Tensor indices
   * @param {number} value - Value to set
   */
  async set(indices, value) {
    // Handle both calling conventions: set([x,y,z], value) and set(x,y,z, value)
    if (arguments.length > 2 && !Array.isArray(indices)) {
      value = arguments[arguments.length - 1];
      indices = Array.from(arguments).slice(0, arguments.length - 1);
    }
    
    this._validateIndices(indices);
    
    // Ensure initialization
    await this._ensureInitialized();
    
    // If we have the full tensor in memory, update it directly
    if (this.fullTensor) {
      this._setInFullTensor(this.fullTensor, indices, value);
      
      // Update storage
      await this.storageManager.store(this.fullTensor, this.id);
      return;
    }
    
    // Get block indices
    const { blockId, blockIndices, indicesInBlock } = this._getBlockIndices(indices);
    
    // Load block
    const blockData = await this._loadBlock(blockId);
    
    // Set value in block
    this._setInBlock(blockData, indicesInBlock, value);
    
    // Store updated block
    await this.storageManager.store(blockData, `${this.id}_block_${blockId}`);
  }
  
  /**
   * Sets a value in a full tensor
   * @private
   * @param {Array} tensor - Tensor to set value in
   * @param {Array<number>} indices - Indices
   * @param {number} value - Value to set
   */
  _setInFullTensor(tensor, indices, value) {
    let current = tensor;
    
    for (let i = 0; i < indices.length - 1; i++) {
      if (!Array.isArray(current)) {
        throw new TensorError(
          'Invalid tensor indices',
          { indices },
          'STORAGE_INVALID_INDICES'
        );
      }
      
      current = current[indices[i]];
    }
    
    current[indices[indices.length - 1]] = value;
  }
  
  /**
   * Sets a value in a block
   * @private
   * @param {Array} block - Block to set value in
   * @param {Array<number>} indices - Indices within block
   * @param {number} value - Value to set
   */
  _setInBlock(block, indices, value) {
    let current = block;
    
    for (let i = 0; i < indices.length - 1; i++) {
      if (!Array.isArray(current)) {
        throw new TensorError(
          'Invalid block structure',
          { indices },
          'STORAGE_INVALID_BLOCK'
        );
      }
      
      current = current[indices[i]];
    }
    
    current[indices[indices.length - 1]] = value;
  }

  /**
   * Validates tensor indices
   * @private
   * @param {Array<number>} indices - Tensor indices
   */
  _validateIndices(indices) {
    if (indices.length !== this.shape.length) {
      throw new TensorError(
        `Invalid number of indices: expected ${this.shape.length}, got ${indices.length}`,
        { indices, shape: this.shape },
        'STORAGE_INVALID_INDICES'
      );
    }
    
    for (let i = 0; i < indices.length; i++) {
      if (indices[i] < 0 || indices[i] >= this.shape[i]) {
        throw new TensorError(
          `Index ${indices[i]} out of bounds for dimension ${i} (0-${this.shape[i] - 1})`,
          { index: indices[i], dimension: i, maxValue: this.shape[i] - 1 },
          'STORAGE_INDEX_OUT_OF_BOUNDS'
        );
      }
    }
  }
  
  /**
   * Gets a subtensor from the tensor
   * @param {Array<Array<number>>} ranges - Array of [start, end] ranges for each dimension
   * @returns {Promise<Array>} Subtensor
   */
  async getSubtensor(ranges) {
    // Validate ranges
    if (!Array.isArray(ranges) || ranges.length !== this.shape.length) {
      throw new TensorError(
        `Invalid ranges: expected ${this.shape.length} dimensions`,
        { ranges, shape: this.shape },
        'STORAGE_INVALID_RANGES'
      );
    }
    
    for (let i = 0; i < ranges.length; i++) {
      const [start, end] = ranges[i];
      
      if (start < 0 || end > this.shape[i] || start >= end) {
        throw new TensorError(
          `Invalid range [${start}, ${end}] for dimension ${i}`,
          { range: ranges[i], dimension: i, shapeValue: this.shape[i] },
          'STORAGE_INVALID_RANGE'
        );
      }
    }
    
    // Ensure initialization
    await this._ensureInitialized();
    
    // Calculate subtensor shape
    const subShape = ranges.map(([start, end]) => end - start);
    
    // Create a new empty tensor for the result
    const result = this._createNestedArray(subShape);
    
    // Fill the subtensor recursively
    await this._fillSubtensor(result, ranges, 0, [], []);
    
    return result;
  }
  
  /**
   * Recursively fills a subtensor
   * @private
   * @param {Array} subtensor - Target subtensor
   * @param {Array<Array<number>>} ranges - Dimension ranges
   * @param {number} dimension - Current dimension
   * @param {Array<number>} subtensorIndices - Current subtensor indices
   * @param {Array<number>} originalIndices - Current original tensor indices
   */
  async _fillSubtensor(subtensor, ranges, dimension, subtensorIndices, originalIndices) {
    if (dimension === ranges.length) {
      // Base case: get the value from the original tensor
      const value = await this.get(originalIndices);
      
      // Set the value in the subtensor
      let current = subtensor;
      for (let i = 0; i < subtensorIndices.length - 1; i++) {
        current = current[subtensorIndices[i]];
      }
      current[subtensorIndices[subtensorIndices.length - 1]] = value;
      
      return;
    }
    
    // Recursive case: iterate through the current dimension range
    const [start, end] = ranges[dimension];
    
    for (let i = start; i < end; i++) {
      // Update indices
      subtensorIndices.push(i - start);
      originalIndices.push(i);
      
      // Recurse to next dimension
      await this._fillSubtensor(subtensor, ranges, dimension + 1, subtensorIndices, originalIndices);
      
      // Remove indices for backtracking
      subtensorIndices.pop();
      originalIndices.pop();
    }
  }
  
  /**
   * Gets the shape of the tensor
   * @returns {Array<number>} Tensor shape
   */
  getShape() {
    return [...this.shape];
  }
  
  /**
   * Maps a function over all elements of the tensor
   * @param {Function} fn - Function to apply to each element
   * @returns {Promise<Array>} New tensor with function applied
   */
  async map(fn) {
    // Ensure initialization
    await this._ensureInitialized();
    
    // If we have the full tensor in memory, map directly
    if (this.fullTensor) {
      return this._mapTensor(this.fullTensor, fn);
    }
    
    // Create a new tensor with the same shape
    const result = this._createNestedArray(this.shape);
    
    // Fill the new tensor with mapped values
    await this._fillMappedTensor(result, fn, 0, []);
    
    return result;
  }
  
  /**
   * Maps a function over a tensor
   * @private
   * @param {Array} tensor - Tensor to map
   * @param {Function} fn - Mapping function
   * @returns {Array} Mapped tensor
   */
  _mapTensor(tensor, fn) {
    if (!Array.isArray(tensor)) {
      return fn(tensor);
    }
    
    return tensor.map(element => {
      if (Array.isArray(element)) {
        return this._mapTensor(element, fn);
      }
      return fn(element);
    });
  }
  
  /**
   * Recursively fills a tensor with mapped values
   * @private
   * @param {Array} target - Target tensor
   * @param {Function} fn - Mapping function
   * @param {number} dimension - Current dimension
   * @param {Array<number>} indices - Current indices
   */
  async _fillMappedTensor(target, fn, dimension, indices) {
    if (dimension === this.shape.length) {
      // Base case: get the value, apply the function, and set the result
      const value = await this.get(indices);
      
      // Set the transformed value in the target tensor
      let current = target;
      for (let i = 0; i < indices.length - 1; i++) {
        current = current[indices[i]];
      }
      current[indices[indices.length - 1]] = fn(value, indices);
      
      return;
    }
    
    // Recursive case: iterate through the current dimension
    for (let i = 0; i < this.shape[dimension]; i++) {
      indices.push(i);
      await this._fillMappedTensor(target, fn, dimension + 1, indices);
      indices.pop();
    }
  }
  
  /**
   * Reduces a tensor to a single value
   * @param {Function} fn - Reducer function (acc, value, indices) => newAcc
   * @param {*} initialValue - Initial accumulator value
   * @returns {Promise<*>} Reduced value
   */
  async reduce(fn, initialValue) {
    // Ensure initialization
    await this._ensureInitialized();
    
    let accumulator = initialValue;
    
    // Recursively reduce the tensor
    await this._reduceTensor(fn, accumulator, 0, [], (result) => {
      accumulator = result;
    });
    
    return accumulator;
  }
  
  /**
   * Recursively reduces a tensor
   * @private
   * @param {Function} fn - Reducer function
   * @param {*} accumulator - Current accumulator value
   * @param {number} dimension - Current dimension
   * @param {Array<number>} indices - Current indices
   * @param {Function} updateAccumulator - Function to update accumulator
   */
  async _reduceTensor(fn, accumulator, dimension, indices, updateAccumulator) {
    if (dimension === this.shape.length) {
      // Base case: get the value and update the accumulator
      const value = await this.get(indices);
      const newAccumulator = fn(accumulator, value, [...indices]);
      updateAccumulator(newAccumulator);
      return;
    }
    
    // Recursive case: iterate through the current dimension
    for (let i = 0; i < this.shape[dimension]; i++) {
      indices.push(i);
      await this._reduceTensor(fn, accumulator, dimension + 1, indices, updateAccumulator);
      indices.pop();
    }
  }
  
  /**
   * Flattens the tensor to a 1D array
   * @returns {Promise<Array>} Flattened array
   */
  async flatten() {
    // Calculate total elements
    const totalElements = this.shape.reduce((a, b) => a * b, 1);
    
    // Create result array
    const result = new Array(totalElements);
    
    // Fill the array recursively
    let index = 0;
    await this._flattenHelper(result, 0, [], (value) => {
      result[index++] = value;
    });
    
    return result;
  }
  
  /**
   * Helper for flattening a tensor
   * @private
   * @param {Array} result - Result array
   * @param {number} dimension - Current dimension
   * @param {Array<number>} indices - Current indices
   * @param {Function} setValue - Function to set value in result
   */
  async _flattenHelper(result, dimension, indices, setValue) {
    if (dimension === this.shape.length) {
      // Base case: get the value and add it to the result
      const value = await this.get(indices);
      setValue(value);
      return;
    }
    
    // Recursive case: iterate through the current dimension
    for (let i = 0; i < this.shape[dimension]; i++) {
      indices.push(i);
      await this._flattenHelper(result, dimension + 1, indices, setValue);
      indices.pop();
    }
  }
  
  /**
   * Gets cache statistics
   * @returns {Object} Cache statistics
   */
  getCacheStats() {
    if (!this.initialized) {
      return {
        size: 0,
        hits: 0,
        misses: 0,
        evictions: 0,
        hitRate: 0
      };
    }
    
    return {
      size: this.blockCache.size,
      hits: this.cacheHits,
      misses: this.cacheMisses,
      evictions: this.cacheEvictions,
      hitRate: this.cacheHits + this.cacheMisses > 0 ? 
        this.cacheHits / (this.cacheHits + this.cacheMisses) : 0
    };
  }
  
  /**
   * Performs element-wise addition with another tensor
   * @param {Object} other - Other tensor
   * @returns {Promise<Array>} Result tensor
   */
  async add(other) {
    // Calculate and validate other tensor's shape
    const otherShape = await this._getOtherShape(other);
    
    // Validate compatibility for element-wise addition
    this._validateElementwiseCompatibility(otherShape);
    
    // Create a new tensor with the same shape
    const result = this._createNestedArray(this.shape);
    
    // Fill the new tensor with sum values
    await this._fillBinaryOperation(result, other, (a, b) => a + b, 0, []);
    
    return result;
  }
  
  /**
   * Gets the shape of another tensor-like object
   * @private
   * @param {Object} other - Other tensor
   * @returns {Promise<Array<number>>} Shape array
   */
  async _getOtherShape(other) {
    // Handle SwappableTensor case
    if (other instanceof SwappableTensor) {
      return other.getShape();
    }
    
    // Handle array case
    if (Array.isArray(other)) {
      return this._determineShape(other);
    }
    
    // Handle scalar case
    return [];
  }
  
  /**
   * Validates compatibility for element-wise operations
   * @private
   * @param {Array<number>} otherShape - Shape of other tensor
   */
  _validateElementwiseCompatibility(otherShape) {
    // Handle broadcasting:
    // 1. Shapes must have the same number of dimensions or one can be a scalar
    // 2. For each dimension, the sizes must be equal or one must be 1 (for broadcasting)
    
    if (otherShape.length === 0) {
      // Other is a scalar, always compatible
      return;
    }
    
    if (otherShape.length !== this.shape.length) {
      throw new TensorError(
        'Incompatible tensor shapes for element-wise operation',
        { thisShape: this.shape, otherShape },
        'STORAGE_INCOMPATIBLE_SHAPES'
      );
    }
    
    for (let i = 0; i < this.shape.length; i++) {
      if (this.shape[i] !== otherShape[i] && otherShape[i] !== 1 && this.shape[i] !== 1) {
        throw new TensorError(
          'Incompatible tensor shapes for element-wise operation',
          { thisShape: this.shape, otherShape, dimension: i },
          'STORAGE_INCOMPATIBLE_SHAPES'
        );
      }
    }
  }
  
  /**
   * Recursively fills a tensor with the result of a binary operation
   * @private
   * @param {Array} result - Result tensor
   * @param {Object} other - Other tensor
   * @param {Function} operation - Binary operation function
   * @param {number} dimension - Current dimension
   * @param {Array<number>} indices - Current indices
   */
  async _fillBinaryOperation(result, other, operation, dimension, indices) {
    if (dimension === this.shape.length) {
      // Base case: get both values, apply the operation, and set the result
      const thisValue = await this.get(indices);
      
      // Get other value based on type
      let otherValue;
      
      if (other instanceof SwappableTensor) {
        // Try to get value from other SwappableTensor, with broadcasting support
        try {
          otherValue = await other.get(indices);
        } catch (e) {
          // If index out of bounds, try broadcast indices
          const broadcastIndices = indices.map((idx, dim) => 
            other.shape[dim] === 1 ? 0 : idx
          );
          otherValue = await other.get(broadcastIndices);
        }
      } else if (Array.isArray(other)) {
        // Handle array case
        otherValue = this._getFromNestedArray(other, indices);
      } else {
        // Handle scalar case
        otherValue = other;
      }
      
      // Set the result
      this._setInNestedArray(result, indices, operation(thisValue, otherValue));
      
      return;
    }
    
    // Recursive case: iterate through the current dimension
    for (let i = 0; i < this.shape[dimension]; i++) {
      indices.push(i);
      await this._fillBinaryOperation(result, other, operation, dimension + 1, indices);
      indices.pop();
    }
  }
  
  /**
   * Gets a value from a nested array with broadcasting support
   * @private
   * @param {Array} array - Nested array
   * @param {Array<number>} indices - Indices
   * @returns {*} Value
   */
  _getFromNestedArray(array, indices) {
    let current = array;
    
    // Calculate effective indices considering broadcasting
    const effectiveIndices = [];
    let shape = this._determineShape(array);
    
    for (let i = 0; i < indices.length; i++) {
      if (i >= shape.length) {
        // Scalar broadcasting for extra dimensions
        return current;
      }
      
      // Handle broadcasting: if dimension size is 1, use index 0
      effectiveIndices.push(shape[i] === 1 ? 0 : indices[i]);
    }
    
    // Navigate to the value
    for (const idx of effectiveIndices) {
      if (!Array.isArray(current)) {
        // Broadcasting: scalar value for all indices
        return current;
      }
      
      if (idx >= current.length) {
        throw new TensorError(
          'Index out of bounds in nested array',
          { index: idx, arrayLength: current.length },
          'STORAGE_INDEX_OUT_OF_BOUNDS'
        );
      }
      
      current = current[idx];
    }
    
    return current;
  }
  
  /**
   * Sets a value in a nested array
   * @private
   * @param {Array} array - Nested array
   * @param {Array<number>} indices - Indices
   * @param {*} value - Value to set
   */
  _setInNestedArray(array, indices, value) {
    let current = array;
    
    for (let i = 0; i < indices.length - 1; i++) {
      if (!Array.isArray(current)) {
        throw new TensorError(
          'Invalid nested array structure',
          { indices },
          'STORAGE_INVALID_NESTED_ARRAY'
        );
      }
      
      current = current[indices[i]];
    }
    
    current[indices[indices.length - 1]] = value;
  }
  
  /**
   * Performs element-wise subtraction with another tensor
   * @param {Object} other - Other tensor
   * @returns {Promise<Array>} Result tensor
   */
  async subtract(other) {
    // Calculate and validate other tensor's shape
    const otherShape = await this._getOtherShape(other);
    
    // Validate compatibility for element-wise subtraction
    this._validateElementwiseCompatibility(otherShape);
    
    // Create a new tensor with the same shape
    const result = this._createNestedArray(this.shape);
    
    // Fill the new tensor with difference values
    await this._fillBinaryOperation(result, other, (a, b) => a - b, 0, []);
    
    return result;
  }
  
  /**
   * Performs element-wise multiplication with another tensor
   * @param {Object} other - Other tensor
   * @returns {Promise<Array>} Result tensor
   */
  async multiply(other) {
    // Calculate and validate other tensor's shape
    const otherShape = await this._getOtherShape(other);
    
    // Validate compatibility for element-wise multiplication
    this._validateElementwiseCompatibility(otherShape);
    
    // Create a new tensor with the same shape
    const result = this._createNestedArray(this.shape);
    
    // Fill the new tensor with product values
    await this._fillBinaryOperation(result, other, (a, b) => a * b, 0, []);
    
    return result;
  }
  
  /**
   * Performs element-wise division with another tensor
   * @param {Object} other - Other tensor
   * @returns {Promise<Array>} Result tensor
   */
  async divide(other) {
    // Calculate and validate other tensor's shape
    const otherShape = await this._getOtherShape(other);
    
    // Validate compatibility for element-wise division
    this._validateElementwiseCompatibility(otherShape);
    
    // Create a new tensor with the same shape
    const result = this._createNestedArray(this.shape);
    
    // Fill the new tensor with quotient values
    await this._fillBinaryOperation(result, other, (a, b) => {
      // Avoid division by zero
      if (b === 0) {
        return a === 0 ? 0 : (a > 0 ? Infinity : -Infinity);
      }
      return a / b;
    }, 0, []);
    
    return result;
  }
  
  /**
   * Tensor contraction (summation over specified dimensions)
   * @param {Array<number>} dims - Dimensions to contract
   * @returns {Promise<Array|number>} Contracted tensor
   */
  async contract(dims) {
    // Ensure dimensions are valid
    if (!Array.isArray(dims)) {
      dims = [dims];
    }
    
    dims = dims.sort((a, b) => b - a); // Sort in descending order
    
    // Validate dimensions
    for (const dim of dims) {
      if (dim < 0 || dim >= this.shape.length) {
        throw new TensorError(
          `Invalid dimension for contraction: ${dim}`,
          { dimension: dim, shape: this.shape },
          'STORAGE_INVALID_DIMENSION'
        );
      }
    }
    
    // Calculate result shape
    const resultShape = [];
    for (let i = 0; i < this.shape.length; i++) {
      if (!dims.includes(i)) {
        resultShape.push(this.shape[i]);
      }
    }
    
    // Handle scalar result case
    if (resultShape.length === 0) {
      // Sum all elements
      return await this.reduce((acc, val) => acc + val, 0);
    }
    
    // Create result tensor
    const result = this._createNestedArray(resultShape);
    
    // Initialize all elements of the result to 0
    this._initializeToZero(result);
    
    // Recursively fill the result tensor
    const contractionInfo = {
      dims,
      resultShape,
      contractionIndices: dims.map(() => 0),
      nonContractionMapping: this.shape.map((_, i) => 
        dims.includes(i) ? -1 : resultShape.length - this.shape.filter((_, j) => !dims.includes(j) && j >= i).length
      )
    };
    
    await this._fillContraction(result, contractionInfo, 0, [], [], 0);
    
    return result;
  }
  
  /**
   * Recursively fills a contraction result
   * @private
   * @param {Array} result - Result tensor
   * @param {Object} contractionInfo - Contraction information
   * @param {number} dimension - Current dimension
   * @param {Array<number>} originalIndices - Current original tensor indices
   * @param {Array<number>} resultIndices - Current result tensor indices
   * @param {number} resultDimension - Current result dimension
   */
  async _fillContraction(result, contractionInfo, dimension, originalIndices, resultIndices, resultDimension) {
    if (dimension === this.shape.length) {
      // Base case: get the value and accumulate in the result
      const value = await this.get(originalIndices);
      let current = result;
      
      for (let i = 0; i < resultIndices.length - 1; i++) {
        current = current[resultIndices[i]];
      }
      
      if (resultIndices.length === 0) {
        // Scalar result
        return value;
      }
      
      // Initialize to 0 if undefined
      if (current[resultIndices[resultIndices.length - 1]] === undefined) {
        current[resultIndices[resultIndices.length - 1]] = 0;
      }
      
      current[resultIndices[resultIndices.length - 1]] += value;
      return;
    }
    
    // Check if this dimension is contracted
    if (contractionInfo.dims.includes(dimension)) {
      // Iterate over all values in this contracted dimension
      for (let i = 0; i < this.shape[dimension]; i++) {
        originalIndices.push(i);
        await this._fillContraction(result, contractionInfo, dimension + 1, originalIndices, resultIndices, resultDimension);
        originalIndices.pop();
      }
    } else {
      // This dimension is preserved in the result
      for (let i = 0; i < this.shape[dimension]; i++) {
        originalIndices.push(i);
        resultIndices.push(i);
        await this._fillContraction(result, contractionInfo, dimension + 1, originalIndices, resultIndices, resultDimension + 1);
        originalIndices.pop();
        resultIndices.pop();
      }
    }
  }
  
  /**
   * Converts the tensor to a standard nested array
   * @returns {Promise<Array>} Tensor as a nested array
   */
  async toArray() {
    // Create a new tensor with the same shape
    const result = this._createNestedArray(this.shape);
    
    // Fill the tensor
    await this._fillTensorFromStorage(result, 0, []);
    
    return result;
  }
  
  /**
   * Recursively fills a tensor from storage
   * @private
   * @param {Array} tensor - Target tensor
   * @param {number} dimension - Current dimension
   * @param {Array<number>} indices - Current indices
   */
  async _fillTensorFromStorage(tensor, dimension, indices) {
    if (dimension === this.shape.length) {
      // Base case: get the value and add it to the result
      const value = await this.get(indices);
      
      // Set the value in the tensor
      let current = tensor;
      for (let i = 0; i < indices.length - 1; i++) {
        current = current[indices[i]];
      }
      current[indices[indices.length - 1]] = value;
      
      return;
    }
    
    // Recursive case: iterate through the current dimension
    for (let i = 0; i < this.shape[dimension]; i++) {
      indices.push(i);
      await this._fillTensorFromStorage(tensor, dimension + 1, indices);
      indices.pop();
    }
  }
  
  /**
   * Reshapes the tensor to a new shape with the same number of elements
   * @param {Array<number>} newShape - New shape
   * @returns {Promise<Array>} Reshaped tensor
   */
  async reshape(newShape) {
    // Validate new shape
    const oldSize = this.shape.reduce((a, b) => a * b, 1);
    const newSize = newShape.reduce((a, b) => a * b, 1);
    
    if (oldSize !== newSize) {
      throw new TensorError(
        'New shape must have the same number of elements',
        { oldShape: this.shape, newShape, oldSize, newSize },
        'STORAGE_INVALID_RESHAPE'
      );
    }
    
    // Get flattened data
    const flatData = await this.flatten();
    
    // Reshape using recursive function
    return this._reshapeFlat(flatData, newShape);
  }
  
  /**
   * Reshapes flat data to a new shape
   * @private
   * @param {Array} flatData - Flat data array
   * @param {Array<number>} shape - New shape
   * @returns {Array} Reshaped tensor
   */
  _reshapeFlat(flatData, shape) {
    if (shape.length === 0) {
      return flatData[0];
    }
    
    if (shape.length === 1) {
      return flatData.slice(0, shape[0]);
    }
    
    const [firstDim, ...restDims] = shape;
    const result = new Array(firstDim);
    const subSize = restDims.reduce((acc, dim) => acc * dim, 1);
    
    for (let i = 0; i < firstDim; i++) {
      const start = i * subSize;
      const end = start + subSize;
      result[i] = this._reshapeFlat(flatData.slice(start, end), restDims);
    }
    
    return result;
  }
  
  /**
   * Performs a matrix multiplication with another tensor along the last two dimensions
   * @param {Object} other - Other tensor
   * @returns {Promise<Array>} Result tensor
   */
  async matmul(other) {
    // Get other tensor's shape
    const otherShape = await this._getOtherShape(other);
    
    // Validate shapes for matrix multiplication
    if (this.shape.length < 2 || otherShape.length < 2) {
      throw new TensorError(
        'Tensors must have at least 2 dimensions for matrix multiplication',
        { thisShape: this.shape, otherShape },
        'STORAGE_INVALID_DIMENSIONS'
      );
    }
    
    // Check that inner dimensions match
    const thisLastDim = this.shape[this.shape.length - 1];
    const otherSecondLastDim = otherShape[otherShape.length - 2];
    
    if (thisLastDim !== otherSecondLastDim) {
      throw new TensorError(
        'Inner dimensions must match for matrix multiplication',
        { 
          thisDim: thisLastDim, 
          otherDim: otherSecondLastDim 
        },
        'STORAGE_INCOMPATIBLE_DIMENSIONS'
      );
    }
    
    // Calculate result shape
    const resultShape = [];
    
    // Add batch dimensions (if any)
    const batchDims = Math.max(this.shape.length, otherShape.length) - 2;
    
    for (let i = 0; i < batchDims; i++) {
      const thisSize = i < this.shape.length - 2 ? this.shape[i] : 1;
      const otherSize = i < otherShape.length - 2 ? otherShape[i] : 1;
      
      if (thisSize !== otherSize && thisSize !== 1 && otherSize !== 1) {
        throw new TensorError(
          'Incompatible batch dimensions for matrix multiplication',
          { thisDim: thisSize, otherDim: otherSize, dimension: i },
          'STORAGE_INCOMPATIBLE_BATCH_DIMS'
        );
      }
      
      resultShape.push(Math.max(thisSize, otherSize));
    }
    
    // Add matrix dimensions
    resultShape.push(this.shape[this.shape.length - 2]); // m
    resultShape.push(otherShape[otherShape.length - 1]); // n
    
    // Create result tensor
    const result = this._createNestedArray(resultShape);
    
    // Initialize all elements to zero
    this._initializeToZero(result);
    
    // Recursively fill the result tensor
    const matmulInfo = {
      commonDim: thisLastDim,
      thisShape: this.shape,
      otherShape: otherShape,
      resultShape
    };
    
    await this._fillMatmul(result, other, matmulInfo, 0, [], [], []);
    
    return result;
  }
  
  /**
   * Initializes a tensor to zero
   * @private
   * @param {Array} tensor - Tensor to initialize
   */
  _initializeToZero(tensor) {
    if (!Array.isArray(tensor)) {
      return;
    }
    
    for (let i = 0; i < tensor.length; i++) {
      if (Array.isArray(tensor[i])) {
        this._initializeToZero(tensor[i]);
      } else {
        tensor[i] = 0;
      }
    }
  }
  
  /**
   * Recursively fills a matrix multiplication result
   * @private
   * @param {Array} result - Result tensor
   * @param {Object} other - Other tensor
   * @param {Object} matmulInfo - Matrix multiplication information
   * @param {number} dimension - Current dimension
   * @param {Array<number>} thisIndices - Current this tensor indices
   * @param {Array<number>} otherIndices - Current other tensor indices
   * @param {Array<number>} resultIndices - Current result tensor indices
   */
  async _fillMatmul(result, other, matmulInfo, dimension, thisIndices, otherIndices, resultIndices) {
    const { thisShape, otherShape, resultShape, commonDim } = matmulInfo;
    
    if (dimension === resultShape.length - 2) {
      // Process each element of the output matrix
      for (let i = 0; i < resultShape[resultShape.length - 2]; i++) {
        for (let j = 0; j < resultShape[resultShape.length - 1]; j++) {
          // Matrix multiplication using loop over common dimension
          let sum = 0;
          
          for (let k = 0; k < commonDim; k++) {
            // Get values from both tensors
            const thisMatrixIndices = [...thisIndices];
            const otherMatrixIndices = [...otherIndices];
            
            // Adjust for broadcasting in batch dimensions
            for (let d = 0; d < thisMatrixIndices.length; d++) {
              if (d < thisShape.length - 2 && thisShape[d] === 1) {
                thisMatrixIndices[d] = 0;
              }
            }
            
            for (let d = 0; d < otherMatrixIndices.length; d++) {
              if (d < otherShape.length - 2 && otherShape[d] === 1) {
                otherMatrixIndices[d] = 0;
              }
            }
            
            // Add matrix indices
            thisMatrixIndices.push(i, k);
            otherMatrixIndices.push(k, j);
            
            // Get values
            let thisValue, otherValue;
            
            if (other instanceof SwappableTensor) {
              thisValue = await this.get(thisMatrixIndices);
              otherValue = await other.get(otherMatrixIndices);
            } else {
              thisValue = await this.get(thisMatrixIndices);
              otherValue = this._getFromNestedArray(other, otherMatrixIndices);
            }
            
            sum += thisValue * otherValue;
          }
          
          // Set result
          const finalResultIndices = [...resultIndices, i, j];
          this._setInNestedArray(result, finalResultIndices, sum);
        }
      }
      
      return;
    }
    
    // Recursive case: handle batch dimensions
    for (let i = 0; i < resultShape[dimension]; i++) {
      // Adjust indices for broadcasting
      const thisIdx = dimension < thisShape.length - 2 ? 
        (thisShape[dimension] === 1 ? 0 : i) : 0;
      
      const otherIdx = dimension < otherShape.length - 2 ? 
        (otherShape[dimension] === 1 ? 0 : i) : 0;
      
      thisIndices.push(thisIdx);
      otherIndices.push(otherIdx);
      resultIndices.push(i);
      
      await this._fillMatmul(result, other, matmulInfo, dimension + 1, thisIndices, otherIndices, resultIndices);
      
      thisIndices.pop();
      otherIndices.pop();
      resultIndices.pop();
    }
  }
  
  /**
   * Computes the trace of the tensor (sum of diagonal elements)
   * @returns {Promise<number>} Trace value
   */
  async trace() {
    // Ensure the tensor has at least 2 dimensions and the last two are the same size
    if (this.shape.length < 2) {
      throw new TensorError(
        'Tensor must have at least 2 dimensions for trace',
        { shape: this.shape },
        'STORAGE_INVALID_DIMENSIONS'
      );
    }
    
    const lastDim = this.shape[this.shape.length - 1];
    const secondLastDim = this.shape[this.shape.length - 2];
    
    if (lastDim !== secondLastDim) {
      throw new TensorError(
        'Last two dimensions must be the same size for trace',
        { dim1: secondLastDim, dim2: lastDim },
        'STORAGE_INVALID_DIMENSIONS'
      );
    }
    
    // Calculate batch dimensions (if any)
    const batchShape = this.shape.slice(0, -2);
    
    // For each batch, calculate the trace of the matrix
    let totalTrace = 0;
    
    // Handle batch dimension recursively
    await this._calculateBatchTraces(batchShape, 0, [], (trace) => {
      totalTrace += trace;
    });
    
    return totalTrace;
  }
  
  /**
   * Recursively calculates traces for each batch
   * @private
   * @param {Array<number>} batchShape - Batch dimensions
   * @param {number} dimension - Current dimension
   * @param {Array<number>} indices - Current batch indices
   * @param {Function} addTrace - Function to add a trace value
   */
  async _calculateBatchTraces(batchShape, dimension, indices, addTrace) {
    if (dimension === batchShape.length) {
      // Base case: calculate trace for this batch
      const matrixSize = this.shape[this.shape.length - 1];
      let trace = 0;
      
      for (let i = 0; i < matrixSize; i++) {
        // Get diagonal element
        const fullIndices = [...indices, i, i];
        trace += await this.get(fullIndices);
      }
      
      addTrace(trace);
      return;
    }
    
    // Recursive case: iterate through the current batch dimension
    for (let i = 0; i < batchShape[dimension]; i++) {
      indices.push(i);
      await this._calculateBatchTraces(batchShape, dimension + 1, indices, addTrace);
      indices.pop();
    }
  }
  
  /**
   * Transposes the tensor by permuting its dimensions
   * @param {Array<number>} [permutation] - Dimension permutation (default: reverse dimensions)
   * @returns {Promise<Array>} Transposed tensor
   */
  async transpose(permutation) {
    // Default permutation is to reverse dimensions
    if (!permutation) {
      permutation = Array.from(this.shape.keys()).reverse();
    }
    
    // Validate permutation
    if (permutation.length !== this.shape.length) {
      throw new TensorError(
        'Permutation must have the same length as tensor dimensions',
        { permutation, shape: this.shape },
        'STORAGE_INVALID_PERMUTATION'
      );
    }
    
    const seen = new Set();
    for (const dim of permutation) {
      if (dim < 0 || dim >= this.shape.length || seen.has(dim)) {
        throw new TensorError(
          'Invalid permutation',
          { permutation, shape: this.shape },
          'STORAGE_INVALID_PERMUTATION'
        );
      }
      seen.add(dim);
    }
    
    // Calculate new shape
    const newShape = permutation.map(dim => this.shape[dim]);
    
    // Create transposed tensor
    const result = this._createNestedArray(newShape);
    
    // Fill the transposed tensor
    await this._fillTranspose(result, permutation, 0, [], []);
    
    return result;
  }
  
  /**
   * Recursively fills a transposed tensor
   * @private
   * @param {Array} result - Result tensor
   * @param {Array<number>} permutation - Dimension permutation
   * @param {number} dimension - Current dimension
   * @param {Array<number>} originalIndices - Current original tensor indices
   * @param {Array<number>} resultIndices - Current result tensor indices
   */
  async _fillTranspose(result, permutation, dimension, originalIndices, resultIndices) {
    if (dimension === this.shape.length) {
      // Base case: get the value and add it to the result
      const value = await this.get(originalIndices);
      
      // Set the value in the transposed tensor
      this._setInNestedArray(result, resultIndices, value);
      
      return;
    }
    
    // Recursive case: iterate through the current dimension
    for (let i = 0; i < this.shape[dimension]; i++) {
      originalIndices.push(i);
      
      // Calculate the corresponding index in the result tensor
      const resultDim = permutation.indexOf(dimension);
      resultIndices[resultDim] = i;
      
      await this._fillTranspose(result, permutation, dimension + 1, originalIndices, resultIndices);
      
      originalIndices.pop();
    }
  }
}

module.exports = SwappableTensor;