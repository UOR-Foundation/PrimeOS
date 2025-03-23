/**
 * PrimeOS JavaScript Library - Virtual Array
 * Array implementation that loads data on demand from storage
 */

const Prime = require('../../core');
const { PrimeStorageError } = require('../core/provider');

/**
 * Virtual array that loads data on demand from storage
 */
class VirtualArray {
  /**
   * Creates a new virtual array
   * @param {StorageManager} storageManager - Storage manager to use
   * @param {VirtualArrayOptions} options - Virtual array options
   */
  constructor(storageManager, options) {
    this.storageManager = storageManager;
    
    this.options = {
      id: options.id,
      length: options.length,
      chunkSize: options.chunkSize || 1000,
      itemFactory: options.itemFactory || null,
      ...options
    };
    
    this.cache = new Map();
    this.length = this.options.length;
  }

  /**
   * Gets an item from the virtual array
   * @param {number} index - Index of the item to get
   * @returns {Promise<*>} The item
   */
  async getItem(index) {
    if (index < 0 || index >= this.length) {
      throw new PrimeStorageError(
        `Index out of bounds: ${index}`,
        { index, length: this.length },
        'STORAGE_INDEX_OUT_OF_BOUNDS'
      );
    }
    
    // Check cache first
    if (this.cache.has(index)) {
      return this.cache.get(index);
    }
    
    // If we have an item factory, use it
    if (this.options.itemFactory) {
      const item = this.options.itemFactory(index);
      this.cache.set(index, item);
      return item;
    }
    
    // Otherwise, load from storage
    try {
      const data = await this.storageManager.load(this.options.id);
      
      if (Array.isArray(data) && index < data.length) {
        const item = data[index];
        this.cache.set(index, item);
        return item;
      }
      
      throw new PrimeStorageError(
        `Failed to get item at index ${index}`,
        { index },
        'STORAGE_ITEM_NOT_FOUND'
      );
    } catch (error) {
      throw new PrimeStorageError(
        `Failed to get item at index ${index}: ${error.message}`,
        { index, originalError: error },
        'STORAGE_GET_ITEM_FAILED',
        error
      );
    }
  }

  /**
   * Creates an iterator that loads data in chunks
   * @param {number} [chunkSize] - Size of chunks to load
   * @returns {AsyncIterator} An async iterator for the array
   */
  async *iterateChunks(chunkSize = this.options.chunkSize) {
    for (let i = 0; i < this.length; i += chunkSize) {
      const chunkLength = Math.min(chunkSize, this.length - i);
      const chunk = new Array(chunkLength);
      
      // If we have an item factory, use it
      if (this.options.itemFactory) {
        for (let j = 0; j < chunkLength; j++) {
          chunk[j] = this.options.itemFactory(i + j);
        }
        
        yield chunk;
        continue;
      }
      
      // Otherwise, load from storage
      try {
        const data = await this.storageManager.load(this.options.id);
        
        if (Array.isArray(data)) {
          const end = Math.min(i + chunkSize, data.length);
          const dataChunk = data.slice(i, end);
          
          yield dataChunk;
        } else {
          throw new PrimeStorageError(
            'Data is not an array',
            { id: this.options.id },
            'STORAGE_NOT_ARRAY'
          );
        }
      } catch (error) {
        throw new PrimeStorageError(
          `Failed to iterate chunks: ${error.message}`,
          { originalError: error },
          'STORAGE_ITERATE_FAILED',
          error
        );
      }
    }
  }

  /**
   * Maps a function over the virtual array
   * @param {Function} callback - Function to apply to each item
   * @param {number} [chunkSize] - Size of chunks to process
   * @returns {Promise<Array>} Mapped array
   */
  async map(callback, chunkSize = this.options.chunkSize) {
    const result = new Array(this.length);
    
    for (let i = 0; i < this.length; i += chunkSize) {
      const end = Math.min(i + chunkSize, this.length);
      const chunk = [];
      
      // Load chunk
      for (let j = i; j < end; j++) {
        chunk.push(await this.getItem(j));
      }
      
      // Apply callback to chunk
      for (let j = 0; j < chunk.length; j++) {
        result[i + j] = callback(chunk[j], i + j, this);
      }
    }
    
    return result;
  }

  /**
   * Filters the virtual array
   * @param {Function} callback - Filter function
   * @param {number} [chunkSize] - Size of chunks to process
   * @returns {Promise<Array>} Filtered array
   */
  async filter(callback, chunkSize = this.options.chunkSize) {
    const result = [];
    
    for (let i = 0; i < this.length; i += chunkSize) {
      const end = Math.min(i + chunkSize, this.length);
      const chunk = [];
      
      // Load chunk
      for (let j = i; j < end; j++) {
        chunk.push(await this.getItem(j));
      }
      
      // Apply callback to chunk
      for (let j = 0; j < chunk.length; j++) {
        if (callback(chunk[j], i + j, this)) {
          result.push(chunk[j]);
        }
      }
    }
    
    return result;
  }

  /**
   * Reduces the virtual array
   * @param {Function} callback - Reducer function
   * @param {*} initialValue - Initial value
   * @param {number} [chunkSize] - Size of chunks to process
   * @returns {Promise<*>} Reduced value
   */
  async reduce(callback, initialValue, chunkSize = this.options.chunkSize) {
    let accumulator = initialValue;
    
    for (let i = 0; i < this.length; i += chunkSize) {
      const end = Math.min(i + chunkSize, this.length);
      const chunk = [];
      
      // Load chunk
      for (let j = i; j < end; j++) {
        chunk.push(await this.getItem(j));
      }
      
      // Apply callback to chunk
      for (let j = 0; j < chunk.length; j++) {
        accumulator = callback(accumulator, chunk[j], i + j, this);
      }
    }
    
    return accumulator;
  }

  /**
   * Gets a slice of the virtual array
   * @param {number} start - Start index
   * @param {number} [end] - End index (exclusive)
   * @returns {Promise<Array>} Array slice
   */
  async slice(start, end = this.length) {
    // Normalize indices
    start = Math.max(0, start);
    end = Math.min(this.length, end);
    
    if (start >= end) {
      return [];
    }
    
    const result = new Array(end - start);
    
    for (let i = start; i < end; i++) {
      result[i - start] = await this.getItem(i);
    }
    
    return result;
  }

  /**
   * Gets a range of items from the virtual array
   * @param {number} start - Start index
   * @param {number} [end] - End index (exclusive)
   * @returns {Promise<Array>} Array range
   */
  async getRange(start, end = this.length) {
    return this.slice(start, end);
  }

  /**
   * Finds an item in the virtual array
   * @param {Function} predicate - Predicate function
   * @param {number} [chunkSize] - Size of chunks to process
   * @returns {Promise<*>} Found item or undefined
   */
  async find(predicate, chunkSize = this.options.chunkSize) {
    for (let i = 0; i < this.length; i += chunkSize) {
      const end = Math.min(i + chunkSize, this.length);
      const chunk = [];
      
      // Load chunk
      for (let j = i; j < end; j++) {
        chunk.push(await this.getItem(j));
      }
      
      // Apply predicate to chunk
      for (let j = 0; j < chunk.length; j++) {
        if (predicate(chunk[j], i + j, this)) {
          return chunk[j];
        }
      }
    }
    
    return undefined;
  }

  /**
   * Finds the index of an item in the virtual array
   * @param {Function} predicate - Predicate function
   * @param {number} [chunkSize] - Size of chunks to process
   * @returns {Promise<number>} Found index or -1
   */
  async findIndex(predicate, chunkSize = this.options.chunkSize) {
    for (let i = 0; i < this.length; i += chunkSize) {
      const end = Math.min(i + chunkSize, this.length);
      const chunk = [];
      
      // Load chunk
      for (let j = i; j < end; j++) {
        chunk.push(await this.getItem(j));
      }
      
      // Apply predicate to chunk
      for (let j = 0; j < chunk.length; j++) {
        if (predicate(chunk[j], i + j, this)) {
          return i + j;
        }
      }
    }
    
    return -1;
  }

  /**
   * Prefetches a range of items into the cache
   * @param {number} start - Start index
   * @param {number} [end] - End index (exclusive)
   * @returns {Promise<void>}
   */
  async prefetch(start, end = start + 100) {
    // Normalize indices
    start = Math.max(0, start);
    end = Math.min(this.length, end);
    
    if (start >= end) {
      return;
    }
    
    // If we have an item factory, use it
    if (this.options.itemFactory) {
      for (let i = start; i < end; i++) {
        if (!this.cache.has(i)) {
          this.cache.set(i, this.options.itemFactory(i));
        }
      }
      return;
    }
    
    // Otherwise, load from storage
    try {
      const data = await this.storageManager.load(this.options.id);
      
      if (Array.isArray(data)) {
        for (let i = start; i < end && i < data.length; i++) {
          this.cache.set(i, data[i]);
        }
      }
    } catch (error) {
      throw new PrimeStorageError(
        `Failed to prefetch items: ${error.message}`,
        { start, end, originalError: error },
        'STORAGE_PREFETCH_FAILED',
        error
      );
    }
  }

  /**
   * Clears the cache
   */
  clearCache() {
    this.cache.clear();
  }
}

module.exports = VirtualArray;