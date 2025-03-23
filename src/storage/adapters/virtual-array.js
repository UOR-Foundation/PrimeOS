/**
 * PrimeOS JavaScript Library - Virtual Array
 * Array implementation that loads data on demand from storage
 */

const Prime = require("../../core");
const { StorageError } = require("../index");

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
      defaultValue: 0,
      chunkSize: 1000,
      prefetchSize: 1,
      cacheSize: 5,
      ...options,
    };

    this.length = this.options.length || 0;
    this.id =
      this.options.id ||
      `virtual_array_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
    this.initialized = false;

    // Chunk management
    this.chunks = new Map();
    this.chunkAccess = []; // For LRU tracking
    this.loadedChunks = 0;
    this.chunkHits = 0;
    this.chunkMisses = 0;
    this.pendingChunks = new Map(); // Promises for chunks being loaded
  }

  /**
   * Initializes the virtual array
   * @returns {Promise<void>}
   */
  async init() {
    if (this.initialized) {
      return;
    }

    try {
      // Try to load metadata if existing id is provided
      if (this.options.id) {
        const metadata = await this.storageManager.load(`${this.id}_metadata`);

        if (metadata) {
          this.length = metadata.length;
          this.options = {
            ...this.options,
            ...metadata.options,
          };
        }
      }

      // Store metadata for new arrays
      if (
        !this.options.id ||
        !(await this.storageManager.load(`${this.id}_metadata`))
      ) {
        await this.storageManager.store(
          {
            length: this.length,
            options: {
              defaultValue: this.options.defaultValue,
              chunkSize: this.options.chunkSize,
            },
            created: Date.now(),
          },
          `${this.id}_metadata`,
        );
      }

      this.initialized = true;
    } catch (error) {
      throw new StorageError(
        `Failed to initialize virtual array: ${error.message}`,
        { originalError: error },
        "STORAGE_ARRAY_INIT_FAILED",
        error,
      );
    }
  }

  /**
   * Gets a chunk of data
   * @private
   * @param {number} chunkIndex - Chunk index
   * @returns {Promise<Array>} Chunk data
   */
  async _getChunk(chunkIndex) {
    // Check if chunk is in memory
    if (this.chunks.has(chunkIndex)) {
      // Track access for LRU
      this._updateChunkAccess(chunkIndex);
      this.chunkHits++;
      return this.chunks.get(chunkIndex);
    }

    // Check if there's a pending load for this chunk
    if (this.pendingChunks.has(chunkIndex)) {
      return this.pendingChunks.get(chunkIndex);
    }

    // Create a promise for this chunk load
    this.chunkMisses++;
    const chunkPromise = this._loadChunk(chunkIndex);
    this.pendingChunks.set(chunkIndex, chunkPromise);

    try {
      // Await the chunk load
      const chunk = await chunkPromise;
      // Remove from pending once loaded
      this.pendingChunks.delete(chunkIndex);
      return chunk;
    } catch (error) {
      // Clean up on error
      this.pendingChunks.delete(chunkIndex);
      throw error;
    }
  }

  /**
   * Loads a chunk from storage
   * @private
   * @param {number} chunkIndex - Chunk index
   * @returns {Promise<Array>} Chunk data
   */
  async _loadChunk(chunkIndex) {
    const chunkKey = `${this.id}_chunk_${chunkIndex}`;

    try {
      // Try to load chunk from storage
      const chunk = await this.storageManager.load(chunkKey);

      if (chunk) {
        // Store chunk in memory
        this._storeChunk(chunkIndex, chunk);
        return chunk;
      }

      // If chunk doesn't exist, create it with default values
      const startIndex = chunkIndex * this.options.chunkSize;
      const endIndex = Math.min(
        startIndex + this.options.chunkSize,
        this.length,
      );
      const newChunk = new Array(endIndex - startIndex).fill(
        this.options.defaultValue,
      );

      // Store in memory and storage
      this._storeChunk(chunkIndex, newChunk);
      await this.storageManager.store(newChunk, chunkKey);

      return newChunk;
    } catch (error) {
      throw new StorageError(
        `Failed to load chunk ${chunkIndex}: ${error.message}`,
        { chunkIndex, originalError: error },
        "STORAGE_CHUNK_LOAD_FAILED",
        error,
      );
    }
  }

  /**
   * Stores a chunk in memory
   * @private
   * @param {number} chunkIndex - Chunk index
   * @param {Array} chunk - Chunk data
   */
  _storeChunk(chunkIndex, chunk) {
    // Evict chunks if cache is full
    if (this.chunks.size >= this.options.cacheSize) {
      this._evictChunk();
    }

    // Store chunk in memory
    this.chunks.set(chunkIndex, chunk);
    this._updateChunkAccess(chunkIndex);
    this.loadedChunks++;
  }

  /**
   * Updates the access order for a chunk
   * @private
   * @param {number} chunkIndex - Chunk index
   */
  _updateChunkAccess(chunkIndex) {
    // Remove from current position
    const index = this.chunkAccess.indexOf(chunkIndex);
    if (index !== -1) {
      this.chunkAccess.splice(index, 1);
    }

    // Add to the end (most recently used)
    this.chunkAccess.push(chunkIndex);
  }

  /**
   * Evicts a chunk from memory
   * @private
   */
  _evictChunk() {
    if (this.chunkAccess.length === 0) {
      return;
    }

    // Get least recently used chunk
    const chunkIndex = this.chunkAccess.shift();
    const chunk = this.chunks.get(chunkIndex);

    // If chunk is modified, save it to storage
    if (chunk && chunk.modified) {
      const chunkKey = `${this.id}_chunk_${chunkIndex}`;
      this.storageManager.store(chunk, chunkKey).catch((error) => {
        console.error(
          `Failed to save chunk ${chunkIndex} during eviction:`,
          error,
        );
      });
    }

    // Remove from memory
    this.chunks.delete(chunkIndex);
  }

  /**
   * Gets a value from the virtual array
   * @param {number} index - Array index
   * @returns {Promise<*>} Value at the index
   */
  async get(index) {
    if (!this.initialized) {
      await this.init();
    }

    // Validate index
    if (index < 0 || index >= this.length) {
      throw new StorageError(
        `Index ${index} out of bounds (0-${this.length - 1})`,
        { index, length: this.length },
        "STORAGE_INDEX_OUT_OF_BOUNDS",
      );
    }

    // Calculate chunk info
    const chunkIndex = Math.floor(index / this.options.chunkSize);
    const indexInChunk = index % this.options.chunkSize;

    // Get the chunk
    const chunk = await this._getChunk(chunkIndex);

    // Return value from chunk
    return chunk[indexInChunk];
  }

  /**
   * Sets a value in the virtual array
   * @param {number} index - Array index
   * @param {*} value - Value to set
   * @returns {Promise<void>}
   */
  async set(index, value) {
    if (!this.initialized) {
      await this.init();
    }

    // Validate index
    if (index < 0 || index >= this.length) {
      throw new StorageError(
        `Index ${index} out of bounds (0-${this.length - 1})`,
        { index, length: this.length },
        "STORAGE_INDEX_OUT_OF_BOUNDS",
      );
    }

    // Calculate chunk info
    const chunkIndex = Math.floor(index / this.options.chunkSize);
    const indexInChunk = index % this.options.chunkSize;

    // Get the chunk
    const chunk = await this._getChunk(chunkIndex);

    // Set value in chunk
    chunk[indexInChunk] = value;
    chunk.modified = true;

    // Prefetch next chunk if near the end
    if (indexInChunk > this.options.chunkSize - this.options.prefetchSize) {
      this._prefetchChunk(chunkIndex + 1).catch(() => {
        // Ignore prefetch errors
      });
    }
  }

  /**
   * Prefetches a chunk
   * @private
   * @param {number} chunkIndex - Chunk index to prefetch
   * @returns {Promise<void>}
   */
  async _prefetchChunk(chunkIndex) {
    // Only prefetch if the chunk exists and is not already loaded
    if (
      chunkIndex < Math.ceil(this.length / this.options.chunkSize) &&
      !this.chunks.has(chunkIndex)
    ) {
      await this._getChunk(chunkIndex);
    }
  }

  /**
   * Gets multiple values from the virtual array
   * @param {number} startIndex - Start index
   * @param {number} count - Number of values to get
   * @returns {Promise<Array>} Values in the range
   */
  async getBulk(startIndex, count) {
    if (!this.initialized) {
      await this.init();
    }

    // Validate range
    if (startIndex < 0 || startIndex + count > this.length) {
      throw new StorageError(
        `Range (${startIndex}-${startIndex + count - 1}) out of bounds (0-${this.length - 1})`,
        { startIndex, count, length: this.length },
        "STORAGE_RANGE_OUT_OF_BOUNDS",
      );
    }

    // Calculate chunk info
    const startChunkIndex = Math.floor(startIndex / this.options.chunkSize);
    const endChunkIndex = Math.floor(
      (startIndex + count - 1) / this.options.chunkSize,
    );

    // Create result array
    const result = new Array(count);

    // Load chunks in parallel
    const chunkPromises = [];
    for (let i = startChunkIndex; i <= endChunkIndex; i++) {
      chunkPromises.push(this._getChunk(i));
    }

    const chunks = await Promise.all(chunkPromises);

    // Fill result array from chunks
    for (let i = 0; i < count; i++) {
      const globalIndex = startIndex + i;
      const chunkIndex =
        Math.floor(globalIndex / this.options.chunkSize) - startChunkIndex;
      const indexInChunk = globalIndex % this.options.chunkSize;
      result[i] = chunks[chunkIndex][indexInChunk];
    }

    return result;
  }

  /**
   * Sets multiple values in the virtual array
   * @param {number} startIndex - Start index
   * @param {Array} values - Values to set
   * @returns {Promise<void>}
   */
  async setBulk(startIndex, values) {
    if (!this.initialized) {
      await this.init();
    }

    if (!Array.isArray(values)) {
      throw new StorageError(
        "Values must be an array",
        { values },
        "STORAGE_INVALID_VALUES",
      );
    }

    // Validate range
    if (startIndex < 0 || startIndex + values.length > this.length) {
      throw new StorageError(
        `Range (${startIndex}-${startIndex + values.length - 1}) out of bounds (0-${this.length - 1})`,
        { startIndex, valuesLength: values.length, length: this.length },
        "STORAGE_RANGE_OUT_OF_BOUNDS",
      );
    }

    // Calculate chunk info
    const startChunkIndex = Math.floor(startIndex / this.options.chunkSize);
    const endChunkIndex = Math.floor(
      (startIndex + values.length - 1) / this.options.chunkSize,
    );

    // Initialize chunks
    const chunkUpdates = new Map();

    // Group values by chunk
    for (let i = 0; i < values.length; i++) {
      const globalIndex = startIndex + i;
      const chunkIndex = Math.floor(globalIndex / this.options.chunkSize);
      const indexInChunk = globalIndex % this.options.chunkSize;

      // Create chunk update if it doesn't exist
      if (!chunkUpdates.has(chunkIndex)) {
        chunkUpdates.set(chunkIndex, {
          indices: [],
          values: [],
        });
      }

      // Add value to chunk update
      const update = chunkUpdates.get(chunkIndex);
      update.indices.push(indexInChunk);
      update.values.push(values[i]);
    }

    // Apply updates to chunks
    for (const [chunkIndex, update] of chunkUpdates.entries()) {
      // Get the chunk
      const chunk = await this._getChunk(chunkIndex);

      // Update values
      for (let i = 0; i < update.indices.length; i++) {
        chunk[update.indices[i]] = update.values[i];
      }

      chunk.modified = true;
    }
  }

  /**
   * Iterates over a range of values in the virtual array
   * @param {number} startIndex - Start index
   * @param {number} count - Number of values to iterate over
   * @param {Function} callback - Callback function(value, index)
   * @returns {Promise<void>}
   */
  async forEach(startIndex, count, callback) {
    if (!this.initialized) {
      await this.init();
    }

    if (typeof callback !== "function") {
      throw new StorageError(
        "Callback must be a function",
        { callback },
        "STORAGE_INVALID_CALLBACK",
      );
    }

    // Get values in range
    const values = await this.getBulk(startIndex, count);

    // Call callback for each value
    for (let i = 0; i < values.length; i++) {
      callback(values[i], startIndex + i);
    }
  }

  /**
   * Maps a range of values in the virtual array
   * @param {number} startIndex - Start index
   * @param {number} count - Number of values to map
   * @param {Function} callback - Mapping function(value, index)
   * @returns {Promise<Array>} Mapped values
   */
  async map(startIndex, count, callback) {
    if (!this.initialized) {
      await this.init();
    }

    if (typeof callback !== "function") {
      throw new StorageError(
        "Callback must be a function",
        { callback },
        "STORAGE_INVALID_CALLBACK",
      );
    }

    // Get values in range
    const values = await this.getBulk(startIndex, count);

    // Map values
    return values.map((value, i) => callback(value, startIndex + i));
  }

  /**
   * Flushes all modified chunks to storage
   * @returns {Promise<void>}
   */
  async flush() {
    if (!this.initialized) {
      await this.init();
    }

    // Store all modified chunks
    const savePromises = [];

    for (const [chunkIndex, chunk] of this.chunks.entries()) {
      if (chunk.modified) {
        const chunkKey = `${this.id}_chunk_${chunkIndex}`;
        savePromises.push(this.storageManager.store(chunk, chunkKey));
        chunk.modified = false;
      }
    }

    // Wait for all saves to complete
    await Promise.all(savePromises);
  }

  /**
   * Gets statistics about the virtual array
   * @returns {Object} Statistics
   */
  getChunkStats() {
    return {
      length: this.length,
      chunkSize: this.options.chunkSize,
      totalChunks: Math.ceil(this.length / this.options.chunkSize),
      loadedChunks: this.chunks.size,
      chunkHits: this.chunkHits,
      chunkMisses: this.chunkMisses,
      hitRate:
        this.chunkHits + this.chunkMisses > 0
          ? this.chunkHits / (this.chunkHits + this.chunkMisses)
          : 0,
    };
  }
}

module.exports = VirtualArray;
