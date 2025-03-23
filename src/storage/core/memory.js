/**
 * PrimeOS JavaScript Library - Memory Storage Provider
 * In-memory storage provider for fallback and testing
 */

const Prime = require('../../core');
const { StorageProvider, PrimeStorageError } = require('./provider');
const { EventEmitter } = require('events');

/**
 * Memory-based storage provider
 */
class MemoryProvider extends StorageProvider {
  /**
   * Creates a new memory provider
   * @param {StorageOptions} options - Storage options
   */
  constructor(options = {}) {
    super(options);
    
    this.store = new Map();
    this.streams = {};
  }

  /**
   * Initializes the memory provider
   * @returns {Promise<void>}
   */
  async init() {
    this.isInitialized = true;
    return Promise.resolve();
  }

  /**
   * Stores data with the given ID
   * @param {*} data - Data to store
   * @param {string} [id] - Optional ID (if not provided, a UUID will be generated)
   * @returns {Promise<string>} The ID of the stored data
   */
  async store(data, id) {
    const dataId = id || Prime.Utils.uuid();
    
    // Clone the data to prevent reference issues
    let dataToStore;
    try {
      dataToStore = Prime.Utils.deepClone(data);
    } catch (error) {
      // If cloning fails, store as is
      dataToStore = data;
    }
    
    this.store.set(dataId, dataToStore);
    return Promise.resolve(dataId);
  }

  /**
   * Loads data with the given ID
   * @param {string} id - ID of the data to load
   * @returns {Promise<*>} The loaded data
   */
  async load(id) {
    if (!this.store.has(id)) {
      throw new PrimeStorageError(
        `Data not found for ID: ${id}`,
        { id },
        'STORAGE_NOT_FOUND'
      );
    }
    
    // Clone the data to prevent reference issues
    let data;
    try {
      data = Prime.Utils.deepClone(this.store.get(id));
    } catch (error) {
      // If cloning fails, return as is
      data = this.store.get(id);
    }
    
    return Promise.resolve(data);
  }

  /**
   * Deletes data with the given ID
   * @param {string} id - ID of the data to delete
   * @returns {Promise<boolean>} True if successful
   */
  async delete(id) {
    const result = this.store.delete(id);
    return Promise.resolve(result);
  }

  /**
   * Checks if data with the given ID exists
   * @param {string} id - ID to check
   * @returns {Promise<boolean>} True if data exists
   */
  async exists(id) {
    return Promise.resolve(this.store.has(id));
  }

  /**
   * Lists all stored data IDs
   * @returns {Promise<string[]>} Array of stored data IDs
   */
  async getAllKeys() {
    return Promise.resolve(Array.from(this.store.keys()));
  }

  /**
   * Clears all stored data
   * @returns {Promise<void>}
   */
  async clear() {
    this.store.clear();
    return Promise.resolve();
  }

  /**
   * Gets information about the storage
   * @returns {Promise<StorageInfo>} Storage information
   */
  async getStorageInfo() {
    // For memory provider, we don't have much info
    return Promise.resolve({
      available: Number.MAX_SAFE_INTEGER,
      used: this.getUsedSpace(),
      total: Number.MAX_SAFE_INTEGER,
      provider: 'memory'
    });
  }

  /**
   * Creates a read stream for the data with the given ID
   * @param {string} id - ID of the data to stream
   * @param {StreamOptions} [options] - Stream options
   * @returns {ReadableStream} A readable stream of the data
   */
  createReadStream(id, options = {}) {
    if (!this.store.has(id)) {
      throw new PrimeStorageError(
        `Data not found for ID: ${id}`,
        { id },
        'STORAGE_NOT_FOUND'
      );
    }
    
    const stream = new MemoryReadStream(this.store.get(id), options);
    return stream;
  }

  /**
   * Creates a write stream for storing data
   * @param {string} [id] - Optional ID (if not provided, a UUID will be generated)
   * @param {StreamOptions} [options] - Stream options
   * @returns {WritableStream} A writable stream to store data
   */
  createWriteStream(id, options = {}) {
    const dataId = id || Prime.Utils.uuid();
    const stream = new MemoryWriteStream(this, dataId, options);
    return stream;
  }

  /**
   * Gets the provider type
   * @returns {string} The provider type
   */
  getProviderType() {
    return 'memory';
  }

  /**
   * Estimates the used space in bytes
   * @private
   * @returns {number} Used space in bytes
   */
  getUsedSpace() {
    let totalSize = 0;
    
    for (const [id, data] of this.store.entries()) {
      let size = 0;
      
      if (typeof data === 'string') {
        size = data.length * 2; // Approximate for UTF-16
      } else if (Array.isArray(data)) {
        size = this.estimateArraySize(data);
      } else if (typeof Buffer !== 'undefined' && Buffer.isBuffer(data)) {
        size = data.length;
      } else if (ArrayBuffer.isView(data)) {
        size = data.byteLength;
      } else if (data instanceof ArrayBuffer) {
        size = data.byteLength;
      } else if (typeof data === 'object' && data !== null) {
        // Estimate object size
        try {
          const json = JSON.stringify(data);
          size = json.length * 2;
        } catch (e) {
          size = 1024; // Default size if stringify fails
        }
      } else {
        size = 8; // Default size for primitives
      }
      
      totalSize += size;
    }
    
    return totalSize;
  }

  /**
   * Estimates the size of an array in bytes
   * @private
   * @param {Array} array - Array to estimate size for
   * @returns {number} Estimated size in bytes
   */
  estimateArraySize(array) {
    if (array.length === 0) {
      return 0;
    }
    
    // Sample a few elements to estimate size
    const sampleSize = Math.min(array.length, 10);
    let totalSampleSize = 0;
    
    for (let i = 0; i < sampleSize; i++) {
      const index = Math.floor(array.length * (i / sampleSize));
      let elemSize = 0;
      
      const elem = array[index];
      if (typeof elem === 'string') {
        elemSize = elem.length * 2;
      } else if (Array.isArray(elem)) {
        elemSize = this.estimateArraySize(elem);
      } else if (typeof elem === 'object' && elem !== null) {
        try {
          const json = JSON.stringify(elem);
          elemSize = json.length * 2;
        } catch (e) {
          elemSize = 1024;
        }
      } else {
        elemSize = 8;
      }
      
      totalSampleSize += elemSize;
    }
    
    const averageElementSize = totalSampleSize / sampleSize;
    return Math.ceil(averageElementSize * array.length);
  }
}

/**
 * Memory-based readable stream
 */
class MemoryReadStream extends EventEmitter {
  /**
   * Creates a new memory read stream
   * @param {*} data - Data to stream
   * @param {StreamOptions} [options] - Stream options
   */
  constructor(data, options = {}) {
    super();
    
    this.data = data;
    this.options = {
      highWaterMark: 16384, // 16KB
      objectMode: true,
      chunkSize: 1024,
      ...options
    };
    
    this.position = 0;
    this.flowing = false;
    
    process.nextTick(() => {
      this.emit('readable');
    });
  }

  /**
   * Starts the flow of data
   * @private
   */
  _read() {
    this.flowing = true;
    
    // Process data differently based on type
    if (Array.isArray(this.data)) {
      this._readArray();
    } else if (typeof this.data === 'string') {
      this._readString();
    } else if (typeof Buffer !== 'undefined' && Buffer.isBuffer(this.data)) {
      this._readBuffer();
    } else if (ArrayBuffer.isView(this.data)) {
      this._readTypedArray();
    } else {
      // For other types, push as is
      this.emit('data', this.data);
      this.emit('end');
    }
  }

  /**
   * Reads array data in chunks
   * @private
   */
  _readArray() {
    const chunkSize = this.options.chunkSize;
    
    while (this.position < this.data.length) {
      const end = Math.min(this.position + chunkSize, this.data.length);
      const chunk = this.data.slice(this.position, end);
      
      this.emit('data', chunk);
      this.position = end;
      
      if (this.position >= this.data.length) {
        this.emit('end');
        break;
      }
    }
  }

  /**
   * Reads string data in chunks
   * @private
   */
  _readString() {
    const chunkSize = this.options.chunkSize;
    
    while (this.position < this.data.length) {
      const end = Math.min(this.position + chunkSize, this.data.length);
      const chunk = this.data.substring(this.position, end);
      
      this.emit('data', chunk);
      this.position = end;
      
      if (this.position >= this.data.length) {
        this.emit('end');
        break;
      }
    }
  }

  /**
   * Reads buffer data in chunks
   * @private
   */
  _readBuffer() {
    const chunkSize = this.options.chunkSize;
    
    while (this.position < this.data.length) {
      const end = Math.min(this.position + chunkSize, this.data.length);
      const chunk = this.data.slice(this.position, end);
      
      this.emit('data', chunk);
      this.position = end;
      
      if (this.position >= this.data.length) {
        this.emit('end');
        break;
      }
    }
  }

  /**
   * Reads typed array data in chunks
   * @private
   */
  _readTypedArray() {
    const chunkSize = this.options.chunkSize;
    
    while (this.position < this.data.length) {
      const end = Math.min(this.position + chunkSize, this.data.length);
      const chunk = this.data.slice(this.position, end);
      
      this.emit('data', chunk);
      this.position = end;
      
      if (this.position >= this.data.length) {
        this.emit('end');
        break;
      }
    }
  }

  /**
   * Pauses the stream
   * @returns {MemoryReadStream} This stream
   */
  pause() {
    this.flowing = false;
    return this;
  }

  /**
   * Resumes the stream
   * @returns {MemoryReadStream} This stream
   */
  resume() {
    if (!this.flowing) {
      this.flowing = true;
      this._read();
    }
    return this;
  }

  /**
   * Pipes the stream to a writable stream
   * @param {WritableStream} destination - Destination stream
   * @param {Object} [options] - Pipe options
   * @returns {WritableStream} The destination stream
   */
  pipe(destination, options) {
    this.on('data', (chunk) => {
      const canContinue = destination.write(chunk);
      if (!canContinue) {
        this.pause();
      }
    });
    
    destination.on('drain', () => {
      this.resume();
    });
    
    this.on('end', () => {
      destination.end();
    });
    
    this.resume();
    return destination;
  }
}

/**
 * Memory-based writable stream
 */
class MemoryWriteStream extends EventEmitter {
  /**
   * Creates a new memory write stream
   * @param {MemoryProvider} provider - Memory provider
   * @param {string} id - ID for the data
   * @param {StreamOptions} [options] - Stream options
   */
  constructor(provider, id, options = {}) {
    super();
    
    this.provider = provider;
    this.id = id;
    this.options = {
      highWaterMark: 16384, // 16KB
      objectMode: true,
      ...options
    };
    
    this.chunks = [];
    this.ended = false;
  }

  /**
   * Writes data to the stream
   * @param {*} chunk - Data chunk to write
   * @returns {boolean} Whether the write was successful
   */
  write(chunk) {
    if (this.ended) {
      throw new PrimeStorageError(
        'Cannot write to ended stream',
        {},
        'STORAGE_STREAM_ENDED'
      );
    }
    
    this.chunks.push(chunk);
    return true;
  }

  /**
   * Ends the stream and finalizes the write
   * @param {*} [chunk] - Final chunk to write
   */
  end(chunk) {
    if (chunk) {
      this.write(chunk);
    }
    
    this.ended = true;
    
    // Combine chunks based on their type
    let finalData;
    
    if (this.chunks.length === 0) {
      finalData = null;
    } else if (this.chunks.length === 1) {
      finalData = this.chunks[0];
    } else {
      const firstChunk = this.chunks[0];
      
      if (typeof firstChunk === 'string') {
        finalData = this.chunks.join('');
      } else if (Array.isArray(firstChunk)) {
        finalData = this.chunks.flat();
      } else if (typeof Buffer !== 'undefined' && Buffer.isBuffer(firstChunk)) {
        finalData = Buffer.concat(this.chunks);
      } else if (ArrayBuffer.isView(firstChunk)) {
        // Combine TypedArrays
        const totalLength = this.chunks.reduce((sum, chunk) => sum + chunk.length, 0);
        const result = new firstChunk.constructor(totalLength);
        
        let offset = 0;
        for (const chunk of this.chunks) {
          result.set(chunk, offset);
          offset += chunk.length;
        }
        
        finalData = result;
      } else {
        // For other types, just use the last chunk
        finalData = this.chunks;
      }
    }
    
    // Store the final data
    this.provider.store(finalData, this.id)
      .then(() => {
        this.emit('finish', this.id);
      })
      .catch((error) => {
        this.emit('error', new PrimeStorageError(
          `Failed to store stream data: ${error.message}`,
          { id: this.id, originalError: error },
          'STORAGE_STREAM_STORE_FAILED',
          error
        ));
      });
  }
}

module.exports = MemoryProvider;