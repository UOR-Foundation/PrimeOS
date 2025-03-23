/**
 * PrimeOS JavaScript Library - IndexedDB Storage Provider
 * Browser-based storage provider using IndexedDB
 */

const Prime = require('../../core');
const { StorageProvider, PrimeStorageError } = require('../core/provider');
const { EventEmitter } = require('events');

/**
 * IndexedDB-based storage provider for browsers
 */
class IndexedDBProvider extends StorageProvider {
  /**
   * Creates a new IndexedDB provider
   * @param {StorageOptions} options - Storage options
   */
  constructor(options = {}) {
    super(options);
    
    this.options = {
      databaseName: 'primeos-storage',
      storeName: 'data',
      ...this.options
    };
    
    this.db = null;
    this.isInitialized = false;
  }

  /**
   * Initializes the IndexedDB provider
   * @returns {Promise<void>}
   */
  async init() {
    // Check environment
    if (typeof window === 'undefined' || typeof indexedDB === 'undefined') {
      throw new PrimeStorageError(
        'IndexedDB is not available in this environment',
        {},
        'STORAGE_INDEXEDDB_UNAVAILABLE'
      );
    }
    
    try {
      this.db = await this.openDatabase();
      this.isInitialized = true;
    } catch (error) {
      throw new PrimeStorageError(
        `Failed to initialize IndexedDB: ${error.message}`,
        { originalError: error },
        'STORAGE_INDEXEDDB_INIT_FAILED',
        error
      );
    }
  }

  /**
   * Opens the IndexedDB database
   * @private
   * @returns {Promise<IDBDatabase>} The database instance
   */
  openDatabase() {
    return new Promise((resolve, reject) => {
      const request = indexedDB.open(this.options.databaseName, 1);
      
      request.onerror = (event) => {
        reject(new Error(`IndexedDB open error: ${event.target.error.message}`));
      };
      
      request.onsuccess = (event) => {
        resolve(event.target.result);
      };
      
      request.onupgradeneeded = (event) => {
        const db = event.target.result;
        
        // Create object store if it doesn't exist
        if (!db.objectStoreNames.contains(this.options.storeName)) {
          db.createObjectStore(this.options.storeName);
        }
      };
    });
  }

  /**
   * Performs a database transaction
   * @private
   * @param {string} mode - Transaction mode ('readonly' or 'readwrite')
   * @param {Function} callback - Callback that receives the object store
   * @returns {Promise<*>} Result of the transaction
   */
  transaction(mode, callback) {
    return new Promise((resolve, reject) => {
      const tx = this.db.transaction(this.options.storeName, mode);
      const store = tx.objectStore(this.options.storeName);
      
      tx.oncomplete = () => resolve();
      tx.onerror = (event) => reject(new Error(`Transaction error: ${event.target.error.message}`));
      
      callback(store, resolve, reject);
    });
  }

  /**
   * Stores data with the given ID
   * @param {*} data - Data to store
   * @param {string} [id] - Optional ID (if not provided, a UUID will be generated)
   * @returns {Promise<string>} The ID of the stored data
   */
  async store(data, id) {
    const dataId = id || Prime.Utils.uuid();
    
    await this.transaction('readwrite', (store, resolve, reject) => {
      const request = store.put(data, dataId);
      
      request.onsuccess = () => resolve(dataId);
      request.onerror = (event) => reject(new Error(`Store error: ${event.target.error.message}`));
    });
    
    return dataId;
  }

  /**
   * Loads data with the given ID
   * @param {string} id - ID of the data to load
   * @returns {Promise<*>} The loaded data
   */
  async load(id) {
    return new Promise((resolve, reject) => {
      this.transaction('readonly', (store, txResolve, txReject) => {
        const request = store.get(id);
        
        request.onsuccess = (event) => {
          const data = event.target.result;
          
          if (data === undefined) {
            reject(new PrimeStorageError(
              `Data not found for ID: ${id}`,
              { id },
              'STORAGE_NOT_FOUND'
            ));
          } else {
            resolve(data);
          }
        };
        
        request.onerror = (event) => {
          reject(new Error(`Load error: ${event.target.error.message}`));
        };
      });
    });
  }

  /**
   * Deletes data with the given ID
   * @param {string} id - ID of the data to delete
   * @returns {Promise<boolean>} True if successful
   */
  async delete(id) {
    return new Promise((resolve, reject) => {
      this.transaction('readwrite', (store, txResolve, txReject) => {
        const request = store.delete(id);
        
        request.onsuccess = () => resolve(true);
        request.onerror = (event) => reject(new Error(`Delete error: ${event.target.error.message}`));
      });
    });
  }

  /**
   * Checks if data with the given ID exists
   * @param {string} id - ID to check
   * @returns {Promise<boolean>} True if data exists
   */
  async exists(id) {
    return new Promise((resolve, reject) => {
      this.transaction('readonly', (store, txResolve, txReject) => {
        const request = store.count(id);
        
        request.onsuccess = (event) => {
          resolve(event.target.result > 0);
        };
        
        request.onerror = (event) => {
          reject(new Error(`Exists error: ${event.target.error.message}`));
        };
      });
    });
  }

  /**
   * Lists all stored data IDs
   * @returns {Promise<string[]>} Array of stored data IDs
   */
  async getAllKeys() {
    return new Promise((resolve, reject) => {
      this.transaction('readonly', (store, txResolve, txReject) => {
        const request = store.getAllKeys();
        
        request.onsuccess = (event) => {
          resolve(event.target.result);
        };
        
        request.onerror = (event) => {
          reject(new Error(`GetAllKeys error: ${event.target.error.message}`));
        };
      });
    });
  }

  /**
   * Clears all stored data
   * @returns {Promise<void>}
   */
  async clear() {
    return this.transaction('readwrite', (store, resolve, reject) => {
      const request = store.clear();
      
      request.onsuccess = () => resolve();
      request.onerror = (event) => reject(new Error(`Clear error: ${event.target.error.message}`));
    });
  }

  /**
   * Gets information about the storage
   * @returns {Promise<StorageInfo>} Storage information
   */
  async getStorageInfo() {
    // Attempt to estimate storage usage
    // Note: This is an approximation as browsers don't provide direct access to quota information
    
    try {
      // Use the Storage API if available
      if (navigator.storage && navigator.storage.estimate) {
        const estimate = await navigator.storage.estimate();
        
        return {
          available: estimate.quota - estimate.usage,
          used: estimate.usage,
          total: estimate.quota,
          provider: 'indexeddb'
        };
      }
      
      // Fallback method - count keys and estimate size
      const keys = await this.getAllKeys();
      const used = keys.length * 10240; // Rough estimate of 10KB per item
      
      return {
        available: 50 * 1024 * 1024, // Assume 50MB
        used: used,
        total: 50 * 1024 * 1024,
        provider: 'indexeddb'
      };
    } catch (error) {
      // If estimation fails, return default values
      return {
        available: 50 * 1024 * 1024, // Assume 50MB
        used: 0,
        total: 50 * 1024 * 1024,
        provider: 'indexeddb'
      };
    }
  }

  /**
   * Creates a read stream for the data with the given ID
   * @param {string} id - ID of the data to stream
   * @param {StreamOptions} [options] - Stream options
   * @returns {ReadableStream} A readable stream of the data
   */
  createReadStream(id, options = {}) {
    return new IndexedDBReadStream(this, id, options);
  }

  /**
   * Creates a write stream for storing data
   * @param {string} [id] - Optional ID (if not provided, a UUID will be generated)
   * @param {StreamOptions} [options] - Stream options
   * @returns {WritableStream} A writable stream to store data
   */
  createWriteStream(id, options = {}) {
    return new IndexedDBWriteStream(this, id || Prime.Utils.uuid(), options);
  }

  /**
   * Gets the provider type
   * @returns {string} The provider type
   */
  getProviderType() {
    return 'indexeddb';
  }
}

/**
 * IndexedDB-based readable stream
 */
class IndexedDBReadStream extends EventEmitter {
  /**
   * Creates a new IndexedDB read stream
   * @param {IndexedDBProvider} provider - IndexedDB provider
   * @param {string} id - ID of the data to stream
   * @param {StreamOptions} [options] - Stream options
   */
  constructor(provider, id, options = {}) {
    super();
    
    this.provider = provider;
    this.id = id;
    this.options = {
      highWaterMark: 16384, // 16KB
      objectMode: true,
      chunkSize: 1024,
      ...options
    };
    
    this.position = 0;
    this.flowing = false;
    this.data = null;
    
    // Load data asynchronously
    this._loadData();
  }

  /**
   * Loads data from IndexedDB
   * @private
   */
  async _loadData() {
    try {
      this.data = await this.provider.load(this.id);
      this.emit('readable');
    } catch (error) {
      this.emit('error', new PrimeStorageError(
        `Failed to load data for streaming: ${error.message}`,
        { id: this.id, originalError: error },
        'STORAGE_STREAM_LOAD_FAILED',
        error
      ));
    }
  }

  /**
   * Starts the flow of data
   * @private
   */
  _read() {
    if (!this.data) {
      // Wait for data to be loaded
      this.once('readable', () => this._read());
      return;
    }
    
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
   * @returns {IndexedDBReadStream} This stream
   */
  pause() {
    this.flowing = false;
    return this;
  }

  /**
   * Resumes the stream
   * @returns {IndexedDBReadStream} This stream
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
 * IndexedDB-based writable stream
 */
class IndexedDBWriteStream extends EventEmitter {
  /**
   * Creates a new IndexedDB write stream
   * @param {IndexedDBProvider} provider - IndexedDB provider
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
        // For other types, just use the chunks array
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

module.exports = IndexedDBProvider;