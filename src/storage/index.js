/**
 * PrimeOS JavaScript Library - Storage Module
 * Provides persistent storage capabilities for PrimeOS
 */

const Prime = require('../core');
const StorageManager = require('./core/manager');
const { PrimeStorageError } = require('./core/provider');
const SwappableMatrix = require('./adapters/swappable-matrix');
const VirtualArray = require('./adapters/virtual-array');
const DataProvider = require('./adapters/data-provider');

/**
 * Storage module API
 */
const Storage = {
  /**
   * Version of the storage module
   */
  VERSION: '1.0.0',
  
  /**
   * Creates a new storage manager
   * @param {StorageOptions} [options] - Storage options
   * @returns {StorageManager} A new storage manager instance
   */
  createManager(options = {}) {
    return new StorageManager(options);
  },
  
  /**
   * Gets the current environment
   * @returns {string} 'browser', 'node', or 'unknown'
   */
  getEnvironment() {
    if (typeof window !== 'undefined' && typeof document !== 'undefined') {
      return 'browser';
    }
    
    if (typeof process !== 'undefined' && process.versions && process.versions.node) {
      return 'node';
    }
    
    return 'unknown';
  },
  
  /**
   * Creates a swappable matrix backed by storage
   * @param {StorageManager} storageManager - Storage manager to use
   * @param {string} id - ID of the stored matrix
   * @param {SwappableMatrixOptions} [options] - Matrix options
   * @returns {Promise<SwappableMatrix>} Swappable matrix
   */
  async createSwappableMatrix(storageManager, id, options = {}) {
    const matrix = await storageManager.load(id);
    
    if (!matrix || typeof matrix.rows !== 'number' || typeof matrix.columns !== 'number') {
      throw new PrimeStorageError(
        'Invalid matrix data',
        { id },
        'STORAGE_INVALID_MATRIX'
      );
    }
    
    return new SwappableMatrix(storageManager, id, matrix, options);
  },
  
  /**
   * Creates a virtual array backed by storage
   * @param {StorageManager} storageManager - Storage manager to use
   * @param {VirtualArrayOptions} options - Virtual array options
   * @returns {VirtualArray} Virtual array
   */
  createVirtualArray(storageManager, options) {
    return new VirtualArray(storageManager, options);
  },
  
  /**
   * Creates a data provider for training neural models
   * @param {StorageManager} storageManager - Storage manager to use
   * @param {DataProviderOptions} options - Data provider options
   * @returns {DataProvider} Data provider
   */
  createDataProvider(storageManager, options) {
    return new DataProvider(storageManager, options);
  },
  
  /**
   * Clears all storage for testing purposes
   * @returns {Promise<void>}
   */
  async clearAllForTesting() {
    const manager = new StorageManager();
    await manager.init();
    await manager.clear();
  }
};

// Expose error class
Storage.StorageError = PrimeStorageError;

// Expose the StorageManager class
Storage.StorageManager = StorageManager;

// Add storage to Prime object
Prime.Storage = Storage;

// Export the Storage object
module.exports = Storage;