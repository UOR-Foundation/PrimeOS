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
const MatrixAdapter = require('./adapters/matrix-adapter');

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
    
    // Handle different possible matrix formats
    if (!matrix) {
      throw new PrimeStorageError(
        'Matrix not found in storage',
        { id },
        'STORAGE_INVALID_MATRIX'
      );
    }
    
    // Case 1: It's a regular array/matrix
    if (MatrixAdapter._isMatrix(matrix)) {
      // Convert to format compatible with SwappableMatrix
      const adaptedMatrix = MatrixAdapter.fromMatrix(matrix);
      return new SwappableMatrix(storageManager, id, adaptedMatrix, options);
    }
    
    // Case 2: It's already in the format expected by SwappableMatrix
    if (typeof matrix.rows === 'number' && typeof matrix.columns === 'number') {
      return new SwappableMatrix(storageManager, id, matrix, options);
    }
    
    // Case 3: It has a data property that is a matrix
    if (matrix.data && MatrixAdapter._isMatrix(matrix.data)) {
      return new SwappableMatrix(storageManager, id, matrix, options);
    }
    
    // None of the above - error
    throw new PrimeStorageError(
      'Invalid matrix data format',
      { id, matrixType: typeof matrix },
      'STORAGE_INVALID_MATRIX'
    );
  },
  
  /**
   * Creates a swappable matrix directly from a Prime.Math.Matrix
   * @param {StorageManager} storageManager - Storage manager to use
   * @param {Array|TypedArray} matrix - Prime.Math.Matrix to convert
   * @param {string} id - ID to use for storage
   * @param {SwappableMatrixOptions} [options] - Matrix options
   * @returns {Promise<SwappableMatrix>} Swappable matrix
   */
  async createSwappableMatrixFromMatrix(storageManager, matrix, id, options = {}) {
    // Validate the matrix using the adapter's direct method to avoid circular dependency
    if (!MatrixAdapter._isMatrix(matrix)) {
      throw new PrimeStorageError(
        'Invalid matrix object',
        { matrix },
        'STORAGE_INVALID_MATRIX'
      );
    }
    
    // Convert to format compatible with SwappableMatrix
    const adaptedMatrix = MatrixAdapter.fromMatrix(matrix);
    
    // Store the matrix
    const storedId = await storageManager.store(adaptedMatrix, id);
    
    // Create and return the swappable matrix
    return new SwappableMatrix(storageManager, storedId, adaptedMatrix, options);
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
    const provider = new DataProvider(storageManager, options);
    
    // Initialize the provider immediately
    provider.init().catch(err => {
      Prime.Logger.error('Failed to initialize data provider', { error: err.message });
    });
    
    return provider;
  },
  
  /**
   * Stores a neural model
   * @param {StorageManager} storageManager - Storage manager to use
   * @param {NeuralModel} model - Neural model to store
   * @param {string} id - ID to use for storage
   * @returns {Promise<string>} Stored ID
   */
  async storeModel(storageManager, model, id) {
    if (!model || typeof model.toJSON !== 'function') {
      throw new PrimeStorageError(
        'Invalid neural model',
        { model },
        'STORAGE_INVALID_MODEL'
      );
    }
    
    const modelData = model.toJSON();
    return await storageManager.store(modelData, id);
  },
  
  /**
   * Loads a neural model
   * @param {StorageManager} storageManager - Storage manager to use
   * @param {string} id - ID of the stored model
   * @returns {Promise<NeuralModel>} Loaded neural model
   */
  async loadModel(storageManager, id) {
    const modelData = await storageManager.load(id);
    
    if (!modelData || !modelData.layers) {
      throw new PrimeStorageError(
        'Invalid model data',
        { id },
        'STORAGE_INVALID_MODEL'
      );
    }
    
    return Prime.Neural.Model.NeuralModel.fromJSON(modelData);
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

// Expose adapters
Storage.MatrixAdapter = MatrixAdapter;
Storage.SwappableMatrix = SwappableMatrix;
Storage.VirtualArray = VirtualArray;
Storage.DataProvider = DataProvider;

// Add storage to Prime object
Prime.Storage = Storage;

// Export the Storage object
module.exports = Storage;