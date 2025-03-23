/**
 * PrimeOS JavaScript Library - Storage Provider Interface
 * Abstract base class for storage providers
 */

const Prime = require("../../core");

/**
 * Abstract storage provider that defines the interface all providers must implement
 */
class StorageProvider {
  /**
   * Creates a new storage provider instance
   * @param {StorageOptions} options - Configuration options
   */
  constructor(options = {}) {
    this.options = {
      chunkSize: 1048576, // 1MB
      compression: false,
      ...options,
    };

    this.isInitialized = false;
  }

  /**
   * Initializes the storage provider
   * @returns {Promise<void>}
   */
  async init() {
    throw new Prime.UnsupportedOperationError(
      "Method not implemented: init()",
      { class: "StorageProvider" },
      "STORAGE_NOT_IMPLEMENTED",
    );
  }

  /**
   * Stores data with the given ID
   * @param {*} data - Data to store
   * @param {string} [id] - Optional ID (if not provided, a UUID will be generated)
   * @returns {Promise<string>} The ID of the stored data
   */
  async store(data, id) {
    throw new Prime.UnsupportedOperationError(
      "Method not implemented: store()",
      { class: "StorageProvider" },
      "STORAGE_NOT_IMPLEMENTED",
    );
  }

  /**
   * Loads data with the given ID
   * @param {string} id - ID of the data to load
   * @returns {Promise<*>} The loaded data
   */
  async load(id) {
    throw new Prime.UnsupportedOperationError(
      "Method not implemented: load()",
      { class: "StorageProvider" },
      "STORAGE_NOT_IMPLEMENTED",
    );
  }

  /**
   * Deletes data with the given ID
   * @param {string} id - ID of the data to delete
   * @returns {Promise<boolean>} True if successful
   */
  async delete(id) {
    throw new Prime.UnsupportedOperationError(
      "Method not implemented: delete()",
      { class: "StorageProvider" },
      "STORAGE_NOT_IMPLEMENTED",
    );
  }

  /**
   * Checks if data with the given ID exists
   * @param {string} id - ID to check
   * @returns {Promise<boolean>} True if data exists
   */
  async exists(id) {
    throw new Prime.UnsupportedOperationError(
      "Method not implemented: exists()",
      { class: "StorageProvider" },
      "STORAGE_NOT_IMPLEMENTED",
    );
  }

  /**
   * Lists all stored data IDs
   * @returns {Promise<string[]>} Array of stored data IDs
   */
  async getAllKeys() {
    throw new Prime.UnsupportedOperationError(
      "Method not implemented: getAllKeys()",
      { class: "StorageProvider" },
      "STORAGE_NOT_IMPLEMENTED",
    );
  }

  /**
   * Clears all stored data
   * @returns {Promise<void>}
   */
  async clear() {
    throw new Prime.UnsupportedOperationError(
      "Method not implemented: clear()",
      { class: "StorageProvider" },
      "STORAGE_NOT_IMPLEMENTED",
    );
  }

  /**
   * Gets information about the storage
   * @returns {Promise<StorageInfo>} Storage information
   */
  async getStorageInfo() {
    throw new Prime.UnsupportedOperationError(
      "Method not implemented: getStorageInfo()",
      { class: "StorageProvider" },
      "STORAGE_NOT_IMPLEMENTED",
    );
  }

  /**
   * Creates a read stream for the data with the given ID
   * @param {string} id - ID of the data to stream
   * @param {StreamOptions} [options] - Stream options
   * @returns {ReadableStream} A readable stream of the data
   */
  createReadStream(id, options = {}) {
    throw new Prime.UnsupportedOperationError(
      "Method not implemented: createReadStream()",
      { class: "StorageProvider" },
      "STORAGE_NOT_IMPLEMENTED",
    );
  }

  /**
   * Creates a write stream for storing data
   * @param {string} [id] - Optional ID (if not provided, a UUID will be generated)
   * @param {StreamOptions} [options] - Stream options
   * @returns {WritableStream} A writable stream to store data
   */
  createWriteStream(id, options = {}) {
    throw new Prime.UnsupportedOperationError(
      "Method not implemented: createWriteStream()",
      { class: "StorageProvider" },
      "STORAGE_NOT_IMPLEMENTED",
    );
  }

  /**
   * Gets the provider type
   * @returns {string} The provider type
   */
  getProviderType() {
    throw new Prime.UnsupportedOperationError(
      "Method not implemented: getProviderType()",
      { class: "StorageProvider" },
      "STORAGE_NOT_IMPLEMENTED",
    );
  }
}

// Custom error class for storage errors
class PrimeStorageError extends Prime.PrimeError {
  /**
   * Creates a new storage error
   * @param {string} message - Error message
   * @param {Object} [context] - Additional context
   * @param {string} [code='STORAGE_ERROR'] - Error code
   * @param {Error} [cause] - Cause of the error
   */
  constructor(message, context = {}, code = "STORAGE_ERROR", cause = null) {
    super(message, context, code, cause);
  }
}

// Export the provider class
module.exports = {
  StorageProvider,
  PrimeStorageError,
};
