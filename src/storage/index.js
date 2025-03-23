/**
 * PrimeOS Storage System
 * Provides storage capabilities for PrimeOS
 */

const Prime = require("../core");
const { PrimeError } = require("../core/error");
const SwappableMatrix = require("./adapters/swappable-matrix");
const SwappableTensor = require("./adapters/swappable-tensor");
const DataProvider = require("./adapters/data-provider");
const fs = require("fs");
const path = require("path");
const util = require("util");
const os = require("os");

/**
 * Storage error class
 */
class StorageError extends PrimeError {
  constructor(message, details = {}, code = "STORAGE_ERROR") {
    super(message, details, code);
    this.name = "StorageError";
  }
}

/**
 * Memory storage provider
 * Stores data in memory (non-persistent)
 */
class MemoryStorageProvider {
  constructor() {
    this.storage = new Map();
    this.initialized = false;
  }

  async init() {
    this.initialized = true;
    return true;
  }

  async store(data, key) {
    if (!this.initialized) {
      throw new StorageError("Storage provider not initialized");
    }

    this.storage.set(key, {
      data,
      timestamp: Date.now(),
    });

    return key;
  }

  async load(key) {
    if (!this.initialized) {
      throw new StorageError("Storage provider not initialized");
    }

    const entry = this.storage.get(key);
    if (!entry) {
      throw new StorageError("Key not found", { key });
    }

    return entry.data;
  }

  async delete(key) {
    if (!this.initialized) {
      throw new StorageError("Storage provider not initialized");
    }

    const exists = this.storage.has(key);
    this.storage.delete(key);

    return exists;
  }

  async getAllKeys() {
    if (!this.initialized) {
      throw new StorageError("Storage provider not initialized");
    }

    return Array.from(this.storage.keys());
  }

  async clear() {
    if (!this.initialized) {
      throw new StorageError("Storage provider not initialized");
    }

    this.storage.clear();
    return true;
  }

  async getStorageInfo() {
    if (!this.initialized) {
      throw new StorageError("Storage provider not initialized");
    }

    return {
      provider: "memory",
      used: this.storage.size,
      total: Infinity,
      available: Infinity,
    };
  }
}

/**
 * Storage manager
 * Creates and manages storage providers
 */
class StorageManager {
  constructor(options = {}) {
    this.options = {
      provider: "memory",
      ...options,
    };

    this.provider = null;
    this.initialized = false;

    // Create swap space manager
    this.swapSpace = null;
  }

  async init() {
    if (this.initialized) {
      return;
    }

    // Create the provider based on options
    switch (this.options.provider) {
      case "memory":
        this.provider = new MemoryStorageProvider();
        break;
      case "filesystem":
        this.provider = new FilesystemStorageProvider(this.options);
        break;
      case "auto":
        // Use filesystem if in Node.js, memory otherwise
        if (getEnvironment() === "node") {
          this.provider = new FilesystemStorageProvider(this.options);
        } else {
          this.provider = new MemoryStorageProvider();
        }
        break;
      default:
        throw new StorageError(
          `Unknown storage provider: ${this.options.provider}`,
        );
    }

    // Initialize the provider
    await this.provider.init();

    // Initialize swap space manager
    this.swapSpace = new SwapSpaceManager(this);

    this.initialized = true;
  }

  /**
   * Gets the provider type
   * @returns {string} Provider type
   */
  getProviderType() {
    if (!this.initialized) {
      throw new StorageError("Storage manager not initialized");
    }

    return this.provider.options && this.provider.options.provider
      ? this.provider.options.provider
      : this.options.provider;
  }

  async store(data, key) {
    if (!this.initialized) {
      throw new StorageError("Storage manager not initialized");
    }

    return this.provider.store(data, key);
  }

  async load(key) {
    if (!this.initialized) {
      throw new StorageError("Storage manager not initialized");
    }

    try {
      return await this.provider.load(key);
    } catch (error) {
      if (error instanceof StorageError && error.message === "Key not found") {
        // Return undefined instead of throwing when key is not found
        // This matches the behavior expected by tests
        return undefined;
      }
      // Re-throw other errors
      throw error;
    }
  }

  async delete(key) {
    if (!this.initialized) {
      throw new StorageError("Storage manager not initialized");
    }

    // First delete the main data
    const result = await this.provider.delete(key);

    // Clean up any associated swap files
    if (this.swapSpace) {
      try {
        // Look for any swap files related to this key
        const allKeys = await this.getAllKeys();
        const swapKeys = allKeys.filter(
          (k) =>
            k.startsWith(`swap_${key}_`) ||
            k.startsWith(`swap_chunk_${key}_`) ||
            k.startsWith(`swap_meta_${key}`),
        );

        // Delete all related swap files
        for (const swapKey of swapKeys) {
          await this.provider.delete(swapKey);
        }
      } catch (error) {
        // Log the error but don't fail the operation
        console.warn(
          `Failed to clean up swap files for ${key}: ${error.message}`,
        );
      }
    }

    return result;
  }

  async getAllKeys() {
    if (!this.initialized) {
      throw new StorageError("Storage manager not initialized");
    }

    return this.provider.getAllKeys();
  }

  async clear() {
    if (!this.initialized) {
      throw new StorageError("Storage manager not initialized");
    }

    return this.provider.clear();
  }

  async getStorageInfo() {
    if (!this.initialized) {
      throw new StorageError("Storage manager not initialized");
    }

    return this.provider.getStorageInfo();
  }

  /**
   * Stores a neural model's weights
   * @param {Object} model - Neural model to store
   * @param {string} [key] - Optional key to use
   * @returns {Promise<string>} - Key used to store the model
   */
  async storeModel(model, key) {
    if (!this.initialized) {
      throw new StorageError("Storage manager not initialized");
    }

    if (!model || typeof model !== "object") {
      throw new StorageError("Invalid model", { model });
    }

    // If no key is provided, generate one
    const modelKey =
      key || `model_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;

    // Extract model weights
    const weights = [];
    const numLayers = model.getNumLayers
      ? model.getNumLayers()
      : model.layers.length;

    for (let i = 0; i < numLayers; i++) {
      const layer = model.getLayer ? model.getLayer(i) : model.layers[i];

      if (layer && layer.weights) {
        weights.push({
          layerIndex: i,
          weights: layer.weights,
          biases: layer.biases,
        });
      }
    }

    // Store model metadata
    const metadata = {
      name: model.name || "unnamed_model",
      type: model.type || "unknown",
      layers: numLayers,
      timestamp: Date.now(),
    };

    // Store model data
    await this.store(
      {
        metadata,
        weights,
      },
      modelKey,
    );

    return modelKey;
  }

  /**
   * Loads model weights into a model
   * @param {Object} model - Neural model to load weights into
   * @param {string} key - Key of the stored model
   * @returns {Promise<boolean>} - Whether the operation was successful
   */
  async loadModelWeights(model, key) {
    if (!this.initialized) {
      throw new StorageError("Storage manager not initialized");
    }

    if (!model || typeof model !== "object") {
      throw new StorageError("Invalid model", { model });
    }

    // Load model data
    const modelData = await this.load(key);

    if (!modelData || !modelData.weights || !Array.isArray(modelData.weights)) {
      throw new StorageError("Invalid model data", { key });
    }

    // Apply weights to model
    for (const layerData of modelData.weights) {
      const layer = model.getLayer
        ? model.getLayer(layerData.layerIndex)
        : model.layers[layerData.layerIndex];

      if (layer) {
        // Copy weights
        if (layerData.weights) {
          if (typeof layer.setWeights === "function") {
            layer.setWeights(layerData.weights);
          } else {
            layer.weights = layerData.weights;
          }
        }

        // Copy biases if available
        if (layerData.biases) {
          if (typeof layer.setBiases === "function") {
            layer.setBiases(layerData.biases);
          } else {
            layer.biases = layerData.biases;
          }
        }
      }
    }

    return true;
  }

  /**
   * Stores component state
   * @param {Object} component - Component to store
   * @param {string} [key] - Optional key to use
   * @returns {Promise<string>} - Key used to store the component
   */
  async storeComponentState(component, key) {
    if (!this.initialized) {
      throw new StorageError("Storage manager not initialized");
    }

    if (!component || typeof component !== "object") {
      throw new StorageError("Invalid component", { component });
    }

    // If no key is provided, generate one
    const componentKey =
      key || `component_${component.name || "unnamed"}_${Date.now()}`;

    // Store component state
    await this.store(
      {
        name: component.name || "unnamed_component",
        state: component.state || {},
        timestamp: Date.now(),
      },
      componentKey,
    );

    return componentKey;
  }

  /**
   * Loads component state
   * @param {Object} component - Component to load state into
   * @param {string} key - Key of the stored component
   * @returns {Promise<boolean>} - Whether the operation was successful
   */
  async loadComponentState(component, key) {
    if (!this.initialized) {
      throw new StorageError("Storage manager not initialized");
    }

    if (!component || typeof component !== "object") {
      throw new StorageError("Invalid component", { component });
    }

    // Load component data
    const componentData = await this.load(key);

    if (!componentData || !componentData.state) {
      throw new StorageError("Invalid component data", { key });
    }

    // Copy state properties
    if (component.state) {
      Object.assign(component.state, componentData.state);
    } else {
      component.state = componentData.state;
    }

    return true;
  }
}

/**
 * Create a new storage manager
 * @param {Object} options - Storage manager options
 * @returns {StorageManager} - Storage manager instance
 */
function createManager(options = {}) {
  return new StorageManager(options);
}

/**
 * Creates a swappable matrix that keeps part of the data in memory
 * and swaps to storage as needed
 * @param {StorageManager} storageManager - Storage manager to use
 * @param {string} id - ID of the stored matrix
 * @param {Object} options - Matrix options
 * @returns {Promise<SwappableMatrix>} Swappable matrix instance
 */
async function createSwappableMatrix(storageManager, id, options = {}) {
  if (!storageManager || !(storageManager instanceof StorageManager)) {
    throw new StorageError("Invalid storage manager");
  }

  // Load the original matrix from storage
  const matrix = await storageManager.load(id);

  // Create a swappable matrix
  const swappableMatrix = new SwappableMatrix(
    storageManager,
    id,
    matrix,
    options,
  );

  // Store the original matrix for initialization
  swappableMatrix.originalMatrix = matrix;

  // Initialize blocks
  if (!swappableMatrix.fullMatrix) {
    await swappableMatrix._splitAndStoreBlocks(matrix);
    swappableMatrix.initialized = true;
  }

  return swappableMatrix;
}

/**
 * Creates a data provider for training neural models
 * @param {StorageManager} storageManager - Storage manager to use
 * @param {Object} options - Data provider options
 * @returns {DataProvider} Data provider instance
 */
function createDataProvider(storageManager, options) {
  if (!storageManager || !(storageManager instanceof StorageManager)) {
    throw new StorageError("Invalid storage manager");
  }

  return new DataProvider(storageManager, options);
}

/**
 * Swap space manager
 * Manages temporary swap files for large data
 */
class SwapSpaceManager {
  constructor(storageManager) {
    this.storageManager = storageManager;
    this.allocations = new Map();
  }

  /**
   * Allocates a new swap space
   * @param {number} size - Size of the swap space in bytes
   * @param {Object} [options] - Allocation options
   * @returns {Promise<string>} Swap space ID
   */
  async allocate(size, options = {}) {
    const id = `swap_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;

    // Create placeholder data
    const data = {
      id,
      size,
      created: Date.now(),
      options,
      chunks: Math.ceil(size / (options.chunkSize || 1024 * 1024)),
    };

    // Store metadata
    await this.storageManager.store(data, `swap_meta_${id}`);

    // Track allocation
    this.allocations.set(id, data);

    return id;
  }

  /**
   * Frees a swap space
   * @param {string} id - Swap space ID
   * @returns {Promise<boolean>} Whether the operation was successful
   */
  async free(id) {
    // Delete metadata
    await this.storageManager.delete(`swap_meta_${id}`);

    // Delete all chunks
    const allKeys = await this.storageManager.getAllKeys();
    const chunkKeys = allKeys.filter((key) =>
      key.startsWith(`swap_chunk_${id}_`),
    );

    await Promise.all(chunkKeys.map((key) => this.storageManager.delete(key)));

    // Remove from tracking
    this.allocations.delete(id);

    return true;
  }

  /**
   * Writes data to a swap space
   * @param {string} id - Swap space ID
   * @param {number} offset - Offset in bytes
   * @param {Array|Uint8Array} data - Data to write
   * @returns {Promise<boolean>} Whether the operation was successful
   */
  async write(id, offset, data) {
    const metadata = this.allocations.get(id);

    if (!metadata) {
      throw new StorageError("Invalid swap space ID", { id });
    }

    const chunkSize = metadata.options.chunkSize || 1024 * 1024;
    const startChunk = Math.floor(offset / chunkSize);
    const endChunk = Math.floor((offset + data.length - 1) / chunkSize);

    // Write data chunks
    for (let i = startChunk; i <= endChunk; i++) {
      const chunkOffset = offset - i * chunkSize;
      const chunkData = data.slice(
        Math.max(0, chunkOffset),
        Math.min(data.length, chunkOffset + chunkSize),
      );

      await this.storageManager.store(chunkData, `swap_chunk_${id}_${i}`);
    }

    return true;
  }

  /**
   * Reads data from a swap space
   * @param {string} id - Swap space ID
   * @param {number} offset - Offset in bytes
   * @param {number} length - Length in bytes
   * @returns {Promise<Array|Uint8Array>} Data read
   */
  async read(id, offset, length) {
    const metadata = this.allocations.get(id);

    if (!metadata) {
      throw new StorageError("Invalid swap space ID", { id });
    }

    const chunkSize = metadata.options.chunkSize || 1024 * 1024;
    const startChunk = Math.floor(offset / chunkSize);
    const endChunk = Math.floor((offset + length - 1) / chunkSize);

    // Read and combine data chunks
    const result = [];

    for (let i = startChunk; i <= endChunk; i++) {
      try {
        const chunkData = await this.storageManager.load(
          `swap_chunk_${id}_${i}`,
        );
        const chunkOffset = i * chunkSize;
        const startIndex = Math.max(0, offset - chunkOffset);
        const endIndex = Math.min(
          chunkData.length,
          offset + length - chunkOffset,
        );

        result.push(...chunkData.slice(startIndex, endIndex));
      } catch (error) {
        // If chunk not found, fill with zeros
        const zeros = new Array(
          Math.min(chunkSize, offset + length - i * chunkSize),
        ).fill(0);
        result.push(...zeros);
      }
    }

    return result.slice(0, length);
  }

  /**
   * Forces any cached data to be written to disk
   * @returns {Promise<boolean>} Whether the operation was successful
   */
  async flushToDisk() {
    // In our implementation, data is written immediately
    // This method exists for API compatibility with tests
    return true;
  }
}

/**
 * Filesystem storage provider
 * Stores data in the filesystem (persistent)
 */
class FilesystemStorageProvider {
  constructor(options = {}) {
    this.options = {
      storagePath: path.join(os.tmpdir(), "primeos-storage"),
      ...options,
    };

    // Copy storagePath from options if it exists
    if (options.storagePath) {
      this.options.storagePath = options.storagePath;
    }

    this.initialized = false;
  }

  async init() {
    // Create storage directory if it doesn't exist
    try {
      await util.promisify(fs.mkdir)(this.options.storagePath, {
        recursive: true,
      });
      this.initialized = true;
      return true;
    } catch (error) {
      throw new StorageError(
        `Failed to initialize filesystem storage: ${error.message}`,
        { path: this.options.storagePath },
        "STORAGE_INIT_FAILED",
        error,
      );
    }
  }

  async store(data, key) {
    if (!this.initialized) {
      throw new StorageError("Storage provider not initialized");
    }

    // Generate file path
    const filePath = this._getFilePath(key);

    try {
      // Prepare data for storage
      let storeData;
      let dataType = typeof data;

      // Special handling for Buffer
      if (Buffer.isBuffer(data)) {
        storeData = {
          type: "Buffer",
          data: Array.from(data),
        };
        dataType = "Buffer";
      } else {
        storeData = data;
      }

      // Store data as JSON
      const serialized = JSON.stringify({
        data: storeData,
        timestamp: Date.now(),
        type: dataType,
      });

      // Create directory if it doesn't exist
      if (!fs.existsSync(this.options.storagePath)) {
        fs.mkdirSync(this.options.storagePath, { recursive: true });
      }

      // Write file
      await util.promisify(fs.writeFile)(filePath, serialized, "utf8");

      return key;
    } catch (error) {
      throw new StorageError(
        `Failed to store data: ${error.message}`,
        { key, path: filePath },
        "STORAGE_STORE_FAILED",
        error,
      );
    }
  }

  async load(key) {
    if (!this.initialized) {
      throw new StorageError("Storage provider not initialized");
    }

    // Generate file path
    const filePath = this._getFilePath(key);

    try {
      // Check if file exists
      if (!fs.existsSync(filePath)) {
        throw new StorageError("Key not found", { key, path: filePath });
      }

      // Load data from file
      const serialized = await util.promisify(fs.readFile)(filePath, "utf8");
      const entry = JSON.parse(serialized);

      // Handle special data types
      if (
        entry.type === "Buffer" &&
        entry.data &&
        entry.data.type === "Buffer" &&
        Array.isArray(entry.data.data)
      ) {
        // Reconstruct Buffer from array
        return Buffer.from(entry.data.data);
      }

      return entry.data;
    } catch (error) {
      if (error instanceof StorageError) {
        throw error;
      }

      throw new StorageError(
        `Failed to load data: ${error.message}`,
        { key, path: filePath },
        "STORAGE_LOAD_FAILED",
        error,
      );
    }
  }

  async delete(key) {
    if (!this.initialized) {
      throw new StorageError("Storage provider not initialized");
    }

    // Generate file path
    const filePath = this._getFilePath(key);

    try {
      // Check if file exists
      if (!fs.existsSync(filePath)) {
        return false;
      }

      // Delete file
      await util.promisify(fs.unlink)(filePath);
      return true;
    } catch (error) {
      throw new StorageError(
        `Failed to delete data: ${error.message}`,
        { key, path: filePath },
        "STORAGE_DELETE_FAILED",
        error,
      );
    }
  }

  async getAllKeys() {
    if (!this.initialized) {
      throw new StorageError("Storage provider not initialized");
    }

    try {
      // Get all files in storage directory
      const files = await util.promisify(fs.readdir)(this.options.storagePath);

      // Convert file names to keys
      const keys = files.map((file) => path.parse(file).name);

      return keys;
    } catch (error) {
      throw new StorageError(
        `Failed to get all keys: ${error.message}`,
        { path: this.options.storagePath },
        "STORAGE_GET_KEYS_FAILED",
        error,
      );
    }
  }

  async clear() {
    if (!this.initialized) {
      throw new StorageError("Storage provider not initialized");
    }

    try {
      // Get all files in storage directory
      const files = await util.promisify(fs.readdir)(this.options.storagePath);

      // Delete all files
      await Promise.all(
        files.map((file) => {
          const filePath = path.join(this.options.storagePath, file);
          return util.promisify(fs.unlink)(filePath);
        }),
      );

      return true;
    } catch (error) {
      throw new StorageError(
        `Failed to clear storage: ${error.message}`,
        { path: this.options.storagePath },
        "STORAGE_CLEAR_FAILED",
        error,
      );
    }
  }

  async getStorageInfo() {
    if (!this.initialized) {
      throw new StorageError("Storage provider not initialized");
    }

    try {
      // Get disk space info
      const stats = await util.promisify(fs.statfs || fs.statvfs)(
        this.options.storagePath,
      );

      // Calculate used storage
      const files = await util.promisify(fs.readdir)(this.options.storagePath);
      let used = 0;

      for (const file of files) {
        const filePath = path.join(this.options.storagePath, file);
        const fileStat = await util.promisify(fs.stat)(filePath);
        used += fileStat.size;
      }

      return {
        provider: "filesystem",
        used,
        total: stats.blocks * stats.bsize,
        available: stats.bfree * stats.bsize,
        path: this.options.storagePath,
      };
    } catch (error) {
      // Fallback if statvfs is not available
      return {
        provider: "filesystem",
        used: 0,
        total: 0,
        available: 0,
        path: this.options.storagePath,
      };
    }
  }

  _getFilePath(key) {
    // Handle if key is undefined
    if (key === undefined || key === null) {
      // Generate a random key if none provided
      key = `auto_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
    }

    // Ensure key is a string
    const keyStr = String(key);

    // Sanitize key to be a valid filename
    const sanitizedKey = keyStr.replace(/[^a-zA-Z0-9_-]/g, "_");

    // Use .data extension to match the test expectations
    return path.join(this.options.storagePath, `${sanitizedKey}.data`);
  }
}

/**
 * Detects the current environment
 * @returns {string} Environment ('browser', 'node', or 'unknown')
 */
function getEnvironment() {
  if (typeof window !== "undefined" && typeof document !== "undefined") {
    return "browser";
  } else if (
    typeof process !== "undefined" &&
    process.versions &&
    process.versions.node
  ) {
    return "node";
  }
  return "unknown";
}

/**
 * Clears all storage for testing purposes
 * This function resets all storage providers to a clean state
 * @warning This will delete all data in PrimeOS storage - use with caution
 */
function clearAllForTesting() {
  // This function is designed only for test scenarios to clean up test data

  try {
    // Clear memory storage if available
    const memoryProvider = new MemoryStorageProvider();
    memoryProvider.init().then(() => memoryProvider.clear());

    // Clear filesystem storage if available and in Node environment
    if (getEnvironment() === "node") {
      const filesystemProvider = new FilesystemStorageProvider({
        storagePath: path.join(os.tmpdir(), "primeos-storage-test"),
      });
      filesystemProvider.init().then(() => filesystemProvider.clear());
    }

    return true;
  } catch (error) {
    console.error("Failed to clear storage for testing:", error);
    return false;
  }
}

/**
 * Creates a matrix adapter for working with matrices in storage
 * @param {StorageManager} storageManager - Storage manager to use
 * @param {string} id - ID of the stored matrix
 * @param {Object} options - Matrix adapter options
 * @returns {Promise<MatrixAdapter>} Matrix adapter instance
 */
async function createMatrixAdapter(storageManager, id, options = {}) {
  if (!storageManager || !(storageManager instanceof StorageManager)) {
    throw new StorageError("Invalid storage manager");
  }

  // Import the MatrixAdapter class
  const MatrixAdapter = require("./adapters/matrix-adapter-class");

  // Create and initialize the adapter
  const adapter = new MatrixAdapter(storageManager, id, options);
  await adapter.init();

  return adapter;
}

/**
 * Creates a virtual array that provides array-like access to storage
 * @param {StorageManager} storageManager - Storage manager to use
 * @param {Object} options - Virtual array options
 * @returns {Promise<VirtualArray>} Virtual array instance
 */
async function createVirtualArray(storageManager, options = {}) {
  if (!storageManager || !(storageManager instanceof StorageManager)) {
    throw new StorageError("Invalid storage manager");
  }

  // Import the VirtualArray class
  const VirtualArray = require("./adapters/virtual-array");

  // Create and initialize the virtual array
  const virtualArray = new VirtualArray(storageManager, options);

  return virtualArray;
}

/**
 * Creates a swappable tensor that keeps part of the data in memory
 * and swaps to storage as needed
 * @param {StorageManager} storageManager - Storage manager to use
 * @param {string} id - ID of the stored tensor
 * @param {Object} options - Tensor options
 * @returns {Promise<SwappableTensor>} Swappable tensor instance
 */
async function createSwappableTensor(storageManager, id, options = {}) {
  if (!storageManager || !(storageManager instanceof StorageManager)) {
    throw new StorageError("Invalid storage manager");
  }

  try {
    // Load the original tensor from storage
    const tensor = await storageManager.load(id);

    // Create a swappable tensor
    const swappableTensor = new SwappableTensor(
      storageManager,
      id,
      tensor,
      options,
    );

    // Store the original tensor for initialization
    swappableTensor.originalTensor = tensor;

    // Initialize blocks if needed
    if (!swappableTensor.fullTensor) {
      await swappableTensor._splitAndStoreBlocks(tensor);
      swappableTensor.initialized = true;
    }

    return swappableTensor;
  } catch (error) {
    // Wrap any tensor-specific errors in a StorageError
    if (error.name === "TensorError") {
      throw new StorageError(
        `Tensor operation failed: ${error.message}`,
        error.details || {},
        error.code || "STORAGE_TENSOR_ERROR",
      );
    }
    // Re-throw other errors
    throw error;
  }
}

// Add to Prime namespace
Prime.Storage = {
  createManager,
  createSwappableMatrix,
  createSwappableTensor,
  createDataProvider,
  createMatrixAdapter,
  createVirtualArray,
  getEnvironment,
  clearAllForTesting,
  StorageManager,
  StorageError,
};

module.exports = Prime.Storage;
