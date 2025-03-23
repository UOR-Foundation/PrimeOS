/**
 * PrimeOS JavaScript Library - Storage Manager
 * Central manager for storage operations
 */

const Prime = require("../../core");
const { StorageProvider, PrimeStorageError } = require("./provider");
const Serializer = require("./serializer");
const ChunkManager = require("./chunk");
const { EventEmitter } = require("events");

/**
 * Storage manager that orchestrates storage operations
 */
class StorageManager extends EventEmitter {
  /**
   * Creates a new storage manager
   * @param {StorageOptions} options - Storage options
   */
  constructor(options = {}) {
    super();

    this.options = {
      provider: "auto",
      chunkSize: 1048576, // 1MB
      useSwapSpace: true,
      compression: false,
      ...options,
    };

    this.isInitialized = false;
    this.provider = null;
    this.serializer = new Serializer({
      preserveInstances: true,
      compression: this.options.compression,
    });

    this.chunkManager = new ChunkManager({
      defaultChunkSize: this.options.chunkSize,
    });

    this.swapSpace = null;
    if (this.options.useSwapSpace) {
      this.swapSpace = new SwapSpaceManager({
        maxMemoryUsage: this.options.maxMemoryUsage,
        storagePath: this.options.storagePath,
      });
    }

    // Cache for frequently accessed data
    this.cache = new Map();
    this.metadataCache = new Map();
  }

  /**
   * Initializes the storage manager
   * @returns {Promise<void>}
   */
  async init() {
    if (this.isInitialized) {
      return;
    }

    try {
      // Create provider based on environment and options
      this.provider = this.createProvider();

      // Initialize the provider
      await this.provider.init();

      // Initialize swap space if used
      if (this.swapSpace) {
        await this.swapSpace.init(this);
      }

      this.isInitialized = true;
      this.emit("initialized");
    } catch (error) {
      this.emit("error", error);
      throw new PrimeStorageError(
        `Failed to initialize storage manager: ${error.message}`,
        { originalError: error },
        "STORAGE_INIT_FAILED",
        error,
      );
    }
  }

  /**
   * Creates the appropriate storage provider based on environment
   * @private
   * @returns {StorageProvider} The storage provider instance
   */
  createProvider() {
    const requestedProvider = this.options.provider.toLowerCase();

    // If auto, detect the environment
    if (requestedProvider === "auto") {
      const env = this.getEnvironment();

      if (env === "browser") {
        try {
          // Try IndexedDB first
          if (typeof window !== "undefined" && window.indexedDB) {
            const IndexedDBProvider = require("../browser/indexeddb");
            return new IndexedDBProvider(this.options);
          }
        } catch (error) {
          Prime.Logger.warn(
            "Failed to create IndexedDB provider, falling back to memory",
            {
              error: error.message,
            },
          );
        }
      } else if (env === "node") {
        try {
          const FilesystemProvider = require("../node/filesystem");
          return new FilesystemProvider(this.options);
        } catch (error) {
          Prime.Logger.warn(
            "Failed to create filesystem provider, falling back to memory",
            {
              error: error.message,
            },
          );
        }
      }

      // Fall back to memory provider
      const MemoryProvider = require("./memory");
      return new MemoryProvider(this.options);
    }

    // If explicit provider requested
    switch (requestedProvider) {
      case "indexeddb":
        const IndexedDBProvider = require("../browser/indexeddb");
        return new IndexedDBProvider(this.options);

      case "filesystem":
        const FilesystemProvider = require("../node/filesystem");
        return new FilesystemProvider(this.options);

      case "memory":
        const MemoryProvider = require("./memory");
        return new MemoryProvider(this.options);

      default:
        throw new PrimeStorageError(
          `Unknown storage provider: ${requestedProvider}`,
          { provider: requestedProvider },
          "STORAGE_UNKNOWN_PROVIDER",
        );
    }
  }

  /**
   * Gets the current environment
   * @returns {string} 'browser', 'node', or 'unknown'
   */
  getEnvironment() {
    if (typeof window !== "undefined" && typeof document !== "undefined") {
      return "browser";
    }

    if (
      typeof process !== "undefined" &&
      process.versions &&
      process.versions.node
    ) {
      return "node";
    }

    return "unknown";
  }

  /**
   * Ensures the manager is initialized before operations
   * @private
   */
  ensureInitialized() {
    if (!this.isInitialized) {
      throw new PrimeStorageError(
        "Storage manager is not initialized",
        {},
        "STORAGE_NOT_INITIALIZED",
      );
    }
  }

  /**
   * Stores data with optional ID
   * @param {*} data - Data to store
   * @param {string} [id] - Optional ID
   * @returns {Promise<string>} The ID of the stored data
   */
  async store(data, id) {
    this.ensureInitialized();

    try {
      const dataId = id || Prime.Utils.uuid();

      // Check swap space limits before storing
      if (this.swapSpace) {
        await this.swapSpace.checkMemoryLimits();
      }

      // For small data, store directly
      const dataSize = this.chunkManager.getDataSize(data);

      if (dataSize <= this.options.chunkSize) {
        const { serialized, metadata } = await this.serializer.serialize(data);
        await this.provider.store(serialized, dataId);

        // Cache metadata
        this.metadataCache.set(dataId, metadata);

        return dataId;
      }

      // For large data, split into chunks
      const chunks = this.chunkManager.splitData(
        data,
        dataId,
        this.options.chunkSize,
      );

      // Store each chunk with a derived ID
      const storePromises = chunks.map(async (chunk, index) => {
        const chunkId = `${dataId}_chunk_${index}`;
        const { serialized, metadata } = await this.serializer.serialize(
          chunk.data,
        );

        // Store chunk data
        await this.provider.store(serialized, chunkId);

        // Cache metadata
        this.metadataCache.set(chunkId, {
          ...metadata,
          isChunk: true,
          chunkIndex: index,
          totalChunks: chunks.length,
          parentId: dataId,
        });
      });

      await Promise.all(storePromises);

      // Store metadata about the chunks
      const chunksMetadata = {
        id: dataId,
        totalChunks: chunks.length,
        chunkSize: this.options.chunkSize,
        originalSize: dataSize,
        timestamp: Date.now(),
      };

      await this.provider.store(
        JSON.stringify(chunksMetadata),
        `${dataId}_metadata`,
      );

      // Cache the metadata
      this.metadataCache.set(dataId, chunksMetadata);

      return dataId;
    } catch (error) {
      this.emit("error", error);
      throw new PrimeStorageError(
        `Failed to store data: ${error.message}`,
        { originalError: error },
        "STORAGE_STORE_FAILED",
        error,
      );
    }
  }

  /**
   * Loads data by ID
   * @param {string} id - ID of the data to load
   * @returns {Promise<*>} The loaded data
   */
  async load(id) {
    this.ensureInitialized();

    try {
      // Check cache first
      if (this.cache.has(id)) {
        this.emit("cache-hit", id);
        return this.cache.get(id);
      }

      // Check if this is chunked data
      let metadataId = `${id}_metadata`;
      let isChunked = await this.provider.exists(metadataId);

      if (isChunked) {
        // Load and parse metadata
        const metadataStr = await this.provider.load(metadataId);
        const metadata = JSON.parse(metadataStr);

        // Load all chunks
        const chunkIds = Array.from(
          { length: metadata.totalChunks },
          (_, i) => `${id}_chunk_${i}`,
        );

        const chunkPromises = chunkIds.map(async (chunkId) => {
          const chunkData = await this.provider.load(chunkId);
          const chunkMetadata = this.metadataCache.get(chunkId) || {};

          return {
            data: chunkData,
            metadata: chunkMetadata,
          };
        });

        const chunks = await Promise.all(chunkPromises);

        // Reconstruct data from chunks
        const deserializedChunks = await Promise.all(
          chunks.map(async (chunk) => {
            return {
              data: await this.serializer.deserialize(
                chunk.data,
                chunk.metadata,
              ),
              metadata: {
                index: parseInt(chunk.metadata.chunkIndex || 0),
                totalChunks: metadata.totalChunks,
              },
            };
          }),
        );

        const reassembled =
          this.chunkManager.reassembleChunks(deserializedChunks);

        // Cache the result if not too large
        if (metadata.originalSize <= this.options.chunkSize * 2) {
          this.cache.set(id, reassembled);
        }

        return reassembled;
      } else {
        // Load data directly
        const serialized = await this.provider.load(id);
        const metadata = this.metadataCache.get(id) || {};

        const data = await this.serializer.deserialize(serialized, metadata);

        // Cache the result if not too large
        if (
          this.chunkManager.getDataSize(serialized) <= this.options.chunkSize
        ) {
          this.cache.set(id, data);
        }

        return data;
      }
    } catch (error) {
      this.emit("error", error);
      throw new PrimeStorageError(
        `Failed to load data with ID ${id}: ${error.message}`,
        { id, originalError: error },
        "STORAGE_LOAD_FAILED",
        error,
      );
    }
  }

  /**
   * Deletes data by ID
   * @param {string} id - ID of the data to delete
   * @returns {Promise<boolean>} True if successful
   */
  async delete(id) {
    this.ensureInitialized();

    try {
      // Check if this is chunked data
      let metadataId = `${id}_metadata`;
      let isChunked = await this.provider.exists(metadataId);

      if (isChunked) {
        // Load and parse metadata
        const metadataStr = await this.provider.load(metadataId);
        const metadata = JSON.parse(metadataStr);

        // Delete all chunks
        const chunkIds = Array.from(
          { length: metadata.totalChunks },
          (_, i) => `${id}_chunk_${i}`,
        );

        for (const chunkId of chunkIds) {
          await this.provider.delete(chunkId);
          this.metadataCache.delete(chunkId);
        }

        // Delete metadata
        await this.provider.delete(metadataId);
      }

      // Delete the main data
      await this.provider.delete(id);

      // Remove from caches
      this.cache.delete(id);
      this.metadataCache.delete(id);

      return true;
    } catch (error) {
      this.emit("error", error);
      throw new PrimeStorageError(
        `Failed to delete data with ID ${id}: ${error.message}`,
        { id, originalError: error },
        "STORAGE_DELETE_FAILED",
        error,
      );
    }
  }

  /**
   * Checks if data with the given ID exists
   * @param {string} id - ID to check
   * @returns {Promise<boolean>} True if data exists
   */
  async exists(id) {
    this.ensureInitialized();

    try {
      return this.provider.exists(id);
    } catch (error) {
      this.emit("error", error);
      throw new PrimeStorageError(
        `Failed to check existence for ID ${id}: ${error.message}`,
        { id, originalError: error },
        "STORAGE_EXISTS_FAILED",
        error,
      );
    }
  }

  /**
   * Lists all stored data IDs
   * @returns {Promise<string[]>} Array of stored data IDs
   */
  async getAllKeys() {
    this.ensureInitialized();

    try {
      const allKeys = await this.provider.getAllKeys();

      // Filter out chunk and metadata keys
      return allKeys.filter(
        (key) => !key.includes("_chunk_") && !key.endsWith("_metadata"),
      );
    } catch (error) {
      this.emit("error", error);
      throw new PrimeStorageError(
        `Failed to list keys: ${error.message}`,
        { originalError: error },
        "STORAGE_KEYS_FAILED",
        error,
      );
    }
  }

  /**
   * Clears all stored data
   * @returns {Promise<void>}
   */
  async clear() {
    this.ensureInitialized();

    try {
      await this.provider.clear();
      this.cache.clear();
      this.metadataCache.clear();
    } catch (error) {
      this.emit("error", error);
      throw new PrimeStorageError(
        `Failed to clear storage: ${error.message}`,
        { originalError: error },
        "STORAGE_CLEAR_FAILED",
        error,
      );
    }
  }

  /**
   * Gets information about the storage
   * @returns {Promise<StorageInfo>} Storage information
   */
  async getStorageInfo() {
    this.ensureInitialized();

    try {
      return this.provider.getStorageInfo();
    } catch (error) {
      this.emit("error", error);
      throw new PrimeStorageError(
        `Failed to get storage info: ${error.message}`,
        { originalError: error },
        "STORAGE_INFO_FAILED",
        error,
      );
    }
  }

  /**
   * Gets the provider type
   * @returns {string} The provider type
   */
  getProviderType() {
    return this.provider ? this.provider.getProviderType() : "none";
  }

  /**
   * Gets memory usage statistics
   * @returns {Promise<MemoryStats>} Memory statistics
   */
  async getMemoryStats() {
    this.ensureInitialized();

    const stats = {
      memoryUsed: 0,
      memoryLimit: this.options.maxMemoryUsage || 0,
      swapUsed: 0,
      itemsCached: this.cache.size,
      itemsSwapped: 0,
    };

    if (this.swapSpace) {
      const swapStats = await this.swapSpace.getStats();
      stats.swapUsed = swapStats.swapUsed;
      stats.itemsSwapped = swapStats.itemsSwapped;
    }

    return stats;
  }

  /**
   * Creates a read stream for the data with the given ID
   * @param {string} id - ID of the data to stream
   * @param {StreamOptions} [options] - Stream options
   * @returns {ReadableStream} A readable stream of the data
   */
  createReadStream(id, options = {}) {
    this.ensureInitialized();
    return this.provider.createReadStream(id, options);
  }

  /**
   * Creates a write stream for storing data
   * @param {string} [id] - Optional ID (if not provided, a UUID will be generated)
   * @param {StreamOptions} [options] - Stream options
   * @returns {WritableStream} A writable stream to store data
   */
  createWriteStream(id, options = {}) {
    this.ensureInitialized();
    return this.provider.createWriteStream(id || Prime.Utils.uuid(), options);
  }

  /**
   * Creates a virtual array backed by storage
   * @param {string} id - ID of the stored array data
   * @param {number} size - Size of the virtual array
   * @param {Function} itemFactory - Function to generate items on demand
   * @returns {Object} Virtual array object
   */
  createVirtualArray(id, size, itemFactory) {
    this.ensureInitialized();

    return new VirtualArray({
      storageManager: this,
      id,
      length: size,
      itemFactory,
    });
  }

  /**
   * Stores a model in storage
   * @param {Object} model - Neural model to store
   * @param {string} [id] - Optional ID
   * @returns {Promise<string>} The ID of the stored model
   */
  async storeModel(model, id) {
    // Special handling for neural models with toJSON method
    if (model && typeof model.toJSON === "function") {
      const modelData = model.toJSON();
      return this.store(modelData, id);
    }

    // Special handling for neural models with layers and getLayer method
    if (model && model.layers && typeof model.getLayer === "function") {
      const modelData = {
        name: model.name || "unnamed_model",
        layers: model.layers.map((layer) => ({
          type: layer.constructor.name,
          config:
            typeof layer.getConfig === "function" ? layer.getConfig() : {},
          weights: layer.weights,
          biases: layer.biases,
        })),
      };

      return this.store(modelData, id);
    }

    // Default handling for other models
    return this.store(model, id);
  }

  /**
   * Loads a model from storage
   * @param {string} id - ID of the stored model
   * @returns {Promise<Object>} The loaded model
   */
  async loadModel(id) {
    const modelData = await this.load(id);

    // Check if this is a neural model
    if (modelData && modelData.layers && Array.isArray(modelData.layers)) {
      const Prime = require("../../");

      // If the NeuralModel class has a fromJSON method, use it
      if (
        Prime.Neural.Model.NeuralModel &&
        typeof Prime.Neural.Model.NeuralModel.fromJSON === "function"
      ) {
        return Prime.Neural.Model.NeuralModel.fromJSON(modelData);
      }

      // Otherwise, create a model manually
      const model = new Prime.Neural.Model({
        name: modelData.name,
      });

      for (const layerData of modelData.layers) {
        let layer;

        // Create the correct layer type
        switch (layerData.type) {
          case "Dense":
          case "DenseLayer":
            layer = new Prime.Neural.Layer.Dense(
              layerData.config.inputSize,
              layerData.config.outputSize,
              { activation: layerData.config.activation },
            );
            break;
          case "Convolutional":
          case "ConvolutionalLayer":
            layer = new Prime.Neural.Layer.Convolutional(
              layerData.config.inputShape,
              layerData.config.filterShape,
              layerData.config,
            );
            break;
          case "Recurrent":
          case "RecurrentLayer":
            layer = new Prime.Neural.Layer.Recurrent(
              layerData.config.inputSize,
              layerData.config.hiddenSize,
              layerData.config,
            );
            break;
          default:
            throw new Error(`Unknown layer type: ${layerData.type}`);
        }

        // Set weights and biases
        if (layerData.weights) layer.weights = layerData.weights;
        if (layerData.biases) layer.biases = layerData.biases;

        model.addLayer(layer);
      }

      return model;
    }

    // Return the model data as is
    return modelData;
  }

  /**
   * Loads model weights from storage into an existing model
   * @param {Object} model - Model to load weights into
   * @param {string} id - ID of the stored model
   * @returns {Promise<void>}
   */
  async loadModelWeights(model, id) {
    const modelData = await this.load(id);

    // Check if this is a neural model with layers
    if (modelData && modelData.layers && Array.isArray(modelData.layers)) {
      // Verify the model structure is compatible
      if (model.layers.length !== modelData.layers.length) {
        throw new PrimeStorageError(
          "Model architecture mismatch",
          { expected: modelData.layers.length, actual: model.layers.length },
          "STORAGE_MODEL_MISMATCH",
        );
      }

      // Load weights for each layer
      for (let i = 0; i < model.layers.length; i++) {
        if (modelData.layers[i].weights) {
          model.layers[i].weights = modelData.layers[i].weights;
        }

        if (modelData.layers[i].biases) {
          model.layers[i].biases = modelData.layers[i].biases;
        }
      }
    }
  }

  /**
   * Stores component state
   * @param {Object} component - Component to store state for
   * @param {string} [id] - Optional ID
   * @returns {Promise<string>} The ID of the stored state
   */
  async storeComponentState(component, id) {
    if (!component || !component.state) {
      throw new PrimeStorageError(
        "Invalid component or missing state",
        { component },
        "STORAGE_INVALID_COMPONENT",
      );
    }

    const stateId = id || `component_${component.name}_${Prime.Utils.uuid()}`;

    const stateData = {
      name: component.name,
      state: component.state,
      timestamp: Date.now(),
    };

    return this.store(stateData, stateId);
  }

  /**
   * Loads component state
   * @param {Object} component - Component to load state into
   * @param {string} id - ID of the stored state
   * @returns {Promise<void>}
   */
  async loadComponentState(component, id) {
    if (!component) {
      throw new PrimeStorageError(
        "Invalid component",
        { id },
        "STORAGE_INVALID_COMPONENT",
      );
    }

    const stateData = await this.load(id);

    if (!stateData || !stateData.state) {
      throw new PrimeStorageError(
        "Invalid or missing component state data",
        { id },
        "STORAGE_INVALID_STATE",
      );
    }

    // Apply the state to the component
    component.state = stateData.state;
  }

  /**
   * Creates a data provider for training neural models
   * @param {DataProviderOptions} options - Data provider options
   * @returns {Object} Data provider for training
   */
  createDataProvider(options) {
    this.ensureInitialized();

    // Use the DataProvider class directly
    const provider = new DataProvider(this, options);

    // Initialize the provider immediately
    provider.init().catch((err) => {
      Prime.Logger.error("Failed to initialize data provider", {
        error: err.message,
      });
    });

    return provider;
  }
}

/**
 * Manages swap space for offloading memory to storage
 */
class SwapSpaceManager {
  /**
   * Creates a new swap space manager
   * @param {Object} options - Swap space options
   * @param {number} [options.maxMemoryUsage] - Maximum memory usage before swapping
   * @param {string} [options.storagePath] - Path for swap files
   */
  constructor(options = {}) {
    this.options = {
      maxMemoryUsage: 100 * 1024 * 1024, // 100MB default
      ...options,
    };

    this.storageManager = null;
    this.swappedItems = new Map();
    this.isInitialized = false;
  }

  /**
   * Initializes the swap space manager
   * @param {StorageManager} storageManager - Storage manager to use
   * @returns {Promise<void>}
   */
  async init(storageManager) {
    this.storageManager = storageManager;
    this.isInitialized = true;
  }

  /**
   * Allocates memory and swaps to storage if needed
   * @param {string} id - ID for the data
   * @param {*} data - Data to allocate
   * @returns {Promise<void>}
   */
  async allocate(id, data) {
    // If we don't have data, just register the ID
    if (!data) {
      this.swappedItems.set(id, { isSwapped: false, size: 0 });
      return;
    }

    const size = this.storageManager.chunkManager.getDataSize(data);

    this.swappedItems.set(id, {
      isSwapped: false,
      size,
      data,
    });

    // Check memory limits and swap if needed
    await this.checkMemoryLimits();
  }

  /**
   * Checks memory limits and swaps data if needed
   * @returns {Promise<void>}
   */
  async checkMemoryLimits() {
    // Calculate total memory usage
    let totalMemory = 0;

    for (const [id, item] of this.swappedItems.entries()) {
      if (!item.isSwapped) {
        totalMemory += item.size;
      }
    }

    // If memory usage is too high, swap some items
    if (totalMemory > this.options.maxMemoryUsage) {
      // Sort items by size (largest first)
      const sortedItems = Array.from(this.swappedItems.entries())
        .filter(([_, item]) => !item.isSwapped && item.data)
        .sort((a, b) => b[1].size - a[1].size);

      // Swap items until memory usage is acceptable
      for (const [id, item] of sortedItems) {
        if (totalMemory <= this.options.maxMemoryUsage) {
          break;
        }

        await this.swapToDisk(id);
        totalMemory -= item.size;
      }
    }
  }

  /**
   * Swaps data to disk
   * @param {string} id - ID of the data to swap
   * @returns {Promise<void>}
   */
  async swapToDisk(id) {
    const item = this.swappedItems.get(id);

    if (!item || item.isSwapped) {
      return;
    }

    try {
      // Store the data in storage
      const swapId = `swap_${id}`;
      await this.storageManager.store(item.data, swapId);

      // Update the item
      this.swappedItems.set(id, {
        isSwapped: true,
        size: item.size,
        swapId,
      });

      // Remove the data reference
      item.data = null;
    } catch (error) {
      Prime.Logger.error(`Failed to swap data to disk: ${error.message}`, {
        id,
        error,
      });
    }
  }

  /**
   * Flush all pending items to disk
   * @returns {Promise<void>}
   */
  async flushToDisk() {
    const promises = [];

    // Identify items that need to be swapped
    for (const [id, item] of this.swappedItems.entries()) {
      if (!item.isSwapped && item.data) {
        promises.push(this.swapToDisk(id));
      }
    }

    // Wait for all swap operations to complete
    await Promise.all(promises);
  }

  /**
   * Loads swapped data from disk
   * @param {string} id - ID of the data to load
   * @returns {Promise<*>} The loaded data
   */
  async loadFromDisk(id) {
    const item = this.swappedItems.get(id);

    if (!item || !item.isSwapped) {
      return null;
    }

    try {
      // Load the data from storage
      const data = await this.storageManager.load(item.swapId);

      // Update the item
      this.swappedItems.set(id, {
        isSwapped: false,
        size: item.size,
        data,
      });

      return data;
    } catch (error) {
      Prime.Logger.error(
        `Failed to load swapped data from disk: ${error.message}`,
        {
          id,
          error,
        },
      );

      return null;
    }
  }

  /**
   * Frees allocated memory
   * @param {string} id - ID of the data to free
   * @returns {Promise<void>}
   */
  async free(id) {
    const item = this.swappedItems.get(id);

    if (!item) {
      return;
    }

    if (item.isSwapped) {
      try {
        // Delete the swap file
        await this.storageManager.delete(item.swapId);
      } catch (error) {
        Prime.Logger.warn(`Failed to delete swap file: ${error.message}`, {
          id,
          swapId: item.swapId,
          error,
        });
      }
    }

    // Remove the item
    this.swappedItems.delete(id);
  }

  /**
   * Gets swap space statistics
   * @returns {Promise<Object>} Swap space statistics
   */
  async getStats() {
    let swapUsed = 0;
    let itemsSwapped = 0;

    for (const [id, item] of this.swappedItems.entries()) {
      if (item.isSwapped) {
        swapUsed += item.size;
        itemsSwapped++;
      }
    }

    return {
      swapUsed,
      itemsSwapped,
      totalItems: this.swappedItems.size,
    };
  }
}

/**
 * Virtual array that loads data on demand from storage
 */
class VirtualArray {
  /**
   * Creates a new virtual array
   * @param {Object} options - Virtual array options
   * @param {StorageManager} options.storageManager - Storage manager to use
   * @param {string} options.id - ID of the stored array data
   * @param {number} options.length - Length of the virtual array
   * @param {Function} [options.itemFactory] - Function to generate items on demand
   */
  constructor(options) {
    this.storageManager = options.storageManager;
    this.id = options.id;
    this.length = options.length;
    this.itemFactory = options.itemFactory;
    this.chunkSize = options.chunkSize || 1000;

    this.cache = new Map();
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
        "STORAGE_INDEX_OUT_OF_BOUNDS",
      );
    }

    // Check cache first
    if (this.cache.has(index)) {
      return this.cache.get(index);
    }

    // If we have an item factory, use it
    if (this.itemFactory) {
      const item = this.itemFactory(index);
      this.cache.set(index, item);
      return item;
    }

    // Otherwise, load from storage
    try {
      const data = await this.storageManager.load(this.id);

      if (Array.isArray(data) && index < data.length) {
        const item = data[index];
        this.cache.set(index, item);
        return item;
      }

      throw new PrimeStorageError(
        `Failed to get item at index ${index}`,
        { index },
        "STORAGE_ITEM_NOT_FOUND",
      );
    } catch (error) {
      throw new PrimeStorageError(
        `Failed to get item at index ${index}: ${error.message}`,
        { index, originalError: error },
        "STORAGE_GET_ITEM_FAILED",
        error,
      );
    }
  }

  /**
   * Creates an iterator that loads data in chunks
   * @param {number} [chunkSize] - Size of chunks to load
   * @returns {AsyncIterator} An async iterator for the array
   */
  async *iterateChunks(chunkSize = this.chunkSize) {
    for (let i = 0; i < this.length; i += chunkSize) {
      const chunkLength = Math.min(chunkSize, this.length - i);
      const chunk = new Array(chunkLength);

      // If we have an item factory, use it
      if (this.itemFactory) {
        for (let j = 0; j < chunkLength; j++) {
          chunk[j] = this.itemFactory(i + j);
        }

        yield chunk;
        continue;
      }

      // Otherwise, load from storage
      try {
        const data = await this.storageManager.load(this.id);

        if (Array.isArray(data)) {
          const end = Math.min(i + chunkSize, data.length);
          const dataChunk = data.slice(i, end);

          yield dataChunk;
        } else {
          throw new PrimeStorageError(
            "Data is not an array",
            { id: this.id },
            "STORAGE_NOT_ARRAY",
          );
        }
      } catch (error) {
        throw new PrimeStorageError(
          `Failed to iterate chunks: ${error.message}`,
          { originalError: error },
          "STORAGE_ITERATE_FAILED",
          error,
        );
      }
    }
  }
}

/**
 * Data provider for training neural models
 */
class DataProvider {
  /**
   * Creates a new data provider
   * @param {StorageManager} storageManager - Storage manager to use
   * @param {DataProviderOptions} options - Data provider options
   */
  constructor(storageManager, options) {
    this.storageManager = storageManager;
    this.options = {
      batchSize: 32,
      shuffle: true,
      ...options,
    };

    if (!this.options.inputId) {
      throw new PrimeStorageError(
        "Input ID is required",
        { options },
        "STORAGE_MISSING_INPUT_ID",
      );
    }

    this.currentBatch = 0;
    this.totalBatches = 0;
    this.dataSize = 0;
    this.initialized = false;
  }

  /**
   * Initializes the data provider
   * @returns {Promise<void>}
   */
  async init() {
    if (this.initialized) {
      return;
    }

    try {
      // Load input data to get size
      const inputData = await this.storageManager.load(this.options.inputId);

      if (!Array.isArray(inputData)) {
        throw new PrimeStorageError(
          "Input data is not an array",
          { id: this.options.inputId },
          "STORAGE_NOT_ARRAY",
        );
      }

      this.dataSize = inputData.length;
      this.totalBatches = Math.ceil(this.dataSize / this.options.batchSize);

      // If output ID is provided, verify size
      if (this.options.outputId) {
        const outputData = await this.storageManager.load(
          this.options.outputId,
        );

        if (!Array.isArray(outputData)) {
          throw new PrimeStorageError(
            "Output data is not an array",
            { id: this.options.outputId },
            "STORAGE_NOT_ARRAY",
          );
        }

        if (outputData.length !== this.dataSize) {
          throw new PrimeStorageError(
            "Input and output data sizes do not match",
            { inputSize: this.dataSize, outputSize: outputData.length },
            "STORAGE_SIZE_MISMATCH",
          );
        }
      }

      this.initialized = true;
    } catch (error) {
      throw new PrimeStorageError(
        `Failed to initialize data provider: ${error.message}`,
        { originalError: error },
        "STORAGE_PROVIDER_INIT_FAILED",
        error,
      );
    }
  }

  /**
   * Gets the next batch of data
   * @returns {Promise<Object>} The next batch of data
   */
  async nextBatch() {
    if (!this.initialized) {
      await this.init();
    }

    if (this.currentBatch >= this.totalBatches) {
      // Reset batch counter and shuffle if needed
      this.currentBatch = 0;

      if (this.options.shuffle) {
        // Note: This doesn't actually shuffle the data in storage,
        // instead we would use a shuffled index array in a real implementation
      }
    }

    try {
      const start = this.currentBatch * this.options.batchSize;
      const end = Math.min(start + this.options.batchSize, this.dataSize);

      // Load input batch
      const inputData = await this.storageManager.load(this.options.inputId);
      const inputBatch = inputData.slice(start, end);

      // Apply preprocessing if provided
      if (this.options.preprocessInput) {
        for (let i = 0; i < inputBatch.length; i++) {
          inputBatch[i] = this.options.preprocessInput(inputBatch[i]);
        }
      }

      // Load output batch if provided
      let outputBatch = null;
      if (this.options.outputId) {
        const outputData = await this.storageManager.load(
          this.options.outputId,
        );
        outputBatch = outputData.slice(start, end);

        // Apply preprocessing if provided
        if (this.options.preprocessOutput) {
          for (let i = 0; i < outputBatch.length; i++) {
            outputBatch[i] = this.options.preprocessOutput(outputBatch[i]);
          }
        }
      }

      this.currentBatch++;

      return {
        input: inputBatch,
        output: outputBatch,
        batchIndex: this.currentBatch - 1,
        totalBatches: this.totalBatches,
      };
    } catch (error) {
      throw new PrimeStorageError(
        `Failed to get next batch: ${error.message}`,
        { batch: this.currentBatch, originalError: error },
        "STORAGE_BATCH_FAILED",
        error,
      );
    }
  }

  /**
   * Resets the data provider
   * @returns {Promise<void>}
   */
  async reset() {
    this.currentBatch = 0;
  }

  /**
   * Gets the number of samples
   * @returns {number} The number of samples
   */
  getNumSamples() {
    return this.dataSize;
  }

  /**
   * Gets the number of batches
   * @returns {number} The number of batches
   */
  getNumBatches() {
    return this.totalBatches;
  }
}

module.exports = StorageManager;
