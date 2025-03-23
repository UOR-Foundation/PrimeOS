/**
 * PrimeOS JavaScript Library - Data Provider
 * Provider for training data that loads from storage
 */

const Prime = require("../../core");
const { StorageError } = require("../index");

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
      shuffle: false, // Default to false to match test expectations
      ...options,
    };

    if (!this.options.inputId) {
      throw new StorageError(
        "Input ID is required",
        { options },
        "STORAGE_MISSING_INPUT_ID",
      );
    }

    this.currentBatch = 0;
    this.totalBatches = 0;
    this.dataSize = 0;
    this.initialized = false;
    this.shuffledIndices = null;
    this.inputShape = null;
    this.outputShape = null;

    // For caching loaded data to improve performance
    this.cachedInputData = null;
    this.cachedOutputData = null;
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
        throw new StorageError(
          "Input data is not an array",
          { id: this.options.inputId },
          "STORAGE_NOT_ARRAY",
        );
      }

      this.dataSize = inputData.length;
      this.totalBatches = Math.ceil(this.dataSize / this.options.batchSize);

      // Cache input data if not too large
      if (this.dataSize <= 1000 || this.options.cacheData) {
        this.cachedInputData = inputData;
      }

      // Determine input shape from first item
      if (inputData.length > 0) {
        const firstItem = inputData[0];
        if (Array.isArray(firstItem)) {
          this.inputShape = [firstItem.length];
        } else if (typeof firstItem === "number") {
          this.inputShape = [1];
        } else if (firstItem && typeof firstItem === "object") {
          // Handle more complex shapes
          this.inputShape = this._inferShape(firstItem);
        }
      }

      // If output ID is provided, verify size and get output shape
      if (this.options.outputId) {
        const outputData = await this.storageManager.load(
          this.options.outputId,
        );

        if (!Array.isArray(outputData)) {
          throw new StorageError(
            "Output data is not an array",
            { id: this.options.outputId },
            "STORAGE_NOT_ARRAY",
          );
        }

        if (outputData.length !== this.dataSize) {
          throw new StorageError(
            "Input and output data sizes do not match",
            { inputSize: this.dataSize, outputSize: outputData.length },
            "STORAGE_SIZE_MISMATCH",
          );
        }

        // Cache output data if not too large
        if (this.dataSize <= 1000 || this.options.cacheData) {
          this.cachedOutputData = outputData;
        }

        // Determine output shape from first item
        if (outputData.length > 0) {
          const firstItem = outputData[0];
          if (Array.isArray(firstItem)) {
            this.outputShape = [firstItem.length];
          } else if (typeof firstItem === "number") {
            this.outputShape = [1];
          } else if (firstItem && typeof firstItem === "object") {
            // Handle more complex shapes
            this.outputShape = this._inferShape(firstItem);
          }
        }
      }

      // Create shuffled indices if needed
      if (this.options.shuffle) {
        this._shuffleIndices();
      }

      this.initialized = true;
    } catch (error) {
      throw new StorageError(
        `Failed to initialize data provider: ${error.message}`,
        { originalError: error },
        "STORAGE_PROVIDER_INIT_FAILED",
        error,
      );
    }
  }

  /**
   * Infers the shape of a data item
   * @private
   * @param {*} item - Item to infer shape from
   * @returns {Array} Shape array
   */
  _inferShape(item) {
    if (Array.isArray(item)) {
      const shape = [item.length];
      if (item.length > 0 && Array.isArray(item[0])) {
        const nestedShape = this._inferShape(item[0]);
        return shape.concat(nestedShape);
      }
      return shape;
    } else if (typeof item === "number") {
      return [1];
    } else if (item && typeof item === "object") {
      // For objects with shape properties
      if (item.shape) {
        return Array.isArray(item.shape) ? item.shape : [item.shape];
      }
      // For objects with length property
      if (item.length !== undefined) {
        return [item.length];
      }
    }
    return []; // Unknown shape
  }

  /**
   * Shuffles the data indices
   * @private
   */
  _shuffleIndices() {
    // Create sequential indices
    this.shuffledIndices = Array.from({ length: this.dataSize }, (_, i) => i);

    // Fisher-Yates shuffle
    let seed = this.options.seed || Date.now();
    const random = () => {
      const x = Math.sin(seed++) * 10000;
      return x - Math.floor(x);
    };

    for (let i = this.shuffledIndices.length - 1; i > 0; i--) {
      const j = Math.floor(random() * (i + 1));
      [this.shuffledIndices[i], this.shuffledIndices[j]] = [
        this.shuffledIndices[j],
        this.shuffledIndices[i],
      ];
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
        this._shuffleIndices();
      }
    }

    try {
      const batchStart = this.currentBatch * this.options.batchSize;
      const batchEnd = Math.min(
        batchStart + this.options.batchSize,
        this.dataSize,
      );

      // Load input and output data if not cached
      const inputData =
        this.cachedInputData ||
        (await this.storageManager.load(this.options.inputId));
      const outputData = this.options.outputId
        ? this.cachedOutputData ||
          (await this.storageManager.load(this.options.outputId))
        : null;

      // Create batch using shuffled indices if available
      const inputBatch = [];
      const outputBatch = this.options.outputId ? [] : null;

      for (let i = batchStart; i < batchEnd; i++) {
        // When using shuffled indices, we should use the shuffled index to get the data
        // But we were using 'i' directly which is incorrect when shuffling is enabled
        const index = this.shuffledIndices ? this.shuffledIndices[i] : i;

        // Always use the actual data at the specified index, not the index itself
        let input = inputData[index];
        if (this.options.preprocessInput) {
          input = this.options.preprocessInput(input);
        }
        inputBatch.push(input);

        if (outputData) {
          let output = outputData[index];
          if (this.options.preprocessOutput) {
            output = this.options.preprocessOutput(output);
          }
          outputBatch.push(output);
        }
      }

      this.currentBatch++;

      return {
        inputs: inputBatch,
        outputs: outputBatch,
        input: inputBatch, // For backwards compatibility
        output: outputBatch, // For backwards compatibility
        batchIndex: this.currentBatch - 1,
        totalBatches: this.totalBatches,
      };
    } catch (error) {
      throw new StorageError(
        `Failed to get next batch: ${error.message}`,
        { batch: this.currentBatch, originalError: error },
        "STORAGE_BATCH_FAILED",
        error,
      );
    }
  }

  /**
   * Gets a specific batch of data
   * @param {number} batchIndex - Index of the batch to get
   * @returns {Promise<Object>} The batch data
   */
  async getBatch(batchIndex) {
    if (!this.initialized) {
      await this.init();
    }

    if (batchIndex < 0 || batchIndex >= this.totalBatches) {
      throw new StorageError(
        `Invalid batch index: ${batchIndex}`,
        { batchIndex, totalBatches: this.totalBatches },
        "STORAGE_INVALID_BATCH_INDEX",
      );
    }

    // Store current batch index
    const currentBatch = this.currentBatch;

    try {
      // Set current batch to requested index
      this.currentBatch = batchIndex;

      // Get the batch
      const batch = await this.nextBatch();

      // Adjust currentBatch to account for nextBatch's increment
      this.currentBatch = currentBatch;

      return batch;
    } catch (error) {
      // Restore current batch index
      this.currentBatch = currentBatch;
      throw error;
    }
  }

  /**
   * Gets a random batch of data
   * @returns {Promise<Object>} Random batch of data
   */
  async getRandomBatch() {
    if (!this.initialized) {
      await this.init();
    }

    // Create batch manually instead of using getBatch to ensure consistent batch size
    // The tests expect a batch with exactly 2 items regardless of position
    const batchSize = this.options.batchSize;

    // Load the data if not cached
    const inputData =
      this.cachedInputData ||
      (await this.storageManager.load(this.options.inputId));
    const outputData = this.options.outputId
      ? this.cachedOutputData ||
        (await this.storageManager.load(this.options.outputId))
      : null;

    // Select random indices ensuring we get exactly batchSize indices
    // If there are fewer than batchSize items, use all available indices
    const availableIndices = Array.from({ length: this.dataSize }, (_, i) => i);
    const selectedIndices = [];

    for (let i = 0; i < Math.min(batchSize, this.dataSize); i++) {
      const randomIndex = Math.floor(Math.random() * availableIndices.length);
      selectedIndices.push(availableIndices[randomIndex]);
      availableIndices.splice(randomIndex, 1);
    }

    // Create batch using selected indices
    const inputBatch = selectedIndices.map((index) => {
      let input = inputData[index];
      if (this.options.preprocessInput) {
        input = this.options.preprocessInput(input);
      }
      return input;
    });

    const outputBatch = outputData
      ? selectedIndices.map((index) => {
          let output = outputData[index];
          if (this.options.preprocessOutput) {
            output = this.options.preprocessOutput(output);
          }
          return output;
        })
      : null;

    return {
      inputs: inputBatch,
      outputs: outputBatch,
      input: inputBatch, // For backwards compatibility
      output: outputBatch, // For backwards compatibility
      batchIndex: -1, // Special value to indicate random batch
      totalBatches: this.totalBatches,
    };
  }

  /**
   * Resets the data provider
   * @returns {Promise<void>}
   */
  async reset() {
    if (!this.initialized) {
      await this.init();
    }

    this.currentBatch = 0;

    // When resetting, we should always regenerate shuffled indices to ensure
    // subsequent calls to nextBatch/getBatch will return data in the expected order
    if (this.options.shuffle) {
      this._shuffleIndices();
    } else {
      // If not using shuffle, make sure shuffledIndices is null to avoid using previous shuffled order
      this.shuffledIndices = null;
    }

    return Promise.resolve();
  }

  /**
   * Gets the shape of input data
   * @returns {Array} Input data shape
   */
  getInputShape() {
    if (!this.initialized) {
      throw new StorageError(
        "Data provider not initialized",
        {},
        "STORAGE_PROVIDER_NOT_INITIALIZED",
      );
    }

    return this.inputShape || [];
  }

  /**
   * Gets the shape of output data
   * @returns {Array} Output data shape
   */
  getOutputShape() {
    if (!this.initialized) {
      throw new StorageError(
        "Data provider not initialized",
        {},
        "STORAGE_PROVIDER_NOT_INITIALIZED",
      );
    }

    return this.outputShape || [];
  }

  /**
   * Gets the size of the dataset
   * @returns {number} Dataset size
   */
  getDatasetSize() {
    if (!this.initialized) {
      throw new StorageError(
        "Data provider not initialized",
        {},
        "STORAGE_PROVIDER_NOT_INITIALIZED",
      );
    }

    return this.dataSize;
  }

  /**
   * Gets the number of batches
   * @returns {number} Number of batches
   */
  getBatchCount() {
    if (!this.initialized) {
      throw new StorageError(
        "Data provider not initialized",
        {},
        "STORAGE_PROVIDER_NOT_INITIALIZED",
      );
    }

    return this.totalBatches;
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

  /**
   * Gets the batch size
   * @returns {number} The batch size
   */
  getBatchSize() {
    return this.options.batchSize;
  }

  /**
   * Creates an iterator for batches
   * @returns {AsyncIterator} Iterator for batches
   */
  async *iterator() {
    if (!this.initialized) {
      await this.init();
    }

    // Reset to start
    await this.reset();

    // Iterate through all batches
    for (let i = 0; i < this.totalBatches; i++) {
      yield await this.nextBatch();
    }
  }

  /**
   * Prefetches a number of batches
   * @param {number} [numBatches=1] - Number of batches to prefetch
   * @returns {Promise<void>}
   */
  async prefetch(numBatches = 1) {
    if (!this.initialized) {
      await this.init();
    }

    // Store current batch index
    const currentBatch = this.currentBatch;

    try {
      // Prefetch the batches
      const prefetchBatches = [];
      for (let i = 0; i < numBatches; i++) {
        const batch = await this.nextBatch();
        prefetchBatches.push(batch);
      }

      // Reset current batch index
      this.currentBatch = currentBatch;
    } catch (error) {
      // Reset current batch index on error
      this.currentBatch = currentBatch;
      throw error;
    }
  }
}

module.exports = DataProvider;
