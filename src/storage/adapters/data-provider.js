/**
 * PrimeOS JavaScript Library - Data Provider
 * Provider for training data that loads from storage
 */

const Prime = require('../../core');
const { PrimeStorageError } = require('../core/provider');

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
      ...options
    };
    
    if (!this.options.inputId) {
      throw new PrimeStorageError(
        'Input ID is required',
        { options },
        'STORAGE_MISSING_INPUT_ID'
      );
    }
    
    this.currentBatch = 0;
    this.totalBatches = 0;
    this.dataSize = 0;
    this.initialized = false;
    this.shuffledIndices = null;
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
          'Input data is not an array',
          { id: this.options.inputId },
          'STORAGE_NOT_ARRAY'
        );
      }
      
      this.dataSize = inputData.length;
      this.totalBatches = Math.ceil(this.dataSize / this.options.batchSize);
      
      // If output ID is provided, verify size
      if (this.options.outputId) {
        const outputData = await this.storageManager.load(this.options.outputId);
        
        if (!Array.isArray(outputData)) {
          throw new PrimeStorageError(
            'Output data is not an array',
            { id: this.options.outputId },
            'STORAGE_NOT_ARRAY'
          );
        }
        
        if (outputData.length !== this.dataSize) {
          throw new PrimeStorageError(
            'Input and output data sizes do not match',
            { inputSize: this.dataSize, outputSize: outputData.length },
            'STORAGE_SIZE_MISMATCH'
          );
        }
      }
      
      // Create shuffled indices if needed
      if (this.options.shuffle) {
        this._shuffleIndices();
      }
      
      this.initialized = true;
    } catch (error) {
      throw new PrimeStorageError(
        `Failed to initialize data provider: ${error.message}`,
        { originalError: error },
        'STORAGE_PROVIDER_INIT_FAILED',
        error
      );
    }
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
      [this.shuffledIndices[i], this.shuffledIndices[j]] = [this.shuffledIndices[j], this.shuffledIndices[i]];
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
      const batchEnd = Math.min(batchStart + this.options.batchSize, this.dataSize);
      
      // Load input and output data
      const [inputData, outputData] = await Promise.all([
        this.storageManager.load(this.options.inputId),
        this.options.outputId ? this.storageManager.load(this.options.outputId) : null
      ]);
      
      // Create batch using shuffled indices if available
      const inputBatch = [];
      const outputBatch = this.options.outputId ? [] : null;
      
      for (let i = batchStart; i < batchEnd; i++) {
        const index = this.shuffledIndices ? this.shuffledIndices[i] : i;
        
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
        totalBatches: this.totalBatches
      };
    } catch (error) {
      throw new PrimeStorageError(
        `Failed to get next batch: ${error.message}`,
        { batch: this.currentBatch, originalError: error },
        'STORAGE_BATCH_FAILED',
        error
      );
    }
  }

  /**
   * Resets the data provider
   * @returns {Promise<void>}
   */
  async reset() {
    this.currentBatch = 0;
    
    if (this.options.shuffle) {
      this._shuffleIndices();
    }
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