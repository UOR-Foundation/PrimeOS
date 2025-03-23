/**
 * PrimeOS JavaScript Library - Storage Chunking
 * Utilities for splitting and managing data chunks
 */

const Prime = require('../../core');
const { PrimeStorageError } = require('./provider');

/**
 * Manages data chunking for handling large datasets
 */
class ChunkManager {
  /**
   * Creates a new chunk manager
   * @param {Object} options - Chunk manager options
   * @param {number} [options.defaultChunkSize=1048576] - Default chunk size (1MB)
   * @param {boolean} [options.validateChecksums=true] - Whether to validate checksums
   */
  constructor(options = {}) {
    this.options = {
      defaultChunkSize: 1048576, // 1MB
      validateChecksums: true,
      ...options
    };
  }

  /**
   * Calculates the optimal chunk size for a given data size
   * @param {number} dataSize - Size of data in bytes
   * @returns {number} Optimal chunk size in bytes
   */
  calculateOptimalChunkSize(dataSize) {
    // For very small data, use the data size
    if (dataSize < 1024) {
      return dataSize;
    }
    
    // For small data (< 1MB), use a smaller chunk size
    if (dataSize < 1048576) {
      return Math.max(1024, Math.ceil(dataSize / 10));
    }
    
    // For medium data (1MB - 100MB), use proportional chunks
    if (dataSize < 104857600) {
      return Math.max(524288, Math.ceil(dataSize / 20)); // At least 512KB
    }
    
    // For large data, use larger chunks
    return Math.max(1048576, Math.ceil(dataSize / 50)); // At least 1MB
  }

  /**
   * Creates a data chunk with metadata
   * @param {*} data - Chunk data
   * @param {string} id - ID of the full data set
   * @param {number} index - Index of this chunk
   * @param {number} totalChunks - Total number of chunks
   * @returns {Object} Chunk object with metadata
   */
  createChunk(data, id, index, totalChunks) {
    const checksum = this.calculateChecksum(data);
    
    return {
      data,
      metadata: {
        id,
        index,
        totalChunks,
        size: this.getDataSize(data),
        checksum,
        timestamp: Date.now(),
        isLastChunk: index === totalChunks - 1
      }
    };
  }

  /**
   * Splits data into chunks
   * @param {*} data - Data to split
   * @param {string} id - ID for the chunks
   * @param {number} [chunkSize] - Size of each chunk (defaults to the optimal size)
   * @returns {Array<Object>} Array of chunk objects
   */
  splitData(data, id, chunkSize) {
    // If it's a string, split by character chunks
    if (typeof data === 'string') {
      return this.splitStringData(data, id, chunkSize);
    }
    
    // If it's an array, split by array elements
    if (Array.isArray(data)) {
      return this.splitArrayData(data, id, chunkSize);
    }
    
    // If it's a Buffer or TypedArray, split by bytes
    if (typeof Buffer !== 'undefined' && Buffer.isBuffer(data)) {
      return this.splitBufferData(data, id, chunkSize);
    }
    
    if (ArrayBuffer.isView(data) || data instanceof ArrayBuffer) {
      return this.splitBufferData(data, id, chunkSize);
    }
    
    // For other data types, create a single chunk
    return [this.createChunk(data, id, 0, 1)];
  }

  /**
   * Splits string data into chunks
   * @private
   * @param {string} data - String to split
   * @param {string} id - ID for the chunks
   * @param {number} [chunkSize] - Size of each chunk
   * @returns {Array<Object>} Array of chunk objects
   */
  splitStringData(data, id, chunkSize) {
    const size = data.length;
    
    // Use provided chunk size or calculate optimal size
    const actualChunkSize = chunkSize || this.calculateOptimalChunkSize(size);
    const totalChunks = Math.ceil(size / actualChunkSize);
    
    const chunks = [];
    
    for (let i = 0; i < totalChunks; i++) {
      const start = i * actualChunkSize;
      const end = Math.min(start + actualChunkSize, size);
      const chunkData = data.substring(start, end);
      
      chunks.push(this.createChunk(chunkData, id, i, totalChunks));
    }
    
    return chunks;
  }

  /**
   * Splits array data into chunks
   * @private
   * @param {Array} data - Array to split
   * @param {string} id - ID for the chunks
   * @param {number} [chunkSize] - Number of elements per chunk
   * @returns {Array<Object>} Array of chunk objects
   */
  splitArrayData(data, id, chunkSize) {
    const size = data.length;
    
    // For arrays, chunk size refers to number of elements
    // So we estimate the byte size differently
    const estimatedByteSize = this.estimateArrayByteSize(data);
    const estimatedBytesPerElement = Math.max(1, Math.ceil(estimatedByteSize / size));
    
    // Calculate chunks based on estimated byte size
    let actualChunkSize = chunkSize;
    if (!actualChunkSize) {
      const optimalByteChunkSize = this.calculateOptimalChunkSize(estimatedByteSize);
      actualChunkSize = Math.max(1, Math.floor(optimalByteChunkSize / estimatedBytesPerElement));
    }
    
    const totalChunks = Math.ceil(size / actualChunkSize);
    const chunks = [];
    
    for (let i = 0; i < totalChunks; i++) {
      const start = i * actualChunkSize;
      const end = Math.min(start + actualChunkSize, size);
      const chunkData = data.slice(start, end);
      
      chunks.push(this.createChunk(chunkData, id, i, totalChunks));
    }
    
    return chunks;
  }

  /**
   * Splits buffer data into chunks
   * @private
   * @param {Buffer|ArrayBuffer|TypedArray} data - Buffer to split
   * @param {string} id - ID for the chunks
   * @param {number} [chunkSize] - Size of each chunk in bytes
   * @returns {Array<Object>} Array of chunk objects
   */
  splitBufferData(data, id, chunkSize) {
    // Get data as Uint8Array
    let uint8Data;
    if (typeof Buffer !== 'undefined' && Buffer.isBuffer(data)) {
      uint8Data = new Uint8Array(data);
    } else if (data instanceof ArrayBuffer) {
      uint8Data = new Uint8Array(data);
    } else if (ArrayBuffer.isView(data)) {
      uint8Data = new Uint8Array(data.buffer, data.byteOffset, data.byteLength);
    } else {
      throw new PrimeStorageError(
        'Unsupported buffer type',
        { type: typeof data },
        'STORAGE_UNSUPPORTED_TYPE'
      );
    }
    
    const size = uint8Data.length;
    
    // Use provided chunk size or calculate optimal size
    const actualChunkSize = chunkSize || this.calculateOptimalChunkSize(size);
    const totalChunks = Math.ceil(size / actualChunkSize);
    
    const chunks = [];
    
    for (let i = 0; i < totalChunks; i++) {
      const start = i * actualChunkSize;
      const end = Math.min(start + actualChunkSize, size);
      const chunkData = uint8Data.slice(start, end);
      
      chunks.push(this.createChunk(chunkData, id, i, totalChunks));
    }
    
    return chunks;
  }

  /**
   * Reassembles chunks back into the original data
   * @param {Array<Object>} chunks - Array of chunk objects
   * @returns {*} Reassembled data
   */
  reassembleChunks(chunks) {
    if (!chunks || chunks.length === 0) {
      throw new PrimeStorageError(
        'No chunks provided for reassembly',
        {},
        'STORAGE_EMPTY_CHUNKS'
      );
    }
    
    // Sort chunks by index
    chunks.sort((a, b) => a.metadata.index - b.metadata.index);
    
    // Validate that we have all chunks
    const { totalChunks, id } = chunks[0].metadata;
    
    if (chunks.length !== totalChunks) {
      throw new PrimeStorageError(
        `Missing chunks for data ${id}: expected ${totalChunks}, got ${chunks.length}`,
        { expected: totalChunks, received: chunks.length, id },
        'STORAGE_MISSING_CHUNKS'
      );
    }
    
    // Validate chunk indices are continuous
    for (let i = 0; i < chunks.length; i++) {
      if (chunks[i].metadata.index !== i) {
        throw new PrimeStorageError(
          `Invalid chunk index for data ${id}: expected ${i}, got ${chunks[i].metadata.index}`,
          { expected: i, received: chunks[i].metadata.index, id },
          'STORAGE_INVALID_CHUNK_INDEX'
        );
      }
      
      // Verify checksum if enabled
      if (this.options.validateChecksums) {
        const calculatedChecksum = this.calculateChecksum(chunks[i].data);
        if (calculatedChecksum !== chunks[i].metadata.checksum) {
          throw new PrimeStorageError(
            `Checksum validation failed for chunk ${i} of data ${id}`,
            { expected: chunks[i].metadata.checksum, calculated: calculatedChecksum, id, chunkIndex: i },
            'STORAGE_CHECKSUM_FAILURE'
          );
        }
      }
    }
    
    // Check data type from first chunk
    const data = chunks.map(chunk => chunk.data);
    
    // Handle different data types
    const firstChunk = data[0];
    
    // String data
    if (typeof firstChunk === 'string') {
      return data.join('');
    }
    
    // Array data
    if (Array.isArray(firstChunk)) {
      return data.flat();
    }
    
    // Buffer data
    if (typeof Buffer !== 'undefined' && Buffer.isBuffer(firstChunk)) {
      return Buffer.concat(data);
    }
    
    // TypedArray data
    if (ArrayBuffer.isView(firstChunk)) {
      const totalLength = data.reduce((sum, chunk) => sum + chunk.length, 0);
      const result = new firstChunk.constructor(totalLength);
      
      let offset = 0;
      for (const chunk of data) {
        result.set(chunk, offset);
        offset += chunk.length;
      }
      
      return result;
    }
    
    // If there's only one chunk, return it directly
    if (data.length === 1) {
      return data[0];
    }
    
    // For other data types, throw an error
    throw new PrimeStorageError(
      `Cannot reassemble chunks of type ${typeof firstChunk}`,
      { type: typeof firstChunk, id },
      'STORAGE_UNSUPPORTED_REASSEMBLY'
    );
  }

  /**
   * Calculates a checksum for data
   * @private
   * @param {*} data - Data to calculate checksum for
   * @returns {string} Checksum string
   */
  calculateChecksum(data) {
    // A simple hash function for demonstration
    // In real implementation, this should be replaced with a proper hash algorithm
    let hash = 0;
    
    if (typeof data === 'string') {
      for (let i = 0; i < data.length; i++) {
        const char = data.charCodeAt(i);
        hash = ((hash << 5) - hash) + char;
        hash = hash & hash; // Convert to 32-bit integer
      }
    } else if (Array.isArray(data)) {
      hash = data.length; // Simple length-based hash for demo
    } else if (typeof Buffer !== 'undefined' && Buffer.isBuffer(data)) {
      for (let i = 0; i < data.length; i++) {
        hash = ((hash << 5) - hash) + data[i];
        hash = hash & hash;
      }
    } else if (ArrayBuffer.isView(data)) {
      const view = new Uint8Array(data.buffer, data.byteOffset, data.byteLength);
      for (let i = 0; i < view.length; i++) {
        hash = ((hash << 5) - hash) + view[i];
        hash = hash & hash;
      }
    } else {
      // For other types, use JSON serialization if possible
      try {
        const jsonStr = JSON.stringify(data);
        for (let i = 0; i < jsonStr.length; i++) {
          const char = jsonStr.charCodeAt(i);
          hash = ((hash << 5) - hash) + char;
          hash = hash & hash;
        }
      } catch (e) {
        // If JSON serialization fails, use a simple hash
        hash = Date.now();
      }
    }
    
    return hash.toString(16);
  }

  /**
   * Gets the size of data in bytes (estimated)
   * @private
   * @param {*} data - Data to get size for
   * @returns {number} Size in bytes
   */
  getDataSize(data) {
    if (typeof data === 'string') {
      return data.length;
    }
    
    if (Array.isArray(data)) {
      return this.estimateArrayByteSize(data);
    }
    
    if (typeof Buffer !== 'undefined' && Buffer.isBuffer(data)) {
      return data.length;
    }
    
    if (ArrayBuffer.isView(data)) {
      return data.byteLength;
    }
    
    if (data instanceof ArrayBuffer) {
      return data.byteLength;
    }
    
    // For other types, estimate using JSON serialization
    try {
      const jsonStr = JSON.stringify(data);
      return jsonStr.length;
    } catch (e) {
      return 0;
    }
  }

  /**
   * Estimates the byte size of an array
   * @private
   * @param {Array} array - Array to estimate size for
   * @returns {number} Estimated size in bytes
   */
  estimateArrayByteSize(array) {
    if (array.length === 0) {
      return 0;
    }
    
    // Sample a few elements to estimate size
    const sampleSize = Math.min(array.length, 10);
    let totalSampleSize = 0;
    
    for (let i = 0; i < sampleSize; i++) {
      const index = Math.floor(array.length * (i / sampleSize));
      totalSampleSize += this.getDataSize(array[index]);
    }
    
    const averageElementSize = totalSampleSize / sampleSize;
    return Math.ceil(averageElementSize * array.length);
  }
}

module.exports = ChunkManager;