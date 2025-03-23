/**
 * PrimeOS JavaScript Library - Storage Types
 * Type definitions for the storage module
 */

/**
 * @typedef {Object} StorageOptions
 * @property {string} [provider='auto'] - Provider to use: 'auto', 'memory', 'indexeddb', 'filesystem'
 * @property {string} [storagePath] - Path for filesystem storage (Node.js only)
 * @property {number} [chunkSize=1048576] - Size of chunks for large data (1MB default)
 * @property {boolean} [useSwapSpace=true] - Whether to use swap space for memory management
 * @property {number} [maxMemoryUsage] - Maximum memory usage before swapping (bytes)
 * @property {number} [expirationTime] - Time in ms before cached data expires
 * @property {boolean} [compression=false] - Whether to compress stored data
 * @property {string} [databaseName='primeos-storage'] - Name for IndexedDB database
 * @property {string} [storeName='data'] - Name for IndexedDB object store
 */

/**
 * @typedef {Object} StorageInfo
 * @property {number} available - Available storage space in bytes
 * @property {number} used - Used storage space in bytes
 * @property {number} total - Total storage space in bytes
 * @property {string} provider - Current storage provider type
 */

/**
 * @typedef {Object} MemoryStats
 * @property {number} memoryUsed - Memory currently used in bytes
 * @property {number} memoryLimit - Memory limit in bytes
 * @property {number} swapUsed - Swap space used in bytes
 * @property {number} itemsCached - Number of items in memory cache
 * @property {number} itemsSwapped - Number of items in swap
 */

/**
 * @typedef {Object} DataProviderOptions
 * @property {string} inputId - ID of stored input data
 * @property {string} [outputId] - ID of stored output data
 * @property {number} [batchSize=32] - Size of each batch
 * @property {boolean} [shuffle=true] - Whether to shuffle data
 * @property {number} [seed] - Random seed for shuffling
 * @property {Function} [preprocessInput] - Function to preprocess input data
 * @property {Function} [preprocessOutput] - Function to preprocess output data
 */

/**
 * @typedef {Object} SwappableMatrixOptions
 * @property {number} [blockSize=100] - Size of matrix blocks
 * @property {number} [maxCachedBlocks=10] - Maximum number of blocks to keep in memory
 * @property {string} [evictionPolicy='lru'] - Cache eviction policy: 'lru', 'fifo', 'random'
 */

/**
 * @typedef {Object} VirtualArrayOptions
 * @property {number} length - Length of the virtual array
 * @property {number} [chunkSize=1000] - Size of chunks for iteration
 * @property {Function} [itemFactory] - Function to generate items on demand
 */

/**
 * @typedef {Object} StorageKey
 * @property {string} id - Unique identifier for the stored data
 * @property {string} [type] - Data type identifier
 * @property {Object} [metadata] - Additional metadata
 */

/**
 * @typedef {Object} ChunkMetadata
 * @property {string} id - ID of the data this chunk belongs to
 * @property {number} index - Index of this chunk
 * @property {number} totalChunks - Total number of chunks for this data
 * @property {number} size - Size of this chunk in bytes
 * @property {string} [checksum] - Checksum for data integrity verification
 * @property {boolean} [compressed] - Whether the chunk is compressed
 * @property {string} [format] - Serialization format
 */

/**
 * @typedef {Object} StreamOptions
 * @property {number} [highWaterMark] - Buffer size for streaming
 * @property {boolean} [objectMode=true] - Whether stream is in object mode
 * @property {number} [chunkSize] - Size of each chunk
 * @property {boolean} [autoClose=true] - Whether to auto-close stream
 */

module.exports = {}; // This module only provides TypeScript typings