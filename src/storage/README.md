# PrimeOS Storage Module

The Storage module provides persistent storage capabilities for PrimeOS, enabling applications to work with datasets larger than available RAM and persist application state across sessions.

## Features

- **Environment Detection**: Automatically selects the appropriate storage backend for the current environment (browser or Node.js)
- **Chunked Storage**: Efficiently stores large datasets by breaking them into manageable chunks
- **Serialization**: Preserves complex JavaScript objects, including PrimeOS-specific types
- **Streaming API**: Process large datasets without loading everything into memory at once
- **Swap Space**: Intelligently manages memory usage by offloading data to storage when needed
- **Virtual Collections**: Work with arrays and matrices larger than memory
- **Data Provider**: Feed large training datasets to neural models efficiently
- **Coherence Preservation**: Maintains mathematical coherence when storing PrimeOS objects

## Storage Providers

- **Memory**: In-memory storage for ephemeral data and testing
- **IndexedDB**: Browser-based persistent storage
- **Filesystem**: Node.js-based storage using the local filesystem

## Basic Usage

```javascript
const Prime = require('primeos');

// Create a storage manager
const storageManager = Prime.Storage.createManager();

// Initialize the manager
await storageManager.init();

// Store data
const data = { /* large dataset */ };
const id = await storageManager.store(data);

// Load data
const loadedData = await storageManager.load(id);

// Delete data
await storageManager.delete(id);

// Clear all data
await storageManager.clear();
```

## Advanced Usage

### Working with Large Matrices

```javascript
// Store a large matrix
const matrix = new Prime.Math.Matrix(10000, 10000);
const id = await storageManager.store(matrix);

// Create a swappable matrix that keeps only part in memory
const swappableMatrix = await Prime.Storage.createSwappableMatrix(storageManager, id, {
  blockSize: 200, // Work with 200x200 blocks
  maxCachedBlocks: 10 // Keep only 10 blocks in memory at once
});

// Use the swappable matrix
const value = await swappableMatrix.get(5000, 5000);
await swappableMatrix.set(5000, 5000, 42);
```

### Virtual Arrays

```javascript
// Create a virtual array
const virtualArray = Prime.Storage.createVirtualArray(storageManager, {
  length: 1000000, // 1 million items
  itemFactory: index => ({ index, value: `Item ${index}` })
});

// Get items from the virtual array
const item = await virtualArray.getItem(500000);

// Process in chunks
for await (const chunk of virtualArray.iterateChunks(1000)) {
  // Process each chunk of 1000 items
}
```

### Neural Network Training

```javascript
// Create a data provider for training
const dataProvider = Prime.Storage.createDataProvider(storageManager, {
  inputId: 'training-inputs',
  outputId: 'training-outputs',
  batchSize: 32,
  shuffle: true
});

// Train a model
await model.train({
  dataProvider,
  epochs: 10,
  learningRate: 0.01
});
```

## Configuration

```javascript
const storageManager = Prime.Storage.createManager({
  // Storage provider to use ('auto', 'memory', 'indexeddb', 'filesystem')
  provider: 'auto',
  
  // Path for filesystem storage (Node.js only)
  storagePath: '/tmp/primeos-storage',
  
  // Size of chunks for large data (in bytes)
  chunkSize: 1048576, // 1MB
  
  // Whether to use swap space for memory management
  useSwapSpace: true,
  
  // Maximum memory usage before swapping (in bytes)
  maxMemoryUsage: 100 * 1024 * 1024, // 100MB
  
  // Whether to compress stored data
  compression: false
});
```

## Error Handling

```javascript
try {
  await storageManager.store(data);
} catch (error) {
  if (error instanceof Prime.Storage.StorageError) {
    console.error(`Storage error: ${error.message}, Code: ${error.code}`);
  }
}
```