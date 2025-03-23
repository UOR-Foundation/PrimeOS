# PrimeOS Storage Provider

## Overview
The storage provider for PrimeOS addresses memory limitations when processing large datasets by offering persistent storage solutions across different environments:

1. **Browser Storage** - Using IndexedDB for browser environments
2. **Host Platform Storage** - Using filesystem for Node.js and other host environments

This package allows PrimeOS to:
- Stream data in and out of memory
- Process datasets larger than available RAM
- Persist application and user data
- Provide a unified API across environments

## Architecture

```
src/
└── storage/
    ├── index.js            # Main entry point and exports
    ├── types.js            # Type definitions using JSDoc
    ├── core/
    │   ├── provider.js     # Abstract storage provider interface
    │   ├── manager.js      # Storage manager orchestration
    │   ├── serializer.js   # Data serialization/encoding utilities 
    │   └── chunk.js        # Data chunking utilities
    ├── browser/
    │   ├── indexeddb.js    # IndexedDB implementation
    │   └── utils.js        # Browser-specific utilities
    ├── node/
    │   ├── filesystem.js   # Filesystem implementation
    │   └── utils.js        # Node-specific utilities
    └── adapters/           # Optional adapters for other systems
```

## Implementation Plan

### Phase 1: Core Infrastructure

- [x] Create storage.md with initial plan
- [ ] Create storage directory structure
- [ ] Define core provider interface
- [ ] Create serialization utilities
- [ ] Implement chunking mechanism

### Phase 2: Browser Implementation

- [ ] Implement IndexedDB storage provider
- [ ] Add browser detection and fallback
- [ ] Create browser-specific utilities

### Phase 3: Node.js Implementation

- [ ] Implement filesystem storage provider
- [ ] Add filesystem utilities and helpers
- [ ] Handle platform-specific paths

### Phase 4: Integration and Testing

- [ ] Integrate with PrimeOS core
- [ ] Create comprehensive test suite
- [ ] Document the API and usage
- [ ] Optimize performance

## API Design (Draft)

```javascript
// Basic Usage
const storageManager = PrimeOS.storage.createManager();
await storageManager.init();

// Storing data
const dataId = await storageManager.store(largeDataArray);

// Loading data
const data = await storageManager.load(dataId);

// Streaming API
const stream = storageManager.createReadStream(dataId);
stream.on('data', chunk => {
  // Process chunk
});

// Working with models
const model = createNeuralModel();
await storageManager.storeModel(model, 'my-model');
const loadedModel = await storageManager.loadModel('my-model');
```

## Progress Tracking
- [x] Initial storage.md created
- [x] Core framework complete
- [x] Browser implementation complete
- [x] Node.js implementation complete
- [x] Basic tests passing
- [x] Example created and working
- [x] Documentation complete

## Implementation Status
The storage provider has been successfully implemented with all core functionality working. The basic building blocks are in place, and the storage module is ready for use in PrimeOS applications.

### Key Features Implemented:
- Storage manager with environment-aware provider selection
- Memory, IndexedDB, and filesystem storage providers
- Chunking and serialization for large datasets
- Streaming API for efficient data processing
- Memory management with swap space
- Error handling and documentation

### Next Steps:
- ✅ Enhance integration tests to work with actual PrimeOS Matrix and Neural implementations
- ✅ Add browser tests for storage integration
- Add compression support for stored data
- Implement distributed storage capabilities
- Add encryption for sensitive data

## Integration with PrimeOS Components

The storage module now fully integrates with PrimeOS Matrix and Neural implementations in both Node.js and browser environments:

### Cross-Environment Support

The storage system automatically detects the current environment and uses the appropriate storage backend:

- **Browser Environment**: Uses IndexedDB for persistent storage
- **Node.js Environment**: Uses filesystem for persistent storage
- **Fallback**: Uses in-memory storage if neither is available

```javascript
// Matrix Integration
const matrix = Prime.Math.Matrix.create(1000, 1000);
// Fill the matrix with data...

// Create swappable matrix backed by storage
const storageManager = Prime.Storage.createManager();
await storageManager.init();
const swappableMatrix = await Prime.Storage.createSwappableMatrixFromMatrix(
  storageManager, 
  matrix, 
  'large-matrix', 
  { blockSize: 100, maxCachedBlocks: 10 }
);

// Use the swappable matrix with standard matrix operations
const standardMatrix = await swappableMatrix.toMatrix();
const transposed = Prime.Math.Matrix.transpose(standardMatrix);

// Neural Model Integration
const model = new Prime.Neural.Model.NeuralModel({
  layers: [
    { type: 'dense', inputSize: 10, outputSize: 5, activation: 'sigmoid' },
    { type: 'dense', inputSize: 5, outputSize: 1, activation: 'sigmoid' }
  ],
  optimizer: { type: 'adam', learningRate: 0.01 }
});

// Store the model
const modelId = await Prime.Storage.storeModel(storageManager, model, 'my-model');

// Load the model later
const loadedModel = await Prime.Storage.loadModel(storageManager, modelId);
```