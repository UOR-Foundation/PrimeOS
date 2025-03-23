# PrimeOS JavaScript Library

A neural network-based operating system built on the Prime Framework, representing a fundamental shift in computing paradigms. Rather than traditional procedural execution, PrimeOS treats computation as a neural network process governed by mathematical coherence principles.

## Features

- **Coherence-Driven Computing**: All operations optimize for mathematical coherence, ensuring consistency across the system
- **Universal Component Model**: Consistent design patterns applied across all system levels
- **Functional Interface**: Pure functions and immutable data structures used throughout the system
- **Neural Computation**: All components implemented as neural network models
- **Resource Optimization**: Intelligent allocation based on coherence requirements
- **Extreme Condition Handling**: Robust numerical computations for demanding scientific applications (e.g., RNA folding)
  - Enhanced SVD implementation handles extreme values (>1e100 or <1e-100) with dynamic algorithm selection
  - Adaptive scaling for numerical stability in matrix operations
- **Storage Provider**: Persistent storage with support for data larger than available memory

## Mathematical Foundation

PrimeOS is built on the Universal Object Reference (UOR) framework, which provides the mathematical foundation for the system:

- **Clifford Algebras**: Geometric algebras serve as the mathematical foundation for representing data and operations
- **Coherence and Inner Product Norms**: Mathematical coherence measures how well system components satisfy constraints
- **Lie Groups**: Employed as symmetry operations that transform elements in the system
- **Robust Matrix Operations**: Specialized numerical implementations with extreme value handling
  - SVD with multi-algorithm approach (Jacobi, QR, Power Iteration)
  - Adaptive tolerance calculation for precision control
  - Automatic scaling for matrices with extreme value ranges
  - Pairwise and compensated summation for numerical stability

## Prime Framework Architecture

PrimeOS is organized into four hierarchical bases:

1. **Base 0: Neural Network Specification** - Abstract mathematical foundation
2. **Base 1: Resource** - Lowest-level concrete implementation
3. **Base 2: Kernel** - Orchestrator of the system
4. **Base 3: Application** - User-space applications

## Installation

### From npm (once published)
```bash
npm install primeos
```

### Directly from GitHub
```bash
npm install UOR-Foundation/PrimeOS
```

### From GitHub Packages
```bash
# Add this to your .npmrc
@uor-foundation:registry=https://npm.pkg.github.com

# Then install
npm install @uor-foundation/primeos
```

## Usage

```javascript
import Prime from '@uor-foundation/primeos';

// Create a Prime Framework instance
const framework = Prime.createPrimeFramework();

// Create an application
const app = framework.createApplication({
  name: 'TestApp',
  behavior: {
    actions: {
      increment: (state) => ({ count: state.count + 1 }),
      decrement: (state) => ({ count: state.count - 1 })
    },
    initialState: {
      count: 0
    }
  },
  structure: {
    components: [
      {
        type: 'div',
        props: { id: 'counter' },
        children: [
          {
            type: 'span',
            props: { innerText: (state) => `Count: ${state.count}` }
          }
        ]
      }
    ]
  }
});

// Start the application
app.start();
```

### Using Storage Provider

```javascript
import Prime from '@uor-foundation/primeos';

// Create and initialize a storage manager
const storageManager = Prime.Storage.createManager();
await storageManager.init();

// Store large datasets
const largeData = /* large array or object */;
const id = await storageManager.store(largeData);

// Retrieve data
const retrievedData = await storageManager.load(id);

// Work with data larger than memory using virtual arrays
const virtualArray = Prime.Storage.createVirtualArray(storageManager, {
  length: 1000000, // 1 million items
  itemFactory: index => ({ id: index, value: `Item ${index}` })
});

// Process in manageable chunks
for await (const chunk of virtualArray.iterateChunks(1000)) {
  // Process chunk without loading entire dataset
}
```

### Matrix Storage Integration

```javascript
import Prime from '@uor-foundation/primeos';

// Create a large matrix
const rows = 5000;
const cols = 5000;
const matrix = Prime.Math.Matrix.create(rows, cols);

// Fill with data
for (let i = 0; i < rows; i++) {
  for (let j = 0; j < cols; j++) {
    matrix[i][j] = (i * j) % 1000;
  }
}

// Create a storage manager
const storageManager = Prime.Storage.createManager();
await storageManager.init();

// Store the large matrix
const swappableMatrix = await Prime.Storage.createSwappableMatrixFromMatrix(
  storageManager,
  matrix,
  'my-large-matrix',
  {
    blockSize: 100, // Work with 100x100 blocks
    maxCachedBlocks: 10 // Keep only 10 blocks in memory at once
  }
);

// Free original matrix from memory
matrix = null;

// Work with the swappable matrix
const value = await swappableMatrix.get(500, 500);
await swappableMatrix.set(500, 500, 42);
const submatrix = await swappableMatrix.submatrix(400, 400, 600, 600);
const standardMatrix = await swappableMatrix.toMatrix();
```

### Neural Model Storage and Training

```javascript
import Prime from '@uor-foundation/primeos';

// Create a neural model
const model = new Prime.Neural.Model.NeuralModel({
  layers: [
    { type: 'dense', inputSize: 10, outputSize: 20, activation: 'relu' },
    { type: 'dense', inputSize: 20, outputSize: 5, activation: 'softmax' }
  ],
  optimizer: { type: 'adam', learningRate: 0.01 }
});

// Compile the model
model.compile({ loss: 'categoricalCrossEntropy', metric: 'accuracy' });

// Create a storage manager
const storageManager = Prime.Storage.createManager();
await storageManager.init();

// Store large training data
const trainingInputs = /* large array of input data */;
const trainingOutputs = /* large array of expected outputs */;

const inputId = await storageManager.store(trainingInputs, 'training-inputs');
const outputId = await storageManager.store(trainingOutputs, 'training-outputs');

// Create a data provider that streams data from storage
const dataProvider = Prime.Storage.createDataProvider(storageManager, {
  inputId,
  outputId,
  batchSize: 32,
  shuffle: true
});

// Train using mini-batches from storage
for (let epoch = 0; epoch < 10; epoch++) {
  for (let i = 0; i < 100; i++) {
    const batch = await dataProvider.nextBatch();
    const result = model.trainOnBatch(batch.inputs, batch.outputs);
    console.log(`Batch ${i}, Loss: ${result.loss}`);
  }
}

// Store the trained model
await Prime.Storage.storeModel(storageManager, model, 'my-trained-model');

// Later, load the model
const loadedModel = await Prime.Storage.loadModel(storageManager, 'my-trained-model');
```

## Documentation

Comprehensive documentation is available in the [primeos-spec.md](./primeos-spec.md) file.

## Testing

PrimeOS has a comprehensive testing suite with tiered strategies for various environments:

### Test Categories

1. **CI-Safe Tests**: Core modules that run in CI environments
   - Core tests (core functionality)
   - Mathematics tests (mathematical operations)
   - Framework tests (framework components)
   - Coherence tests (coherence validation)

2. **Memory-Intensive Tests**: Require significant RAM (8GB+)
   - Extreme condition tests (numerical stability)
   - UOR verification tests (universal object references)
   - Integration tests (cross-module functionality)
   - End-to-End verification tests (unique PrimeOS capabilities)

3. **Browser Tests**: Testing in browser environments
   - Uses Puppeteer to launch a headless browser
   - Validates browser-specific functionality

### Running Tests

```bash
# Run CI-safe tests (used in CI/CD pipelines and publishing)
npm run test:ci

# Run individual test categories
npm test                # Standard tests (excludes memory-intensive tests)
npm run test:extreme    # Extreme condition tests (high memory usage)
npm run test:uor        # UOR verification tests (high memory usage)
npm run test:integration # Integration tests
npm run test:browser    # Browser environment tests
npm run test:verify     # End-to-End verification (unique PrimeOS capabilities)

# Run distributed coherence tests
npm run test:coherence         # Run distributed coherence tests
npm run test:coherence:bench   # Run distributed coherence benchmarks
npm run test:coherence:mock    # Run mock distributed network simulation

# Run complete test suite (all tests)
npm run test:all
```

See [KNOWN-ISSUES.md](./KNOWN-ISSUES.md) for more details on the testing strategy and known limitations.

## License

MIT