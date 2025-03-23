/**
 * PrimeOS JavaScript Library - Storage Integration Tests
 * Tests integration with other PrimeOS systems
 */

const Prime = require('../../src');

describe('PrimeOS Storage Integration', () => {
  let storageManager;

  beforeEach(async () => {
    storageManager = Prime.Storage.createManager();
    await storageManager.init();
  });

  describe('Matrix Integration', () => {
    it('should support large matrices via swappable storage', async () => {
      // Create a large matrix that would normally strain memory
      const rows = 2000;
      const cols = 2000;
      const matrix = new Prime.Math.Matrix(rows, cols);
      
      // Fill with deterministic values
      for (let i = 0; i < rows; i++) {
        for (let j = 0; j < cols; j++) {
          matrix.set(i, j, (i * j) % 1000);
        }
      }
      
      // Store the matrix
      const id = await storageManager.store(matrix);
      
      // Create a swappable proxy matrix that keeps only part in memory
      const swappableMatrix = await Prime.Storage.createSwappableMatrix(storageManager, id, {
        blockSize: 200, // Work with 200x200 blocks
        maxCachedBlocks: 10, // Keep only 10 blocks in memory at once
      });
      
      // Verify values from different parts of the matrix
      expect(swappableMatrix.get(0, 0)).toBe(0);
      expect(swappableMatrix.get(10, 10)).toBe(100);
      expect(swappableMatrix.get(500, 500)).toBe(500 * 500 % 1000);
      expect(swappableMatrix.get(1500, 1500)).toBe(1500 * 1500 % 1000);
      
      // Test matrix operations with the swappable matrix
      const trace = swappableMatrix.trace();
      
      // Calculate expected trace
      let expectedTrace = 0;
      for (let i = 0; i < Math.min(rows, cols); i++) {
        expectedTrace += (i * i) % 1000;
      }
      
      expect(trace).toBeCloseTo(expectedTrace);
    });
  });

  describe('Neural Model Integration', () => {
    it('should store and load neural model weights', async () => {
      // Create a neural model
      const model = new Prime.Neural.Model({
        name: 'TestModel',
        layers: [
          new Prime.Neural.Layer.Dense(10, 20),
          new Prime.Neural.Layer.Dense(20, 5),
        ],
      });
      
      // Initialize with random weights
      model.initializeWeights();
      
      // Store the model weights
      const id = await storageManager.storeModel(model, 'test-model');
      
      // Create a new empty model with the same architecture
      const newModel = new Prime.Neural.Model({
        name: 'TestModel',
        layers: [
          new Prime.Neural.Layer.Dense(10, 20),
          new Prime.Neural.Layer.Dense(20, 5),
        ],
      });
      
      // Load the weights
      await storageManager.loadModelWeights(newModel, id);
      
      // Compare weights between models
      const originalWeights = model.getLayer(0).weights;
      const loadedWeights = newModel.getLayer(0).weights;
      
      expect(loadedWeights.rows).toBe(originalWeights.rows);
      expect(loadedWeights.columns).toBe(originalWeights.columns);
      
      // Check sample values
      expect(loadedWeights.get(0, 0)).toBe(originalWeights.get(0, 0));
      expect(loadedWeights.get(5, 5)).toBe(originalWeights.get(5, 5));
    });

    it('should support training with data from storage', async () => {
      // Create large training dataset
      const inputSize = 10;
      const outputSize = 2;
      const sampleCount = 1000;
      
      const inputs = new Array(sampleCount).fill(0).map(() => 
        new Array(inputSize).fill(0).map(() => Math.random())
      );
      
      const outputs = new Array(sampleCount).fill(0).map(() => 
        new Array(outputSize).fill(0).map(() => Math.random())
      );
      
      // Store the training data
      const inputsId = await storageManager.store(inputs, 'training-inputs');
      const outputsId = await storageManager.store(outputs, 'training-outputs');
      
      // Create a model
      const model = new Prime.Neural.Model({
        name: 'TrainingTestModel',
        layers: [
          new Prime.Neural.Layer.Dense(inputSize, 15),
          new Prime.Neural.Layer.Dense(15, outputSize)
        ],
      });
      
      model.initializeWeights();
      
      // Create a data provider that reads from storage in batches
      const dataProvider = Prime.Storage.createDataProvider(storageManager, {
        inputId: inputsId,
        outputId: outputsId,
        batchSize: 32
      });
      
      // Train for a few epochs
      await model.train({
        dataProvider,
        epochs: 3,
        learningRate: 0.01,
        optimizer: 'sgd'
      });
      
      // Verify model weights were updated
      const weights = model.getLayer(0).weights;
      for (let i = 0; i < 5; i++) {
        for (let j = 0; j < 5; j++) {
          expect(Math.abs(weights.get(i, j))).toBeGreaterThan(0);
        }
      }
    });
  });

  describe('Distributed Computing Integration', () => {
    it('should store and load distributed task states', async () => {
      // Create distributed task state
      const taskState = {
        taskId: 'dist-task-1',
        nodes: ['node1', 'node2', 'node3'],
        progress: 0.5,
        partitioning: {
          type: 'block',
          dimensions: [1000, 1000],
          blockSize: [200, 200]
        },
        metadata: {
          created: Date.now(),
          priority: 'high'
        }
      };
      
      // Store the task state
      await storageManager.store(taskState, 'task-state:dist-task-1');
      
      // Retrieve the task state
      const retrievedState = await storageManager.load('task-state:dist-task-1');
      
      expect(retrievedState).toEqual(taskState);
    });

    it('should share data between distributed nodes via storage', async () => {
      // This test simulates the communication between distributed nodes
      // using the storage provider as a shared data transport
      
      // Create data for node 1
      const node1Data = { 
        nodeId: 'node1', 
        results: [1, 2, 3, 4, 5],
        timestamp: Date.now()
      };
      
      // Store data from node 1
      await storageManager.store(node1Data, 'node-data:node1');
      
      // Simulate node 2 reading node 1's data
      const node1DataFromNode2 = await storageManager.load('node-data:node1');
      expect(node1DataFromNode2).toEqual(node1Data);
      
      // Node 2 creates response data
      const node2Response = {
        nodeId: 'node2',
        receivedFrom: 'node1',
        responseData: [5, 6, 7, 8, 9],
        timestamp: Date.now()
      };
      
      // Store response from node 2
      await storageManager.store(node2Response, 'node-response:node1:node2');
      
      // Simulate node 1 reading node 2's response
      const node2ResponseFromNode1 = await storageManager.load('node-response:node1:node2');
      expect(node2ResponseFromNode1).toEqual(node2Response);
    });
  });

  describe('Framework Component Integration', () => {
    it('should persist component state', async () => {
      // Create a Prime component
      const component = Prime.createComponent({
        name: 'TestStorageComponent',
        state: {
          counter: 0,
          items: ['item1', 'item2'],
          config: { enabled: true }
        },
        methods: {
          increment() { this.state.counter++; },
          addItem(item) { this.state.items.push(item); }
        }
      });
      
      // Modify the component state
      component.methods.increment();
      component.methods.increment();
      component.methods.addItem('item3');
      
      // Persist the component state
      await storageManager.storeComponentState(component, 'test-component');
      
      // Create a new component with the same structure
      const newComponent = Prime.createComponent({
        name: 'TestStorageComponent',
        state: {
          counter: 0,
          items: [],
          config: { enabled: false }
        },
        methods: {
          increment() { this.state.counter++; },
          addItem(item) { this.state.items.push(item); }
        }
      });
      
      // Load the persisted state
      await storageManager.loadComponentState(newComponent, 'test-component');
      
      // Verify state was loaded correctly
      expect(newComponent.state.counter).toBe(2);
      expect(newComponent.state.items).toEqual(['item1', 'item2', 'item3']);
      expect(newComponent.state.config.enabled).toBe(true);
    });
  });

  describe('Coherence Verification', () => {
    it('should maintain coherence when loading stored mathematical objects', async () => {
      // Create a coherent mathematical structure
      const manifold = new Prime.Base0.Manifold({
        dimensions: 3,
        metric: Prime.Math.Matrix.identity(3)
      });
      
      // Verify initial coherence
      const initialCoherence = Prime.coherence.verify(manifold);
      expect(initialCoherence.valid).toBe(true);
      
      // Store the manifold
      const id = await storageManager.store(manifold, 'test-manifold');
      
      // Load the manifold
      const loadedManifold = await storageManager.load(id);
      
      // Verify coherence of loaded object
      const loadedCoherence = Prime.coherence.verify(loadedManifold);
      expect(loadedCoherence.valid).toBe(true);
      
      // Perform operations on the loaded object
      const point = [1, 0, 0];
      const tangentVector = [0, 1, 0];
      
      const geodesic = loadedManifold.computeGeodesic(point, tangentVector);
      expect(geodesic).toBeDefined();
      
      // Verify coherence is maintained after operations
      const finalCoherence = Prime.coherence.verify(loadedManifold);
      expect(finalCoherence.valid).toBe(true);
    });
  });
});