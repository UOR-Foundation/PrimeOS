/**
 * PrimeOS JavaScript Library - Consolidated Distributed Neural Model Test
 * Tests the consolidated implementation of the distributed neural model
 */

const Prime = require("../../../src/core.js");
require("../../../src/mathematics.js");
require("../../../src/math/vector.js");
require("../../../src/math/matrix.js");
require("../../../src/coherence.js");
require("../../../src/distributed/index.js");
require("../../../src/distributed/coherence.js");
require("../../../src/neural/index.js");
require("../../../src/neural/model.js");

// Mock the Neural.Model.NeuralModel class to avoid inheritance issues
Prime.Neural = Prime.Neural || {};
Prime.Neural.Model = Prime.Neural.Model || {};
Prime.Neural.Model.NeuralModel = class NeuralModel {
  constructor(config = {}) {
    this.inputSize = config.inputSize || 10;
    this.layers = [];
    this.metrics = {
      iteration: 0,
      accuracy: 0.5,
      loss: 1.0
    };
    
    if (Array.isArray(config.layers)) {
      for (const layerConfig of config.layers) {
        this.addLayer(layerConfig);
      }
    }
  }
  
  addLayer(layerConfig) {
    const layer = {
      inputSize: layerConfig.inputSize || (this.layers.length > 0 ? this.layers[this.layers.length - 1].outputSize : this.inputSize),
      outputSize: layerConfig.outputSize || 10,
      type: layerConfig.type || 'dense',
      activation: layerConfig.activation || 'relu',
      weights: [],
      biases: []
    };
    
    // Mock weights and biases for testing
    for (let i = 0; i < layer.inputSize; i++) {
      layer.weights[i] = [];
      for (let j = 0; j < layer.outputSize; j++) {
        layer.weights[i][j] = 0.1;
      }
    }
    
    for (let i = 0; i < layer.outputSize; i++) {
      layer.biases[i] = 0.01;
    }
    
    this.layers.push(layer);
    return this;
  }
  
  async train() {
    this.metrics.iteration++;
    return { loss: 0.1 };
  }
};

// Now load the consolidated module
const consolidatedModule = require("../../../src/neural/distributed/index-consolidated.js");
const ConsolidatedModel = consolidatedModule.DistributedNeuralModel;

// Mock the Prime.Logger
Prime.Logger = {
  debug: jest.fn(),
  info: jest.fn(),
  warn: jest.fn(),
  error: jest.fn()
};

describe('Consolidated Distributed Neural Model', () => {
  // Create a mock cluster manager for testing
  const mockClusterManager = {
    nodes: new Map([
      ['node1', { id: 'node1', performance: { compute: 1.0 } }],
      ['node2', { id: 'node2', performance: { compute: 1.2 } }]
    ]),
    register: jest.fn(() => 'local-node'),
    getActiveNodes: jest.fn(() => ['node1', 'node2']),
    getNodeParameters: jest.fn(() => [
      {
        weights: [[[0.1, 0.2], [0.3, 0.4]], [[0.5, 0.6], [0.7, 0.8]]],
        biases: [[0.1, 0.2], [0.3, 0.4]],
        layerConfig: [
          { inputSize: 2, outputSize: 2, type: 'dense' },
          { inputSize: 2, outputSize: 2, type: 'dense' }
        ],
        metadata: {
          extractionTime: Date.now(),
          performance: { accuracy: 0.8, loss: 0.2 }
        }
      }
    ])
  };

  let model;

  beforeEach(() => {
    // Create a new model for each test
    model = new ConsolidatedModel({
      inputSize: 2,
      layers: [
        { type: 'dense', outputSize: 2, activation: 'relu' },
        { type: 'dense', outputSize: 2, activation: 'sigmoid' }
      ],
      distributed: { 
        enabled: true,
        clusterManager: mockClusterManager,
        synchronizationStrategy: 'average' // Use 'average' instead of 'weighted_average' for simplicity
      }
    });
  });

  test('Model initialization with correct input size', () => {
    expect(model.inputSize).toBe(2);
    expect(model.originalInputSize).toBe(2);
    expect(model.layers.length).toBe(2);
  });

  test('Layer dimensions are properly maintained', () => {
    expect(model.layers[0].inputSize).toBe(2);
    expect(model.layers[0].outputSize).toBe(2);
    expect(model.layers[1].inputSize).toBe(2);
    expect(model.layers[1].outputSize).toBe(2);
  });

  test('Distributed configuration is properly set', () => {
    expect(model.distributedConfig.enabled).toBe(true);
    expect(model.distributedConfig.synchronizationStrategy).toBe('average');
    expect(model.distributedState.isInitialized).toBe(true);
  });

  test('Parameter extraction returns correct structure', () => {
    const params = model._extractModelParameters();
    
    expect(params).toHaveProperty('weights');
    expect(params).toHaveProperty('biases');
    expect(params).toHaveProperty('layerConfig');
    expect(params).toHaveProperty('metadata');
    
    expect(params.weights.length).toBe(2);
    expect(params.biases.length).toBe(2);
    expect(params.layerConfig.length).toBe(2);
    
    expect(params.metadata.modelConfig.inputSize).toBe(2);
  });

  test('Model training should call synchronizeParameters when needed', async () => {
    // Mock synchronizeParameters to check if it's called
    model.synchronizeParameters = jest.fn().mockResolvedValue(true);
    
    // Set config to synchronize every 5 iterations
    model.distributedConfig.syncFrequency = 5;
    
    // Train for 10 iterations
    for (let i = 0; i < 10; i++) {
      await model.train([1, 2], [1, 1]);
    }
    
    // Should call synchronizeParameters twice (at iterations 5 and 10)
    expect(model.synchronizeParameters).toHaveBeenCalledTimes(2);
  });

  test('Model training should NOT call synchronizeParameters when disabled', async () => {
    // Mock synchronizeParameters to check if it's called
    model.synchronizeParameters = jest.fn().mockResolvedValue(true);
    
    // Disable distributed functionality
    model.distributedConfig.enabled = false;
    
    // Train for 10 iterations
    for (let i = 0; i < 10; i++) {
      await model.train([1, 2], [1, 1]);
    }
    
    // Should never call synchronizeParameters when disabled
    expect(model.synchronizeParameters).not.toHaveBeenCalled();
  });

  test('Model should create and use checkpoints', () => {
    // Create a checkpoint
    expect(model.createCheckpoint()).toBe(true);
    
    // Should have one checkpoint
    expect(model.distributedState.checkpoints.length).toBe(1);
    
    // Set a test value in the model's weights
    model.layers[0].weights[0][0] = 99.9;
    
    // Rollback should restore the original value
    expect(model._rollbackToCheckpoint()).toBe(true);
    
    // Original value should be restored (0.1 was our test mock value)
    expect(model.layers[0].weights[0][0]).toBe(0.1);
  });
});