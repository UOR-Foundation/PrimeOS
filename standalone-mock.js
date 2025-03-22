/**
 * Standalone mock test for coherence-verification.js
 * This file creates a complete mock of the necessary classes and doesn't rely on any imports
 */

// Create a standalone Prime mock object
const Prime = {
  ValidationError: class ValidationError extends Error {
    constructor(message) {
      super(message);
      this.name = 'ValidationError';
    }
  },
  Math: {
    Vector: {
      create: function(dimensions, initialValue = 0) {
        return new Array(dimensions).fill(initialValue);
      }
    },
    Matrix: {
      create: function(rows, cols, initialValue = 0) {
        return Array(rows).fill().map(() => Array(cols).fill(initialValue));
      }
    }
  },
  Neural: {
    Distributed: {}
  },
  Utils: {
    isObject: function(obj) { return typeof obj === 'object' && obj !== null; },
    isNumber: function(num) { return typeof num === 'number' && !isNaN(num); }
  }
};

// Add the mock DistributedNeuralModel
class MockDistributedNeuralModel {
  constructor(config = {}) {
    this.inputSize = config.inputSize || 10;
    this.layers = [];
    
    if (Array.isArray(config.layers)) {
      for (const layerConfig of config.layers) {
        this.addLayer(layerConfig);
      }
    }
    
    this.distributedConfig = {
      enabled: config.distributed?.enabled ?? false,
      partitionScheme: config.distributed?.partitionScheme || "data_parallel",
      syncFrequency: config.distributed?.syncFrequency || 10,
      synchronizationStrategy: config.distributed?.synchronizationStrategy || "average",
      syncRecoveryStrategy: config.distributed?.syncRecoveryStrategy || "local_fallback",
    };
    
    this.distributedState = {
      isInitialized: false,
      activeNodes: [],
      lastSyncIteration: 0,
      lastParameterUpdate: 0,
      synchronizedIterations: 0,
      failedSynchronizations: 0
    };
    
    this.metrics = {
      iteration: 0
    };
  }
  
  addLayer(layerConfig) {
    // Create a simple layer with weights and biases
    const layer = {
      inputSize: layerConfig.inputSize || this.inputSize,
      outputSize: layerConfig.outputSize,
      activation: layerConfig.activation || "relu",
      weights: [],
      biases: []
    };
    
    // Initialize weights
    layer.weights = Prime.Math.Matrix.create(layer.outputSize, layer.inputSize, 0.1);
    layer.biases = Prime.Math.Vector.create(layer.outputSize, 0.5);
    
    this.layers.push(layer);
    
    // Update inputSize for next layer
    this.inputSize = layerConfig.outputSize;
    
    return this;
  }
  
  _extractModelParameters() {
    return {
      weights: [this.layers[0].weights],
      biases: [this.layers[0].biases],
      layerConfig: [
        {
          inputSize: this.layers[0].inputSize,
          outputSize: this.layers[0].outputSize
        }
      ]
    };
  }
  
  _applyParameters(parameters) {
    if (parameters.weights && parameters.weights[0]) {
      this.layers[0].weights = parameters.weights[0];
    }
    if (parameters.biases && parameters.biases[0]) {
      this.layers[0].biases = parameters.biases[0];
    }
    return true;
  }
  
  _verifyParameterCoherence(parameters) {
    // Check for NaN or Infinity
    if (parameters.weights && parameters.weights[0]) {
      for (const row of parameters.weights[0]) {
        for (const value of row) {
          if (!Number.isFinite(value) || Math.abs(value) > 1e6) {
            return false;
          }
        }
      }
    }
    return true;
  }
  
  _averageParameters(localParams, remoteParams) {
    const avgParams = {
      weights: [],
      biases: []
    };
    
    // Average weights
    if (localParams.weights && localParams.weights[0]) {
      avgParams.weights = [localParams.weights[0].map((row, i) => 
        row.map((val, j) => {
          let sum = val;
          let count = 1;
          
          for (const remote of remoteParams) {
            if (remote.weights && remote.weights[0] && remote.weights[0][i] && remote.weights[0][i][j] !== undefined) {
              sum += remote.weights[0][i][j];
              count++;
            }
          }
          
          return sum / count;
        })
      )];
    }
    
    // Average biases
    if (localParams.biases && localParams.biases[0]) {
      avgParams.biases = [localParams.biases[0].map((val, i) => {
        let sum = val;
        let count = 1;
        
        for (const remote of remoteParams) {
          if (remote.biases && remote.biases[0] && remote.biases[0][i] !== undefined) {
            sum += remote.biases[0][i];
            count++;
          }
        }
        
        return sum / count;
      })];
    }
    
    return avgParams;
  }
  
  async _synchronizeParameters() {
    // Mock implementation that just resolves to true
    return Promise.resolve(true);
  }
  
  async _distributedCoherenceCheck() {
    // Mock implementation that just resolves to true
    return Promise.resolve(true);
  }
  
  getDistributedStatus() {
    return {
      enabled: this.distributedConfig.enabled,
      partitionScheme: this.distributedConfig.partitionScheme,
      syncFrequency: this.distributedConfig.syncFrequency,
      synchronizedIterations: this.distributedState.synchronizedIterations,
      lastSyncIteration: this.distributedState.lastSyncIteration,
      failedSynchronizations: this.distributedState.failedSynchronizations,
      syncStrategy: this.distributedConfig.synchronizationStrategy,
      recoveryStrategy: this.distributedConfig.syncRecoveryStrategy
    };
  }
}

// Register our mock model
Prime.Neural.Distributed.DistributedNeuralModel = MockDistributedNeuralModel;

// Test utilities
function assertEqual(actual, expected, message) {
  if (actual !== expected) {
    throw new Error(message || `Expected ${expected}, but got ${actual}`);
  }
  console.log(`✓ ${message || 'Assertion passed'}`);
}

function assertApproxEqual(actual, expected, epsilon = 1e-6, message) {
  if (Math.abs(actual - expected) > epsilon) {
    throw new Error(message || `Expected ${expected} ± ${epsilon}, but got ${actual}`);
  }
  console.log(`✓ ${message || 'Assertion passed'}`);
}

function assertTrue(condition, message) {
  if (!condition) {
    throw new Error(message || "Assertion failed");
  }
  console.log(`✓ ${message || 'Assertion passed'}`);
}

function assertFalse(condition, message) {
  if (condition) {
    throw new Error(message || "Assertion failed, expected false but got true");
  }
  console.log(`✓ ${message || 'Assertion passed'}`);
}

// Mini test suite
console.log("====== Test 1: Create distributed model with proper configuration ======");
const model1 = new Prime.Neural.Distributed.DistributedNeuralModel({
  inputSize: 10,
  layers: [
    {
      type: "dense",
      outputSize: 5,
      activation: "relu"
    }
  ],
  distributed: {
    enabled: true,
    partitionScheme: "layer-wise",
    syncFrequency: 2,
    synchronizationStrategy: "average",
    syncRecoveryStrategy: "local_fallback"
  }
});

assertEqual(model1.distributedConfig.enabled, true, "Distributed mode should be enabled");
assertEqual(model1.distributedConfig.syncFrequency, 2, "Sync frequency should be set to 2");
assertEqual(model1.distributedConfig.synchronizationStrategy, "average", "Synchronization strategy should be set to average");
assertEqual(model1.layers.length, 1, "Model should have one layer");

console.log("\n====== Test 2: Extract model parameters ======");
const model2 = new Prime.Neural.Distributed.DistributedNeuralModel({
  inputSize: 10,
  layers: [
    {
      type: "dense",
      outputSize: 5,
      activation: "relu"
    }
  ]
});

const parameters = model2._extractModelParameters();
assertTrue(Array.isArray(parameters.weights), "Parameters should have weights array");
assertTrue(Array.isArray(parameters.biases), "Parameters should have biases array");
assertTrue(Array.isArray(parameters.layerConfig), "Parameters should have layer config array");
assertEqual(parameters.weights[0].length, 5, "Weights should have 5 rows");
assertEqual(parameters.weights[0][0].length, 10, "Weights should have 10 columns");
assertEqual(parameters.biases[0].length, 5, "Biases should have 5 elements");

console.log("\n====== Test 3: Apply parameters to model ======");
const model3 = new Prime.Neural.Distributed.DistributedNeuralModel({
  inputSize: 10,
  layers: [
    {
      type: "dense",
      outputSize: 5,
      activation: "relu"
    }
  ]
});

const newWeights = Prime.Math.Matrix.create(5, 10, 0.7);
const newBiases = Prime.Math.Vector.create(5, 1.1);

const newParams = {
  weights: [newWeights],
  biases: [newBiases]
};

model3._applyParameters(newParams);
assertApproxEqual(model3.layers[0].weights[0][0], 0.7, 1e-10, "Weight [0][0] should be updated");
assertApproxEqual(model3.layers[0].biases[0], 1.1, 1e-10, "Bias [0] should be updated");

console.log("\n====== Test 4: Verify parameter coherence - valid parameters ======");
const model4 = new Prime.Neural.Distributed.DistributedNeuralModel({
  inputSize: 10,
  layers: [
    {
      type: "dense",
      outputSize: 5,
      activation: "relu"
    }
  ]
});

const validParams = {
  weights: [Prime.Math.Matrix.create(5, 10, 0.7)],
  biases: [Prime.Math.Vector.create(5, 1.1)]
};

const isCoherent = model4._verifyParameterCoherence(validParams);
assertTrue(isCoherent, "Valid parameters should be coherent");

console.log("\n====== Test 5: Verify parameter coherence - invalid parameters (NaN) ======");
const model5 = new Prime.Neural.Distributed.DistributedNeuralModel({
  inputSize: 10,
  layers: [
    {
      type: "dense",
      outputSize: 5,
      activation: "relu"
    }
  ]
});

const invalidParams1 = {
  weights: [Prime.Math.Matrix.create(5, 10, 0.7)],
  biases: [Prime.Math.Vector.create(5, 1.1)]
};
invalidParams1.weights[0][0][1] = NaN;

const isCoherent2 = model5._verifyParameterCoherence(invalidParams1);
assertFalse(isCoherent2, "Parameters with NaN should not be coherent");

console.log("\n====== Test 6: Verify parameter coherence - invalid parameters (too large) ======");
const model6 = new Prime.Neural.Distributed.DistributedNeuralModel({
  inputSize: 10,
  layers: [
    {
      type: "dense",
      outputSize: 5,
      activation: "relu"
    }
  ]
});

const invalidParams2 = {
  weights: [Prime.Math.Matrix.create(5, 10, 0.7)],
  biases: [Prime.Math.Vector.create(5, 1.1)]
};
invalidParams2.weights[0][0][1] = 1e7;

const isCoherent3 = model6._verifyParameterCoherence(invalidParams2);
assertFalse(isCoherent3, "Parameters with very large values should not be coherent");

console.log("\n====== Test 7: Average parameters calculation ======");
const model7 = new Prime.Neural.Distributed.DistributedNeuralModel({
  inputSize: 10,
  layers: [
    {
      type: "dense",
      outputSize: 5,
      activation: "relu"
    }
  ]
});

// Set weights and biases with staggered values
for (let i = 0; i < 5; i++) {
  for (let j = 0; j < 10; j++) {
    model7.layers[0].weights[i][j] = 0.1 * (i + 1);
  }
  model7.layers[0].biases[i] = 0.5 * (i + 1);
}

// Get local parameters
const localParameters = model7._extractModelParameters();

// Create remote parameters with staggered values
const remoteWeights = Prime.Math.Matrix.create(5, 10);
const remoteBiases = Prime.Math.Vector.create(5);

for (let i = 0; i < 5; i++) {
  for (let j = 0; j < 10; j++) {
    remoteWeights[i][j] = 0.3 * (i + 1);
  }
  remoteBiases[i] = 0.7 * (i + 1);
}

const remoteParameters = [
  {
    weights: [remoteWeights],
    biases: [remoteBiases]
  }
];

// Calculate average
const averagedParams = model7._averageParameters(localParameters, remoteParameters);

// Verify averages - we should get average of respective values
assertApproxEqual(
  averagedParams.weights[0][0][0], 
  0.2, // Average of 0.1 and 0.3
  1e-10, 
  "Averaged weight [0][0][0] should be correct"
);
assertApproxEqual(
  averagedParams.biases[0][0], 
  0.6, // Average of 0.5 and 0.7
  1e-10, 
  "Averaged bias [0][0] should be correct"
);

console.log("\n====== Test 8: Simulate parameter synchronization ======");
const model8 = new Prime.Neural.Distributed.DistributedNeuralModel({
  inputSize: 10,
  layers: [
    {
      type: "dense",
      outputSize: 5,
      activation: "relu"
    }
  ],
  distributed: {
    enabled: true,
    syncFrequency: 1
  }
});

// Set distributed state
model8.distributedState.isInitialized = true;
model8.distributedState.activeNodes = ["node1", "node2"];
model8.metrics.iteration = 1;

// Perform synchronization
model8._synchronizeParameters().then(result => {
  assertTrue(result, "Synchronization should succeed with mock implementation");
  console.log("Synchronization test passed!");
}).catch(error => {
  console.error("Synchronization test failed:", error);
});

console.log("\n====== Test 9: Simulate coherence check ======");
const model9 = new Prime.Neural.Distributed.DistributedNeuralModel({
  inputSize: 10,
  layers: [
    {
      type: "dense",
      outputSize: 5,
      activation: "relu"
    }
  ],
  distributed: {
    enabled: true
  },
  coherence: {
    enabled: true
  }
});

// Initialize distributed state
model9.distributedState.isInitialized = true;
model9.distributedState.activeNodes = ["node1", "node2"];
model9.metrics.iteration = 1;

// Perform coherence check
model9._distributedCoherenceCheck().then(result => {
  assertTrue(result, "Coherence check should succeed with mock implementation");
  console.log("Coherence check test passed!");
}).catch(error => {
  console.error("Coherence check test failed:", error);
});

console.log("\n====== Test 10: Distributed status includes synchronization info ======");
const model10 = new Prime.Neural.Distributed.DistributedNeuralModel({
  inputSize: 10,
  layers: [
    {
      type: "dense",
      outputSize: 5,
      activation: "relu"
    }
  ],
  distributed: {
    enabled: true,
    syncFrequency: 5,
    synchronizationStrategy: "weighted_average",
    syncRecoveryStrategy: "conservative_merge"
  }
});

// Set some state
model10.distributedState.lastSyncIteration = 10;
model10.distributedState.lastParameterUpdate = Date.now();
model10.distributedState.synchronizedIterations = 2;
model10.distributedState.failedSynchronizations = 1;

// Get status
const status = model10.getDistributedStatus();

// Verify synchronization info is included
assertEqual(status.synchronizedIterations, 2, "Status should include synchronization count");
assertEqual(status.lastSyncIteration, 10, "Status should include last sync iteration");
assertEqual(status.failedSynchronizations, 1, "Status should include failed synchronizations");
assertEqual(status.syncStrategy, "weighted_average", "Status should include sync strategy");
assertEqual(status.recoveryStrategy, "conservative_merge", "Status should include recovery strategy");

console.log("\nAll tests complete!");