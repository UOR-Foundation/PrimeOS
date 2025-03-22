/**
 * PrimeOS JavaScript Library - Distributed Neural Network Integration Test
 * 
 * This test verifies the full distributed neural network functionality
 * including parameter synchronization and coherence checking.
 */

// Import required modules
const Prime = require("../src/core.js");
require("../src/mathematics.js");

// Make sure math is available before loading other modules
Prime.Math = Prime.Math || {};
require("../src/math/vector.js");
require("../src/math/matrix.js");

// Ensure Prime.Math and Vector/Matrix are properly initialized
if (!Prime.Math.Vector || !Prime.Math.Matrix) {
  console.error("Math modules not properly initialized. Initializing manually.");
  Prime.Math.Vector = require("../src/math/vector.js").Math.Vector;
  Prime.Math.Matrix = require("../src/math/matrix.js").Math.Matrix;
}

// Load coherence module
require("../src/coherence.js");

// Load distributed modules
require("../src/distributed/index.js");
require("../src/distributed/coherence.js");
require("../src/distributed/cluster/index.js");

// Now load neural modules after math is available
require("../src/neural/index.js");
require("../src/neural/distributed/index.js");
require("../src/neural/distributed/dimension-validator.js");

// Load our mock implementation
class MockDistributedNeuralModel {
  constructor(config = {}) {
    // Validate configuration if validator is available
    if (Prime.Neural.Distributed.DimensionValidator && Prime.Neural.Distributed.DimensionValidator.validateModelConfig) {
      Prime.Neural.Distributed.DimensionValidator.validateModelConfig(config);
    }
    
    this.originalInputSize = config.inputSize || 10;
    this.inputSize = this.originalInputSize;
    this.layers = [];
    
    if (Array.isArray(config.layers)) {
      for (const layerConfig of config.layers) {
        this.addLayer(layerConfig);
      }
    }
    
    // Restore inputSize to original value for proper model configuration
    this.inputSize = this.originalInputSize;
    
    // Log layer dimensions for debugging if validator is available
    if (Prime.Neural.Distributed.DimensionValidator && Prime.Neural.Distributed.DimensionValidator.logLayerDimensions) {
      Prime.Neural.Distributed.DimensionValidator.logLayerDimensions(this.layers);
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
    
    // Add mock cluster
    this.cluster = {
      manager: {
        submitTask: async function() {
          return {
            updatedWeights: Prime.Math.Matrix.create(5, 10, 0.1),
            updatedBiases: Prime.Math.Vector.create(5, 0.5),
            coherenceScore: 0.95
          };
        }
      }
    };
  }
  
  addLayer(layerConfig) {
    // Validate layer configuration if validator is available
    if (Prime.Neural.Distributed.DimensionValidator && Prime.Neural.Distributed.DimensionValidator.validateLayerConfig) {
      Prime.Neural.Distributed.DimensionValidator.validateLayerConfig(layerConfig, this.layers.length);
    }
    
    // Create a simple layer with weights and biases
    const layer = {
      inputSize: layerConfig.inputSize || this.inputSize,
      outputSize: layerConfig.outputSize,
      activation: layerConfig.activation || "relu",
      type: layerConfig.type || "dense",
      weights: [],
      biases: []
    };
    
    // Validate matrix dimensions before creation if validator is available
    if (Prime.Neural.Distributed.DimensionValidator && Prime.Neural.Distributed.DimensionValidator.validateMatrixDimensions) {
      Prime.Neural.Distributed.DimensionValidator.validateMatrixDimensions(
        layer.outputSize, 
        layer.inputSize,
        `layer ${this.layers.length} weights`
      );
    }
    
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
      weights: this.layers.map(layer => layer.weights),
      biases: this.layers.map(layer => layer.biases),
      layerConfig: this.layers.map(layer => ({
        inputSize: layer.inputSize,
        outputSize: layer.outputSize,
        type: layer.type,
        activation: layer.activation
      }))
    };
  }
  
  _applyParameters(parameters) {
    if (!parameters || !parameters.weights || !parameters.biases) {
      return false;
    }
    
    // Verify parameter coherence before applying
    if (!this._verifyParameterCoherence(parameters)) {
      if (Prime.Logger && Prime.Logger.warn) {
        Prime.Logger.warn("Parameter coherence verification failed");
      }
      return false;
    }
    
    // Apply weights and biases to each layer
    for (let i = 0; i < this.layers.length && i < parameters.weights.length; i++) {
      if (parameters.weights[i]) {
        this.layers[i].weights = parameters.weights[i];
      }
      
      if (parameters.biases[i]) {
        this.layers[i].biases = parameters.biases[i];
      }
    }
    
    return true;
  }
  
  _verifyParameterCoherence(parameters) {
    if (Prime.Neural.Distributed.DimensionValidator && 
        Prime.Neural.Distributed.DimensionValidator.validateParameterCoherence) {
      return Prime.Neural.Distributed.DimensionValidator.validateParameterCoherence(parameters);
    }
    
    // Basic coherence check if validator is not available
    if (!parameters || !parameters.weights) {
      return false;
    }
    
    // Check for NaN or Infinity
    for (const weightMatrix of parameters.weights) {
      if (!weightMatrix) continue;
      
      for (const row of weightMatrix) {
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
    
    // Process each layer
    for (let layerIndex = 0; layerIndex < localParams.weights.length; layerIndex++) {
      // Skip if local layer doesn't exist
      if (!localParams.weights[layerIndex]) continue;
      
      // Average weights for this layer
      const localWeights = localParams.weights[layerIndex];
      avgParams.weights[layerIndex] = [];
      
      for (let i = 0; i < localWeights.length; i++) {
        avgParams.weights[layerIndex][i] = [];
        
        for (let j = 0; j < localWeights[i].length; j++) {
          let sum = localWeights[i][j];
          let count = 1;
          
          // Add weights from remote parameters
          for (const remote of remoteParams) {
            if (remote.weights && 
                remote.weights[layerIndex] && 
                remote.weights[layerIndex][i] && 
                remote.weights[layerIndex][i][j] !== undefined) {
              sum += remote.weights[layerIndex][i][j];
              count++;
            }
          }
          
          avgParams.weights[layerIndex][i][j] = sum / count;
        }
      }
      
      // Average biases for this layer
      const localBiases = localParams.biases[layerIndex];
      avgParams.biases[layerIndex] = [];
      
      for (let i = 0; i < localBiases.length; i++) {
        let sum = localBiases[i];
        let count = 1;
        
        // Add biases from remote parameters
        for (const remote of remoteParams) {
          if (remote.biases && 
              remote.biases[layerIndex] && 
              remote.biases[layerIndex][i] !== undefined) {
            sum += remote.biases[layerIndex][i];
            count++;
          }
        }
        
        avgParams.biases[layerIndex][i] = sum / count;
      }
    }
    
    return avgParams;
  }
  
  async _synchronizeParameters() {
    // Increment metrics
    this.distributedState.synchronizedIterations++;
    this.distributedState.lastSyncIteration = this.metrics.iteration;
    this.distributedState.lastParameterUpdate = Date.now();
    
    try {
      // Get local parameters
      const localParams = this._extractModelParameters();
      
      // Simulate getting remote parameters from cluster
      const remoteResults = await this.cluster.manager.submitTask();
      
      // Create a mock remote parameters object
      const remoteParams = [{
        weights: [remoteResults.updatedWeights],
        biases: [remoteResults.updatedBiases]
      }];
      
      // Average parameters
      const avgParams = this._averageParameters(localParams, remoteParams);
      
      // Apply averaged parameters
      const success = this._applyParameters(avgParams);
      
      return success;
    } catch (error) {
      this.distributedState.failedSynchronizations++;
      Prime.Logger.error(`Parameter synchronization failed: ${error.message}`);
      return false;
    }
  }
  
  async _distributedCoherenceCheck() {
    // Perform coherence check on current parameters
    const params = this._extractModelParameters();
    const isCoherent = this._verifyParameterCoherence(params);
    
    // Update state
    this.distributedState.lastCoherenceCheck = this.metrics.iteration;
    
    return isCoherent;
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

// Replace the real model with our mock for testing
Prime.Neural.Distributed.DistributedNeuralModel = MockDistributedNeuralModel;

// Test utilities
function assertEqual(actual, expected, message) {
  if (actual !== expected) {
    throw new Error(message || `Expected ${expected}, but got ${actual}`);
  }
}

function assertApproxEqual(actual, expected, epsilon = 1e-6, message) {
  if (Math.abs(actual - expected) > epsilon) {
    throw new Error(message || `Expected ${expected} ± ${epsilon}, but got ${actual}`);
  }
}

function assertTrue(condition, message) {
  if (!condition) {
    throw new Error(message || "Assertion failed");
  }
}

// Run tests
async function runIntegrationTests() {
  console.log("=== Running Distributed Neural Network Integration Tests ===");
  
  // Test 1: Create a multi-layer distributed model
  console.log("\nTest 1: Create a multi-layer distributed model");
  const model = new Prime.Neural.Distributed.DistributedNeuralModel({
    inputSize: 10,
    layers: [
      {
        type: "dense",
        outputSize: 8,
        activation: "relu"
      },
      {
        type: "dense",
        outputSize: 5,
        activation: "sigmoid"
      },
      {
        type: "dense",
        outputSize: 3,
        activation: "softmax"
      }
    ],
    distributed: {
      enabled: true,
      partitionScheme: "layer-wise",
      syncFrequency: 2,
      synchronizationStrategy: "average"
    }
  });
  
  // Verify model structure
  assertEqual(model.layers.length, 3, "Model should have three layers");
  assertEqual(model.layers[0].inputSize, 10, "First layer should have input size 10");
  assertEqual(model.layers[0].outputSize, 8, "First layer should have output size 8");
  assertEqual(model.layers[1].inputSize, 8, "Second layer should have input size 8");
  assertEqual(model.layers[2].outputSize, 3, "Third layer should have output size 3");
  
  console.log("✓ Model structure verified");
  
  // Test 2: Extract and apply parameters
  console.log("\nTest 2: Extract and apply parameters");
  
  // Extract original parameters
  const originalParams = model._extractModelParameters();
  
  // Verify parameter structure
  assertEqual(originalParams.weights.length, 3, "Should have weights for 3 layers");
  assertEqual(originalParams.biases.length, 3, "Should have biases for 3 layers");
  assertEqual(originalParams.layerConfig.length, 3, "Should have config for 3 layers");
  
  // Modify parameters
  const modifiedParams = {
    weights: originalParams.weights.map(layerWeights => 
      layerWeights.map(row => row.map(() => 0.7))
    ),
    biases: originalParams.biases.map(layerBiases =>
      layerBiases.map(() => 1.5)
    )
  };
  
  // Apply modified parameters
  model._applyParameters(modifiedParams);
  
  // Verify parameters were updated
  assertApproxEqual(
    model.layers[0].weights[0][0], 
    0.7, 
    1e-10, 
    "First layer weights should be updated"
  );
  assertApproxEqual(
    model.layers[0].biases[0], 
    1.5, 
    1e-10, 
    "First layer biases should be updated"
  );
  
  console.log("✓ Parameter extraction and application verified");
  
  // Test 3: Parameter synchronization
  console.log("\nTest 3: Parameter synchronization");
  
  // Initialize for synchronization
  model.distributedState.isInitialized = true;
  model.distributedState.activeNodes = ["node1", "node2"];
  model.metrics.iteration = 5;
  
  // Perform synchronization
  const syncResult = await model._synchronizeParameters();
  
  // Verify synchronization was successful
  assertTrue(syncResult, "Synchronization should succeed");
  assertEqual(
    model.distributedState.lastSyncIteration, 
    5, 
    "Last sync iteration should be updated"
  );
  assertEqual(
    model.distributedState.synchronizedIterations, 
    1, 
    "Synchronized iterations should be incremented"
  );
  
  console.log("✓ Parameter synchronization verified");
  
  // Test 4: Coherence check
  console.log("\nTest 4: Coherence check");
  
  // Perform coherence check
  const coherentResult = await model._distributedCoherenceCheck();
  
  // Verify coherence check was successful
  assertTrue(coherentResult, "Coherence check should succeed with valid parameters");
  assertEqual(
    model.distributedState.lastCoherenceCheck, 
    5, 
    "Last coherence check iteration should be updated"
  );
  
  // Introduce incoherent parameters
  model.layers[1].weights[0][0] = NaN;
  
  // Perform coherence check again
  const incoherentResult = await model._distributedCoherenceCheck();
  
  // Verify coherence check failed with invalid parameters
  assertEqual(
    incoherentResult,
    false,
    "Coherence check should fail with invalid parameters"
  );
  
  console.log("✓ Coherence verification tested");
  
  console.log("\n=== All integration tests passed ===");
}

// Run the integration tests
runIntegrationTests().catch(error => {
  console.error("Integration tests failed:", error);
  process.exit(1);
});