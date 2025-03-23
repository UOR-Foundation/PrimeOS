/**
 * Mock test for DistributedNeuralModel parameter synchronization
 */

// Import required modules
const Prime = {
  ValidationError: class ValidationError extends Error {
    constructor(message) {
      super(message);
      this.name = "ValidationError";
    }
  },
  Math: {
    Vector: {
      create: function (dimensions, initialValue = 0) {
        return new Array(dimensions).fill(initialValue);
      },
    },
    Matrix: {
      create: function (rows, cols, initialValue = 0) {
        return Array(rows)
          .fill()
          .map(() => Array(cols).fill(initialValue));
      },
    },
  },
  Neural: {
    Distributed: {},
  },
  Utils: {
    isObject: function (obj) {
      return typeof obj === "object" && obj !== null;
    },
    isNumber: function (num) {
      return typeof num === "number" && !isNaN(num);
    },
  },
  Logger: {
    info: console.log,
    error: console.error,
    warn: console.warn,
    debug: console.log,
  },
};

// Define our mock model
class MockDistributedNeuralModel {
  constructor(config = {}) {
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

    this.distributedConfig = {
      enabled: config.distributed?.enabled ?? false,
      partitionScheme: config.distributed?.partitionScheme || "data_parallel",
      syncFrequency: config.distributed?.syncFrequency || 10,
      synchronizationStrategy:
        config.distributed?.synchronizationStrategy || "average",
      syncRecoveryStrategy:
        config.distributed?.syncRecoveryStrategy || "local_fallback",
    };

    this.distributedState = {
      isInitialized: false,
      activeNodes: [],
      lastSyncIteration: 0,
      lastParameterUpdate: 0,
      synchronizedIterations: 0,
      failedSynchronizations: 0,
    };

    this.metrics = {
      iteration: 0,
    };

    // Add mock cluster
    this.cluster = {
      manager: {
        submitTask: async function () {
          return {
            updatedWeights: Prime.Math.Matrix.create(5, 10, 0.1),
            updatedBiases: Prime.Math.Vector.create(5, 0.5),
            coherenceScore: 0.95,
          };
        },
      },
    };
  }

  addLayer(layerConfig) {
    // Create a simple layer with weights and biases
    const layer = {
      inputSize: layerConfig.inputSize || this.inputSize,
      outputSize: layerConfig.outputSize,
      activation: layerConfig.activation || "relu",
      weights: [],
      biases: [],
    };

    // Initialize weights
    layer.weights = Prime.Math.Matrix.create(
      layer.outputSize,
      layer.inputSize,
      0.1,
    );
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
          outputSize: this.layers[0].outputSize,
        },
      ],
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
      biases: [],
    };

    // Average weights
    if (localParams.weights && localParams.weights[0]) {
      avgParams.weights = [
        localParams.weights[0].map((row, i) =>
          row.map((val, j) => {
            let sum = val;
            let count = 1;

            for (const remote of remoteParams) {
              if (
                remote.weights &&
                remote.weights[0] &&
                remote.weights[0][i] &&
                remote.weights[0][i][j] !== undefined
              ) {
                sum += remote.weights[0][i][j];
                count++;
              }
            }

            return sum / count;
          }),
        ),
      ];
    }

    // Average biases
    if (localParams.biases && localParams.biases[0]) {
      avgParams.biases = [
        localParams.biases[0].map((val, i) => {
          let sum = val;
          let count = 1;

          for (const remote of remoteParams) {
            if (
              remote.biases &&
              remote.biases[0] &&
              remote.biases[0][i] !== undefined
            ) {
              sum += remote.biases[0][i];
              count++;
            }
          }

          return sum / count;
        }),
      ];
    }

    return avgParams;
  }

  async _synchronizeParameters() {
    // Increment metrics
    this.distributedState.synchronizedIterations++;
    this.distributedState.lastSyncIteration = this.metrics.iteration;
    this.distributedState.lastParameterUpdate = Date.now();

    // Mock implementation that just resolves to true
    return Promise.resolve(true);
  }

  async _distributedCoherenceCheck() {
    // Mock implementation that just resolves to true
    this.distributedState.lastCoherenceCheck = this.metrics.iteration;
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
      recoveryStrategy: this.distributedConfig.syncRecoveryStrategy,
    };
  }
}

// Register our mock model
Prime.Neural.Distributed.DistributedNeuralModel = MockDistributedNeuralModel;

// Run a simple test
async function runTest() {
  console.log("=== Testing MockDistributedNeuralModel ===");

  // Create model with distributed configuration
  const model = new Prime.Neural.Distributed.DistributedNeuralModel({
    inputSize: 10,
    layers: [
      {
        type: "dense",
        outputSize: 5,
        activation: "relu",
      },
    ],
    distributed: {
      enabled: true,
      partitionScheme: "data_parallel",
      syncFrequency: 2,
      synchronizationStrategy: "average",
    },
  });

  // Verify model configuration
  console.log("Model configuration:");
  console.log(`- Input size: ${model.inputSize}`);
  console.log(`- First layer input size: ${model.layers[0].inputSize}`);
  console.log(`- First layer output size: ${model.layers[0].outputSize}`);
  console.log(`- Distributed mode: ${model.distributedConfig.enabled}`);
  console.log(`- Partition scheme: ${model.distributedConfig.partitionScheme}`);

  // Extract parameters
  const parameters = model._extractModelParameters();

  console.log("\nParameter extraction:");
  console.log(
    `- Weights shape: [${parameters.weights[0].length}x${parameters.weights[0][0].length}]`,
  );
  console.log(`- Biases length: ${parameters.biases[0].length}`);

  // Simulate parameter synchronization
  console.log("\nSimulating parameter synchronization...");
  model.metrics.iteration = 1;
  const syncResult = await model._synchronizeParameters();

  console.log(
    `- Synchronization result: ${syncResult ? "success" : "failure"}`,
  );
  console.log(
    `- Last sync iteration: ${model.distributedState.lastSyncIteration}`,
  );
  console.log(
    `- Synchronized iterations: ${model.distributedState.synchronizedIterations}`,
  );

  // Get distributed status
  const status = model.getDistributedStatus();

  console.log("\nDistributed status:");
  console.log(status);

  console.log("\n=== Test completed successfully ===");
}

// Execute the test
runTest().catch((error) => {
  console.error("Test failed with error:", error);
});
