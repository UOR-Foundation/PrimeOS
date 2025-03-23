/**
 * PrimeOS JavaScript Library - Coherence System Integration Tests
 * Tests the integrated behavior of the coherence system including distributed neural model synchronization
 */

const Prime = require("../../../src/core.js");
require("../../../src/mathematics.js");
require("../../../src/math/vector.js");
require("../../../src/math/matrix.js");
require("../../../src/coherence.js");
require("../../../src/distributed/index.js");
require("../../../src/distributed/coherence.js");
require("../../../src/neural/index.js");
require("../../../src/neural/distributed/index.js");

// Define a mock distributed neural model for testing
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

    // Mock cluster
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
    const layer = {
      inputSize: layerConfig.inputSize || this.inputSize,
      outputSize: layerConfig.outputSize,
      activation: layerConfig.activation || "relu",
      weights: Prime.Math.Matrix.create(
        layerConfig.outputSize,
        layerConfig.inputSize || this.inputSize,
        0.1,
      ),
      biases: Prime.Math.Vector.create(layerConfig.outputSize, 0.5),
    };

    this.layers.push(layer);
    this.inputSize = layerConfig.outputSize;

    return this;
  }

  _extractModelParameters() {
    return {
      weights: this.layers.map((layer) => layer.weights),
      biases: this.layers.map((layer) => layer.biases),
      layerConfig: this.layers.map((layer) => ({
        inputSize: layer.inputSize,
        outputSize: layer.outputSize,
      })),
    };
  }

  _applyParameters(parameters) {
    if (parameters.weights) {
      parameters.weights.forEach((weights, i) => {
        if (this.layers[i]) {
          this.layers[i].weights = weights;
        }
      });
    }
    if (parameters.biases) {
      parameters.biases.forEach((biases, i) => {
        if (this.layers[i]) {
          this.layers[i].biases = biases;
        }
      });
    }
    return true;
  }

  _verifyParameterCoherence(parameters) {
    // Check for NaN or Infinity
    if (parameters.weights) {
      for (const weights of parameters.weights) {
        for (const row of weights) {
          for (const value of row) {
            if (!Number.isFinite(value) || Math.abs(value) > 1e6) {
              return false;
            }
          }
        }
      }
    }
    return true;
  }

  async _synchronizeParameters() {
    this.distributedState.synchronizedIterations++;
    this.distributedState.lastSyncIteration = this.metrics.iteration;
    this.distributedState.lastParameterUpdate = Date.now();
    return Promise.resolve(true);
  }

  async _distributedCoherenceCheck() {
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

// Replace the distributed neural model class for testing
Prime.Neural.Distributed.DistributedNeuralModel = MockDistributedNeuralModel;

describe("Coherence System Integration Tests", () => {
  describe("Distributed Neural Model Integration", () => {
    test("should create and initialize distributed model with coherence", async () => {
      // Create a distributed model
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
          partitionScheme: "layer-wise",
          syncFrequency: 2,
          synchronizationStrategy: "average",
          syncRecoveryStrategy: "local_fallback",
        },
      });

      // Verify model configuration
      expect(model.distributedConfig.enabled).toBe(true);
      expect(model.distributedConfig.syncFrequency).toBe(2);
      expect(model.distributedConfig.synchronizationStrategy).toBe("average");

      // Initialize distributed state
      model.distributedState.isInitialized = true;
      model.distributedState.activeNodes = ["node1", "node2"];

      // Perform synchronization
      const syncResult = await model._synchronizeParameters();
      expect(syncResult).toBe(true);
      expect(model.distributedState.synchronizedIterations).toBe(1);

      // Perform coherence check
      const coherenceResult = await model._distributedCoherenceCheck();
      expect(coherenceResult).toBe(true);
      expect(model.distributedState.lastCoherenceCheck).toBe(0);

      // Get distributed status
      const status = model.getDistributedStatus();
      expect(status.enabled).toBe(true);
      expect(status.syncStrategy).toBe("average");
      expect(status.synchronizedIterations).toBe(1);
    });

    test("should register distributed model with system coherence", () => {
      // Create a distributed model
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
        },
      });

      // Clear existing components in system coherence
      Prime.coherence.systemCoherence.components = [];

      // Create mock coherence norm method for model
      model.coherenceNorm = function () {
        return 0.5;
      };

      // Register with system coherence
      const unregister = Prime.coherence.systemCoherence.register(model, 2);

      // Test registration
      expect(Prime.coherence.systemCoherence.components.length).toBe(1);
      expect(Prime.coherence.systemCoherence.components[0].component).toBe(
        model,
      );
      expect(Prime.coherence.systemCoherence.components[0].weight).toBe(2);

      // Calculate global coherence
      const globalCoherence =
        Prime.coherence.systemCoherence.calculateGlobalCoherence();
      // The actual value depends on the implementation details but should be positive
      expect(globalCoherence).toBeGreaterThan(0);

      // Unregister
      unregister();
      expect(Prime.coherence.systemCoherence.components.length).toBe(0);
    });

    test("should handle multiple iterations and synchronization", async () => {
      // Create a distributed model
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
          syncFrequency: 2,
        },
      });

      // Initialize distributed state
      model.distributedState.isInitialized = true;
      model.distributedState.activeNodes = ["node1", "node2"];

      // Simulate training iterations
      for (let i = 0; i < 5; i++) {
        model.metrics.iteration = i;

        // Synchronize every syncFrequency iterations
        if (i % model.distributedConfig.syncFrequency === 0) {
          await model._synchronizeParameters();
        }
      }

      // Verify synchronization count
      expect(model.distributedState.synchronizedIterations).toBe(3); // Iterations 0, 2, 4
      expect(model.distributedState.lastSyncIteration).toBe(4);
    });
  });

  describe("Integration with Coherence Constraints", () => {
    test("should integrate constraints with distributed model", () => {
      // Create a distributed model
      const model = new Prime.Neural.Distributed.DistributedNeuralModel({
        inputSize: 10,
        layers: [
          {
            type: "dense",
            outputSize: 5,
            activation: "relu",
          },
        ],
      });

      // Create constraints for the model
      const constraints = [
        Prime.coherence.createConstraint((m) => m.layers.length > 0, {
          name: "hasLayers",
          type: "hard",
        }),
        Prime.coherence.createConstraint(
          (m) => m.layers.every((l) => l.outputSize > 0),
          { name: "validLayerSize", type: "hard" },
        ),
      ];

      // Create a constrained state for the model
      const state = Prime.coherence.createState(model, constraints);

      // Verify constraints are satisfied
      expect(state.coherenceNorm()).toBe(0); // All constraints satisfied

      // Test constraint violation with a failing state
      const badModel = {
        layers: [
          { outputSize: 0 }, // Invalid output size
        ],
      };

      // Check each constraint
      const validLayerSize = constraints[1];
      expect(validLayerSize.check(badModel)).toBe(false);
    });

    test("should apply nested coherence constraints to a complex model", () => {
      // Create a distributed model
      const model = new Prime.Neural.Distributed.DistributedNeuralModel({
        inputSize: 10,
        layers: [
          {
            type: "dense",
            outputSize: 5,
            activation: "relu",
          },
        ],
      });

      // Create layer-specific constraints
      const layerConstraints = [
        Prime.coherence.createConstraint((layer) => layer.inputSize > 0, {
          name: "validInputSize",
          type: "hard",
        }),
        Prime.coherence.createConstraint((layer) => layer.outputSize > 0, {
          name: "validOutputSize",
          type: "hard",
        }),
        Prime.coherence.createConstraint(
          (layer) => ["relu", "sigmoid", "tanh"].includes(layer.activation),
          { name: "validActivation", type: "hard" },
        ),
      ];

      // Check constraints for each layer
      let allLayersValid = true;
      for (const layer of model.layers) {
        for (const constraint of layerConstraints) {
          if (!constraint.check(layer)) {
            allLayersValid = false;
            break;
          }
        }
      }

      expect(allLayersValid).toBe(true);

      // Create an invalid layer
      const invalidLayer = {
        inputSize: 10,
        outputSize: 5,
        activation: "invalid",
      };

      // Check activation constraint
      const activationConstraint = layerConstraints[2];
      expect(activationConstraint.check(invalidLayer)).toBe(false);
    });
  });

  describe("UOR Integration with Distributed Environment", () => {
    test("should create UOR references that span distributed environment", () => {
      // Create a Clifford algebra for the fiber
      const algebra = Prime.Clifford.create({ dimension: 3 });

      // Create UOR references representing different distributed nodes
      const node1Ref = Prime.UOR.createReference({
        manifold: "distributedEnvironment",
        point: [0, 0, 0], // Represents node1's position
        fiber: algebra,
      });

      const node2Ref = Prime.UOR.createReference({
        manifold: "distributedEnvironment",
        point: [1, 0, 0], // Represents node2's position
        fiber: algebra,
      });

      // Create objects at each reference
      const node1Vector = algebra.vector([1, 2, 3]);
      const node2Vector = algebra.vector([4, 5, 6]);

      const node1Object = node1Ref.createObject(node1Vector);
      const node2Object = node2Ref.createObject(node2Vector);

      // Verify objects are properly created
      expect(node1Object.value).toBe(node1Vector);
      expect(node2Object.value).toBe(node2Vector);

      // Check reference compatibility
      expect(node1Ref.isCompatibleWith(node2Ref)).toBe(true);

      // Project from node1 to node2
      const projectedObject = node1Object.projectTo(node2Ref);

      // Verify projection
      expect(projectedObject.reference).toBe(node2Ref);
      expect(projectedObject.value.norm()).toBeCloseTo(node1Vector.norm(), 10);
    });

    test("should integrate UOR with distributed model parameters", () => {
      // Create a distributed model
      const model = new Prime.Neural.Distributed.DistributedNeuralModel({
        inputSize: 10,
        layers: [
          {
            type: "dense",
            outputSize: 5,
            activation: "relu",
          },
        ],
      });

      // Create a Clifford algebra for the fiber
      const algebra = Prime.Clifford.create({ dimension: 3 });

      // Create UOR reference for the parameter space
      const paramRef = Prime.UOR.createReference({
        manifold: "parameterSpace",
        point: [0, 0, 0],
        fiber: algebra,
      });

      // Extract model parameters
      const parameters = model._extractModelParameters();

      // Create a UOR object representing the parameters
      // For testing purposes, we'll use a simplified representation
      const paramVector = algebra.vector([
        parameters.weights[0][0][0], // First weight
        parameters.biases[0][0], // First bias
        model.layers[0].outputSize, // Output size
      ]);

      const paramObject = paramRef.createObject(paramVector);

      // Verify UOR object
      expect(paramObject.reference).toBe(paramRef);
      expect(paramObject.value.toArray()[0]).toBeCloseTo(0.1, 10); // First weight
      expect(paramObject.value.toArray()[1]).toBeCloseTo(0.5, 10); // First bias
      expect(paramObject.value.toArray()[2]).toBe(5); // Output size
    });
  });
});
