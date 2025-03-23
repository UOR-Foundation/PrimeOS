/**
 * PrimeOS JavaScript Library - Coherence Verification Unit Tests
 * Tests for the distributed neural model coherence and parameter synchronization
 * with isolated unit tests for verification functionality
 */

const Prime = require("../../../src/core.js");
require("../../../src/mathematics.js");
require("../../../src/math/vector.js");
require("../../../src/math/matrix.js");
require("../../../src/coherence.js");

// Import test utilities
const {
  assertAdaptivePrecision,
  assertThrows,
} = require("../../utils/assertions");

// Use Jest's mock capabilities
jest.mock("../../../src/distributed/cluster/index.js", () => ({}));

describe("Coherence Verification - Neural Parameters", () => {
  // Create a mock model for testing
  let mockModel;

  beforeEach(() => {
    // Create a mock distributed model
    mockModel = {
      layers: [],
      distributedConfig: {
        enabled: true,
        partitionScheme: "data_parallel",
        syncFrequency: 10,
        synchronizationStrategy: "average",
        syncRecoveryStrategy: "local_fallback",
      },
      distributedState: {
        isInitialized: false,
        activeNodes: [],
        lastSyncIteration: 0,
        lastParameterUpdate: 0,
        synchronizedIterations: 0,
        failedSynchronizations: 0,
      },
      metrics: {
        iteration: 0,
      },
      addLayer(config) {
        const layer = {
          inputSize: config.inputSize || 10,
          outputSize: config.outputSize || 5,
          activation: config.activation || "relu",
          weights: Prime.Math.Matrix.create(
            config.outputSize || 5,
            config.inputSize || 10,
            0.1,
          ),
          biases: Prime.Math.Vector.create(config.outputSize || 5, 0.5),
        };
        this.layers.push(layer);
        return this;
      },
      _extractModelParameters() {
        return {
          weights: this.layers.map((layer) => layer.weights),
          biases: this.layers.map((layer) => layer.biases),
          layerConfig: this.layers.map((layer) => ({
            inputSize: layer.inputSize,
            outputSize: layer.outputSize,
          })),
        };
      },
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
      },
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
      },
    };

    // Add a test layer
    mockModel.addLayer({
      inputSize: 10,
      outputSize: 5,
      activation: "relu",
    });
  });

  test("should extract model parameters correctly", () => {
    const parameters = mockModel._extractModelParameters();

    expect(parameters.weights).toBeDefined();
    expect(parameters.biases).toBeDefined();
    expect(parameters.layerConfig).toBeDefined();

    expect(parameters.weights.length).toBe(1);
    expect(parameters.biases.length).toBe(1);
    expect(parameters.layerConfig.length).toBe(1);

    expect(parameters.weights[0][0][0]).toBeCloseTo(0.1, 10);
    expect(parameters.biases[0][0]).toBeCloseTo(0.5, 10);
    expect(parameters.layerConfig[0].inputSize).toBe(10);
    expect(parameters.layerConfig[0].outputSize).toBe(5);
  });

  test("should apply parameters to model correctly", () => {
    const weights = Prime.Math.Matrix.create(5, 10, 0.7);
    const biases = Prime.Math.Vector.create(5, 1.1);

    const parameters = {
      weights: [weights],
      biases: [biases],
    };

    mockModel._applyParameters(parameters);

    expect(mockModel.layers[0].weights[0][0]).toBeCloseTo(0.7, 10);
    expect(mockModel.layers[0].biases[0]).toBeCloseTo(1.1, 10);
  });

  test("should verify parameter coherence for valid parameters", () => {
    const weights = Prime.Math.Matrix.create(5, 10, 0.7);
    const biases = Prime.Math.Vector.create(5, 1.1);

    const parameters = {
      weights: [weights],
      biases: [biases],
    };

    const isCoherent = mockModel._verifyParameterCoherence(parameters);
    expect(isCoherent).toBe(true);
  });

  test("should reject parameters with NaN", () => {
    const weights = Prime.Math.Matrix.create(5, 10, 0.7);
    weights[0][1] = NaN;

    const biases = Prime.Math.Vector.create(5, 1.1);

    const parameters = {
      weights: [weights],
      biases: [biases],
    };

    const isCoherent = mockModel._verifyParameterCoherence(parameters);
    expect(isCoherent).toBe(false);
  });

  test("should reject parameters with too large values", () => {
    const weights = Prime.Math.Matrix.create(5, 10, 0.7);
    weights[0][1] = 1e7;

    const biases = Prime.Math.Vector.create(5, 1.1);

    const parameters = {
      weights: [weights],
      biases: [biases],
    };

    const isCoherent = mockModel._verifyParameterCoherence(parameters);
    expect(isCoherent).toBe(false);
  });
});

describe("Coherence Verification - Parameter Averaging", () => {
  // Mock model with parameter averaging function
  let mockModel;

  beforeEach(() => {
    mockModel = {
      _averageParameters(localParams, remoteParams) {
        const avgParams = {
          weights: [],
          biases: [],
        };

        // Average weights
        if (localParams.weights) {
          avgParams.weights = localParams.weights.map(
            (localWeight, layerIdx) => {
              return localWeight.map((row, i) => {
                return row.map((val, j) => {
                  let sum = val;
                  let count = 1;

                  for (const remote of remoteParams) {
                    if (
                      remote.weights &&
                      remote.weights[layerIdx] &&
                      remote.weights[layerIdx][i] &&
                      remote.weights[layerIdx][i][j] !== undefined
                    ) {
                      sum += remote.weights[layerIdx][i][j];
                      count++;
                    }
                  }

                  return sum / count;
                });
              });
            },
          );
        }

        // Average biases
        if (localParams.biases) {
          avgParams.biases = localParams.biases.map((localBias, layerIdx) => {
            return localBias.map((val, i) => {
              let sum = val;
              let count = 1;

              for (const remote of remoteParams) {
                if (
                  remote.biases &&
                  remote.biases[layerIdx] &&
                  remote.biases[layerIdx][i] !== undefined
                ) {
                  sum += remote.biases[layerIdx][i];
                  count++;
                }
              }

              return sum / count;
            });
          });
        }

        return avgParams;
      },
    };
  });

  test("should average parameters correctly", () => {
    // Create local parameters
    const localWeights = [Prime.Math.Matrix.create(5, 10)];
    const localBiases = [Prime.Math.Vector.create(5)];

    // Set local weights and biases
    for (let i = 0; i < 5; i++) {
      for (let j = 0; j < 10; j++) {
        localWeights[0][i][j] = 0.1 * (i + 1);
      }
      localBiases[0][i] = 0.5 * (i + 1);
    }

    const localParameters = {
      weights: localWeights,
      biases: localBiases,
    };

    // Create remote parameters
    const remoteWeights = [Prime.Math.Matrix.create(5, 10)];
    const remoteBiases = [Prime.Math.Vector.create(5)];

    // Set remote weights and biases
    for (let i = 0; i < 5; i++) {
      for (let j = 0; j < 10; j++) {
        remoteWeights[0][i][j] = 0.3 * (i + 1);
      }
      remoteBiases[0][i] = 0.7 * (i + 1);
    }

    const remoteParameters = [
      {
        weights: remoteWeights,
        biases: remoteBiases,
      },
    ];

    // Calculate average
    const averagedParams = mockModel._averageParameters(
      localParameters,
      remoteParameters,
    );

    // Verify averages
    expect(averagedParams.weights[0][0][0]).toBeCloseTo(0.2, 10); // Average of 0.1 and 0.3
    expect(averagedParams.biases[0][0]).toBeCloseTo(0.6, 10); // Average of 0.5 and 0.7

    // Verify average for second position
    expect(averagedParams.weights[0][1][0]).toBeCloseTo(0.4, 10); // Average of 0.2 and 0.6
    expect(averagedParams.biases[0][1]).toBeCloseTo(1.2, 10); // Average of 1.0 and 1.4
  });

  test("should handle missing parameters in some remotes", () => {
    // Create local parameters
    const localWeights = [Prime.Math.Matrix.create(5, 10, 0.1)];
    const localBiases = [Prime.Math.Vector.create(5, 0.5)];

    const localParameters = {
      weights: localWeights,
      biases: localBiases,
    };

    // Create remote parameters with missing data
    const remoteParameters = [
      {
        weights: [Prime.Math.Matrix.create(5, 10, 0.3)],
        // biases missing
      },
      {
        // weights missing
        biases: [Prime.Math.Vector.create(5, 0.7)],
      },
    ];

    // Calculate average
    const averagedParams = mockModel._averageParameters(
      localParameters,
      remoteParameters,
    );

    // Verify averages
    expect(averagedParams.weights[0][0][0]).toBeCloseTo(0.2, 10); // Average of 0.1 and 0.3
    expect(averagedParams.biases[0][0]).toBeCloseTo(0.6, 10); // Average of 0.5 and 0.7
  });

  test("should handle completely missing parameter sets", () => {
    // Create local parameters
    const localWeights = [Prime.Math.Matrix.create(5, 10, 0.1)];
    const localBiases = [Prime.Math.Vector.create(5, 0.5)];

    const localParameters = {
      weights: localWeights,
      biases: localBiases,
    };

    // Empty remote parameters
    const remoteParameters = [];

    // Calculate average
    const averagedParams = mockModel._averageParameters(
      localParameters,
      remoteParameters,
    );

    // Verify it returns exactly local parameters when no remotes
    expect(averagedParams.weights[0][0][0]).toBeCloseTo(0.1, 10);
    expect(averagedParams.biases[0][0]).toBeCloseTo(0.5, 10);
  });
});
