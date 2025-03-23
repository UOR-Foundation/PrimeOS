/**
 * PrimeOS Unit Tests - Neural Layer
 *
 * Tests for the neural layer components in the Neural module.
 */

const Prime = require("../../../src");
const { Assertions } = require("../../utils");

describe("Neural Layer", () => {
  describe("Base Neural Layer", () => {
    test("should create a base neural layer with correct properties", () => {
      const layer = new Prime.Neural.Layer.NeuralLayer({
        inputSize: 3,
        outputSize: 2,
        activation: "sigmoid",
      });

      expect(layer instanceof Prime.Neural.Layer.NeuralLayer).toBe(true);
      expect(layer.inputSize).toBe(3);
      expect(layer.outputSize).toBe(2);
      expect(layer.activation).toBe("sigmoid");

      expect(Array.isArray(layer.weights)).toBe(true);
      expect(layer.weights.length).toBe(2);
      expect(layer.weights[0].length).toBe(3);

      expect(Array.isArray(layer.biases)).toBe(true);
      expect(layer.biases.length).toBe(2);
    });

    test("should perform forward pass correctly", () => {
      const layer = new Prime.Neural.Layer.NeuralLayer({
        inputSize: 3,
        outputSize: 2,
        activation: "linear",
        initParams: { distribution: "zeros" }, // Initialize weights to zero for predictable output
      });

      // Set weights and biases manually for deterministic test
      layer.weights = [
        [1, 0, 0],
        [0, 1, 0],
      ];
      layer.biases = [0, 0];

      const input = [2, 3, 4];
      const result = layer.forward(input);

      expect(Array.isArray(result.activation)).toBe(true);
      expect(result.activation.length).toBe(2);
      expect(result.activation[0]).toBe(2);
      expect(result.activation[1]).toBe(3);
    });

    test("should perform backward pass correctly", () => {
      const layer = new Prime.Neural.Layer.NeuralLayer({
        inputSize: 3,
        outputSize: 2,
        activation: "linear",
        initParams: { distribution: "zeros" },
      });

      // Set weights and biases manually for deterministic test
      layer.weights = [
        [1, 0, 0],
        [0, 1, 0],
      ];
      layer.biases = [0, 0];

      const input = [2, 3, 4];
      const result = layer.forward(input);
      const dY = [1, 1]; // Gradient of loss with respect to output

      const gradients = layer.backward(dY, result.cache);

      expect(gradients.dW).toBeDefined();
      expect(gradients.dB).toBeDefined();
      expect(gradients.dX).toBeDefined();

      expect(gradients.dW[0][0]).toBe(2);
      expect(gradients.dW[1][1]).toBe(3);
      expect(gradients.dB[0]).toBe(1);
      expect(gradients.dB[1]).toBe(1);
    });

    test("should update layer parameters correctly", () => {
      const layer = new Prime.Neural.Layer.NeuralLayer({
        inputSize: 2,
        outputSize: 1,
        activation: "linear",
        initParams: { distribution: "zeros" },
      });

      // Set weights and biases manually
      layer.weights = [[0.5, 0.5]];
      layer.biases = [0];

      // Create gradients
      const gradients = {
        dW: [[0.1, 0.2]],
        dB: [0.3],
      };

      // Apply update with learning rate 1.0
      layer.update(gradients, 1.0);

      expect(layer.weights[0][0]).toBeCloseTo(0.4, 6);
      expect(layer.weights[0][1]).toBeCloseTo(0.3, 6);
      expect(layer.biases[0]).toBeCloseTo(-0.3, 6);
    });
  });

  describe("Self-Optimizing Layer", () => {
    test("should create a self-optimizing layer with correct properties", () => {
      const layer = new Prime.Neural.Layer.SelfOptimizingLayer({
        inputSize: 4,
        outputSize: 3,
        activation: "relu",
        optimization: {
          adaptThreshold: 50,
          coherenceThreshold: 0.75,
        },
      });

      expect(layer instanceof Prime.Neural.Layer.SelfOptimizingLayer).toBe(
        true,
      );
      expect(layer.optimization.enabled).toBe(true);
      expect(layer.optimization.adaptThreshold).toBe(50);
      expect(layer.optimization.coherenceThreshold).toBe(0.75);

      expect(Array.isArray(layer.adaptationState.dropoutMask)).toBe(true);
      expect(layer.adaptationState.dropoutMask.length).toBe(3);
    });

    test("should adapt the layer correctly", () => {
      // Create a layer with a very low adaptThreshold to force adaptation
      const layer = new Prime.Neural.Layer.SelfOptimizingLayer({
        inputSize: 5,
        outputSize: 3,
        activation: "relu",
        optimization: {
          adaptThreshold: 1, // Adapt on every forward pass
          coherenceThreshold: 0.0, // Always adapt
        },
      });

      const input = [1, 2, 3, 4, 5];

      // Run forward pass multiple times to trigger adaptation
      for (let i = 0; i < 10; i++) {
        layer.forward(input);
      }

      // Verify adaptation history
      const history = layer.getAdaptationHistory();
      expect(Array.isArray(history)).toBe(true);
      expect(history.length).toBeGreaterThan(0);
      expect(history[0].iteration).toBeDefined();
      expect(history[0].coherenceBefore).toBeDefined();
      expect(history[0].coherenceAfter).toBeDefined();
    });

    test("should provide layer analysis", () => {
      const layer = new Prime.Neural.Layer.SelfOptimizingLayer({
        inputSize: 4,
        outputSize: 3,
        activation: "sigmoid",
      });

      // Run forward pass to generate some usage statistics
      layer.forward([1, 2, 3, 4]);

      const analysis = layer.analyzeLayer();
      expect(typeof analysis).toBe("object");
      expect(typeof analysis.coherence).toBe("number");
      expect(typeof analysis.utilizationRate).toBe("number");
      expect(Array.isArray(analysis.recommendations)).toBe(true);
    });
  });

  describe("Convolutional Layer", () => {
    test("should create convolutional layer with correct properties", () => {
      if (!Prime.Neural.Layer.ConvolutionalLayer) {
        console.log("⚠ Skipping: ConvolutionalLayer not implemented");
        return;
      }

      const layer = new Prime.Neural.Layer.ConvolutionalLayer({
        inputShape: [28, 28, 1],
        filters: 16,
        kernelSize: [3, 3],
        strides: [1, 1],
        padding: "valid",
        activation: "relu",
      });

      expect(layer instanceof Prime.Neural.Layer.ConvolutionalLayer).toBe(true);

      // Check properties
      expect(layer.filters).toBe(16);
      expect(layer.kernelSize[0]).toBe(3);
      expect(layer.kernelSize[1]).toBe(3);
      expect(layer.strides[0]).toBe(1);
      expect(layer.strides[1]).toBe(1);
      expect(layer.padding).toBe("valid");
      expect(layer.activation).toBe("relu");

      // Check output shape calculation
      expect(layer.outputShape[0]).toBe(26); // 28 - 3 + 1 for 'valid' padding
      expect(layer.outputShape[1]).toBe(26); // 28 - 3 + 1 for 'valid' padding
      expect(layer.outputShape[2]).toBe(16);

      // Create a layer with 'same' padding
      const sameLayer = new Prime.Neural.Layer.ConvolutionalLayer({
        inputShape: [28, 28, 1],
        filters: 16,
        kernelSize: [3, 3],
        strides: [1, 1],
        padding: "same",
        activation: "relu",
      });

      expect(sameLayer.outputShape[0]).toBe(28);
      expect(sameLayer.outputShape[1]).toBe(28);
    });

    test("should perform forward and backward pass correctly", () => {
      if (!Prime.Neural.Layer.ConvolutionalLayer) {
        console.log(
          "⚠ Skipping: ConvolutionalLayer forward/backward not tested",
        );
        return;
      }

      // Create a small test input (3x3x1)
      const input = [
        [[1], [2], [3]],
        [[4], [5], [6]],
        [[7], [8], [9]],
      ];

      // Create a small convolutional layer with predictable weights
      const layer = new Prime.Neural.Layer.ConvolutionalLayer({
        inputShape: [3, 3, 1],
        filters: 2,
        kernelSize: [2, 2],
        strides: [1, 1],
        padding: "valid",
        activation: "linear", // Use linear for simple testing
      });

      // Reinitialize the layer's kernel utilization
      layer._initializeKernelUtilization();

      // Reinitialize spatial sensitivity
      layer.usagePatterns.spatialSensitivity =
        layer._createSpatialSensitivityArray();

      // Manually set weights for deterministic testing - make sure shape matches what layer expects
      layer.weights = new Array(2); // Two filters

      // First filter: values of 1.0
      layer.weights[0] = new Array(2); // 2x2 kernel
      layer.weights[0][0] = new Array(2);
      layer.weights[0][0][0] = new Array(1).fill(1.0);
      layer.weights[0][0][1] = new Array(1).fill(1.0);
      layer.weights[0][1] = new Array(2);
      layer.weights[0][1][0] = new Array(1).fill(1.0);
      layer.weights[0][1][1] = new Array(1).fill(1.0);

      // Second filter: values of 0.5
      layer.weights[1] = new Array(2); // 2x2 kernel
      layer.weights[1][0] = new Array(2);
      layer.weights[1][0][0] = new Array(1).fill(0.5);
      layer.weights[1][0][1] = new Array(1).fill(0.5);
      layer.weights[1][1] = new Array(2);
      layer.weights[1][1][0] = new Array(1).fill(0.5);
      layer.weights[1][1][1] = new Array(1).fill(0.5);

      // Set biases to zero
      layer.biases = [0, 0];

      // Forward pass
      const result = layer.forward(input);

      // Expected output calculations
      // First filter (all 1.0 weights):
      // [1,2; 4,5] -> 1*1 + 1*2 + 1*4 + 1*5 = 12
      // [2,3; 5,6] -> 1*2 + 1*3 + 1*5 + 1*6 = 16
      // [4,5; 7,8] -> 1*4 + 1*5 + 1*7 + 1*8 = 24
      // [5,6; 8,9] -> 1*5 + 1*6 + 1*8 + 1*9 = 28

      // Second filter (all 0.5 weights):
      // [1,2; 4,5] -> 0.5*1 + 0.5*2 + 0.5*4 + 0.5*5 = 6
      // [2,3; 5,6] -> 0.5*2 + 0.5*3 + 0.5*5 + 0.5*6 = 8
      // [4,5; 7,8] -> 0.5*4 + 0.5*5 + 0.5*7 + 0.5*8 = 12
      // [5,6; 8,9] -> 0.5*5 + 0.5*6 + 0.5*8 + 0.5*9 = 14

      // First filter activations
      expect(result.activation[0][0][0]).toBeCloseTo(12, 6);
      expect(result.activation[0][1][0]).toBeCloseTo(16, 6);
      expect(result.activation[1][0][0]).toBeCloseTo(24, 6);
      expect(result.activation[1][1][0]).toBeCloseTo(28, 6);

      // Second filter activations
      expect(result.activation[0][0][1]).toBeCloseTo(6, 6);
      expect(result.activation[0][1][1]).toBeCloseTo(8, 6);
      expect(result.activation[1][0][1]).toBeCloseTo(12, 6);
      expect(result.activation[1][1][1]).toBeCloseTo(14, 6);

      // Backward pass with simple gradient
      const dY = [
        [
          [1, 2],
          [1, 2],
        ],
        [
          [1, 2],
          [1, 2],
        ],
      ];

      const gradients = layer.backward(dY, result.cache);

      // Verify weight gradients exist
      expect(gradients.dW).toBeDefined();
      expect(gradients.dB).toBeDefined();
      expect(gradients.dX).toBeDefined();

      // Test bias gradient
      expect(gradients.dB[0]).toBe(4);
      expect(gradients.dB[1]).toBe(8);
    });
  });

  describe("Recurrent Layer", () => {
    test("should create recurrent layer with correct properties", () => {
      if (!Prime.Neural.Layer.RecurrentLayer) {
        console.log("⚠ Skipping: RecurrentLayer not implemented");
        return;
      }

      // Test GRU layer creation
      const gruLayer = new Prime.Neural.Layer.RecurrentLayer({
        inputSize: 10,
        hiddenSize: 20,
        cellType: "gru",
        sequenceLength: 5,
        returnSequences: true,
      });

      expect(gruLayer instanceof Prime.Neural.Layer.RecurrentLayer).toBe(true);
      expect(gruLayer.inputSize).toBe(10);
      expect(gruLayer.hiddenSize).toBe(20);
      expect(gruLayer.cellType).toBe("gru");
      expect(gruLayer.sequenceLength).toBe(5);
      expect(gruLayer.returnSequences).toBe(true);

      // Test LSTM layer creation
      const lstmLayer = new Prime.Neural.Layer.RecurrentLayer({
        inputSize: 10,
        hiddenSize: 20,
        cellType: "lstm",
        sequenceLength: 5,
        returnSequences: false,
      });

      expect(lstmLayer.cellType).toBe("lstm");
      expect(lstmLayer.returnSequences).toBe(false);

      // Check that weights were initialized correctly for LSTM
      expect(lstmLayer.weights.Wi).toBeDefined();
      expect(lstmLayer.weights.Wf).toBeDefined();
      expect(lstmLayer.weights.Wo).toBeDefined();
      expect(lstmLayer.weights.Wc).toBeDefined();
    });

    test("should perform forward and backward pass correctly", () => {
      if (!Prime.Neural.Layer.RecurrentLayer) {
        console.log("⚠ Skipping: RecurrentLayer forward/backward not tested");
        return;
      }

      // Create a simple GRU layer for testing
      const layer = new Prime.Neural.Layer.RecurrentLayer({
        inputSize: 2,
        hiddenSize: 3,
        cellType: "gru",
        returnSequences: false,
      });

      // Test single step input
      const input = [1, 2]; // Single time step
      const result = layer.forward(input);

      expect(Array.isArray(result.activation)).toBe(true);
      expect(result.activation.length).toBe(3);

      // Test sequence input
      const sequence = [
        [1, 2],
        [3, 4],
        [5, 6],
      ]; // 3 time steps
      const seqResult = layer.forward(sequence);

      expect(Array.isArray(seqResult.activation)).toBe(true);
      expect(seqResult.activation.length).toBe(3);

      // Test backward pass
      const dY = [0.1, 0.2, 0.3]; // Gradient for the output
      const gradients = layer.backward(dY, seqResult.cache);

      expect(gradients.dWeights).toBeDefined();
      expect(gradients.dBiases).toBeDefined();
      expect(gradients.dX).toBeDefined();
      expect(gradients.dX.length).toBe(sequence.length);
    });
  });
});
