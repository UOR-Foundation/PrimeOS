/**
 * Tests for PrimeOS Neural Module Advanced Features
 * Tests the new layer types and model capabilities
 */

// Import Prime with the Neural module
const Prime = require("../src");

describe("Neural Module Advanced Tests", () => {
  describe("Convolutional Layer Tests", () => {
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

      const epsilon = 1e-6;

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

  describe("Recurrent Layer Tests", () => {
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

  describe("Neural Model Tests", () => {
    test("should create neural model with correct properties", () => {
      if (!Prime.Neural.Model || !Prime.Neural.Model.NeuralModel) {
        console.log("⚠ Skipping: NeuralModel not implemented");
        return;
      }

      // Create a simple model
      const model = new Prime.Neural.Model.NeuralModel();

      expect(model instanceof Prime.Neural.Model.NeuralModel).toBe(true);

      // Add layers to the model
      model.addLayer({
        type: "dense",
        inputSize: 10,
        outputSize: 20,
        activation: "relu",
      });

      model.addLayer({
        type: "dense",
        outputSize: 5,
        activation: "sigmoid",
      });

      expect(model.layers.length).toBe(2);
      expect(model.layers[0].inputSize).toBe(10);
      expect(model.layers[0].outputSize).toBe(20);
      expect(model.layers[1].inputSize).toBe(20);
      expect(model.layers[1].outputSize).toBe(5);

      // Compile the model
      model.compile({
        loss: "mse",
        metric: "accuracy",
      });

      expect(model.compiled).toBe(true);
      expect(model.lossName).toBe("mse");
      expect(model.metricName).toBe("accuracy");

      // Test prediction
      const input = new Array(10).fill(0).map(() => Math.random());
      const prediction = model.predict(input);

      // Check if the prediction is array-like (either a regular array or a TypedArray)
      expect(prediction && typeof prediction.length === 'number').toBe(true);
      expect(prediction.length).toBe(5);

      // Test model summary
      const summary = model.summary();
      expect(summary.layers.length).toBe(2);
      expect(summary.totalParameters).toBeGreaterThan(0);
    });
  });
});
