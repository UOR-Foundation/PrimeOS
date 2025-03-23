/**
 * PrimeOS JavaScript Library - Neural Network Refactor Tests
 * Tests for the refactored neural network components
 */

const Prime = require("../src/neural/index");
const assert = require("assert");

describe("Neural Network Refactoring", () => {
  describe("Activation Functions", () => {
    it("should provide all activation functions", () => {
      const activation = Prime.Neural.Activation.get("sigmoid");
      assert.ok(activation.forward);
      assert.ok(activation.backward);
      assert.ok(activation.inPlace);
      assert.ok(activation.gradientInPlace);
    });

    it("should apply activation functions to vectors", () => {
      const input = [-2, -1, 0, 1, 2];

      // Test sigmoid
      const sigmoid = Prime.Neural.Activation.get("sigmoid");
      const sigmoidOutput = sigmoid.forward(input);
      assert.equal(sigmoidOutput.length, input.length);
      assert.ok(sigmoidOutput[0] > 0 && sigmoidOutput[0] < 0.2);
      assert.ok(sigmoidOutput[4] > 0.8 && sigmoidOutput[4] < 1);

      // Test ReLU
      const relu = Prime.Neural.Activation.get("relu");
      const reluOutput = relu.forward(input);
      assert.equal(reluOutput.length, input.length);
      assert.equal(reluOutput[0], 0);
      assert.equal(reluOutput[4], 2);
    });

    it("should apply in-place activation functions", () => {
      const input = new Float32Array([-2, -1, 0, 1, 2]);

      // Test sigmoid in-place
      const sigmoid = Prime.Neural.Activation.get("sigmoid");
      sigmoid.inPlace(input);
      assert.ok(input[0] > 0 && input[0] < 0.2);
      assert.ok(input[4] > 0.8 && input[4] < 1);
    });

    it("should calculate activations with the Neural facade", () => {
      const input = [-2, -1, 0, 1, 2];

      // Regular activation
      const output = Prime.Neural.Neural.activate(input, "relu");
      assert.equal(output.length, input.length);
      assert.equal(output[0], 0);
      assert.equal(output[4], 2);

      // In-place activation
      const inPlaceInput = [...input];
      const result = Prime.Neural.Neural.activate(inPlaceInput, "relu", true);
      assert.equal(result, inPlaceInput); // Should return the same array
      assert.equal(inPlaceInput[0], 0);
      assert.equal(inPlaceInput[4], 2);
    });
  });

  describe("Dense Layer", () => {
    it("should create a dense layer", () => {
      const layer = new Prime.Neural.Layer.DenseLayer({
        inputSize: 3,
        outputSize: 2,
        activation: "sigmoid",
        useTypedArrays: false,
      });

      assert.equal(layer.inputSize, 3);
      assert.equal(layer.outputSize, 2);
      assert.equal(layer.activation, "sigmoid");
    });

    it("should perform forward and backward passes", () => {
      const layer = new Prime.Neural.Layer.DenseLayer({
        inputSize: 3,
        outputSize: 2,
        activation: "sigmoid",
        useTypedArrays: false,
      });

      const input = [0.5, 0.3, 0.2];
      const { activation, cache } = layer.forward(input);

      assert.equal(activation.length, layer.outputSize);

      // Create a dummy gradient for testing
      const outputGradient = [0.1, 0.2];
      const { dW, dB, dX } = layer.backward(outputGradient, cache);

      assert.ok(dW);
      assert.equal(dW.length, layer.outputSize);
      assert.equal(dW[0].length, layer.inputSize);
      assert.ok(dB);
      assert.equal(dB.length, layer.outputSize);
      assert.ok(dX);
      assert.equal(dX.length, layer.inputSize);
    });

    it("should support TypedArrays for memory efficiency", () => {
      const layer = new Prime.Neural.Layer.DenseLayer({
        inputSize: 3,
        outputSize: 2,
        activation: "sigmoid",
        useTypedArrays: true,
      });

      const input = new Float32Array([0.5, 0.3, 0.2]);
      const { activation, cache } = layer.forward(input);

      assert.ok(activation instanceof Float32Array);

      // Create a dummy gradient for testing
      const outputGradient = new Float32Array([0.1, 0.2]);
      const { dW, dB, dX } = layer.backward(outputGradient, cache);

      assert.ok(dX instanceof Float32Array);
    });
  });

  describe("Optimizers", () => {
    it("should create optimizers with the factory", () => {
      const sgdOptimizer = Prime.Neural.Optimization.OptimizerFactory.create(
        "sgd",
        {
          learningRate: 0.01,
          momentum: 0.9,
        },
      );

      assert.equal(sgdOptimizer.learningRate, 0.01);
      assert.equal(sgdOptimizer.momentum, 0.9);

      const adamOptimizer = Prime.Neural.Optimization.OptimizerFactory.create(
        "adam",
        {
          learningRate: 0.001,
          beta1: 0.9,
          beta2: 0.999,
        },
      );

      assert.equal(adamOptimizer.learningRate, 0.001);
      assert.equal(adamOptimizer.beta1, 0.9);
      assert.equal(adamOptimizer.beta2, 0.999);
    });

    it("should update parameters with SGD optimizer", () => {
      const optimizer = new Prime.Neural.Optimization.SGDOptimizer({
        learningRate: 0.1,
        momentum: 0.9,
      });

      const parameters = {
        weights: [
          [0.1, 0.2, 0.3],
          [0.4, 0.5, 0.6],
        ],
        biases: [0.1, 0.2],
      };

      const gradients = {
        weights: [
          [0.01, 0.02, 0.03],
          [0.04, 0.05, 0.06],
        ],
        biases: [0.01, 0.02],
      };

      const updated = optimizer.update(parameters, gradients);

      // Since this is the first update and momentum starts at 0,
      // we expect weights to be reduced by learningRate * gradient
      assert.ok(updated.weights[0][0] < parameters.weights[0][0]);
      assert.ok(updated.biases[0] < parameters.biases[0]);
    });

    it("should update parameters with Adam optimizer", () => {
      const optimizer = new Prime.Neural.Optimization.AdamOptimizer({
        learningRate: 0.1,
      });

      const parameters = {
        weights: [
          [0.1, 0.2, 0.3],
          [0.4, 0.5, 0.6],
        ],
        biases: [0.1, 0.2],
      };

      const gradients = {
        weights: [
          [0.01, 0.02, 0.03],
          [0.04, 0.05, 0.06],
        ],
        biases: [0.01, 0.02],
      };

      const updated = optimizer.update(parameters, gradients);

      // Adam should adjust parameters
      assert.ok(updated.weights[0][0] < parameters.weights[0][0]);
      assert.ok(updated.biases[0] < parameters.biases[0]);
    });
  });

  describe("Neural Facade", () => {
    it("should create layers through the facade", () => {
      const denseLayer = Prime.Neural.Neural.createLayer("dense", {
        inputSize: 3,
        outputSize: 2,
        activation: "relu",
      });

      assert.ok(denseLayer);
      assert.equal(denseLayer.inputSize, 3);
      assert.equal(denseLayer.outputSize, 2);
      assert.equal(denseLayer.activation, "relu");
    });

    it("should create optimizers through the facade", () => {
      const optimizer = Prime.Neural.Neural.createOptimizer("sgd", {
        learningRate: 0.01,
        momentum: 0.9,
      });

      assert.ok(optimizer);
      assert.equal(optimizer.learningRate, 0.01);
      assert.equal(optimizer.momentum, 0.9);
    });

    it("should convert between typed arrays and standard arrays", () => {
      const standardArray = [
        [1, 2, 3],
        [4, 5, 6],
      ];

      // Convert to typed array
      const typedArray = Prime.Neural.Neural.toTypedArray(standardArray);

      // Verify structure and values
      assert.equal(typedArray.length, standardArray.length);
      assert.equal(typedArray[0].length, standardArray[0].length);
      assert.equal(typedArray[0][0], standardArray[0][0]);
      assert.equal(typedArray[1][2], standardArray[1][2]);

      // Convert back to standard array
      const convertedBack = Prime.Neural.Neural.fromTypedArray(typedArray);

      // Verify conversion preserves structure and values
      assert.equal(convertedBack.length, standardArray.length);
      assert.equal(convertedBack[0].length, standardArray[0].length);
      assert.equal(convertedBack[0][0], standardArray[0][0]);
      assert.equal(convertedBack[1][2], standardArray[1][2]);
    });
  });
});
