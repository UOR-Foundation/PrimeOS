/**
 * PrimeOS Integration Tests - Neural Network Integration
 *
 * Tests the integration of neural network components within the Neural module.
 */

const Prime = require("../../../src");
const { Assertions } = require("../../utils");

describe("Neural Network Integration", () => {
  describe("Model Training Pipeline", () => {
    test("should construct and train a simple model through the pipeline", () => {
      if (!Prime.Neural.Model || !Prime.Neural.Model.NeuralModel) {
        console.log("⚠ Skipping: NeuralModel not implemented");
        return;
      }

      // Create a simple regression model
      const model = new Prime.Neural.Model.NeuralModel();

      // Add layers
      model.addLayer({
        type: "dense",
        inputSize: 2,
        outputSize: 4,
        activation: "relu",
      });

      model.addLayer({
        type: "dense",
        outputSize: 1,
        activation: "linear",
      });

      // Compile with MSE loss
      model.compile({
        loss: "mse",
        optimizer: {
          type: "sgd",
          learningRate: 0.1,
        },
      });

      // Simple training data: y = x1 + 2*x2
      const trainingData = [];
      for (let i = 0; i < 20; i++) {
        const x1 = Math.random() * 2 - 1; // [-1, 1]
        const x2 = Math.random() * 2 - 1; // [-1, 1]
        const y = x1 + 2 * x2;

        trainingData.push({
          input: [x1, x2],
          output: [y],
        });
      }

      // Train the model
      const trainingResult = model.train({
        data: trainingData,
        epochs: 50,
        batchSize: 4,
        verbose: false,
      });

      // Validate training metrics
      expect(trainingResult.history).toBeDefined();
      expect(Array.isArray(trainingResult.history.loss)).toBe(true);
      expect(trainingResult.history.loss.length).toBe(50);

      // Final loss should be lower than initial loss
      expect(trainingResult.history.loss[49]).toBeLessThan(
        trainingResult.history.loss[0],
      );

      // Test prediction
      const testX = [0.5, -0.5];
      const expectedY = 0.5 + 2 * -0.5; // = -0.5

      const prediction = model.predict(testX);

      // Should be approximately correct (reasonable error margin since it's a small network)
      expect(prediction[0]).toBeCloseTo(expectedY, 0);
    });
  });

  describe("Optimizer Integration", () => {
    test("should correctly integrate optimizer with model", () => {
      if (!Prime.Neural.Model || !Prime.Neural.Model.NeuralModel) {
        console.log("⚠ Skipping: Optimizer integration not tested");
        return;
      }

      // Create a model with Adam optimizer
      const model = new Prime.Neural.Model.NeuralModel();

      model.addLayer({
        type: "dense",
        inputSize: 2,
        outputSize: 2,
        activation: "relu",
      });

      model.compile({
        loss: "mse",
        optimizer: {
          type: "adam",
          learningRate: 0.01,
          beta1: 0.9,
          beta2: 0.999,
        },
      });

      // Verify optimizer is created and configured
      expect(model.optimizer).toBeDefined();
      expect(
        model.optimizer instanceof Prime.Neural.Optimization.CoherenceAdam,
      ).toBe(true);
      expect(model.optimizer.learningRate).toBe(0.01);

      // Generate dummy data
      const dummyData = [
        { input: [1, 2], output: [3] },
        { input: [2, 3], output: [5] },
      ];

      // Train for just one epoch
      const result = model.train({
        data: dummyData,
        epochs: 1,
        verbose: false,
      });

      // Verify the optimizer was used (stats should be tracked)
      expect(model.optimizer.getStatistics().iterations).toBeGreaterThan(0);
    });
  });

  describe("Self-Optimizing Layer Integration", () => {
    test("should integrate self-optimizing layers in model architecture", () => {
      if (!Prime.Neural.Model || !Prime.Neural.Model.NeuralModel) {
        console.log(
          "⚠ Skipping: Self-optimizing layer integration not tested",
        );
        return;
      }

      // Create model with self-optimizing hidden layer
      const model = new Prime.Neural.Model.NeuralModel();

      model.addLayer({
        type: "self-optimizing",
        inputSize: 2,
        outputSize: 4,
        activation: "relu",
        optimization: {
          adaptThreshold: 2, // Adapt frequently for testing
          coherenceThreshold: 0.7,
        },
      });

      model.addLayer({
        type: "dense",
        outputSize: 1,
        activation: "linear",
      });

      model.compile({
        loss: "mse",
        optimizer: {
          type: "sgd",
          learningRate: 0.1,
        },
      });

      // Verify layer types
      expect(
        model.layers[0] instanceof Prime.Neural.Layer.SelfOptimizingLayer,
      ).toBe(true);
      expect(model.layers[1] instanceof Prime.Neural.Layer.NeuralLayer).toBe(
        true,
      );

      // Simple training data
      const trainingData = [
        { input: [0, 0], output: [0] },
        { input: [0, 1], output: [1] },
        { input: [1, 0], output: [1] },
        { input: [1, 1], output: [0] },
      ];

      // Train for a few epochs
      model.train({
        data: trainingData,
        epochs: 10,
        verbose: false,
      });

      // Check adaptation history
      const selfOptimizingLayer = model.layers[0];
      const adaptationHistory = selfOptimizingLayer.getAdaptationHistory();

      expect(adaptationHistory.length).toBeGreaterThan(0);
    });
  });

  describe("Advanced Layer Integration", () => {
    test("should integrate convolutional layers if available", () => {
      // Ensure ConvolutionalLayer and NeuralModel are available
      expect(Prime.Neural.Layer.ConvolutionalLayer).toBeDefined();
      expect(Prime.Neural.Model.NeuralModel).toBeDefined();

      // Create a model with convolutional layers
      const model = new Prime.Neural.Model.NeuralModel();

      // Add a convolutional layer
      model.addLayer({
        type: "convolutional",
        inputShape: [8, 8, 1],
        filters: 4,
        kernelSize: [3, 3],
        strides: [1, 1],
        padding: "valid",
        activation: "relu",
      });

      // Add a flatten layer
      model.addLayer({
        type: "flatten",
      });

      // Add a dense output layer
      model.addLayer({
        type: "dense",
        outputSize: 1,
        activation: "sigmoid",
      });

      model.compile({
        loss: "binaryCrossentropy",
        optimizer: {
          type: "adam",
          learningRate: 0.001,
        },
      });

      // Create a simple 8x8 input image
      const inputImage = Array(8)
        .fill()
        .map(() =>
          Array(8)
            .fill()
            .map(() => [Math.random()]),
        );

      // Test prediction
      const prediction = model.predict(inputImage);

      expect(prediction.length).toBe(1);
      expect(prediction[0] >= 0 && prediction[0] <= 1).toBe(true);
    });

    test("should integrate recurrent layers if available", () => {
      // Ensure RecurrentLayer and NeuralModel are available
      expect(Prime.Neural.Layer.RecurrentLayer).toBeDefined();
      expect(Prime.Neural.Model.NeuralModel).toBeDefined();

      // Create a model with recurrent layers
      const model = new Prime.Neural.Model.NeuralModel();

      // Add an LSTM layer
      model.addLayer({
        type: "recurrent",
        inputSize: 4,
        hiddenSize: 8,
        cellType: "lstm",
        returnSequences: false,
      });

      // Add a dense output layer
      model.addLayer({
        type: "dense",
        outputSize: 1,
        activation: "linear",
      });

      model.compile({
        loss: "mse",
        optimizer: {
          type: "adam",
          learningRate: 0.001,
        },
      });

      // Create a simple sequence
      const sequence = [
        [1, 2, 3, 4],
        [5, 6, 7, 8],
        [9, 10, 11, 12],
      ];

      // Test prediction
      const prediction = model.predict(sequence);

      expect(prediction.length).toBe(1);
    });
  });
});
