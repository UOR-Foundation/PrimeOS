/**
 * Tests for PrimeOS Neural Module
 */

// Import Prime with the Neural module
const Prime = require("../src");

// Test utilities
const assert = (condition, message) => {
  if (!condition) {
    throw new Error(`Assertion failed: ${message}`);
  }
  console.log(`✓ PASS: ${message}`);
};

const assertApproximatelyEqual = (a, b, message, epsilon = 1e-6) => {
  const diff = Math.abs(a - b);
  if (diff > epsilon) {
    throw new Error(
      `Assertion failed: ${message} - values differ by ${diff} (${a} vs ${b})`,
    );
  }
  console.log(`✓ PASS: ${message}`);
};

const runTests = () => {
  console.log("=== Running Neural Module Tests ===\n");

  // Test group: Neural Layer
  console.log("--- Neural Layer Tests ---");

  // Test base neural layer creation
  {
    const layer = new Prime.Neural.Layer.NeuralLayer({
      inputSize: 3,
      outputSize: 2,
      activation: "sigmoid",
    });

    assert(
      layer instanceof Prime.Neural.Layer.NeuralLayer,
      "NeuralLayer can be instantiated",
    );

    assert(layer.inputSize === 3, "Layer has correct input size");
    assert(layer.outputSize === 2, "Layer has correct output size");
    assert(layer.activation === "sigmoid", "Layer has correct activation");

    assert(Array.isArray(layer.weights), "Weights are initialized as array");
    assert(layer.weights.length === 2, "Weights array has correct dimensions");
    assert(
      layer.weights[0].length === 3,
      "Weights array has correct second dimension",
    );

    assert(Array.isArray(layer.biases), "Biases are initialized as array");
    assert(layer.biases.length === 2, "Biases array has correct length");
  }

  // Test forward pass
  {
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

    assert(
      Array.isArray(result.activation),
      "Forward pass returns activation array",
    );
    assert(result.activation.length === 2, "Activation has correct dimensions");
    assert(result.activation[0] === 2, "First neuron has correct activation");
    assert(result.activation[1] === 3, "Second neuron has correct activation");
  }

  // Test backward pass
  {
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

    assert(
      gradients.dW !== undefined,
      "Backward pass returns weight gradients",
    );
    assert(gradients.dB !== undefined, "Backward pass returns bias gradients");
    assert(gradients.dX !== undefined, "Backward pass returns input gradients");

    assert(gradients.dW[0][0] === 2, "First weight gradient is correct");
    assert(gradients.dW[1][1] === 3, "Second weight gradient is correct");
    assert(gradients.dB[0] === 1, "First bias gradient is correct");
    assert(gradients.dB[1] === 1, "Second bias gradient is correct");
  }

  // Test layer update
  {
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

    assertApproximatelyEqual(
      layer.weights[0][0],
      0.4,
      "Weight updated correctly",
    );
    assertApproximatelyEqual(
      layer.weights[0][1],
      0.3,
      "Weight updated correctly",
    );
    assertApproximatelyEqual(layer.biases[0], -0.3, "Bias updated correctly");
  }

  // Test group: Self-Optimizing Layer
  console.log("\n--- Self-Optimizing Layer Tests ---");

  // Test self-optimizing layer creation
  {
    const layer = new Prime.Neural.Layer.SelfOptimizingLayer({
      inputSize: 4,
      outputSize: 3,
      activation: "relu",
      optimization: {
        adaptThreshold: 50,
        coherenceThreshold: 0.75,
      },
    });

    assert(
      layer instanceof Prime.Neural.Layer.SelfOptimizingLayer,
      "SelfOptimizingLayer can be instantiated",
    );

    assert(
      layer.optimization.enabled === true,
      "Optimization is enabled by default",
    );
    assert(
      layer.optimization.adaptThreshold === 50,
      "Custom adaptation threshold set correctly",
    );
    assert(
      layer.optimization.coherenceThreshold === 0.75,
      "Custom coherence threshold set correctly",
    );

    assert(
      Array.isArray(layer.adaptationState.dropoutMask),
      "Dropout mask initialized",
    );
    assert(
      layer.adaptationState.dropoutMask.length === 3,
      "Dropout mask has correct size",
    );
  }

  // Test layer adaptation
  {
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
    assert(Array.isArray(history), "Adaptation history is available");
    assert(history.length > 0, "At least one adaptation event recorded");
    assert(history[0].iteration !== undefined, "Adaptation records iteration");
    assert(
      history[0].coherenceBefore !== undefined,
      "Adaptation records coherence before",
    );
    assert(
      history[0].coherenceAfter !== undefined,
      "Adaptation records coherence after",
    );
  }

  // Test layer analysis
  {
    const layer = new Prime.Neural.Layer.SelfOptimizingLayer({
      inputSize: 4,
      outputSize: 3,
      activation: "sigmoid",
    });

    // Run forward pass to generate some usage statistics
    layer.forward([1, 2, 3, 4]);

    const analysis = layer.analyzeLayer();
    assert(typeof analysis === "object", "Layer analysis returns an object");
    assert(
      typeof analysis.coherence === "number",
      "Analysis includes coherence score",
    );
    assert(
      typeof analysis.utilizationRate === "number",
      "Analysis includes utilization rate",
    );
    assert(
      Array.isArray(analysis.recommendations),
      "Analysis includes recommendations",
    );
  }

  // Test group: Neural Optimization
  console.log("\n--- Neural Optimization Tests ---");

  // Test coherence SGD optimizer
  {
    const optimizer = new Prime.Neural.Optimization.CoherenceSGD({
      learningRate: 0.1,
      momentum: 0.9,
      minCoherence: 0.5,
    });

    assert(
      optimizer instanceof Prime.Neural.Optimization.CoherenceOptimizer,
      "CoherenceSGD extends CoherenceOptimizer",
    );

    assert(optimizer.learningRate === 0.1, "Learning rate set correctly");
    assert(optimizer.momentum === 0.9, "Momentum set correctly");
    assert(optimizer.minCoherence === 0.5, "Minimum coherence set correctly");
  }

  // Test optimizer update with coherence constraint
  {
    const optimizer = new Prime.Neural.Optimization.CoherenceSGD({
      learningRate: 0.1,
      minCoherence: 0.5,
    });

    // Simple parameters and gradients
    const params = {
      weights: [
        [1, 1],
        [1, 1],
      ],
      biases: [0, 0],
    };

    const gradients = {
      weights: [
        [0.1, 0.1],
        [0.1, 0.1],
      ],
      biases: [0.1, 0.1],
    };

    // Simple coherence function that returns 0.8 for any input
    const coherenceFn = () => 0.8;

    const updatedParams = optimizer.update(params, gradients, coherenceFn);

    assert(
      updatedParams.weights[0][0] < params.weights[0][0],
      "Parameter updated in the direction of negative gradient",
    );
    assert(
      typeof optimizer.getStatistics().iterations === "number",
      "Optimizer tracks iterations",
    );
  }

  // Test optimizer update with coherence violation
  {
    const optimizer = new Prime.Neural.Optimization.CoherenceSGD({
      learningRate: 0.1,
      minCoherence: 0.7,
    });

    // Simple parameters and gradients
    const params = {
      weights: [
        [1, 1],
        [1, 1],
      ],
      biases: [0, 0],
    };

    const gradients = {
      weights: [
        [0.1, 0.1],
        [0.1, 0.1],
      ],
      biases: [0.1, 0.1],
    };

    // Coherence function that starts at 0.8 but drops to 0.6 after update
    let calls = 0;
    const coherenceFn = () => {
      calls++;
      return calls === 1 ? 0.8 : 0.6;
    };

    const updatedParams = optimizer.update(params, gradients, coherenceFn);

    assert(
      updatedParams.weights[0][0] < params.weights[0][0],
      "Parameter still updated despite coherence drop",
    );
    assert(calls > 1, "Coherence function called multiple times");
  }

  // Test Adam optimizer
  {
    const optimizer = new Prime.Neural.Optimization.CoherenceAdam({
      learningRate: 0.001,
      beta1: 0.9,
      beta2: 0.999,
      minCoherence: 0.5,
    });

    assert(
      optimizer instanceof Prime.Neural.Optimization.CoherenceOptimizer,
      "CoherenceAdam extends CoherenceOptimizer",
    );

    assert(optimizer.learningRate === 0.001, "Learning rate set correctly");
    assert(optimizer.beta1 === 0.9, "Beta1 set correctly");
    assert(optimizer.beta2 === 0.999, "Beta2 set correctly");

    // Simple parameters and gradients
    const params = {
      weights: [
        [1, 1],
        [1, 1],
      ],
      biases: [0, 0],
    };

    const gradients = {
      weights: [
        [0.1, 0.1],
        [0.1, 0.1],
      ],
      biases: [0.1, 0.1],
    };

    // Simple coherence function that returns 0.8 for any input
    const coherenceFn = () => 0.8;

    const updatedParams = optimizer.update(params, gradients, coherenceFn);

    assert(
      updatedParams.weights[0][0] < params.weights[0][0],
      "Parameter updated in the direction of negative gradient",
    );
  }

  // Test integrated neural network with self-optimization
  console.log("\n--- Integrated Neural Network Test ---");

  // Simple XOR test
  {
    // Create a 2-layer network for XOR problem
    const hiddenLayer = new Prime.Neural.Layer.SelfOptimizingLayer({
      inputSize: 2,
      outputSize: 4,
      activation: "sigmoid",
      optimization: {
        adaptThreshold: 5, // Adapt more frequently for test
        coherenceThreshold: 1.0, // Always adapt
        adaptationRate: 0.05,
      },
    });

    const outputLayer = new Prime.Neural.Layer.NeuralLayer({
      // Use regular layer for output
      inputSize: 4,
      outputSize: 1,
      activation: "sigmoid",
    });

    // Training data for XOR
    const trainingData = [
      { input: [0, 0], expected: [0] },
      { input: [0, 1], expected: [1] },
      { input: [1, 0], expected: [1] },
      { input: [1, 1], expected: [0] },
    ];

    // Simple training loop without optimizer for testing
    const epochs = 50; // Reduce epochs for faster testing

    for (let epoch = 0; epoch < epochs; epoch++) {
      for (const sample of trainingData) {
        // Forward pass
        const hiddenResult = hiddenLayer.forward(sample.input);
        const outputResult = outputLayer.forward(hiddenResult.activation);

        // Calculate output gradient
        const prediction = outputResult.activation[0];
        const target = sample.expected[0];
        const dY = [prediction - target];

        // Backward pass
        const outputGradients = outputLayer.backward(dY, outputResult.cache);
        const hiddenGradients = hiddenLayer.backward(
          outputGradients.dX,
          hiddenResult.cache,
        );

        // Update parameters directly
        outputLayer.update(outputGradients, 0.1);
        hiddenLayer.update(hiddenGradients, 0.1);
      }
    }

    // Test for adaptation history only
    const adaptationHistory = hiddenLayer.getAdaptationHistory();
    assert(
      adaptationHistory.length > 0,
      "Hidden layer adapted during training",
    );

    console.log(`Adaptation history entries: ${adaptationHistory.length}`);
    console.log(`Hidden layer coherence: ${hiddenLayer.metrics.coherence}`);

    // Run prediction on a single sample
    const testSample = trainingData[1]; // [0,1] -> 1
    const hiddenResult = hiddenLayer.forward(testSample.input);
    const outputResult = outputLayer.forward(hiddenResult.activation);

    console.log(
      `Test prediction: Input [${testSample.input}], Output ${outputResult.activation[0]}`,
    );
  }

  console.log("\n=== All Neural Module Tests Passed ===");
};

// Run the tests
try {
  runTests();
} catch (error) {
  console.error("Test failed:", error.message);
  console.error(error.stack);
  process.exit(1);
}
