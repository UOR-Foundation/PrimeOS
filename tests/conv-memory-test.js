/**
 * Memory test for PrimeOS Convolutional Layer
 * This test is designed to detect potential memory leaks in the ConvolutionalLayer
 */

// Import Prime with the Neural module
const Prime = require("../src");

// Get initial memory usage
const getMemoryUsage = () => {
  const memoryUsage = process.memoryUsage();
  return {
    rss: Math.round(memoryUsage.rss / 1024 / 1024),
    heapTotal: Math.round(memoryUsage.heapTotal / 1024 / 1024),
    heapUsed: Math.round(memoryUsage.heapUsed / 1024 / 1024),
    external: Math.round(memoryUsage.external / 1024 / 1024),
  };
};

console.log("=== ConvolutionalLayer Memory Test ===\n");
console.log("Initial memory usage:", getMemoryUsage());

// Check if ConvolutionalLayer is available
if (
  !Prime.Neural ||
  !Prime.Neural.Layer ||
  !Prime.Neural.Layer.ConvolutionalLayer
) {
  console.log("ConvolutionalLayer not available, skipping test");
  process.exit(0);
}

// Create a small test input (8x8x3)
const createTestInput = (height, width, channels) => {
  const input = new Array(height);
  for (let y = 0; y < height; y++) {
    input[y] = new Array(width);
    for (let x = 0; x < width; x++) {
      input[y][x] = new Array(channels);
      for (let c = 0; c < channels; c++) {
        input[y][x][c] = Math.random();
      }
    }
  }
  return input;
};

// Create a memory-intensive test that runs many forward and backward passes
const runMemoryTest = async (iterations, inputSize, filterCount) => {
  console.log(
    `\nRunning test with ${iterations} iterations, input size ${inputSize}x${inputSize}x3, ${filterCount} filters`,
  );

  try {
    // Create test layer
    const layer = new Prime.Neural.Layer.ConvolutionalLayer({
      inputShape: [inputSize, inputSize, 3],
      filters: filterCount,
      kernelSize: [3, 3],
      strides: [1, 1],
      padding: "same",
      activation: "relu",
    });

    console.log("Layer created successfully");

    // Memory check after layer creation
    console.log("Memory after layer creation:", getMemoryUsage());

    // Run multiple iterations
    for (let i = 0; i < iterations; i++) {
      // Create fresh input each time to avoid caching
      const input = createTestInput(inputSize, inputSize, 3);

      // Forward pass
      const result = layer.forward(input);

      // Create gradient for backward pass (same shape as output)
      const dY = new Array(result.activation.length);
      for (let y = 0; y < result.activation.length; y++) {
        dY[y] = new Array(result.activation[0].length);
        for (let x = 0; x < result.activation[0].length; x++) {
          dY[y][x] = new Array(result.activation[0][0].length);
          for (let f = 0; f < result.activation[0][0].length; f++) {
            dY[y][x][f] = Math.random() * 0.1;
          }
        }
      }

      // Backward pass
      const gradients = layer.backward(dY, result.cache);

      // Update weights (important to test the full cycle)
      layer.update(gradients, 0.01);

      // Force garbage collection if available
      if (global.gc) {
        global.gc();
      }

      // Report memory usage periodically
      if ((i + 1) % 10 === 0 || i === iterations - 1) {
        console.log(
          `Iteration ${i + 1}/${iterations}, memory:`,
          getMemoryUsage(),
        );
      }
    }

    console.log("\nTest completed successfully");
    return true;
  } catch (error) {
    console.error("Test failed with error:", error);
    return false;
  }
};

// Run test with increasing complexity
const runAllTests = async () => {
  // Start with a small test
  await runMemoryTest(50, 16, 8);

  // Medium size test
  await runMemoryTest(30, 32, 16);

  // Larger test
  await runMemoryTest(20, 64, 32);

  console.log("\n=== Memory Test Summary ===");
  console.log("Final memory usage:", getMemoryUsage());
  console.log("Test completed");
};

runAllTests().catch((err) => {
  console.error("Test execution failed:", err);
  process.exit(1);
});
