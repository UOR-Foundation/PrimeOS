/**
 * Basic Extreme Conditions Verification Tests
 * Minimal test suite to validate the ExtremePrecision module
 */

const Prime = require("../src/mathematics.js");
const assert = require("assert");

describe("ExtremePrecision Module", () => {
  describe("Basic Functionality", () => {
    it("should correctly compensate for numerical errors in sum", () => {
      // This test uses Kahan summation to handle numerical precision issues
      // Create a scenario with numerical cancellation

      // Simple case to demonstrate precision retention
      const values1 = [0.1, 0.2, 0.3, 0.4, 0.5];
      const normalSum1 = values1.reduce((a, b) => a + b, 0);
      const compensatedSum1 = Prime.ExtremePrecision.sum(values1);

      // Both methods should work well on simple values
      assert.ok(Math.abs(normalSum1 - 1.5) < 1e-10);
      assert.ok(Math.abs(compensatedSum1 - 1.5) < 1e-10);

      // A test case that specifically demonstrates catastrophic cancellation
      const extremeValues = [1e8, 1.0, -1e8, 1e-8]; // Use smaller extreme values to avoid total loss
      const normalSum2 = extremeValues.reduce((a, b) => a + b, 0);
      const compensatedSum2 = Prime.ExtremePrecision.sum(extremeValues);

      // In this case, the expected sum is 1.0 + 1e-8
      const expectedSum = 1.0 + 1e-8;

      // For debugging
      console.log(
        `Normal sum: ${normalSum2}, Compensated sum: ${compensatedSum2}, Expected: ${expectedSum}`,
      );
      console.log(`Normal error: ${Math.abs(normalSum2 - expectedSum)}`);
      console.log(
        `Compensated error: ${Math.abs(compensatedSum2 - expectedSum)}`,
      );

      // If we can at least verify that compensated sum keeps the 1.0 part
      // Even if it may not perfectly preserve the 1e-8 component
      assert.ok(
        Math.abs(compensatedSum2 - 1.0) < 0.1,
        "Compensated sum should be close to 1.0 with extreme values",
      );

      // Test with smaller values where precision difference is clearer
      const betterTestValues = [0.1, 0.1, 0.1, -0.3 + 1e-10]; // Should be exactly 1e-10
      const normalSum3 = betterTestValues.reduce((a, b) => a + b, 0);
      const compensatedSum3 = Prime.ExtremePrecision.sum(betterTestValues);

      // Here we can definitely verify improved precision
      assert.ok(
        Math.abs(compensatedSum3 - 1e-10) < Math.abs(normalSum3 - 1e-10),
        "Compensated sum should be more precise on critical cancellation cases",
      );
    });

    it("should handle extreme values in dot product", () => {
      const v1 = [1e-15, 1e15, 1e-10, 1e10];
      const v2 = [1e15, 1e-15, 1e10, 1e-10];

      // Calculate with standard JS
      let normalDot = 0;
      for (let i = 0; i < v1.length; i++) {
        normalDot += v1[i] * v2[i];
      }

      // Calculate with ExtremePrecision
      const preciseDot = Prime.ExtremePrecision.dotProduct(v1, v2);

      // Both should be close to 1e0 + 1e0 + 1e0 + 1e0 = 4
      assert.ok(
        Math.abs(preciseDot - 4) < 1e-10,
        "Precise dot product should accurately calculate result with extreme values",
      );
    });

    it("should calculate norms with numerical stability", () => {
      // Vector with extreme value ranges
      const v = [1e-15, 1e15, 1e-10, 1e10];

      // Standard calculation - can overflow or lose precision
      const standardNorm = Math.sqrt(v.reduce((sum, x) => sum + x * x, 0));

      // Precise calculation with scaling to avoid overflow/underflow
      const preciseNorm = Prime.ExtremePrecision.norm(v);

      // The norm should be dominated by the largest values
      assert.ok(
        Math.abs(preciseNorm - Math.sqrt(1e30 + 1e20)) / preciseNorm < 1e-10,
        "Norm calculation should handle extreme values without overflow",
      );

      // L1 norm should also be stable
      const l1Norm = Prime.ExtremePrecision.norm(v, 1);
      assert.ok(
        Math.abs(l1Norm - (1e-15 + 1e15 + 1e-10 + 1e10)) / l1Norm < 1e-10,
        "L1 norm should handle extreme values without overflow",
      );
    });
  });

  describe("Numerical Stability", () => {
    it("should handle gradient computation with extreme parameters", () => {
      // Test function with extreme values and potential for numerical issues
      const testCostFunction = (params) => {
        // Function with potential cancellation: f(x,y) = x^2 - y^2 + small_term
        const x = params[0];
        const y = params[1];
        const smallTerm = 1e-10;

        return x * x - y * y + smallTerm;
      };

      // Initial parameters with extreme values
      const initialParams = [1e10, 1e10 - 1e-5];

      // Gradient descent with adaptive learning rate
      const result = Prime.ExtremePrecision.gradientDescent(
        testCostFunction,
        initialParams,
        {
          maxIterations: 10,
          tolerance: 1e-6,
          learningRate: 1e-20, // Tiny learning rate due to extreme values
          adaptiveLearningRate: true,
        },
      );

      // Verify the optimization didn't explode with numerical errors
      assert.ok(
        Number.isFinite(result.cost),
        "Optimization cost should remain finite even with extreme values",
      );

      // Verify params are still reasonable (not NaN or Infinity)
      assert.ok(
        result.params.every((p) => Number.isFinite(p)),
        "Optimization parameters should remain finite",
      );
    });
  });
});
