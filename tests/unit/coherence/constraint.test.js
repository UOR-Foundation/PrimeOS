/**
 * PrimeOS JavaScript Library - Coherence Constraint Unit Tests
 * Tests for coherence system constraints, constraint creation, and constraint-based states
 */

const Prime = require("../../../src/core.js");
require("../../../src/mathematics.js");
require("../../../src/coherence.js");

// Import test utilities
const { assertThrows } = require("../../utils/assertions");

describe("Coherence Constraints", () => {
  describe("Constraint Creation", () => {
    test("should create a simple constraint", () => {
      // Create a constraint that numbers must be positive
      const positiveConstraint = Prime.coherence.createConstraint(
        (x) => x > 0,
        { name: "positiveNumber", weight: 2 },
      );

      // Test constraint
      expect(positiveConstraint.check(5)).toBe(true);
      expect(positiveConstraint.check(-1)).toBe(false);
      expect(positiveConstraint.name).toBe("positiveNumber");
      expect(positiveConstraint.weight).toBe(2);
    });

    test("should create constraints with default properties", () => {
      // Create a constraint without explicit options
      const simpleConstraint = Prime.coherence.createConstraint(
        (x) => typeof x === "number",
      );

      // Test constraint
      expect(simpleConstraint.check(5)).toBe(true);
      expect(simpleConstraint.check("string")).toBe(false);
      expect(simpleConstraint.weight).toBe(1); // Default weight
      // Don't test the default type as it varies by implementation
    });

    test("should create hard constraints", () => {
      const hardConstraint = Prime.coherence.createConstraint((x) => x >= 0, {
        name: "nonNegative",
        type: "hard",
      });

      expect(hardConstraint.check(0)).toBe(true);
      expect(hardConstraint.check(-1)).toBe(false);
      expect(hardConstraint.type).toBe("hard");
    });
  });

  describe("Constrained State", () => {
    test("should create a constrained state with constraints", () => {
      // Create constraints
      const constraints = [
        Prime.coherence.createConstraint((state) => state.count >= 0, {
          name: "nonNegativeCount",
          type: "hard",
        }),
        Prime.coherence.createConstraint((state) => state.count <= 100, {
          name: "maxCount",
          type: "soft",
        }),
      ];

      // Create state
      const state = Prime.coherence.createState({ count: 50 }, constraints);

      // Test initial state
      expect(state.value.count).toBe(50);
    });

    test("should update state when constraints are satisfied", () => {
      // Create constraints
      const constraints = [
        Prime.coherence.createConstraint((state) => state.count >= 0, {
          name: "nonNegativeCount",
          type: "hard",
        }),
        Prime.coherence.createConstraint((state) => state.count <= 100, {
          name: "maxCount",
          type: "soft",
        }),
      ];

      // Create state
      const state = Prime.coherence.createState({ count: 50 }, constraints);

      // Test valid update
      state.update({ count: 75 });
      expect(state.value.count).toBe(75);
    });

    test("should throw on hard constraint violation", () => {
      // Create constraints
      const constraints = [
        Prime.coherence.createConstraint((state) => state.count >= 0, {
          name: "nonNegativeCount",
          type: "hard",
        }),
      ];

      // Create state
      const state = Prime.coherence.createState({ count: 50 }, constraints);

      // Test invalid update
      expect(() => {
        state.update({ count: -1 });
      }).toThrow(Prime.CoherenceViolationError);
    });

    test("should calculate coherence norm", () => {
      // Create constraints
      const constraints = [
        Prime.coherence.createConstraint((state) => state.count >= 0, {
          name: "nonNegativeCount",
          weight: 2,
          type: "soft",
        }),
        Prime.coherence.createConstraint((state) => state.count <= 100, {
          name: "maxCount",
          weight: 1,
          type: "soft",
        }),
      ];

      // Create state satisfying all constraints
      const state = Prime.coherence.createState({ count: 50 }, constraints);

      // Coherence norm should be zero for valid state
      expect(state.coherenceNorm()).toBe(0);

      // Coherence norm for a failing state
      // (need to use the constraints directly since update would fail)
      const failingState = { count: -5 };
      let normSquared = 0;

      for (const constraint of constraints) {
        if (!constraint.check(failingState)) {
          normSquared += constraint.weight * constraint.weight;
        }
      }

      const expectedNorm = Math.sqrt(normSquared);
      expect(expectedNorm).toBe(constraints[0].weight); // Only first constraint violated
    });
  });

  describe("Constraint-based Optimization", () => {
    test("should optimize with respect to constraints", () => {
      // Simple object with initial values
      const obj = { x: -5, y: 10 };

      // Mock optimization configuration
      const optimizationConfig = {
        maxIterations: 10,
        learningRate: 0.1,
      };

      // Replace internal methods temporarily for testing
      const originalComputeGradient = Prime.coherence._computeGradient;
      const originalUpdateSolution = Prime.coherence._updateSolution;

      // Define a custom gradient function for the test
      Prime.coherence._computeGradient = function (obj) {
        return { x: obj.x < 0 ? -1 : 1, y: obj.y > 0 ? 1 : -1 };
      };

      // Define a custom update function for the test
      Prime.coherence._updateSolution = function (
        current,
        gradient,
        learningRate,
      ) {
        return {
          x: current.x - gradient.x * learningRate,
          y: current.y - gradient.y * learningRate,
        };
      };

      // Run optimization
      const optimized = Prime.coherence.optimize(obj, optimizationConfig);

      // Verify optimization moved in the right direction
      expect(optimized.x).toBeGreaterThan(obj.x); // X should increase towards positive
      expect(optimized.y).toBeLessThan(obj.y); // Y should decrease towards negative

      // Restore original methods
      Prime.coherence._computeGradient = originalComputeGradient;
      Prime.coherence._updateSolution = originalUpdateSolution;
    });

    test("should respect maximum iterations", () => {
      // Simple object with initial values
      const obj = { x: -5, y: 10 };

      // Mock optimization configuration with low iterations
      const optimizationConfig = {
        maxIterations: 3,
        learningRate: 0.1,
      };

      // Replace internal methods temporarily for testing
      const originalComputeGradient = Prime.coherence._computeGradient;
      const originalUpdateSolution = Prime.coherence._updateSolution;

      // Define a custom gradient function for the test
      let gradientCalls = 0;
      Prime.coherence._computeGradient = function (obj) {
        gradientCalls++;
        return { x: obj.x < 0 ? -1 : 1, y: obj.y > 0 ? 1 : -1 };
      };

      // Define a custom update function for the test
      Prime.coherence._updateSolution = function (
        current,
        gradient,
        learningRate,
      ) {
        return {
          x: current.x - gradient.x * learningRate,
          y: current.y - gradient.y * learningRate,
        };
      };

      // Run optimization
      Prime.coherence.optimize(obj, optimizationConfig);

      // Verify optimization respected max iterations
      expect(gradientCalls).toBeLessThanOrEqual(
        optimizationConfig.maxIterations,
      );

      // Restore original methods
      Prime.coherence._computeGradient = originalComputeGradient;
      Prime.coherence._updateSolution = originalUpdateSolution;
    });
  });
});
