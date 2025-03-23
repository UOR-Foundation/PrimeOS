/**
 * Custom test runner for matrix-operations-extreme.test.js
 * This adds Jest-like functions for running the tests
 */

// Tracking test success/failure counts
const stats = {
  total: 0,
  passed: 0,
  failed: 0,
  skipped: 0,
};

// Set up test globals
global.describe = (name, fn) => {
  console.log(`\n==== ${name} ====`);
  const describeFn = fn;
  try {
    describeFn();
  } catch (e) {
    console.error(`Error in describe block '${name}': ${e.message}`);
  }
};

global.test = (name, fn) => {
  stats.total++;
  process.stdout.write(`- ${name}... `);
  try {
    fn();
    console.log("✅ PASSED");
    stats.passed++;
  } catch (e) {
    console.log("❌ FAILED");
    console.error(`  Error: ${e.message}`);
    if (e.stack) {
      console.error(`  Stack trace: ${e.stack.split("\n")[1]}`);
    }
    stats.failed++;
  }
};

// Alias for test
global.it = global.test;

global.expect = (actual) => {
  // Base expect object with basic matchers
  const expectObj = {
    // Equality
    toBe: (expected) => {
      if (actual !== expected) {
        throw new Error(`Expected ${expected}, got ${actual}`);
      }
      return expectObj;
    },

    // Defined check
    toBeDefined: () => {
      if (actual === undefined) {
        throw new Error("Expected value to be defined, but got undefined");
      }
      return expectObj;
    },

    // Comparison matchers
    toBeLessThan: (expected) => {
      if (!(actual < expected)) {
        throw new Error(`Expected ${actual} to be less than ${expected}`);
      }
      return expectObj;
    },

    toBeGreaterThan: (expected) => {
      if (!(actual > expected)) {
        throw new Error(`Expected ${actual} to be greater than ${expected}`);
      }
      return expectObj;
    },

    // Approximate equality
    toBeCloseTo: (expected, precision = 2) => {
      if (typeof actual !== "number" || typeof expected !== "number") {
        throw new Error(
          `Both values must be numbers for toBeCloseTo. Got ${typeof actual} and ${typeof expected}`,
        );
      }
      const epsilon = Math.pow(10, -precision);
      const diff = Math.abs(expected - actual);
      if (diff > epsilon) {
        throw new Error(
          `Expected ${actual} to be close to ${expected} (within ${epsilon})`,
        );
      }
      return expectObj;
    },

    // String matchers
    toMatch: (regex) => {
      if (typeof actual !== "string") {
        throw new Error(`Expected a string, got ${typeof actual}`);
      }
      if (!regex.test(actual)) {
        throw new Error(`Expected "${actual}" to match ${regex}`);
      }
      return expectObj;
    },

    // Numeric matchers
    toBeFinite: () => {
      if (!Number.isFinite(actual)) {
        throw new Error(`Expected value to be finite, but got ${actual}`);
      }
      return expectObj;
    },

    // Negated matcher
    not: {
      // Function throw matcher (negated)
      toThrow: (expected) => {
        try {
          if (typeof actual === "function") {
            actual();
          }
        } catch (e) {
          throw new Error(
            `Expected function not to throw, but it threw: ${e.message}`,
          );
        }
        return expectObj;
      },

      // Equality (negated)
      toBe: (expected) => {
        if (actual === expected) {
          throw new Error(`Expected ${actual} not to be ${expected}`);
        }
        return expectObj;
      },
    },
  };

  return expectObj;
};

// Mock implementation of Jest functions for the matrix tests
global.jest = {
  fn: () => {
    const mockFunction = (...args) => {
      mockFunction.mock.calls.push(args);
      return mockFunction.mock.results.length > 0
        ? mockFunction.mock.results[0].value
        : undefined;
    };

    mockFunction.mock = {
      calls: [],
      results: [],
    };

    return mockFunction;
  },
};

// Helper for the matrix equality check in the tests
global.matrixApproxEqual = (A, B, epsilon = 1e-10) => {
  if (!A || !B) return false;
  if (A.length !== B.length) return false;

  let isEqual = true;
  let maxDiff = 0;
  let maxDiffLocation = [0, 0];
  let maxRelDiff = 0;
  let maxRelDiffLocation = [0, 0];

  for (let i = 0; i < A.length; i++) {
    if (A[i].length !== B[i].length) return false;

    for (let j = 0; j < A[i].length; j++) {
      const diff = Math.abs(A[i][j] - B[i][j]);
      const relDiff =
        Math.abs(A[i][j]) > 1e-10 ? diff / Math.abs(A[i][j]) : diff;

      if (diff > maxDiff) {
        maxDiff = diff;
        maxDiffLocation = [i, j];
      }

      if (relDiff > maxRelDiff) {
        maxRelDiff = relDiff;
        maxRelDiffLocation = [i, j];
      }

      if (diff > epsilon) {
        isEqual = false;
        // Don't return immediately so we can collect all diagnostic information
      }
    }
  }

  // For debugging poorly scaled matrix test
  const isDebug =
    A.length === 3 &&
    Math.abs(A[0][0] - 1e10) < 1e9 &&
    Math.abs(A[0][1] - 2e10) < 1e9 &&
    Math.abs(A[0][2] - 3e-10) < 1e-9;

  if (!isEqual && isDebug) {
    console.log("=== Matrix Comparison Debug ===");
    console.log(`Epsilon: ${epsilon}`);
    console.log(`Max absolute difference: ${maxDiff} at [${maxDiffLocation}]`);
    console.log(
      `A[${maxDiffLocation}] = ${A[maxDiffLocation[0]][maxDiffLocation[1]]}`,
    );
    console.log(
      `B[${maxDiffLocation}] = ${B[maxDiffLocation[0]][maxDiffLocation[1]]}`,
    );
    console.log(
      `Max relative difference: ${maxRelDiff} at [${maxRelDiffLocation}]`,
    );

    console.log("\nOriginal matrix:");
    for (let i = 0; i < A.length; i++) {
      console.log(`[${A[i].map((v) => v.toExponential(2)).join(", ")}]`);
    }

    console.log("\nReconstructed matrix:");
    for (let i = 0; i < B.length; i++) {
      console.log(`[${B[i].map((v) => v.toExponential(2)).join(", ")}]`);
    }

    console.log("\nDifference matrix:");
    for (let i = 0; i < A.length; i++) {
      console.log(
        `[${A[i].map((v, j) => Math.abs(v - B[i][j]).toExponential(2)).join(", ")}]`,
      );
    }
  }

  return isEqual;
};

// Skip test (useful for debugging specific tests)
global.skip = () => {
  stats.skipped++;
  return true;
};

// Run the test
console.log("=== Running Matrix Operations Extreme Tests ===");
try {
  require("../extreme/math/matrix-operations-extreme.test.js");
} catch (e) {
  console.error(`\nCritical error in test execution: ${e.message}`);
  if (e.stack) {
    console.error(e.stack);
  }
}

console.log(`\n=== Test Summary ===`);
console.log(`Total: ${stats.total}`);
console.log(`Passed: ${stats.passed}`);
console.log(`Failed: ${stats.failed}`);
if (stats.skipped > 0) {
  console.log(`Skipped: ${stats.skipped}`);
}
console.log(`Success rate: ${Math.round((stats.passed / stats.total) * 100)}%`);
