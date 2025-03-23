/**
 * PrimeOS Test Utilities
 *
 * Standardized utilities for PrimeOS tests.
 * This module exports all test utilities from a single entry point.
 */

const Assertions = require("./assertions");
const Mocking = require("./mocking");
const Setup = require("./setup");
const Environments = require("./environments");

/**
 * Test fixture utilities for creating standardized test data
 */
const Fixtures = {
  /**
   * Create a test vector with specified dimension and pattern
   *
   * @param {string} pattern - Pattern type ('identity', 'random', 'sequence', 'zeros', 'ones')
   * @param {number} dimension - Vector dimension
   * @param {Object} [options] - Additional options
   * @returns {Array} - Test vector
   */
  createVector: (pattern, dimension, options = {}) => {
    switch (pattern) {
      case "identity":
        return Array(dimension)
          .fill(0)
          .map((_, i) => (i === options.index ? 1 : 0));
      case "random":
        return Array(dimension)
          .fill(0)
          .map(() => Math.random());
      case "sequence":
        return Array(dimension)
          .fill(0)
          .map((_, i) => i + (options.start || 0));
      case "zeros":
        return Array(dimension).fill(0);
      case "ones":
        return Array(dimension).fill(1);
      case "extreme":
        return Array(dimension)
          .fill(0)
          .map((_, i) => {
            if (i % 4 === 0) return 1e-15; // Extremely small
            if (i % 4 === 1) return 1e15; // Extremely large
            if (i % 4 === 2) return 0; // Zero
            return 1; // Regular value
          });
      default:
        throw new Error(`Unknown vector pattern: ${pattern}`);
    }
  },

  /**
   * Create a test matrix with specified dimensions and pattern
   *
   * @param {string} pattern - Pattern type ('identity', 'random', 'sequence', 'zeros', 'ones')
   * @param {number} rows - Number of rows
   * @param {number} cols - Number of columns
   * @param {Object} [options] - Additional options
   * @returns {Array} - Test matrix
   */
  createMatrix: (pattern, rows, cols, options = {}) => {
    const matrix = Array(rows)
      .fill()
      .map(() => Array(cols).fill(0));

    switch (pattern) {
      case "identity":
        for (let i = 0; i < Math.min(rows, cols); i++) {
          matrix[i][i] = 1;
        }
        break;
      case "random":
        for (let i = 0; i < rows; i++) {
          for (let j = 0; j < cols; j++) {
            matrix[i][j] = Math.random();
          }
        }
        break;
      case "sequence":
        for (let i = 0; i < rows; i++) {
          for (let j = 0; j < cols; j++) {
            matrix[i][j] = i * cols + j + (options.start || 0);
          }
        }
        break;
      case "zeros":
        // Already filled with zeros
        break;
      case "ones":
        for (let i = 0; i < rows; i++) {
          for (let j = 0; j < cols; j++) {
            matrix[i][j] = 1;
          }
        }
        break;
      case "extreme":
        for (let i = 0; i < rows; i++) {
          for (let j = 0; j < cols; j++) {
            const index = i * cols + j;
            if (index % 5 === 0)
              matrix[i][j] = 1e-15; // Extremely small
            else if (index % 5 === 1)
              matrix[i][j] = 1e15; // Extremely large
            else if (index % 5 === 2)
              matrix[i][j] = 0; // Zero
            else if (index % 5 === 3)
              matrix[i][j] = 1; // Regular value
            else matrix[i][j] = -1; // Negative value
          }
        }
        break;
      default:
        throw new Error(`Unknown matrix pattern: ${pattern}`);
    }

    return matrix;
  },

  /**
   * Create test data for a neural network
   *
   * @param {Object} options - Options for the test data
   * @param {number} [options.inputSize=10] - Input size
   * @param {number} [options.outputSize=2] - Output size
   * @param {number} [options.samples=100] - Number of samples
   * @returns {Object} - Neural network test data
   */
  createNeuralTestData: (options = {}) => {
    const inputSize = options.inputSize || 10;
    const outputSize = options.outputSize || 2;
    const samples = options.samples || 100;

    const inputs = [];
    const outputs = [];

    for (let i = 0; i < samples; i++) {
      // Create input vector
      const input = Array(inputSize)
        .fill(0)
        .map(() => Math.random());
      inputs.push(input);

      // Create corresponding output
      const output = Array(outputSize)
        .fill(0)
        .map(() => Math.random());
      outputs.push(output);
    }

    return { inputs, outputs, inputSize, outputSize, samples };
  },

  /**
   * Create test data for coherence testing
   *
   * @param {Object} options - Options for the test data
   * @param {number} [options.constraintCount=3] - Number of constraints
   * @param {number} [options.dimension=10] - State dimension
   * @returns {Object} - Coherence test data
   */
  createCoherenceTestData: (options = {}) => {
    const constraintCount = options.constraintCount || 3;
    const dimension = options.dimension || 10;

    // Create state vector
    const state = Array(dimension)
      .fill(0)
      .map(() => Math.floor(Math.random() * 100));

    // Create constraints
    const constraints = [];

    // Constraint 1: Sum >= threshold
    constraints.push({
      name: "SumConstraint",
      check: (state, params) => {
        const sum = state.reduce((a, b) => a + b, 0);
        return sum >= params.threshold;
      },
      params: { threshold: dimension * 25 }, // average value at least 25
      weight: 2,
    });

    // Constraint 2: Max <= threshold
    constraints.push({
      name: "MaxConstraint",
      check: (state, params) => {
        const max = Math.max(...state);
        return max <= params.threshold;
      },
      params: { threshold: 90 },
      weight: 1,
    });

    // Constraint 3: Min >= threshold
    constraints.push({
      name: "MinConstraint",
      check: (state, params) => {
        const min = Math.min(...state);
        return min >= params.threshold;
      },
      params: { threshold: 10 },
      weight: 1,
    });

    // Add more constraints if needed
    for (let i = 3; i < constraintCount; i++) {
      constraints.push({
        name: `CustomConstraint${i}`,
        check: (state, params) => {
          // Every third value must be even
          for (let j = 0; j < state.length; j += 3) {
            if (state[j] % 2 !== 0) {
              return false;
            }
          }
          return true;
        },
        params: {},
        weight: 1,
      });
    }

    return { state, constraints };
  },
};

module.exports = {
  Assertions,
  Mocking,
  Setup,
  Environments,
  Fixtures,
};
