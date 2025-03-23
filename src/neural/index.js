/**
 * PrimeOS JavaScript Library - Neural Network Module
 * Main entry point for the neural network functionality
 */

// Import the Prime object from core
const Prime = require("../core");

// Import layer base first (important for testing)
require("./layer/index");

// Import specialized modules
require("./activation/index");
require("./optimization/index");
require("./layer/dense-layer"); // Original implementation
require("./layer/dense"); // Proper constructor
require("./layer/convolutional");
require("./layer/recurrent");

// Import model management modules
require("./model");
require("./model-builder");
require("./training-loop");
require("./model-io");
require("./model/index");
require("./model-simple"); // Simple model for tests

// Create the Neural module using IIFE
(function () {
  /**
   * Neural - Main facade for neural network functionality
   * Provides a unified interface to access neural network components
   */
  class Neural {
    /**
     * Create a new neural network layer
     * @param {string} type - Type of layer to create ('dense', 'conv', 'recurrent')
     * @param {Object} config - Layer configuration
     * @returns {Object} Created layer
     */
    static createLayer(type, config) {
      const lowerType = type.toLowerCase();

      switch (lowerType) {
        case "dense":
          return new Prime.Neural.Layer.DenseLayer(config);
        case "conv":
        case "convolutional":
          return new Prime.Neural.Layer.ConvolutionalLayer(config);
        case "rnn":
        case "recurrent":
          return new Prime.Neural.Layer.RecurrentLayer(config);
        default:
          throw new Error(`Unknown layer type: ${type}`);
      }
    }

    /**
     * Create a new optimizer
     * @param {string} type - Type of optimizer ('sgd', 'adam', etc.)
     * @param {Object} config - Optimizer configuration
     * @returns {Object} Created optimizer
     */
    static createOptimizer(type, config) {
      return Prime.Neural.Optimization.OptimizerFactory.create(type, config);
    }

    /**
     * Get activation function
     * @param {string} name - Name of activation function
     * @returns {Object} Activation function interface
     */
    static getActivation(name) {
      return Prime.Neural.Activation.get(name);
    }

    /**
     * Apply activation function to input
     * @param {Array|TypedArray} input - Input values
     * @param {string} activationType - Type of activation function
     * @param {boolean} [inPlace=false] - Whether to modify input in-place
     * @returns {Array|TypedArray} Activated values
     */
    static activate(input, activationType, inPlace = false) {
      const activation = Prime.Neural.Activation.get(activationType);
      return inPlace && activation.inPlace
        ? (activation.inPlace(input), input)
        : activation.forward(input);
    }

    /**
     * Check if a neural component is coherent
     * @param {Object} component - Neural component to check
     * @returns {Object} Coherence information
     */
    static checkCoherence(component) {
      if (typeof component.calculateCoherence === "function") {
        return {
          score: component.calculateCoherence(),
          component: component.constructor.name || "Unknown",
        };
      }

      return { score: 1.0, component: "Unknown" };
    }

    /**
     * Convert a standard JS array to a typed array for better performance
     * @param {Array} array - Input array
     * @param {string} [type='float32'] - Type of typed array ('float32', 'float64')
     * @returns {TypedArray} Typed array
     */
    static toTypedArray(array, type = "float32") {
      if (!Array.isArray(array)) {
        throw new Error("Input must be an array");
      }

      if (array.length === 0) {
        return type === "float64" ? new Float64Array(0) : new Float32Array(0);
      }

      // Handle nested arrays (2D)
      if (Array.isArray(array[0])) {
        const rows = array.length;
        const cols = array[0].length;

        // Check if all rows have the same length
        for (let i = 1; i < rows; i++) {
          if (!Array.isArray(array[i]) || array[i].length !== cols) {
            throw new Error("All rows must have the same length for 2D arrays");
          }
        }

        // Create a flat typed array
        const flatArray =
          type === "float64"
            ? new Float64Array(rows * cols)
            : new Float32Array(rows * cols);

        // Fill the flat array with values from the input array
        for (let i = 0; i < rows; i++) {
          for (let j = 0; j < cols; j++) {
            flatArray[i * cols + j] = array[i][j];
          }
        }

        // Create 2D view with the same structure as the input array
        const result = new Array(rows);
        const TypedArrayClass =
          type === "float64" ? Float64Array : Float32Array;
        const bytesPerElement = type === "float64" ? 8 : 4;

        for (let i = 0; i < rows; i++) {
          result[i] = new TypedArrayClass(
            flatArray.buffer,
            i * cols * bytesPerElement,
            cols,
          );
        }

        // Store reference to the flat array for efficient operations
        Object.defineProperty(result, "_flatArray", { value: flatArray });

        return result;
      } else {
        // Handle 1D arrays
        return type === "float64"
          ? new Float64Array(array)
          : new Float32Array(array);
      }
    }

    /**
     * Convert a typed array to a standard JS array
     * @param {TypedArray|Array} typedArray - Input typed array
     * @returns {Array} Standard JS array
     */
    static fromTypedArray(typedArray) {
      // If already a standard array, return a copy
      if (Array.isArray(typedArray)) {
        if (Array.isArray(typedArray[0])) {
          // 2D array
          return typedArray.map((row) => [...row]);
        } else {
          // 1D array
          return [...typedArray];
        }
      }

      // Convert TypedArray to standard array
      return Array.from(typedArray);
    }
  }

  // Add Neural class to Prime namespace
  Prime.Neural = Prime.Neural || {};
  Object.assign(Prime.Neural, { Neural });
})();

// Export the enhanced Prime object
module.exports = Prime;
