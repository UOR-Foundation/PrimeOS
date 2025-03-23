/**
 * PrimeOS JavaScript Library - Neural Layer Module
 * Dense (Fully-Connected) Layer Implementation
 */

// Import the Prime object from core
const Prime = require("../../core");

// Create the Dense class
class Dense {
  /**
   * Create a new dense layer with specified dimensions
   * @param {number} inputSize - Size of input
   * @param {number} outputSize - Size of output
   * @param {Object} [options={}] - Layer options
   */
  constructor(inputSize, outputSize, options = {}) {
    // Create configuration object
    const config = {
      inputSize,
      outputSize,
      activation: options.activation || "sigmoid",
      useTypedArrays: options.useTypedArrays || false,
      initParams: options.initParams || {},
    };

    // Create underlying layer implementation
    this.layer = new Prime.Neural.Layer.DenseLayer(config);

    // Copy properties for convenience
    this.inputSize = inputSize;
    this.outputSize = outputSize;
    this.activation = config.activation;
    this.weights = this.layer.weights;
    this.biases = this.layer.biases;
  }

  /**
   * Forward pass through layer
   * @param {Array|TypedArray} input - Input data
   * @param {Object} options - Forward options
   * @returns {Array|TypedArray} Activated output
   */
  forward(input, options) {
    const result = this.layer.forward(input, options);
    return result.activation;
  }

  /**
   * Backward pass through layer
   * @param {Array|TypedArray} gradient - Gradient from next layer
   * @param {Object} cache - Cache from forward pass
   * @returns {Object} Gradients for parameters and inputs
   */
  backward(gradient, cache = {}) {
    // Ensure the cache has required properties
    const fullCache = {
      input: cache.input || [],
      z: cache.z || [],
      activation: cache.activation || [],
    };

    return this.layer.backward(gradient, fullCache);
  }

  /**
   * Update layer parameters
   * @param {Object} gradients - Weight and bias gradients
   * @param {number} learningRate - Learning rate
   * @param {Object} options - Update options
   */
  update(gradients, learningRate, options) {
    this.layer.update(gradients, learningRate, options);

    // Update local references
    this.weights = this.layer.weights;
    this.biases = this.layer.biases;
  }

  /**
   * Get configuration for serialization
   * @returns {Object} Layer configuration
   */
  getConfig() {
    return {
      inputSize: this.inputSize,
      outputSize: this.outputSize,
      activation: this.activation,
    };
  }

  /**
   * Get a summary of the layer
   * @returns {Object} Layer summary
   */
  getSummary() {
    return this.layer.getSummary();
  }
}

// Add Dense class to Prime.Neural.Layer namespace
Prime.Neural.Layer = Prime.Neural.Layer || {};
Prime.Neural.Layer.Dense = Dense;

// Export the enhanced Prime object
module.exports = Prime;
