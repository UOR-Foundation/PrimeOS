/**
 * PrimeOS JavaScript Library - Neural Network Model Management
 * Central module for model creation, training, and storage
 */

// Import the Prime object from core
const Prime = require("../../core");

// Import model components
require("../model.js");
require("../model-builder.js");
require("../training-loop.js");
require("../model-io.js");

// Create the Neural Model Management module using IIFE
(function () {
  /**
   * Neural Model Management
   * Provides centralized access to model management functionality
   */
  class ModelManagement {
    /**
     * Create a new model
     * @param {Object} config - Model configuration
     * @returns {Prime.Neural.Model.NeuralModel} New neural model
     */
    static createModel(config) {
      return new Prime.Neural.Model.NeuralModel(config);
    }

    /**
     * Create a model builder
     * @param {Object} config - Global model configuration
     * @returns {Prime.Neural.Model.ModelBuilder} Model builder
     */
    static createBuilder(config) {
      return new Prime.Neural.Model.ModelBuilder(config);
    }

    /**
     * Create a sequential model with simplified configuration
     * @param {Array} layers - Array of layer configurations
     * @param {Object} config - Model configuration
     * @returns {Prime.Neural.Model.NeuralModel} Sequential model
     */
    static createSequential(layers, config) {
      return Prime.Neural.Model.ModelBuilder.sequential(layers, config);
    }

    /**
     * Create a model from a predefined architecture
     * @param {string} architecture - Predefined architecture name
     * @param {Object} config - Model configuration
     * @returns {Prime.Neural.Model.NeuralModel} Model with predefined architecture
     */
    static createFromArchitecture(architecture, config) {
      return Prime.Neural.Model.ModelBuilder.fromArchitecture(
        architecture,
        config,
      );
    }

    /**
     * Create a training loop for a model
     * @param {Prime.Neural.Model.NeuralModel} model - Model to train
     * @param {Object} config - Training configuration
     * @returns {Prime.Neural.Model.TrainingLoop} Training loop
     */
    static createTraining(model, config) {
      return new Prime.Neural.Model.TrainingLoop(model, config);
    }

    /**
     * Save model to JSON string
     * @param {Prime.Neural.Model.NeuralModel} model - Model to save
     * @param {Object} options - Serialization options
     * @returns {string} Serialized model
     */
    static saveModel(model, options) {
      return Prime.Neural.Model.ModelIO.serialize(model, options);
    }

    /**
     * Load model from JSON string
     * @param {string} json - Serialized model JSON
     * @param {Object} options - Deserialization options
     * @returns {Prime.Neural.Model.NeuralModel} Loaded model
     */
    static loadModel(json, options) {
      return Prime.Neural.Model.ModelIO.deserialize(json, options);
    }

    /**
     * Extract weights from a model
     * @param {Prime.Neural.Model.NeuralModel} model - Source model
     * @returns {Object} Extracted weights
     */
    static extractWeights(model) {
      return Prime.Neural.Model.ModelIO.extractWeights(model);
    }

    /**
     * Apply weights to a model
     * @param {Prime.Neural.Model.NeuralModel} model - Target model
     * @param {Object} weights - Weights to apply
     * @param {boolean} validateStructure - Whether to validate weights structure
     * @returns {Prime.Neural.Model.NeuralModel} Updated model
     */
    static applyWeights(model, weights, validateStructure) {
      return Prime.Neural.Model.ModelIO.applyWeights(
        model,
        weights,
        validateStructure,
      );
    }

    /**
     * Save model to a file (Node.js environment)
     * @param {Prime.Neural.Model.NeuralModel} model - Model to save
     * @param {string} filePath - Path to save file
     * @param {Object} options - Serialization options
     * @returns {Promise<void>}
     */
    static async saveToFile(model, filePath, options) {
      return Prime.Neural.Model.ModelIO.saveToFile(model, filePath, options);
    }

    /**
     * Load model from a file (Node.js environment)
     * @param {string} filePath - Path to model file
     * @param {Object} options - Deserialization options
     * @returns {Promise<Prime.Neural.Model.NeuralModel>} Loaded model
     */
    static async loadFromFile(filePath, options) {
      return Prime.Neural.Model.ModelIO.loadFromFile(filePath, options);
    }
  }

  // Add to Prime.Neural namespace
  Prime.Neural.ModelManagement = ModelManagement;
})();

// Export the enhanced Prime object
module.exports = Prime;
