/**
 * PrimeOS Neural Distributed - Coherence Validator
 *
 * Utility to validate mathematical coherence of neural network parameters.
 * Ensures numerical stability, coherence between model parts, and detects issues
 * that could cause model divergence in distributed environments.
 */

const Prime = require("../../core/prime.js");

// Create the CoherenceValidator namespace
Prime.Neural = Prime.Neural || {};
Prime.Neural.Distributed = Prime.Neural.Distributed || {};
Prime.Neural.Distributed.CoherenceValidator = {
  /**
   * Validates overall model coherence
   * @param {Object} model - The neural model to validate
   * @returns {Boolean} True if coherent
   */
  validateModelCoherence(model) {
    if (!model || !Array.isArray(model.layers) || model.layers.length === 0) {
      return false;
    }

    // Check layer connectivity
    if (!this._validateLayerConnectivity(model.layers)) {
      return false;
    }

    // Check parameter stability
    if (!this._validateParameterStability(model)) {
      return false;
    }

    // Check activation functions
    if (!this._validateActivationFunctions(model.layers)) {
      return false;
    }

    return true;
  },

  /**
   * Validates parameter numerical stability
   * @param {Object} model - The neural model to validate
   * @returns {Boolean} True if stable
   * @private
   */
  _validateParameterStability(model) {
    for (const layer of model.layers) {
      // Skip layers without weights
      if (!layer.weights || !layer.biases) continue;

      // Check for NaN or Infinity
      if (!this._checkFiniteValues(layer.weights, "weights")) {
        return false;
      }

      if (!this._checkFiniteValues(layer.biases, "biases")) {
        return false;
      }

      // Check for extreme values
      if (!this._checkValueMagnitude(layer.weights, 1e6, "weights")) {
        return false;
      }

      if (!this._checkValueMagnitude(layer.biases, 1e6, "biases")) {
        return false;
      }
    }

    return true;
  },

  /**
   * Checks if all values in a matrix or vector are finite
   * @param {Array} values - Matrix or vector to check
   * @param {String} context - Context for error reporting
   * @returns {Boolean} True if all values are finite
   * @private
   */
  _checkFiniteValues(values, context) {
    if (Array.isArray(values)) {
      for (let i = 0; i < values.length; i++) {
        const row = values[i];

        if (Array.isArray(row)) {
          for (let j = 0; j < row.length; j++) {
            if (!Number.isFinite(row[j])) {
              if (Prime.Logger && Prime.Logger.warn) {
                Prime.Logger.warn(
                  `Non-finite ${context} value at [${i},${j}]: ${row[j]}`,
                );
              }
              return false;
            }
          }
        } else if (!Number.isFinite(row)) {
          if (Prime.Logger && Prime.Logger.warn) {
            Prime.Logger.warn(`Non-finite ${context} value at [${i}]: ${row}`);
          }
          return false;
        }
      }
    }

    return true;
  },

  /**
   * Checks if values exceed a magnitude threshold
   * @param {Array} values - Matrix or vector to check
   * @param {Number} threshold - Maximum allowed absolute value
   * @param {String} context - Context for error reporting
   * @returns {Boolean} True if all values are within range
   * @private
   */
  _checkValueMagnitude(values, threshold, context) {
    if (Array.isArray(values)) {
      for (let i = 0; i < values.length; i++) {
        const row = values[i];

        if (Array.isArray(row)) {
          for (let j = 0; j < row.length; j++) {
            if (Math.abs(row[j]) > threshold) {
              if (Prime.Logger && Prime.Logger.warn) {
                Prime.Logger.warn(
                  `${context} value exceeds threshold at [${i},${j}]: ${row[j]}`,
                );
              }
              return false;
            }
          }
        } else if (Math.abs(row) > threshold) {
          if (Prime.Logger && Prime.Logger.warn) {
            Prime.Logger.warn(
              `${context} value exceeds threshold at [${i}]: ${row}`,
            );
          }
          return false;
        }
      }
    }

    return true;
  },

  /**
   * Validates connectivity between layers
   * @param {Array} layers - Model layers to validate
   * @returns {Boolean} True if connectivity is valid
   * @private
   */
  _validateLayerConnectivity(layers) {
    for (let i = 0; i < layers.length - 1; i++) {
      const currentLayer = layers[i];
      const nextLayer = layers[i + 1];

      if (currentLayer.outputSize !== nextLayer.inputSize) {
        if (Prime.Logger && Prime.Logger.error) {
          Prime.Logger.error(
            `Layer connectivity error: Layer ${i} output (${currentLayer.outputSize}) ` +
              `doesn't match Layer ${i + 1} input (${nextLayer.inputSize})`,
          );
        }
        return false;
      }
    }

    return true;
  },

  /**
   * Validates activation functions
   * @param {Array} layers - Model layers to validate
   * @returns {Boolean} True if activation functions are valid
   * @private
   */
  _validateActivationFunctions(layers) {
    const validActivations = [
      "linear",
      "relu",
      "sigmoid",
      "tanh",
      "softmax",
      "leakyRelu",
    ];

    for (let i = 0; i < layers.length; i++) {
      const layer = layers[i];

      if (layer.activation && !validActivations.includes(layer.activation)) {
        if (Prime.Logger && Prime.Logger.warn) {
          Prime.Logger.warn(
            `Unknown activation function in layer ${i}: ${layer.activation}`,
          );
        }
        return false;
      }
    }

    return true;
  },

  /**
   * Validates gradient stability during training
   * @param {Array} gradients - Gradients to validate
   * @param {Number} threshold - Maximum allowed gradient magnitude
   * @returns {Boolean} True if gradients are stable
   */
  validateGradientStability(gradients, threshold = 1e3) {
    if (!Array.isArray(gradients)) {
      return false;
    }

    let hasExtremeGradients = false;

    for (const layerGradient of gradients) {
      if (!layerGradient) continue;

      // Handle weight gradients (matrix)
      if (Array.isArray(layerGradient.weights)) {
        for (const row of layerGradient.weights) {
          for (const value of row) {
            if (!Number.isFinite(value) || Math.abs(value) > threshold) {
              hasExtremeGradients = true;
              break;
            }
          }
          if (hasExtremeGradients) break;
        }
      }

      // Handle bias gradients (vector)
      if (Array.isArray(layerGradient.biases)) {
        for (const value of layerGradient.biases) {
          if (!Number.isFinite(value) || Math.abs(value) > threshold) {
            hasExtremeGradients = true;
            break;
          }
        }
      }

      if (hasExtremeGradients) break;
    }

    if (hasExtremeGradients && Prime.Logger && Prime.Logger.warn) {
      Prime.Logger.warn(
        "Extreme gradient values detected. Model training may be unstable.",
      );
    }

    return !hasExtremeGradients;
  },

  /**
   * Calculates model coherence metrics
   * @param {Object} model - The neural model
   * @returns {Object} Coherence metrics
   */
  calculateCoherenceMetrics(model) {
    const metrics = {
      layerCount: model.layers.length,
      parameterCount: 0,
      maxParameterValue: -Infinity,
      minParameterValue: Infinity,
      parameterMean: 0,
      parameterStd: 0,
      isCoherent: true,
    };

    const allParameters = [];

    // Collect all parameters
    for (const layer of model.layers) {
      if (!layer.weights || !layer.biases) continue;

      // Process weights
      for (const row of layer.weights) {
        for (const value of row) {
          if (Number.isFinite(value)) {
            allParameters.push(value);
            metrics.parameterCount++;
            metrics.maxParameterValue = Math.max(
              metrics.maxParameterValue,
              value,
            );
            metrics.minParameterValue = Math.min(
              metrics.minParameterValue,
              value,
            );
          }
        }
      }

      // Process biases
      for (const value of layer.biases) {
        if (Number.isFinite(value)) {
          allParameters.push(value);
          metrics.parameterCount++;
          metrics.maxParameterValue = Math.max(
            metrics.maxParameterValue,
            value,
          );
          metrics.minParameterValue = Math.min(
            metrics.minParameterValue,
            value,
          );
        }
      }
    }

    // Calculate mean
    if (allParameters.length > 0) {
      metrics.parameterMean =
        allParameters.reduce((a, b) => a + b, 0) / allParameters.length;

      // Calculate standard deviation
      const variance =
        allParameters.reduce(
          (acc, val) => acc + Math.pow(val - metrics.parameterMean, 2),
          0,
        ) / allParameters.length;
      metrics.parameterStd = Math.sqrt(variance);
    }

    // Determine overall coherence
    metrics.isCoherent =
      Number.isFinite(metrics.parameterMean) &&
      Number.isFinite(metrics.parameterStd) &&
      metrics.parameterStd < 10 &&
      Math.abs(metrics.maxParameterValue) < 1e6 &&
      Math.abs(metrics.minParameterValue) < 1e6;

    return metrics;
  },
};

// Export the module
module.exports = { Neural: Prime.Neural };
