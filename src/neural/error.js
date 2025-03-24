/**
 * PrimeOS JavaScript Library - Neural Error Classes
 * Error hierarchy for neural network-specific errors
 * Version 1.0.0
 */

// Import core Prime object to extend the error hierarchy
const Prime = require("../core");

(function (Prime) {
  // Create Neural namespace if it doesn't exist
  Prime.Neural = Prime.Neural || {};
  
  // Create Errors namespace under Neural
  Prime.Neural.Errors = Prime.Neural.Errors || {};

  /**
   * Base error class for all neural-specific errors
   */
  class NeuralError extends Prime.PrimeError {
    /**
     * Creates a new NeuralError
     * @param {string} message - Error message
     * @param {Object} [context] - Additional context
     * @param {string|number} [code] - Error code
     * @param {Error} [cause] - Cause of the error
     */
    constructor(message, context = {}, code = "NEURAL_ERROR", cause = null) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for layer-related issues
   */
  class LayerError extends NeuralError {
    constructor(
      message,
      context = {},
      code = "LAYER_ERROR",
      cause = null
    ) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for layer shape mismatch
   */
  class LayerShapeMismatchError extends LayerError {
    /**
     * Creates a new LayerShapeMismatchError
     * @param {string} message - Error message
     * @param {Array|Object} expected - Expected shape
     * @param {Array|Object} actual - Actual shape
     * @param {Object} [context] - Additional context
     * @param {string} [code] - Error code
     * @param {Error} [cause] - Cause of the error
     */
    constructor(
      message,
      expected,
      actual,
      context = {},
      code = "LAYER_SHAPE_MISMATCH",
      cause = null
    ) {
      // Copy the context to avoid modifying the original
      const contextCopy = Object.assign({}, context, {
        expected,
        actual
      });

      super(message, contextCopy, code, cause);
      this.expected = expected;
      this.actual = actual;
    }
  }

  /**
   * Error for model-related issues
   */
  class ModelError extends NeuralError {
    constructor(
      message,
      context = {},
      code = "MODEL_ERROR",
      cause = null
    ) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for incompatible layer combinations
   */
  class IncompatibleLayersError extends ModelError {
    constructor(
      message,
      context = {},
      code = "INCOMPATIBLE_LAYERS",
      cause = null
    ) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for activation function related issues
   */
  class ActivationError extends NeuralError {
    constructor(
      message,
      context = {},
      code = "ACTIVATION_ERROR",
      cause = null
    ) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for optimizer related issues
   */
  class OptimizerError extends NeuralError {
    constructor(
      message,
      context = {},
      code = "OPTIMIZER_ERROR",
      cause = null
    ) {
      super(message, context, code, cause);
    }
  }
  
  /**
   * Error for training-related issues
   */
  class TrainingError extends NeuralError {
    constructor(
      message,
      context = {},
      code = "TRAINING_ERROR",
      cause = null
    ) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for gradient-related numerical problems
   */
  class GradientError extends TrainingError {
    /**
     * Creates a new GradientError
     * @param {string} message - Error message
     * @param {number} [magnitude] - Magnitude of the gradient issue
     * @param {Object} [context] - Additional context
     * @param {string} [code] - Error code
     * @param {Error} [cause] - Cause of the error
     */
    constructor(
      message,
      magnitude = null,
      context = {},
      code = "GRADIENT_ERROR",
      cause = null
    ) {
      // Copy the context to avoid modifying the original
      const contextCopy = Object.assign({}, context);
      if (magnitude !== null) {
        contextCopy.magnitude = magnitude;
      }

      super(message, contextCopy, code, cause);
      this.magnitude = magnitude;
    }
  }
  
  /**
   * Error for exploding gradient problems
   */
  class ExplodingGradientError extends GradientError {
    constructor(
      message,
      magnitude = null,
      context = {},
      code = "EXPLODING_GRADIENT",
      cause = null
    ) {
      super(message, magnitude, context, code, cause);
    }
  }
  
  /**
   * Error for vanishing gradient problems
   */
  class VanishingGradientError extends GradientError {
    constructor(
      message,
      magnitude = null,
      context = {},
      code = "VANISHING_GRADIENT",
      cause = null
    ) {
      super(message, magnitude, context, code, cause);
    }
  }
  
  /**
   * Error for neural coherence violations
   */
  class NeuralCoherenceError extends NeuralError {
    /**
     * Creates a new NeuralCoherenceError
     * @param {string} message - Error message
     * @param {number} [threshold] - The coherence threshold that was violated
     * @param {number} [actual] - The actual coherence value
     * @param {Object} [context] - Additional context
     * @param {string} [code] - Error code
     * @param {Error} [cause] - Cause of the error
     */
    constructor(
      message,
      threshold = null,
      actual = null,
      context = {},
      code = "NEURAL_COHERENCE_ERROR",
      cause = null
    ) {
      // Copy the context to avoid modifying the original
      const contextCopy = Object.assign({}, context);
      if (threshold !== null) contextCopy.threshold = threshold;
      if (actual !== null) contextCopy.actual = actual;

      super(message, contextCopy, code, cause);
      this.threshold = threshold;
      this.actual = actual;
    }

    /**
     * Calculate violation magnitude
     * @returns {number} The magnitude of the coherence violation
     */
    getViolationMagnitude() {
      if (this.threshold !== null && this.actual !== null) {
        return Math.abs(this.threshold - this.actual);
      }
      return null;
    }
  }

  /**
   * Error for distributed neural network specific issues
   */
  class DistributedNeuralError extends NeuralError {
    constructor(
      message,
      context = {},
      code = "DISTRIBUTED_NEURAL_ERROR",
      cause = null
    ) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for parameter synchronization failures in distributed neural networks
   */
  class ParameterSynchronizationError extends DistributedNeuralError {
    constructor(
      message,
      context = {},
      code = "PARAMETER_SYNC_ERROR",
      cause = null
    ) {
      super(message, context, code, cause);
    }
  }

  // Attach error classes to Prime.Neural.Errors namespace
  Prime.Neural.Errors.NeuralError = NeuralError;
  Prime.Neural.Errors.LayerError = LayerError;
  Prime.Neural.Errors.LayerShapeMismatchError = LayerShapeMismatchError;
  Prime.Neural.Errors.ModelError = ModelError;
  Prime.Neural.Errors.IncompatibleLayersError = IncompatibleLayersError;
  Prime.Neural.Errors.ActivationError = ActivationError;
  Prime.Neural.Errors.OptimizerError = OptimizerError;
  Prime.Neural.Errors.TrainingError = TrainingError;
  Prime.Neural.Errors.GradientError = GradientError;
  Prime.Neural.Errors.ExplodingGradientError = ExplodingGradientError;
  Prime.Neural.Errors.VanishingGradientError = VanishingGradientError;
  Prime.Neural.Errors.NeuralCoherenceError = NeuralCoherenceError;
  Prime.Neural.Errors.DistributedNeuralError = DistributedNeuralError;
  Prime.Neural.Errors.ParameterSynchronizationError = ParameterSynchronizationError;

  // For backward compatibility, also attach directly to Prime.Neural
  Prime.Neural.NeuralError = NeuralError;
  Prime.Neural.LayerError = LayerError;
  Prime.Neural.LayerShapeMismatchError = LayerShapeMismatchError;
  Prime.Neural.ModelError = ModelError;
  Prime.Neural.IncompatibleLayersError = IncompatibleLayersError;
  Prime.Neural.ActivationError = ActivationError;
  Prime.Neural.OptimizerError = OptimizerError;
  Prime.Neural.TrainingError = TrainingError;
  Prime.Neural.GradientError = GradientError;
  Prime.Neural.ExplodingGradientError = ExplodingGradientError;
  Prime.Neural.VanishingGradientError = VanishingGradientError;
  Prime.Neural.NeuralCoherenceError = NeuralCoherenceError;
  Prime.Neural.DistributedNeuralError = DistributedNeuralError;
  Prime.Neural.ParameterSynchronizationError = ParameterSynchronizationError;
})(Prime);

// Export the enhanced Prime object
module.exports = Prime;