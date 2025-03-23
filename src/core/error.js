/**
 * PrimeOS JavaScript Library - Error Classes
 * Comprehensive error hierarchy for PrimeOS
 * Version 1.0.0
 */

// Import Prime object from prime.js
const Prime = require("./prime.js");

(function (Prime) {
  /**
   * Base error class for all Prime errors
   */
  class PrimeError extends Error {
    /**
     * Creates a new PrimeError
     * @param {string} message - Error message
     * @param {Object} [context] - Additional context
     * @param {string|number} [code] - Error code
     * @param {Error} [cause] - Cause of the error
     */
    constructor(message, context = {}, code = "PRIME_ERROR", cause = null) {
      super(message);
      this.name = this.constructor.name;
      this.timestamp = new Date().toISOString();

      // Ensure context is a plain object
      this.context =
        context && typeof context === "object"
          ? Object.assign({}, context)
          : {};

      this.code = code;
      this.cause = cause;

      // Capture stack trace
      if (Error.captureStackTrace) {
        Error.captureStackTrace(this, this.constructor);
      }
    }

    /**
     * Get error details for logging or serialization
     * @returns {Object} Error details
     */
    toJSON() {
      return {
        name: this.name,
        message: this.message,
        code: this.code,
        context: this.context,
        cause: this.cause ? this.cause.message : null,
        stack: this.stack,
      };
    }
  }

  /**
   * Error for validation failures
   */
  class ValidationError extends PrimeError {
    constructor(
      message,
      context = {},
      code = "VALIDATION_ERROR",
      cause = null,
    ) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for configuration issues
   */
  class ConfigurationError extends PrimeError {
    constructor(message, context = {}, code = "CONFIG_ERROR", cause = null) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for invalid operations
   */
  class InvalidOperationError extends PrimeError {
    constructor(
      message,
      context = {},
      code = "INVALID_OPERATION",
      cause = null,
    ) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for unsupported operations
   */
  class UnsupportedOperationError extends PrimeError {
    constructor(
      message,
      context = {},
      code = "UNSUPPORTED_OPERATION",
      cause = null,
    ) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for timeout issues
   */
  class TimeoutError extends PrimeError {
    constructor(message, context = {}, code = "TIMEOUT", cause = null) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for resource exhaustion issues
   */
  class ResourceExhaustionError extends PrimeError {
    constructor(
      message,
      context = {},
      code = "RESOURCE_EXHAUSTED",
      cause = null,
    ) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for security violations
   */
  class SecurityError extends PrimeError {
    constructor(
      message,
      context = {},
      code = "SECURITY_VIOLATION",
      cause = null,
    ) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for network issues
   */
  class NetworkError extends PrimeError {
    constructor(message, context = {}, code = "NETWORK_ERROR", cause = null) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for dependency issues
   */
  class DependencyError extends PrimeError {
    constructor(
      message,
      context = {},
      code = "DEPENDENCY_ERROR",
      cause = null,
    ) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for serialization issues
   */
  class SerializationError extends PrimeError {
    constructor(
      message,
      context = {},
      code = "SERIALIZATION_ERROR",
      cause = null,
    ) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for state management issues
   */
  class StateError extends PrimeError {
    constructor(message, context = {}, code = "STATE_ERROR", cause = null) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for coherence violations
   */
  class CoherenceError extends PrimeError {
    constructor(
      message,
      context = {},
      code = "COHERENCE_VIOLATION",
      cause = null,
    ) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for specific coherence violations with constraint and magnitude
   */
  class CoherenceViolationError extends PrimeError {
    /**
     * Creates a new CoherenceViolationError
     * @param {string} message - Error message
     * @param {Object} constraint - The constraint that was violated
     * @param {number} magnitude - The magnitude of the violation
     * @param {Object} [context] - Additional context
     * @param {string} [code] - Error code
     * @param {Error} [cause] - Cause of the error
     */
    constructor(
      message,
      constraint,
      magnitude,
      context = {},
      code = "COHERENCE_VIOLATION",
      cause = null,
    ) {
      // Copy the context to avoid modifying the original
      const contextCopy = Object.assign({}, context);

      super(message, contextCopy, code, cause);
      this.constraint = constraint;
      this.magnitude = magnitude;
    }
  }

  /**
   * Error for component lifecycle issues
   */
  class ComponentError extends PrimeError {
    constructor(message, context = {}, code = "COMPONENT_ERROR", cause = null) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for mathematical calculation issues
   */
  class MathError extends PrimeError {
    constructor(message, context = {}, code = "MATH_ERROR", cause = null) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for numerical instability issues
   */
  class NumericalInstabilityError extends MathError {
    constructor(
      message,
      context = {},
      code = "NUMERICAL_INSTABILITY",
      cause = null,
    ) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for matrix singularity issues
   */
  class MatrixSingularityError extends MathError {
    constructor(message, context = {}, code = "MATRIX_SINGULAR", cause = null) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for dimension mismatch in mathematical operations
   */
  class DimensionMismatchError extends MathError {
    constructor(
      message,
      context = {},
      code = "DIMENSION_MISMATCH",
      cause = null,
    ) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for overflow/underflow issues
   */
  class NumericOverflowError extends MathError {
    constructor(
      message,
      context = {},
      code = "NUMERIC_OVERFLOW",
      cause = null,
    ) {
      super(message, context, code, cause);
    }
  }

  /**
   * Error for convergence issues in iterative algorithms
   */
  class ConvergenceError extends MathError {
    constructor(
      message,
      context = {},
      code = "CONVERGENCE_FAILURE",
      cause = null,
    ) {
      super(message, context, code, cause);
    }
  }

  // Create Errors object if it doesn't exist already
  Prime.Errors = Prime.Errors || {};

  // Attach error classes to Prime.Errors namespace
  Prime.Errors.PrimeError = PrimeError;
  Prime.Errors.ValidationError = ValidationError;
  Prime.Errors.ConfigurationError = ConfigurationError;
  Prime.Errors.InvalidOperationError = InvalidOperationError;
  Prime.Errors.UnsupportedOperationError = UnsupportedOperationError;
  Prime.Errors.TimeoutError = TimeoutError;
  Prime.Errors.ResourceExhaustionError = ResourceExhaustionError;
  Prime.Errors.SecurityError = SecurityError;
  Prime.Errors.NetworkError = NetworkError;
  Prime.Errors.DependencyError = DependencyError;
  Prime.Errors.SerializationError = SerializationError;
  Prime.Errors.StateError = StateError;
  Prime.Errors.CoherenceError = CoherenceError;
  Prime.Errors.CoherenceViolationError = CoherenceViolationError;
  Prime.Errors.ComponentError = ComponentError;
  Prime.Errors.MathError = MathError;
  Prime.Errors.NumericalInstabilityError = NumericalInstabilityError;
  Prime.Errors.MatrixSingularityError = MatrixSingularityError;
  Prime.Errors.DimensionMismatchError = DimensionMismatchError;
  Prime.Errors.NumericOverflowError = NumericOverflowError;
  Prime.Errors.ConvergenceError = ConvergenceError;

  // For backward compatibility, also attach directly to Prime
  Prime.PrimeError = PrimeError;
  Prime.ValidationError = ValidationError;
  Prime.ConfigurationError = ConfigurationError;
  Prime.InvalidOperationError = InvalidOperationError;
  Prime.UnsupportedOperationError = UnsupportedOperationError;
  Prime.TimeoutError = TimeoutError;
  Prime.ResourceExhaustionError = ResourceExhaustionError;
  Prime.SecurityError = SecurityError;
  Prime.NetworkError = NetworkError;
  Prime.DependencyError = DependencyError;
  Prime.SerializationError = SerializationError;
  Prime.StateError = StateError;
  Prime.CoherenceError = CoherenceError;
  Prime.CoherenceViolationError = CoherenceViolationError;
  Prime.ComponentError = ComponentError;
  Prime.MathError = MathError;
  Prime.NumericalInstabilityError = NumericalInstabilityError;
  Prime.MatrixSingularityError = MatrixSingularityError;
  Prime.DimensionMismatchError = DimensionMismatchError;
  Prime.NumericOverflowError = NumericOverflowError;
  Prime.ConvergenceError = ConvergenceError;
})(Prime);

// CommonJS export
if (typeof module !== "undefined" && module.exports) {
  module.exports = Prime;
}
