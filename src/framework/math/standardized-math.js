/**
 * PrimeOS JavaScript Library - Framework
 * Standardized Math Integration Module
 * Provides a unified interface for all mathematical operations
 */

// Import direct dependencies to avoid circular dependencies
const Prime = require("../../core/prime.js");
const MathUtils = require("./index.js");
const PrimeMath = require("./prime-math.js");
const StandardizedTensor = require("./standardized-tensor.js");
const TypeValidation = require("./type-validation.js");

/**
 * Error context helper for mathematical operations
 * Provides standardized context for error handling in math operations
 */
class MathErrorContext {
  /**
   * Create a standardized context for math error handling
   * @param {string} operation - Operation where error occurred (e.g., 'matrix.multiply')
   * @param {Object} inputs - Input values or references
   * @param {Object} [details={}] - Additional error details
   * @returns {Object} Standardized error context
   */
  static create(operation, inputs, details = {}) {
    // Create the base context
    const context = {
      operation,
      ...details,
    };

    // Add standardized input information
    if (inputs) {
      if (Array.isArray(inputs)) {
        context.inputDimensions = inputs.map((input) => {
          if (Array.isArray(input)) {
            return Array.isArray(input[0])
              ? [input.length, input[0].length]
              : [input.length];
          }
          return typeof input;
        });
      } else if (typeof inputs === "object") {
        // Convert inputs object to a context-friendly format
        const inputInfo = {};
        for (const key in inputs) {
          const input = inputs[key];
          if (Array.isArray(input)) {
            inputInfo[key] = Array.isArray(input[0])
              ? [input.length, input[0].length]
              : [input.length];
          } else {
            inputInfo[key] = typeof input;
          }
        }
        context.inputs = inputInfo;
      }
    }

    return context;
  }
}

/**
 * StandardizedMath - Unified interface for mathematical operations
 *
 * This module integrates all mathematical operations from various modules
 * into a consistent interface. It leverages the best implementations from
 * each module and ensures consistent error handling, naming conventions,
 * and numerical stability approaches.
 */
const StandardizedMath = {
  /**
   * Constants with high precision
   */
  constants: {
    ...PrimeMath.constants,
    // Add any additional constants
    MACHINE_EPSILON: 2.220446049250313e-16, // Double precision machine epsilon
    SAFE_MIN: Number.MIN_VALUE * 1.5, // Safe minimum value for numerical stability
    SAFE_MAX: Number.MAX_VALUE / 1.5, // Safe maximum value for numerical stability
  },

  /**
   * Adaptive precision control that scales with magnitude of inputs
   *
   * @param {number} magnitude - Characteristic magnitude of the calculation
   * @param {string} context - Context of the calculation (e.g., 'vector', 'matrix')
   * @returns {number} Appropriate epsilon value scaled to the magnitude
   */
  adaptiveEpsilon: function (magnitude, context = "general") {
    // Simple implementation to avoid circular dependencies
    const EPSILON = 2.220446049250313e-16; // standard double precision epsilon
    const TOLERANCES = {
      vector: 1e-12,
      matrix: 1e-12,
      integration: 1e-10,
      optimization: 1e-8,
      eigenvalue: 1e-14,
      general: 1e-10,
    };

    // Get base tolerance for the context
    const baseTolerance = TOLERANCES[context] || TOLERANCES.general;

    // Scale epsilon with magnitude
    if (magnitude === 0) return baseTolerance;

    const absValue = Math.abs(magnitude);
    // For very small values, use a more relaxed tolerance
    if (absValue < 1e-8) {
      return Math.max(baseTolerance, EPSILON * absValue * 10);
    }
    // For very large values, scale tolerance to avoid underflow
    if (absValue > 1e8) {
      return Math.max(baseTolerance, EPSILON * absValue);
    }

    return baseTolerance;
  },

  /**
   * Enhanced Kahan summation algorithm with magnitude tracking
   *
   * @param {Array} values - Array of values to sum
   * @returns {Object} Sum and error estimates
   */
  kahanSum: function (values) {
    if (!Array.isArray(values)) {
      throw new Prime.ValidationError("Expected an array of values");
    }

    let sum = 0;
    let compensation = 0;
    let maxAbs = 0;
    let minAbs = Infinity;

    // Track smallest and largest values for precision analysis
    for (let i = 0; i < values.length; i++) {
      if (values[i] !== 0) {
        const absVal = Math.abs(values[i]);
        maxAbs = Math.max(maxAbs, absVal);
        minAbs = Math.min(minAbs, absVal);
      }

      // Kahan summation step
      const y = values[i] - compensation;
      const t = sum + y;
      compensation = t - sum - y;
      sum = t;
    }

    // Calculate condition number as measure of potential precision loss
    const conditionNumber = minAbs === Infinity ? 0 : maxAbs / minAbs;
    const EPSILON = 2.220446049250313e-16;

    return {
      sum,
      compensation,
      conditionNumber,
      maxValue: maxAbs,
      minValue: minAbs === Infinity ? 0 : minAbs,
      precision: Math.log10(1 / (EPSILON * conditionNumber || EPSILON)),
    };
  },

  /**
   * Vector operations with enhanced precision
   */
  Vector: {
    // Import from PrimeMath.Vector and enhance with methods from MathUtils.vector
    ...PrimeMath.Vector,

    /**
     * Create a new vector
     * @param {Array<number>|number} values - Vector values or dimension
     * @returns {Vector} New vector
     */
    create: function (values) {
      // Validate inputs
      TypeValidation.assertDefined(values, "values", {
        operation: "Vector.create",
      });

      if (TypeValidation._isArray(values)) {
        // Creating from array - validate it's an array of numbers
        TypeValidation.assertNumberArray(values, "values", {
          operation: "Vector.create",
        });
      } else if (TypeValidation._isNumber(values)) {
        // Creating with dimension - validate it's a positive integer
        TypeValidation.assertPositiveInteger(values, "values", {
          operation: "Vector.create",
          details:
            "When creating a vector with a dimension, the dimension must be a positive integer",
        });
      } else {
        // Invalid type
        throw new Prime.ValidationError(
          "Parameter values must be an array of numbers or a positive integer",
          {
            operation: "Vector.create",
            expectedTypes: ["Array<number>", "positive integer"],
            actualType: typeof values,
            actual: values,
          },
        );
      }

      // Call the original implementation with validated inputs
      return PrimeMath.createVector(values);
    },

    /**
     * Create a vector from an array
     * @param {Array<number>} array - Input array
     * @returns {Vector} New vector
     */
    fromArray: PrimeMath.vectorFromArray,

    /**
     * Create a zero vector
     * @param {number} dimension - Vector dimension
     * @returns {Vector} Zero vector
     */
    zeros: PrimeMath.zeroVector,

    /**
     * Create a vector of ones
     * @param {number} dimension - Vector dimension
     * @returns {Vector} Vector of ones
     */
    ones: PrimeMath.onesVector,

    /**
     * Create a vector with elements from start to end (inclusive)
     * @param {number} start - Start value
     * @param {number} end - End value
     * @param {number} [step=1] - Step size
     * @returns {Vector} Range vector
     */
    range: PrimeMath.rangeVector,

    /**
     * Add two vectors
     * @param {Vector|Array<number>} v1 - First vector
     * @param {Vector|Array<number>} v2 - Second vector
     * @returns {Vector} Result of addition
     */
    add: function (v1, v2) {
      // Validate inputs
      TypeValidation.assertArray(v1, "v1", { operation: "Vector.add" });
      TypeValidation.assertArray(v2, "v2", { operation: "Vector.add" });
      TypeValidation.assertNumberArray(v1, "v1", { operation: "Vector.add" });
      TypeValidation.assertNumberArray(v2, "v2", { operation: "Vector.add" });
      TypeValidation.assertSameDimension(v1, v2, "v1", "v2", {
        operation: "Vector.add",
      });

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateArrayMagnitudes(
          v1,
          "v1",
          {
            allowZero: true,
          },
          { operation: "Vector.add" },
        );

        TypeValidation.validateArrayMagnitudes(
          v2,
          "v2",
          {
            allowZero: true,
          },
          { operation: "Vector.add" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        // since addition can still work with careful handling
        console.warn(`Warning in Vector.add: ${error.message}`);
      }

      // Call the original implementation with validated inputs
      return PrimeMath.addVectors(v1, v2);
    },

    /**
     * Subtract two vectors
     * @param {Vector|Array<number>} v1 - First vector
     * @param {Vector|Array<number>} v2 - Second vector
     * @returns {Vector} Result of subtraction
     */
    subtract: function (v1, v2) {
      // Validate inputs
      TypeValidation.assertArray(v1, "v1", { operation: "Vector.subtract" });
      TypeValidation.assertArray(v2, "v2", { operation: "Vector.subtract" });
      TypeValidation.assertNumberArray(v1, "v1", {
        operation: "Vector.subtract",
      });
      TypeValidation.assertNumberArray(v2, "v2", {
        operation: "Vector.subtract",
      });
      TypeValidation.assertSameDimension(v1, v2, "v1", "v2", {
        operation: "Vector.subtract",
      });

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateArrayMagnitudes(
          v1,
          "v1",
          {
            allowZero: true,
          },
          { operation: "Vector.subtract" },
        );

        TypeValidation.validateArrayMagnitudes(
          v2,
          "v2",
          {
            allowZero: true,
          },
          { operation: "Vector.subtract" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Vector.subtract: ${error.message}`);
      }

      // Check for potential catastrophic cancellation when vectors are nearly identical
      let almostIdentical = true;
      for (let i = 0; i < v1.length; i++) {
        // Check if relative difference is small
        const relDiff =
          Math.abs(v1[i] - v2[i]) /
          Math.max(Math.abs(v1[i]), Math.abs(v2[i]), 1e-10);
        if (relDiff > 1e-10) {
          almostIdentical = false;
          break;
        }
      }

      if (almostIdentical) {
        console.warn(
          "Warning in Vector.subtract: Potential catastrophic cancellation detected when subtracting nearly identical vectors",
        );
      }

      // Call the original implementation with validated inputs
      return PrimeMath.subtractVectors(v1, v2);
    },

    /**
     * Scale a vector by a scalar
     * @param {Vector|Array<number>} v - Vector
     * @param {number} scalar - Scalar value
     * @returns {Vector} Scaled vector
     */
    scale: function (v, scalar) {
      // Validate inputs
      TypeValidation.assertArray(v, "v", { operation: "Vector.scale" });
      TypeValidation.assertNumberArray(v, "v", { operation: "Vector.scale" });
      TypeValidation.assertNumber(scalar, "scalar", {
        operation: "Vector.scale",
      });
      TypeValidation.assertFinite(scalar, "scalar", {
        operation: "Vector.scale",
      });

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateArrayMagnitudes(
          v,
          "v",
          {
            allowZero: true,
          },
          { operation: "Vector.scale" },
        );

        TypeValidation.validateMagnitude(
          scalar,
          "scalar",
          {
            allowZero: true,
          },
          { operation: "Vector.scale" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Vector.scale: ${error.message}`);
      }

      // Call the original implementation with validated inputs
      return PrimeMath.scaleVector(v, scalar);
    },

    /**
     * Calculate the dot product of two vectors
     * @param {Vector|Array<number>} v1 - First vector
     * @param {Vector|Array<number>} v2 - Second vector
     * @returns {number} Dot product
     */
    dot: function (v1, v2) {
      // Validate inputs
      TypeValidation.assertArray(v1, "v1", { operation: "Vector.dot" });
      TypeValidation.assertArray(v2, "v2", { operation: "Vector.dot" });
      TypeValidation.assertNumberArray(v1, "v1", { operation: "Vector.dot" });
      TypeValidation.assertNumberArray(v2, "v2", { operation: "Vector.dot" });
      TypeValidation.assertSameDimension(v1, v2, "v1", "v2", {
        operation: "Vector.dot",
      });

      // Create standard validation context for error reporting
      const context = TypeValidation.createValidationContext("Vector.dot", {
        v1,
        v2,
      });

      // Call the original implementation with validated inputs
      return PrimeMath.dotProduct(v1, v2);
    },

    /**
     * Calculate the cross product of two 3D vectors
     * @param {Vector|Array<number>} v1 - First vector
     * @param {Vector|Array<number>} v2 - Second vector
     * @returns {Vector} Cross product
     */
    cross: function (v1, v2) {
      // Validate inputs
      TypeValidation.assertArray(v1, "v1", { operation: "Vector.cross" });
      TypeValidation.assertArray(v2, "v2", { operation: "Vector.cross" });
      TypeValidation.assertNumberArray(v1, "v1", { operation: "Vector.cross" });
      TypeValidation.assertNumberArray(v2, "v2", { operation: "Vector.cross" });

      // Check if both vectors are 3D
      TypeValidation.assertExactLength(v1, 3, "v1", {
        operation: "Vector.cross",
        details: "Cross product requires 3D vectors",
      });
      TypeValidation.assertExactLength(v2, 3, "v2", {
        operation: "Vector.cross",
        details: "Cross product requires 3D vectors",
      });

      // Call the original implementation with validated inputs
      return PrimeMath.crossProduct(v1, v2);
    },

    /**
     * Calculate the norm (magnitude) of a vector
     * @param {Vector|Array<number>} v - Vector
     * @param {number} [p=2] - Norm order (1=L1, 2=L2/Euclidean)
     * @returns {number} Vector norm
     */
    norm: function (v, p = 2) {
      // Validate inputs
      TypeValidation.assertArray(v, "v", { operation: "Vector.norm" });
      TypeValidation.assertNumberArray(v, "v", { operation: "Vector.norm" });

      if (p !== undefined) {
        TypeValidation.assertNumber(p, "p", { operation: "Vector.norm" });
        TypeValidation.assertPositiveNumber(p, "p", {
          operation: "Vector.norm",
        });
      }

      // Call the original implementation with validated inputs
      return PrimeMath.vectorNorm(v, p);
    },

    /**
     * Normalize a vector to unit length
     * @param {Vector|Array<number>} v - Vector
     * @returns {Vector} Normalized vector
     */
    normalize: function (v) {
      // Validate inputs
      TypeValidation.assertArray(v, "v", { operation: "Vector.normalize" });
      TypeValidation.assertNumberArray(v, "v", {
        operation: "Vector.normalize",
      });

      // Check if vector is zero
      const isZeroVector = v.every((val) => val === 0);
      if (isZeroVector) {
        throw new Prime.ValidationError("Cannot normalize a zero vector", {
          operation: "Vector.normalize",
          vector: v,
        });
      }

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateArrayMagnitudes(
          v,
          "v",
          {
            allowZero: false, // Individual elements can be zero, but not all
          },
          { operation: "Vector.normalize" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Vector.normalize: ${error.message}`);
      }

      // Call the original implementation with validated inputs
      return PrimeMath.normalizeVector(v);
    },

    /**
     * Calculate the distance between two vectors
     * @param {Vector|Array<number>} v1 - First vector
     * @param {Vector|Array<number>} v2 - Second vector
     * @param {number} [p=2] - Norm order (1=L1, 2=L2/Euclidean)
     * @returns {number} Distance
     */
    distance: function (v1, v2, p = 2) {
      // Validate inputs
      TypeValidation.assertArray(v1, "v1", { operation: "Vector.distance" });
      TypeValidation.assertArray(v2, "v2", { operation: "Vector.distance" });
      TypeValidation.assertNumberArray(v1, "v1", {
        operation: "Vector.distance",
      });
      TypeValidation.assertNumberArray(v2, "v2", {
        operation: "Vector.distance",
      });
      TypeValidation.assertSameDimension(v1, v2, "v1", "v2", {
        operation: "Vector.distance",
      });

      if (p !== undefined) {
        TypeValidation.assertNumber(p, "p", { operation: "Vector.distance" });
        TypeValidation.assertPositiveNumber(p, "p", {
          operation: "Vector.distance",
        });
      }

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateArrayMagnitudes(
          v1,
          "v1",
          {
            allowZero: true,
          },
          { operation: "Vector.distance" },
        );

        TypeValidation.validateArrayMagnitudes(
          v2,
          "v2",
          {
            allowZero: true,
          },
          { operation: "Vector.distance" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Vector.distance: ${error.message}`);
      }

      // Call the original implementation with validated inputs
      return PrimeMath.vectorDistance(v1, v2, p);
    },

    /**
     * Calculate the angle between two vectors
     * @param {Vector|Array<number>} v1 - First vector
     * @param {Vector|Array<number>} v2 - Second vector
     * @returns {number} Angle in radians
     */
    angle: function (v1, v2) {
      // Validate inputs
      TypeValidation.assertArray(v1, "v1", { operation: "Vector.angle" });
      TypeValidation.assertArray(v2, "v2", { operation: "Vector.angle" });
      TypeValidation.assertNumberArray(v1, "v1", { operation: "Vector.angle" });
      TypeValidation.assertNumberArray(v2, "v2", { operation: "Vector.angle" });
      TypeValidation.assertSameDimension(v1, v2, "v1", "v2", {
        operation: "Vector.angle",
      });

      // Check if either vector is zero
      const isZeroVector1 = v1.every((val) => val === 0);
      const isZeroVector2 = v2.every((val) => val === 0);

      if (isZeroVector1 || isZeroVector2) {
        throw new Prime.ValidationError(
          "Cannot calculate angle involving a zero vector",
          {
            operation: "Vector.angle",
            isZeroVector1,
            isZeroVector2,
          },
        );
      }

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateArrayMagnitudes(
          v1,
          "v1",
          {
            allowZero: false, // Individual elements can be zero, but not all
          },
          { operation: "Vector.angle" },
        );

        TypeValidation.validateArrayMagnitudes(
          v2,
          "v2",
          {
            allowZero: false, // Individual elements can be zero, but not all
          },
          { operation: "Vector.angle" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Vector.angle: ${error.message}`);
      }

      // Call the original implementation with validated inputs
      return PrimeMath.angleBetweenVectors(v1, v2);
    },

    /**
     * Project one vector onto another
     * @param {Vector|Array<number>} v1 - Vector to project
     * @param {Vector|Array<number>} v2 - Vector to project onto
     * @returns {Vector} Projection vector
     */
    project: function (v1, v2) {
      // Validate inputs
      TypeValidation.assertArray(v1, "v1", { operation: "Vector.project" });
      TypeValidation.assertArray(v2, "v2", { operation: "Vector.project" });
      TypeValidation.assertNumberArray(v1, "v1", {
        operation: "Vector.project",
      });
      TypeValidation.assertNumberArray(v2, "v2", {
        operation: "Vector.project",
      });
      TypeValidation.assertSameDimension(v1, v2, "v1", "v2", {
        operation: "Vector.project",
      });

      // Check if the second vector is zero
      const isZeroVector2 = v2.every((val) => val === 0);

      if (isZeroVector2) {
        throw new Prime.ValidationError("Cannot project onto a zero vector", {
          operation: "Vector.project",
          vector: v2,
        });
      }

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateArrayMagnitudes(
          v1,
          "v1",
          {
            allowZero: true,
          },
          { operation: "Vector.project" },
        );

        TypeValidation.validateArrayMagnitudes(
          v2,
          "v2",
          {
            allowZero: false, // Individual elements can be zero, but not all
          },
          { operation: "Vector.project" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Vector.project: ${error.message}`);
      }

      // Call the original implementation with validated inputs
      return PrimeMath.projectVector(v1, v2);
    },

    /**
     * Apply Gram-Schmidt orthogonalization to a set of vectors
     * @param {Array<Vector>|Array<Array<number>>} vectors - Array of vectors
     * @returns {Array<Vector>} Orthogonalized vectors
     */
    gramSchmidt: PrimeMath.gramSchmidt,

    /**
     * Linear interpolation between vectors with enhanced precision
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @param {number} t - Interpolation parameter (0-1)
     * @returns {Array} Interpolated vector
     */
    lerp: function (a, b, t) {
      // Create a simple implementation to avoid circular dependencies
      if (!Array.isArray(a) || !Array.isArray(b)) {
        throw new Prime.ValidationError("Vectors must be arrays");
      }

      // Ensure t is clamped to [0,1]
      const tClamped = Math.max(0, Math.min(1, t));

      const maxLength = Math.max(a.length, b.length);
      const result = new Array(maxLength);

      // Perform interpolation
      for (let i = 0; i < maxLength; i++) {
        const aVal = i < a.length ? a[i] : 0;
        const bVal = i < b.length ? b[i] : 0;

        // Use mathematically stable lerp: (1-t)*a + t*b
        result[i] = (1 - tClamped) * aVal + tClamped * bVal;
      }

      return result;
    },

    /**
     * Calculate cosine similarity with enhanced stability and edge case handling
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @param {Object} options - Calculation options
     * @returns {Object} Similarity result with error estimation
     */
    cosineSimilarity: function (a, b, options = {}) {
      // Simple implementation to avoid circular dependencies
      if (!Array.isArray(a) || !Array.isArray(b)) {
        throw new Prime.ValidationError("Vectors must be arrays");
      }

      const dotProduct = this.dot(a, b);
      const normA = this.norm(a);
      const normB = this.norm(b);

      // Handle zero vectors
      if (normA === 0 || normB === 0) {
        return {
          similarity: normA === 0 && normB === 0 ? 1 : 0,
          distance: normA === 0 && normB === 0 ? 0 : 1,
          reason:
            normA === 0 && normB === 0
              ? "Both vectors are zero"
              : "One vector is zero",
        };
      }

      const similarity = dotProduct / (normA * normB);

      // Ensure value is within valid range [-1, 1]
      const boundedSimilarity = Math.max(-1, Math.min(1, similarity));

      return {
        similarity: boundedSimilarity,
        distance: 1 - boundedSimilarity,
      };
    },

    /**
     * Calculate Manhattan distance with enhanced stability
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {Object} Distance result with error estimation
     */
    manhattanDistance: function (a, b) {
      // Simple implementation to avoid circular dependencies
      if (!Array.isArray(a) || !Array.isArray(b)) {
        throw new Prime.ValidationError("Vectors must be arrays");
      }

      const maxLength = Math.max(a.length, b.length);
      let distance = 0;

      for (let i = 0; i < maxLength; i++) {
        const aVal = i < a.length ? a[i] : 0;
        const bVal = i < b.length ? b[i] : 0;
        distance += Math.abs(aVal - bVal);
      }

      return {
        distance: distance,
      };
    },

    /**
     * Calculate Chebyshev distance (maximum norm)
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {Object} Distance result
     */
    chebyshevDistance: function (a, b) {
      // Simple implementation to avoid circular dependencies
      if (!Array.isArray(a) || !Array.isArray(b)) {
        throw new Prime.ValidationError("Vectors must be arrays");
      }

      const maxLength = Math.max(a.length, b.length);
      let maxDiff = 0;
      let maxDiffIndex = -1;

      for (let i = 0; i < maxLength; i++) {
        const aVal = i < a.length ? a[i] : 0;
        const bVal = i < b.length ? b[i] : 0;
        const absDiff = Math.abs(aVal - bVal);

        if (absDiff > maxDiff) {
          maxDiff = absDiff;
          maxDiffIndex = i;
        }
      }

      return {
        distance: maxDiff,
        maxDiffIndex: maxDiffIndex,
      };
    },

    /**
     * Embed data into a fixed dimension vector space
     * @param {*} data - Data to embed (any type)
     * @param {number} dimensions - Target embedding dimension
     * @returns {Array} Embedding vector with specified dimension
     */
    embedData: function (data, dimensions) {
      // Simple implementation to avoid circular dependencies
      if (!Number.isInteger(dimensions) || dimensions <= 0) {
        throw new Prime.ValidationError(
          "Embedding dimensions must be a positive integer",
        );
      }

      const result = new Array(dimensions).fill(0);

      if (typeof data === "number") {
        // For numbers, use a simple encoding
        result[0] = Math.tanh(data / 100);
        for (let i = 1; i < dimensions; i++) {
          result[i] = Math.sin((data * i) / dimensions);
        }
      } else if (typeof data === "string") {
        // For strings, use character codes
        for (let i = 0; i < data.length; i++) {
          const idx = i % dimensions;
          result[idx] += Math.sin((data.charCodeAt(i) * (i + 1)) / dimensions);
        }
      } else if (Array.isArray(data)) {
        // For arrays, copy or average values
        if (data.length <= dimensions) {
          for (let i = 0; i < data.length; i++) {
            result[i] = data[i];
          }
        } else {
          const stride = data.length / dimensions;
          for (let i = 0; i < dimensions; i++) {
            const start = Math.floor(i * stride);
            const end = Math.floor((i + 1) * stride);
            let sum = 0;
            for (let j = start; j < end; j++) {
              sum += data[j];
            }
            result[i] = sum / (end - start);
          }
        }
      } else if (data === null || data === undefined) {
        // For null/undefined, leave as zeros
      } else if (typeof data === "boolean") {
        // For booleans, set first value
        result[0] = data ? 1 : -1;
      } else if (typeof data === "object") {
        // For objects, use keys and values
        const keys = Object.keys(data);
        for (let i = 0; i < keys.length; i++) {
          const idx = i % dimensions;
          const val = data[keys[i]];
          if (typeof val === "number") {
            result[idx] += Math.tanh(val / 100);
          } else {
            result[idx] += 0.1;
          }
        }
      }

      // Normalize the result
      const norm = Math.sqrt(result.reduce((sum, val) => sum + val * val, 0));
      if (norm > 0) {
        for (let i = 0; i < dimensions; i++) {
          result[i] /= norm;
        }
      }

      return result;
    },
  },

  /**
   * Matrix operations with enhanced precision
   */
  Matrix: {
    // Import from PrimeMath.Matrix and enhance with methods from MathUtils.matrix
    ...PrimeMath.Matrix,

    /**
     * Create a new matrix
     * @param {Array<Array<number>>|number[]|number} values - Matrix values or dimensions
     * @param {number} [rows] - Number of rows (if values is flat array)
     * @param {number} [cols] - Number of columns (if values is flat array)
     * @returns {Matrix} New matrix
     */
    create: function (values, rows, cols) {
      // Validate inputs
      TypeValidation.assertDefined(values, "values", {
        operation: "Matrix.create",
      });

      if (TypeValidation._isArray(values)) {
        if (values.length > 0 && TypeValidation._isArray(values[0])) {
          // Creating from 2D array
          TypeValidation.assertMatrix(values, "values", {
            operation: "Matrix.create",
          });
        } else {
          // Creating from flat array
          TypeValidation.assertNumberArray(values, "values", {
            operation: "Matrix.create",
          });
          TypeValidation.assertDefined(rows, "rows", {
            operation: "Matrix.create",
            details:
              "When creating a matrix from a flat array, rows must be specified",
          });
          TypeValidation.assertDefined(cols, "cols", {
            operation: "Matrix.create",
            details:
              "When creating a matrix from a flat array, cols must be specified",
          });
          TypeValidation.assertPositiveInteger(rows, "rows", {
            operation: "Matrix.create",
          });
          TypeValidation.assertPositiveInteger(cols, "cols", {
            operation: "Matrix.create",
          });

          // Ensure the flat array has the correct length
          if (values.length !== rows * cols) {
            throw new Prime.ValidationError(
              "Flat array length must equal rows * cols",
              {
                operation: "Matrix.create",
                expectedLength: rows * cols,
                actualLength: values.length,
              },
            );
          }
        }
      } else if (
        TypeValidation._isNumber(values) &&
        TypeValidation._isNumber(rows)
      ) {
        // Creating with dimensions
        TypeValidation.assertPositiveInteger(values, "values", {
          operation: "Matrix.create",
          details:
            "When creating a matrix with dimensions, both dimensions must be positive integers",
        });
        TypeValidation.assertPositiveInteger(rows, "rows", {
          operation: "Matrix.create",
        });
      } else {
        // Invalid type
        throw new Prime.ValidationError(
          "Invalid arguments for matrix creation",
          {
            operation: "Matrix.create",
            expectedTypes: [
              "2D array",
              "flat array with dimensions",
              "two dimensions",
            ],
            actualTypes: [typeof values, typeof rows, typeof cols],
          },
        );
      }

      // Check for extreme values that might cause numerical instability
      if (TypeValidation._isArray(values)) {
        try {
          if (values.length > 0 && TypeValidation._isArray(values[0])) {
            // 2D array
            TypeValidation.validateMatrixMagnitudes(
              values,
              "values",
              {
                allowZero: true,
              },
              { operation: "Matrix.create" },
            );
          } else {
            // Flat array
            TypeValidation.validateArrayMagnitudes(
              values,
              "values",
              {
                allowZero: true,
              },
              { operation: "Matrix.create" },
            );
          }
        } catch (error) {
          // If validation fails due to extreme values, log a warning but continue
          console.warn(`Warning in Matrix.create: ${error.message}`);
        }
      }

      // Call the original implementation with validated inputs
      return PrimeMath.createMatrix(values, rows, cols);
    },

    /**
     * Create a matrix from a 2D array
     * @param {Array<Array<number>>} array - 2D array
     * @returns {Matrix} New matrix
     */
    fromArray: PrimeMath.matrixFromArray,

    /**
     * Create a matrix from a flat array
     * @param {Array<number>} array - Flat array
     * @param {number} rows - Number of rows
     * @param {number} cols - Number of columns
     * @returns {Matrix} New matrix
     */
    fromFlatArray: PrimeMath.matrixFromFlatArray,

    /**
     * Create a zero matrix
     * @param {number} rows - Number of rows
     * @param {number} cols - Number of columns
     * @returns {Matrix} Zero matrix
     */
    zeros: PrimeMath.zeroMatrix,

    /**
     * Create a matrix of ones
     * @param {number} rows - Number of rows
     * @param {number} cols - Number of columns
     * @returns {Matrix} Matrix of ones
     */
    ones: PrimeMath.onesMatrix,

    /**
     * Create an identity matrix
     * @param {number} size - Matrix size
     * @returns {Matrix} Identity matrix
     */
    identity: PrimeMath.identityMatrix,

    /**
     * Create a diagonal matrix
     * @param {Array<number>|Vector} diagonal - Diagonal elements
     * @returns {Matrix} Diagonal matrix
     */
    diagonal: PrimeMath.diagonalMatrix,

    /**
     * Add two matrices
     * @param {Matrix|Array<Array<number>>} m1 - First matrix
     * @param {Matrix|Array<Array<number>>} m2 - Second matrix
     * @returns {Matrix} Result of addition
     */
    add: function (m1, m2) {
      // Validate inputs
      TypeValidation.assertMatrix(m1, "m1", { operation: "Matrix.add" });
      TypeValidation.assertMatrix(m2, "m2", { operation: "Matrix.add" });
      TypeValidation.assertSameMatrixDimensions(m1, m2, "m1", "m2", {
        operation: "Matrix.add",
      });

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateMatrixMagnitudes(
          m1,
          "m1",
          {
            allowZero: true,
          },
          { operation: "Matrix.add" },
        );

        TypeValidation.validateMatrixMagnitudes(
          m2,
          "m2",
          {
            allowZero: true,
          },
          { operation: "Matrix.add" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Matrix.add: ${error.message}`);
      }

      // Call the original implementation with validated inputs
      return PrimeMath.addMatrices(m1, m2);
    },

    /**
     * Subtract two matrices
     * @param {Matrix|Array<Array<number>>} m1 - First matrix
     * @param {Matrix|Array<Array<number>>} m2 - Second matrix
     * @returns {Matrix} Result of subtraction
     */
    subtract: function (m1, m2) {
      // Validate inputs
      TypeValidation.assertMatrix(m1, "m1", { operation: "Matrix.subtract" });
      TypeValidation.assertMatrix(m2, "m2", { operation: "Matrix.subtract" });
      TypeValidation.assertSameMatrixDimensions(m1, m2, "m1", "m2", {
        operation: "Matrix.subtract",
      });

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateMatrixMagnitudes(
          m1,
          "m1",
          {
            allowZero: true,
          },
          { operation: "Matrix.subtract" },
        );

        TypeValidation.validateMatrixMagnitudes(
          m2,
          "m2",
          {
            allowZero: true,
          },
          { operation: "Matrix.subtract" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Matrix.subtract: ${error.message}`);
      }

      // Check for potential catastrophic cancellation when matrices are nearly identical
      let almostIdentical = true;
      for (let i = 0; i < m1.length; i++) {
        for (let j = 0; j < m1[i].length; j++) {
          // Check if relative difference is small
          const relDiff =
            Math.abs(m1[i][j] - m2[i][j]) /
            Math.max(Math.abs(m1[i][j]), Math.abs(m2[i][j]), 1e-10);
          if (relDiff > 1e-10) {
            almostIdentical = false;
            break;
          }
        }
        if (!almostIdentical) break;
      }

      if (almostIdentical) {
        console.warn(
          "Warning in Matrix.subtract: Potential catastrophic cancellation detected when subtracting nearly identical matrices",
        );
      }

      // Call the original implementation with validated inputs
      return PrimeMath.subtractMatrices(m1, m2);
    },

    /**
     * Scale a matrix by a scalar
     * @param {Matrix|Array<Array<number>>} m - Matrix
     * @param {number} scalar - Scalar value
     * @returns {Matrix} Scaled matrix
     */
    scale: function (m, scalar) {
      // Validate inputs
      TypeValidation.assertMatrix(m, "m", { operation: "Matrix.scale" });
      TypeValidation.assertNumber(scalar, "scalar", {
        operation: "Matrix.scale",
      });
      TypeValidation.assertFinite(scalar, "scalar", {
        operation: "Matrix.scale",
      });

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateMatrixMagnitudes(
          m,
          "m",
          {
            allowZero: true,
          },
          { operation: "Matrix.scale" },
        );

        TypeValidation.validateMagnitude(
          scalar,
          "scalar",
          {
            allowZero: true,
          },
          { operation: "Matrix.scale" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Matrix.scale: ${error.message}`);
      }

      // Call the original implementation with validated inputs
      return PrimeMath.scaleMatrix(m, scalar);
    },

    /**
     * Multiply two matrices or a matrix and a vector
     * @param {Matrix|Array<Array<number>>} m1 - First matrix
     * @param {Matrix|Vector|Array<Array<number>>|Array<number>} m2 - Second matrix or vector
     * @returns {Matrix|Vector} Result of multiplication
     */
    multiply: function (m1, m2) {
      // Validate inputs
      TypeValidation.assertMatrix(m1, "m1", { operation: "Matrix.multiply" });

      // Check if m2 is a matrix or a vector
      const isVector =
        TypeValidation._isArray(m2) &&
        (m2.length === 0 || !TypeValidation._isArray(m2[0]));

      if (isVector) {
        // Matrix-vector multiplication
        TypeValidation.assertArray(m2, "m2", { operation: "Matrix.multiply" });
        TypeValidation.assertNumberArray(m2, "m2", {
          operation: "Matrix.multiply",
        });
        TypeValidation.assertMatrixVectorMultiplicable(m1, m2, "m1", "m2", {
          operation: "Matrix.multiply",
        });
      } else {
        // Matrix-matrix multiplication
        TypeValidation.assertMatrix(m2, "m2", { operation: "Matrix.multiply" });
        TypeValidation.assertMultiplicableMatrices(m1, m2, "m1", "m2", {
          operation: "Matrix.multiply",
        });
      }

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateMatrixMagnitudes(
          m1,
          "m1",
          {
            allowZero: true,
          },
          { operation: "Matrix.multiply" },
        );

        if (isVector) {
          TypeValidation.validateArrayMagnitudes(
            m2,
            "m2",
            {
              allowZero: true,
            },
            { operation: "Matrix.multiply" },
          );
        } else {
          TypeValidation.validateMatrixMagnitudes(
            m2,
            "m2",
            {
              allowZero: true,
            },
            { operation: "Matrix.multiply" },
          );
        }
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Matrix.multiply: ${error.message}`);
      }

      // Check for potential numerical stability issues in matrix multiplication
      if (!isVector && m1.length > 0 && m2.length > 0) {
        // Check for large condition number which indicates potential numerical instability
        const innerDimension = m1[0].length;
        if (innerDimension > 50) {
          // This is a simplistic check - a full condition number computation would be better
          // but too expensive to do inline
          console.warn(
            `Warning in Matrix.multiply: Large inner dimension (${innerDimension}) may lead to numerical instability`,
          );
        }

        // Check for very small values in the matrices that may be lost in accumulation
        let hasSmallValues = false;
        for (let i = 0; i < m1.length && !hasSmallValues; i++) {
          for (let j = 0; j < m1[i].length; j++) {
            if (m1[i][j] !== 0 && Math.abs(m1[i][j]) < 1e-8) {
              hasSmallValues = true;
              break;
            }
          }
        }

        for (let i = 0; i < m2.length && !hasSmallValues; i++) {
          for (let j = 0; j < m2[i].length; j++) {
            if (m2[i][j] !== 0 && Math.abs(m2[i][j]) < 1e-8) {
              hasSmallValues = true;
              break;
            }
          }
        }

        if (hasSmallValues) {
          console.warn(
            "Warning in Matrix.multiply: Very small values detected which may be lost in accumulation",
          );
        }
      }

      // Call the original implementation with validated inputs
      return PrimeMath.multiplyMatrices(m1, m2);
    },

    /**
     * Calculate the transpose of a matrix
     * @param {Matrix|Array<Array<number>>} m - Matrix
     * @returns {Matrix} Transposed matrix
     */
    transpose: function (m) {
      // Validate inputs
      TypeValidation.assertMatrix(m, "m", { operation: "Matrix.transpose" });

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateMatrixMagnitudes(
          m,
          "m",
          {
            allowZero: true,
          },
          { operation: "Matrix.transpose" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Matrix.transpose: ${error.message}`);
      }

      // Call the original implementation with validated inputs
      return PrimeMath.transposeMatrix(m);
    },

    /**
     * Calculate the trace of a matrix
     * @param {Matrix|Array<Array<number>>} m - Matrix
     * @returns {number} Trace
     */
    trace: function (m) {
      // Validate inputs
      TypeValidation.assertMatrix(m, "m", { operation: "Matrix.trace" });
      TypeValidation.assertSquareMatrix(m, "m", { operation: "Matrix.trace" });

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateMatrixMagnitudes(
          m,
          "m",
          {
            allowZero: true,
          },
          { operation: "Matrix.trace" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Matrix.trace: ${error.message}`);
      }

      // Call the original implementation with validated inputs
      return PrimeMath.matrixTrace(m);
    },

    /**
     * Calculate the determinant of a matrix
     * @param {Matrix|Array<Array<number>>} m - Matrix
     * @returns {number} Determinant
     */
    determinant: function (m) {
      // Validate inputs
      TypeValidation.assertMatrix(m, "m", { operation: "Matrix.determinant" });
      TypeValidation.assertSquareMatrix(m, "m", {
        operation: "Matrix.determinant",
      });

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateMatrixMagnitudes(
          m,
          "m",
          {
            allowZero: true,
          },
          { operation: "Matrix.determinant" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Matrix.determinant: ${error.message}`);
      }

      // Warn if matrix is large (determinant calculation can be numerically unstable)
      if (m.length > 4) {
        console.warn(
          `Warning in Matrix.determinant: Computing determinant of ${m.length}x${m.length} matrix may lead to numerical instability. Consider using LU decomposition.`,
        );
      }

      // Check if matrix is close to singular
      // This is a very simple check and might not catch all cases
      if (m.length > 1) {
        const hasSmallDiagonal = m.some(
          (row, index) => Math.abs(row[index]) < 1e-10,
        );
        if (hasSmallDiagonal) {
          console.warn(
            "Warning in Matrix.determinant: Matrix may be close to singular, determinant might be unreliable",
          );
        }
      }

      // Call the original implementation with validated inputs
      return PrimeMath.matrixDeterminant(m);
    },

    /**
     * Perform LU decomposition of a matrix
     * @param {Matrix|Array<Array<number>>} m - Matrix
     * @returns {Object} Object with L, U, P matrices and exchanges count
     */
    luDecomposition: function (m) {
      // Validate inputs
      TypeValidation.assertMatrix(m, "m", {
        operation: "Matrix.luDecomposition",
      });
      TypeValidation.assertSquareMatrix(m, "m", {
        operation: "Matrix.luDecomposition",
      });

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateMatrixMagnitudes(
          m,
          "m",
          {
            allowZero: true,
          },
          { operation: "Matrix.luDecomposition" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Matrix.luDecomposition: ${error.message}`);
      }

      // Check if matrix might be singular
      // This is a very simple check and might not catch all cases
      if (m.length > 1) {
        const hasSmallDiagonal = m.some(
          (row, index) => Math.abs(row[index]) < 1e-10,
        );
        if (hasSmallDiagonal) {
          console.warn(
            "Warning in Matrix.luDecomposition: Matrix may be close to singular, decomposition might be numerically unstable",
          );
        }
      }

      // Call the original implementation with validated inputs
      return PrimeMath.luDecomposition(m);
    },

    /**
     * Calculate the inverse of a matrix
     * @param {Matrix|Array<Array<number>>} m - Matrix
     * @returns {Matrix} Inverse matrix
     */
    inverse: function (m) {
      // Validate inputs
      TypeValidation.assertMatrix(m, "m", { operation: "Matrix.inverse" });
      TypeValidation.assertSquareMatrix(m, "m", {
        operation: "Matrix.inverse",
      });

      // Check that matrix is invertible (not singular)
      try {
        TypeValidation.validateInvertibleMatrix(
          m,
          "m",
          { tolerance: 1e-10 },
          { operation: "Matrix.inverse" },
        );
      } catch (error) {
        // For singularity errors, we should throw the error rather than just warn
        throw error;
      }

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateMatrixMagnitudes(
          m,
          "m",
          {
            allowZero: false, // Zero determinant would make the matrix singular
          },
          { operation: "Matrix.inverse" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Matrix.inverse: ${error.message}`);
      }

      // Warn if matrix is large or ill-conditioned
      if (m.length > 4) {
        console.warn(
          `Warning in Matrix.inverse: Computing inverse of ${m.length}x${m.length} matrix may lead to numerical instability. Consider using SVD or pseudoinverse for better stability.`,
        );
      }

      // Call the original implementation with validated inputs
      return PrimeMath.inverseMatrix(m);
    },

    /**
     * Solve a system of linear equations Ax = b
     * @param {Matrix|Array<Array<number>>} A - Coefficient matrix
     * @param {Vector|Array<number>} b - Right-hand side vector
     * @returns {Vector} Solution vector
     */
    solve: function (A, b) {
      // Validate inputs
      TypeValidation.assertMatrix(A, "A", { operation: "Matrix.solve" });
      TypeValidation.assertArray(b, "b", { operation: "Matrix.solve" });
      TypeValidation.assertNumberArray(b, "b", { operation: "Matrix.solve" });
      TypeValidation.assertSquareMatrix(A, "A", { operation: "Matrix.solve" });

      // Check if the dimensions are compatible
      if (A.length !== b.length) {
        throw new Prime.DimensionMismatchError(
          "Incompatible dimensions in linear system",
          {
            operation: "Matrix.solve",
            matrixDimensions: [A.length, A[0].length],
            vectorDimension: b.length,
            details: "The number of rows in A must equal the length of b",
          },
        );
      }

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateMatrixMagnitudes(
          A,
          "A",
          {
            allowZero: true,
          },
          { operation: "Matrix.solve" },
        );

        TypeValidation.validateArrayMagnitudes(
          b,
          "b",
          {
            allowZero: true,
          },
          { operation: "Matrix.solve" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Matrix.solve: ${error.message}`);
      }

      // Check if matrix might be singular or ill-conditioned
      try {
        TypeValidation.validateInvertibleMatrix(
          A,
          "A",
          { tolerance: 1e-10 },
          { operation: "Matrix.solve" },
        );
      } catch (error) {
        // For singularity errors, we should throw the error rather than just warn
        throw error;
      }

      // Warn if the system is large
      if (A.length > 50) {
        console.warn(
          `Warning in Matrix.solve: Solving a large ${A.length}x${A.length} linear system may lead to numerical instability. Consider using an iterative solver for better performance and stability.`,
        );
      }

      // Call the original implementation with validated inputs
      return PrimeMath.solveSystem(A, b);
    },

    /**
     * Calculate the eigenvalues and eigenvectors of a matrix
     * @param {Matrix|Array<Array<number>>} m - Matrix
     * @returns {Object} Object with eigenvalues and eigenvectors
     */
    eigen: function (m) {
      // Validate inputs
      TypeValidation.assertMatrix(m, "m", { operation: "Matrix.eigen" });
      TypeValidation.assertSquareMatrix(m, "m", { operation: "Matrix.eigen" });

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateMatrixMagnitudes(
          m,
          "m",
          {
            allowZero: true,
          },
          { operation: "Matrix.eigen" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Matrix.eigen: ${error.message}`);
      }

      // Warn if matrix is large (eigenvalue computation can be computationally expensive)
      if (m.length > 100) {
        console.warn(
          `Warning in Matrix.eigen: Computing eigenvalues of ${m.length}x${m.length} matrix may be computationally expensive. Consider using iterative methods for large matrices.`,
        );
      }

      // Special warning for non-symmetric matrices
      let isSymmetric = true;
      for (let i = 0; i < m.length && isSymmetric; i++) {
        for (let j = i + 1; j < m[i].length; j++) {
          if (Math.abs(m[i][j] - m[j][i]) > 1e-10) {
            isSymmetric = false;
            break;
          }
        }
      }

      if (!isSymmetric) {
        console.warn(
          "Warning in Matrix.eigen: Non-symmetric matrix detected. Eigenvalues may be complex or the computation may be less stable.",
        );
      }

      // Call the original implementation with validated inputs
      return PrimeMath.eigendecomposition(m);
    },

    /**
     * Perform QR decomposition of a matrix
     * @param {Matrix|Array<Array<number>>} m - Matrix
     * @returns {Object} Object with Q and R matrices
     */
    qrDecomposition: function (m) {
      // Validate inputs
      TypeValidation.assertMatrix(m, "m", {
        operation: "Matrix.qrDecomposition",
      });

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateMatrixMagnitudes(
          m,
          "m",
          {
            allowZero: true,
          },
          { operation: "Matrix.qrDecomposition" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Matrix.qrDecomposition: ${error.message}`);
      }

      // Warn if matrix is large
      if (m.length > 0 && m[0].length > 100) {
        console.warn(
          `Warning in Matrix.qrDecomposition: Computing QR decomposition of a ${m.length}x${m[0].length} matrix may be computationally expensive.`,
        );
      }

      // Warn if matrix has linearly dependent columns which can affect numerical stability
      if (m.length > 0 && m[0].length > 0 && m.length >= m[0].length) {
        // This is a simplistic check - a proper rank calculation would be better
        // but too expensive to do inline
        const hasZeroColumns = m[0].some((_, j) => {
          return m.every((row) => Math.abs(row[j]) < 1e-10);
        });

        if (hasZeroColumns) {
          console.warn(
            "Warning in Matrix.qrDecomposition: Matrix has zero or near-zero columns which can lead to numerical instability.",
          );
        }
      }

      // Call the original implementation with validated inputs
      return PrimeMath.qrDecomposition(m);
    },

    /**
     * Calculate the singular value decomposition (SVD) of a matrix
     * @param {Matrix|Array<Array<number>>} m - Matrix
     * @returns {Object} Object with U, S, and V matrices
     */
    svd: function (m) {
      // Validate inputs
      TypeValidation.assertMatrix(m, "m", { operation: "Matrix.svd" });

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateMatrixMagnitudes(
          m,
          "m",
          {
            allowZero: true,
          },
          { operation: "Matrix.svd" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Matrix.svd: ${error.message}`);
      }

      // Warn if matrix is large (SVD computation can be computationally expensive)
      if (
        m.length > 0 &&
        m[0].length > 0 &&
        (m.length > 100 || m[0].length > 100)
      ) {
        console.warn(
          `Warning in Matrix.svd: Computing SVD of ${m.length}x${m[0].length} matrix may be computationally expensive. Consider using an iterative or randomized SVD algorithm for large matrices.`,
        );
      }

      // Call the original implementation with validated inputs
      return PrimeMath.svd(m);
    },

    /**
     * Enhanced SVD implementation with robust handling of extreme values
     * and detailed error information
     * @param {Matrix|Array<Array<number>>} m - Matrix
     * @param {Object} [options={}] - Algorithm options
     * @returns {Object} Object with U, S, V matrices and metadata
     */
    svdWithMetrics: function (m, options = {}) {
      // Validate inputs
      TypeValidation.assertMatrix(m, "m", {
        operation: "Matrix.svdWithMetrics",
      });

      if (options !== undefined) {
        TypeValidation.assertObject(options, "options", {
          operation: "Matrix.svdWithMetrics",
        });
      }

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateMatrixMagnitudes(
          m,
          "m",
          {
            allowZero: true,
          },
          { operation: "Matrix.svdWithMetrics" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Matrix.svdWithMetrics: ${error.message}`);
      }

      // Warn if matrix is large (SVD computation can be computationally expensive)
      if (
        m.length > 0 &&
        m[0].length > 0 &&
        (m.length > 100 || m[0].length > 100)
      ) {
        console.warn(
          `Warning in Matrix.svdWithMetrics: Computing SVD of ${m.length}x${m[0].length} matrix may be computationally expensive. Consider using an iterative or randomized SVD algorithm for large matrices.`,
        );
      }

      // Dynamically load the enhanced SVD implementation
      const {
        computeSVDWithErrorContext,
      } = require("./enhanced-svd-integration.js");

      try {
        return computeSVDWithErrorContext(m, options);
      } catch (error) {
        // Add operation context if not already present
        if (!error.context || !error.context.operation) {
          error.context = error.context || {};
          error.context.operation = "Matrix.svdWithMetrics";
        }
        throw error;
      }
    },

    /**
     * Calculate the condition number of a matrix
     * @param {Matrix|Array<Array<number>>} m - Matrix
     * @returns {number} Condition number
     */
    conditionNumber: function (m) {
      // Validate inputs
      TypeValidation.assertMatrix(m, "m", {
        operation: "Matrix.conditionNumber",
      });
      TypeValidation.assertSquareMatrix(m, "m", {
        operation: "Matrix.conditionNumber",
      });

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateMatrixMagnitudes(
          m,
          "m",
          {
            allowZero: true,
          },
          { operation: "Matrix.conditionNumber" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Matrix.conditionNumber: ${error.message}`);
      }

      // Call the original implementation with validated inputs
      return PrimeMath.conditionNumber(m);
    },

    /**
     * Calculate the rank of a matrix
     * @param {Matrix|Array<Array<number>>} m - Matrix
     * @param {number} [tolerance=1e-10] - Tolerance for singular values
     * @returns {number} Rank
     */
    rank: function (m, tolerance = 1e-10) {
      // Validate inputs
      TypeValidation.assertMatrix(m, "m", { operation: "Matrix.rank" });

      if (tolerance !== undefined) {
        TypeValidation.assertNumber(tolerance, "tolerance", {
          operation: "Matrix.rank",
        });
        TypeValidation.assertPositiveNumber(tolerance, "tolerance", {
          operation: "Matrix.rank",
        });
      }

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateMatrixMagnitudes(
          m,
          "m",
          {
            allowZero: true,
          },
          { operation: "Matrix.rank" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Matrix.rank: ${error.message}`);
      }

      // Warn if matrix is large (rank computation via SVD can be expensive)
      if (
        m.length > 0 &&
        m[0].length > 0 &&
        (m.length > 100 || m[0].length > 100)
      ) {
        console.warn(
          `Warning in Matrix.rank: Computing rank of ${m.length}x${m[0].length} matrix may be computationally expensive.`,
        );
      }

      // Call the original implementation with validated inputs
      return PrimeMath.matrixRank(m, tolerance);
    },

    /**
     * Calculate the Frobenius norm of a matrix
     * @param {Matrix|Array<Array<number>>} m - Matrix
     * @returns {number} Frobenius norm
     */
    norm: function (m) {
      // Validate inputs
      TypeValidation.assertMatrix(m, "m", { operation: "Matrix.norm" });

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateMatrixMagnitudes(
          m,
          "m",
          {
            allowZero: true,
          },
          { operation: "Matrix.norm" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(`Warning in Matrix.norm: ${error.message}`);
      }

      // Call the original implementation with validated inputs
      return PrimeMath.matrixNorm(m);
    },

    /**
     * Multiply two matrices with enhanced precision
     * @param {Array} a - First matrix (array of arrays)
     * @param {Array} b - Second matrix (array of arrays)
     * @returns {Object} Result matrix and error metrics
     */
    multiplyWithMetrics: function (a, b) {
      // Independent implementation to avoid circular dependency
      const EPSILON = StandardizedMath.constants.MACHINE_EPSILON;

      // Validate inputs
      if (
        !Array.isArray(a) ||
        !a.every(Array.isArray) ||
        !Array.isArray(b) ||
        !b.every(Array.isArray)
      ) {
        const context = MathErrorContext.create("Matrix.multiplyWithMetrics", {
          a,
          b,
        });
        throw new Prime.ValidationError(
          "Matrices must be arrays of arrays",
          context,
        );
      }

      const aRows = a.length;
      const aCols = a[0].length;
      const bRows = b.length;
      const bCols = b[0].length;

      // Check matrix dimensions
      if (aCols !== bRows) {
        const context = MathErrorContext.create(
          "Matrix.multiplyWithMetrics",
          { a, b },
          {
            dimensions: {
              a: [aRows, aCols],
              b: [bRows, bCols],
            },
          },
        );
        throw new Prime.DimensionMismatchError(
          `Matrix dimensions mismatch: ${aRows}x${aCols} * ${bRows}x${bCols}`,
          context,
        );
      }

      // Initialize result matrix
      const result = Array(aRows)
        .fill()
        .map(() => Array(bCols).fill(0));
      const maxErrors = Array(aRows)
        .fill()
        .map(() => Array(bCols).fill(0));
      let maxConditionNumber = 0;

      // Helper function for Kahan summation
      function kahanSum(values) {
        if (!Array.isArray(values)) {
          const context = MathErrorContext.create("kahanSum", { values });
          throw new Prime.ValidationError(
            "Expected an array of values",
            context,
          );
        }

        let sum = 0;
        let compensation = 0;
        let maxAbs = 0;
        let minAbs = Infinity;

        // Track smallest and largest values for precision analysis
        for (let i = 0; i < values.length; i++) {
          if (values[i] !== 0) {
            const absVal = Math.abs(values[i]);
            maxAbs = Math.max(maxAbs, absVal);
            minAbs = Math.min(minAbs, absVal);
          }

          // Kahan summation step
          const y = values[i] - compensation;
          const t = sum + y;
          compensation = t - sum - y;
          sum = t;
        }

        // Calculate condition number as measure of potential precision loss
        const conditionNumber = minAbs === Infinity ? 0 : maxAbs / minAbs;

        return {
          sum,
          compensation,
          conditionNumber,
          maxValue: maxAbs,
          minValue: minAbs === Infinity ? 0 : minAbs,
          precision: Math.log10(1 / (EPSILON * conditionNumber || EPSILON)),
        };
      }

      // Perform matrix multiplication with enhanced precision
      for (let i = 0; i < aRows; i++) {
        for (let j = 0; j < bCols; j++) {
          // Prepare terms for dot product
          const terms = new Array(aCols);
          for (let k = 0; k < aCols; k++) {
            terms[k] = a[i][k] * b[k][j];
          }

          // Use Kahan summation for numerical stability
          const sumResult = kahanSum(terms);
          result[i][j] = sumResult.sum;

          // Track largest condition number for error estimation
          maxConditionNumber = Math.max(
            maxConditionNumber,
            sumResult.conditionNumber,
          );

          // Calculate error bound for this element
          maxErrors[i][j] =
            EPSILON * sumResult.conditionNumber * Math.abs(sumResult.sum);
        }
      }

      return {
        matrix: result,
        maxRelativeError: EPSILON * maxConditionNumber,
        elementErrors: maxErrors,
        conditionNumber: maxConditionNumber,
      };
    },

    /**
     * Calculate matrix determinant with numerical stability enhancements
     * @param {Array} matrix - Input matrix
     * @returns {Object} Determinant and error estimation
     */
    determinantWithMetrics: function (matrix) {
      // Independent implementation to avoid circular dependency
      const EPSILON = StandardizedMath.constants.MACHINE_EPSILON;

      if (!Array.isArray(matrix) || !matrix.every(Array.isArray)) {
        const context = MathErrorContext.create(
          "Matrix.determinantWithMetrics",
          { matrix },
        );
        throw new Prime.ValidationError(
          "Matrix must be an array of arrays",
          context,
        );
      }

      const n = matrix.length;

      // Check if matrix is square
      if (!matrix.every((row) => row.length === n)) {
        const context = MathErrorContext.create(
          "Matrix.determinantWithMetrics",
          { matrix },
          {
            dimensions: matrix.map((row) => row.length),
            expected: `${n}x${n} square matrix`,
          },
        );
        throw new Prime.DimensionMismatchError(
          "Matrix must be square",
          context,
        );
      }

      // Handle special cases
      if (n === 1) {
        return {
          determinant: matrix[0][0],
          relativeError: EPSILON,
          absoluteError: EPSILON * Math.abs(matrix[0][0]),
        };
      }

      if (n === 2) {
        const det = matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0];
        return {
          determinant: det,
          relativeError: 2 * EPSILON,
          absoluteError: 2 * EPSILON * Math.abs(det),
        };
      }

      // For larger matrices (n >= 3), implement simplified determinant calculation
      // Note: For full implementation, LU decomposition would be better but requires more code

      // Create a copy of the matrix to avoid modifying the input
      const mtx = matrix.map((row) => [...row]);

      let det = 1;
      let swaps = 0;

      // Gaussian elimination with pivoting
      for (let i = 0; i < n; i++) {
        // Find pivot
        let pivotRow = i;
        let maxPivot = Math.abs(mtx[i][i]);

        for (let r = i + 1; r < n; r++) {
          if (Math.abs(mtx[r][i]) > maxPivot) {
            maxPivot = Math.abs(mtx[r][i]);
            pivotRow = r;
          }
        }

        // Check for singularity
        if (maxPivot < EPSILON) {
          return {
            determinant: 0,
            relativeError: 0,
            absoluteError: 0,
            isSingular: true,
          };
        }

        // Swap rows if needed
        if (pivotRow !== i) {
          [mtx[i], mtx[pivotRow]] = [mtx[pivotRow], mtx[i]];
          swaps++;
        }

        // Eliminate below
        for (let r = i + 1; r < n; r++) {
          const factor = mtx[r][i] / mtx[i][i];

          for (let c = i; c < n; c++) {
            mtx[r][c] -= factor * mtx[i][c];
          }
        }

        // Multiply diagonal elements
        det *= mtx[i][i];
      }

      // Apply sign change if odd number of swaps
      if (swaps % 2 === 1) {
        det = -det;
      }

      // Estimate error based on matrix size
      const relativeError = n * EPSILON;

      return {
        determinant: det,
        relativeError,
        absoluteError: relativeError * Math.abs(det),
      };
    },
  },

  /**
   * Tensor operations with numerical stability
   */
  Tensor: StandardizedTensor,

  /**
   * Advanced math operations with enhanced precision
   */

  /**
   * Calculate the square root with enhanced precision
   * @param {number} x - Input value
   * @returns {number} Square root
   */
  sqrt: PrimeMath.sqrt,

  /**
   * Calculate the power with enhanced precision
   * @param {number} base - Base value
   * @param {number} exponent - Exponent value
   * @returns {number} Result of base raised to exponent
   */
  pow: PrimeMath.pow,

  /**
   * Calculate the exponential function (e^x) with enhanced precision
   * @param {number} x - Exponent
   * @returns {number} e^x
   */
  exp: PrimeMath.exp,

  /**
   * Calculate the natural logarithm with enhanced precision
   * @param {number} x - Input value
   * @returns {number} Natural logarithm
   */
  log: PrimeMath.log,

  /**
   * Calculate sine with enhanced precision
   * @param {number} x - Angle in radians
   * @returns {number} Sine value
   */
  sin: PrimeMath.sin,

  /**
   * Calculate cosine with enhanced precision
   * @param {number} x - Angle in radians
   * @returns {number} Cosine value
   */
  cos: PrimeMath.cos,

  /**
   * Calculate tangent with enhanced precision
   * @param {number} x - Angle in radians
   * @returns {number} Tangent value
   */
  tan: PrimeMath.tan,

  /**
   * Calculate the numeric derivative of a function at a point
   * @param {Function} f - Function to differentiate
   * @param {number} x - Point at which to calculate derivative
   * @param {number} [h=1e-8] - Step size for finite difference
   * @returns {number} Derivative value
   */
  derivative: PrimeMath.derivative,

  /**
   * Calculate a numerical integral of a function over an interval
   * @param {Function} f - Function to integrate
   * @param {number} a - Lower bound
   * @param {number} b - Upper bound
   * @param {Object} [options={}] - Integration options
   * @returns {number} Definite integral value
   */
  integrate: PrimeMath.integrate,

  /**
   * Solve a nonlinear equation f(x) = 0 using Newton's method
   * @param {Function} f - Function
   * @param {Function} df - Derivative of f
   * @param {number} x0 - Initial guess
   * @param {Object} [options={}] - Solution options
   * @returns {number} Root of the equation
   */
  solveNewton: PrimeMath.solveNewton,

  /**
   * Solve an optimization problem using gradient descent
   * @param {Function} f - Function to minimize
   * @param {Array<number>|Vector} initialGuess - Initial point
   * @param {Object} [options={}] - Optimization options
   * @returns {Object} Optimization result
   */
  minimizeGradient: PrimeMath.minimizeGradient,

  /**
   * Interpolate between values
   * @param {number} a - First value
   * @param {number} b - Second value
   * @param {number} t - Interpolation parameter (0-1)
   * @returns {number} Interpolated value
   */
  lerp: PrimeMath.lerp,

  /**
   * Clamp a value between a minimum and maximum
   * @param {number} value - Value to clamp
   * @param {number} min - Minimum value
   * @param {number} max - Maximum value
   * @returns {number} Clamped value
   */
  clamp: PrimeMath.clamp,

  /**
   * Check if two numbers are approximately equal
   * @param {number} a - First number
   * @param {number} b - Second number
   * @param {number} [epsilon=Number.EPSILON] - Tolerance
   * @returns {boolean} True if numbers are approximately equal
   */
  approxEqual: PrimeMath.approxEqual,

  /**
   * Advanced numerical integration algorithms
   */
  Integration: {
    /**
     * Adaptive numerical integration using Gauss-Kronrod quadrature
     * @param {Function} f - Function to integrate
     * @param {number} a - Lower bound
     * @param {number} b - Upper bound
     * @param {Object} options - Integration options
     * @returns {Object} Integration result and error estimation
     */
    adaptiveQuadrature: function (f, a, b, options = {}) {
      // Independent implementation to avoid circular dependency
      if (typeof f !== "function") {
        throw new TypeError("First argument must be a function");
      }

      if (typeof a !== "number" || typeof b !== "number") {
        throw new TypeError("Integration bounds must be numbers");
      }

      // Configure integration options
      const EPSILON = StandardizedMath.constants.MACHINE_EPSILON;
      const tolerance = options.tolerance || 1e-10; // Default tolerance
      const maxDepth = options.maxDepth || 20;
      const initialIntervals = options.initialIntervals || 1;

      // Initialize result
      let result = 0;
      let error = 0;
      let evaluations = 0;

      // Define Gauss-Kronrod weights and points
      // 7-15 point rule
      const gkPoints = [
        0, 0.2077849550078985, -0.2077849550078985, 0.4058451513773972,
        -0.4058451513773972, 0.5860872354676911, -0.5860872354676911,
        0.7415311855993944, -0.7415311855993944, 0.8648644233597691,
        -0.8648644233597691, 0.9491079123427585, -0.9491079123427585,
        0.9914553711208126, -0.9914553711208126,
      ];

      const gkWeights = [
        0.2094821410847278, 0.2044329400752989, 0.2044329400752989,
        0.1903505780647854, 0.1903505780647854, 0.1690047266392679,
        0.1690047266392679, 0.1406532597155259, 0.1406532597155259,
        0.1047900103222502, 0.1047900103222502, 0.0630920926299786,
        0.0630920926299786, 0.0229353220105292, 0.0229353220105292,
      ];

      const gPoints = [
        0, 0.4058451513773972, -0.4058451513773972, 0.7415311855993944,
        -0.7415311855993944, 0.9491079123427585, -0.9491079123427585, 0, 0, 0,
        0, 0, 0, 0, 0,
      ];

      const gWeights = [
        0.4179591836734694, 0.3818300505051189, 0.3818300505051189,
        0.2797053914892767, 0.2797053914892767, 0.1294849661688697,
        0.1294849661688697, 0, 0, 0, 0, 0, 0, 0, 0,
      ];

      // Adaptive integration function
      const adaptiveIntegrate = (a, b, depth) => {
        const center = (a + b) / 2;
        const halfLength = (b - a) / 2;

        // Compute Gauss-Kronrod quadrature
        let gkSum = 0;
        let gSum = 0;

        for (let i = 0; i < gkPoints.length; i++) {
          const x = center + halfLength * gkPoints[i];
          const fValue = f(x);
          gkSum += gkWeights[i] * fValue;

          // For Gauss quadrature points only
          if (i < gPoints.length && gPoints[i] !== 0) {
            gSum += gWeights[i] * fValue;
          }

          evaluations++;
        }

        // Scale by half-length
        const gkIntegral = halfLength * gkSum;
        const gIntegral = halfLength * gSum;

        // Error estimate
        const errorEstimate = Math.abs(gkIntegral - gIntegral);

        // Check if this interval is sufficiently accurate
        if (errorEstimate <= tolerance * halfLength || depth >= maxDepth) {
          return {
            integral: gkIntegral,
            error: errorEstimate,
          };
        }

        // Otherwise, split interval and recurse
        const leftResult = adaptiveIntegrate(a, center, depth + 1);
        const rightResult = adaptiveIntegrate(center, b, depth + 1);

        return {
          integral: leftResult.integral + rightResult.integral,
          error: leftResult.error + rightResult.error,
        };
      };

      // Split integration range into initial intervals
      const intervalSize = (b - a) / initialIntervals;
      let totalIntegral = 0;
      let totalError = 0;

      for (let i = 0; i < initialIntervals; i++) {
        const intervalStart = a + i * intervalSize;
        const intervalEnd = intervalStart + intervalSize;
        const intervalResult = adaptiveIntegrate(intervalStart, intervalEnd, 0);

        totalIntegral += intervalResult.integral;
        totalError += intervalResult.error;
      }

      return {
        integral: totalIntegral,
        error: totalError,
        evaluations,
        relativeError:
          totalIntegral !== 0 ? totalError / Math.abs(totalIntegral) : 0,
        precision: Math.log10(1 / (EPSILON || Math.min(totalError, EPSILON))),
      };
    },
  },

  /**
   * Advanced optimization algorithms
   */
  Optimization: {
    /**
     * Find minimum of a function using gradient descent with adaptive step sizing
     * @param {Function} f - Function to minimize
     * @param {Array} initialPoint - Starting point
     * @param {Object} options - Optimization options
     * @returns {Object} Optimization result
     */
    gradientDescent: function (f, initialPoint, options = {}) {
      // Independent implementation to avoid circular dependency
      if (typeof f !== "function") {
        throw new TypeError("First argument must be a function");
      }

      if (!Array.isArray(initialPoint)) {
        throw new TypeError("Initial point must be an array");
      }

      // Configuration options with defaults
      const EPSILON = StandardizedMath.constants.MACHINE_EPSILON;
      const maxIterations = options.maxIterations || 1000;
      const tolerance = options.tolerance || 1e-8;
      const learningRate = options.learningRate || 0.01;
      const adaptiveLR = options.adaptiveLearningRate !== false;
      const momentum = options.momentum || 0;

      // Initialize variables
      const x = [...initialPoint];
      let fx = f(x);
      let iter = 0;
      let converged = false;
      let stepSize = learningRate;
      let previousGradient = null;

      // Function to compute gradient with numerical differencing
      const computeGradient = (f, x) => {
        const n = x.length;
        const gradient = new Array(n);
        const h = Math.max(1e-6, EPSILON * 100); // Step size for numerical differentiation

        // Use central differences for better accuracy
        for (let i = 0; i < n; i++) {
          const xPlus = [...x];
          const xMinus = [...x];

          xPlus[i] += h;
          xMinus[i] -= h;

          gradient[i] = (f(xPlus) - f(xMinus)) / (2 * h);
        }

        // Normalize gradient to unit length if it's not zero
        let norm = 0;
        for (let i = 0; i < n; i++) {
          norm += gradient[i] * gradient[i];
        }

        norm = Math.sqrt(norm);

        if (norm > EPSILON) {
          for (let i = 0; i < n; i++) {
            gradient[i] /= norm;
          }
        }

        return gradient;
      };

      // Track progress
      const history = options.trackHistory
        ? [
            {
              iteration: 0,
              x: [...x],
              fx,
              stepSize,
              converged: false,
            },
          ]
        : null;

      // Main optimization loop
      while (iter < maxIterations && !converged) {
        // Compute gradient using numerical differentiation
        const gradient = computeGradient(f, x);

        // Update with momentum if enabled
        for (let i = 0; i < x.length; i++) {
          let update = -stepSize * gradient[i];

          // Add momentum term if available
          if (previousGradient) {
            update += momentum * previousGradient[i];
          }

          x[i] += update;
        }

        // Evaluate function at the new point
        const newFx = f(x);

        // Update adaptive learning rate if improvement seen
        if (adaptiveLR) {
          if (newFx < fx) {
            // Successful step, increase step size
            stepSize *= 1.2;
          } else {
            // Unsuccessful step, reduce step size
            stepSize *= 0.5;

            // Revert the step if it made things worse
            for (let i = 0; i < x.length; i++) {
              x[i] -= -stepSize * gradient[i];
              if (previousGradient) {
                x[i] -= momentum * previousGradient[i];
              }
            }

            // Re-evaluate function
            newFx = f(x);
          }
        }

        // Check for convergence
        const fxChange = Math.abs(newFx - fx);
        converged = fxChange < tolerance;

        // Update for next iteration
        fx = newFx;
        previousGradient = gradient;
        iter++;

        // Save history if tracking is enabled
        if (history) {
          history.push({
            iteration: iter,
            x: [...x],
            fx,
            stepSize,
            converged,
          });
        }
      }

      return {
        minimizer: x,
        minimum: fx,
        iterations: iter,
        converged,
        evaluations: iter * (x.length * 2 + 1), // Evaluations for gradient + function evaluations
        history: history || undefined,
        message: converged
          ? "Converged successfully"
          : "Maximum iterations reached",
      };
    },

    /**
     * Enhanced simulated annealing with adaptive temperature and constraints
     * @param {Function} f - Function to minimize
     * @param {Array} initialPoint - Starting point
     * @param {Object} options - Annealing options
     * @returns {Object} Optimization result
     */
    simulatedAnnealing: function (f, initialPoint, options = {}) {
      // Independent implementation to avoid circular dependency
      if (typeof f !== "function") {
        throw new TypeError("First argument must be a function");
      }

      if (!Array.isArray(initialPoint)) {
        throw new TypeError("Initial point must be an array");
      }

      // Configure algorithm options
      const maxIterations = options.maxIterations || 1000;
      const initialTemp = options.initialTemperature || 100;
      const finalTemp = options.finalTemperature || 1e-8;
      const coolingRate = options.coolingRate || 0.95;
      const moveSize = options.moveSize || 1.0;
      const adaptiveMove = options.adaptiveMove !== false;
      const reheating = options.reheating !== false;

      // Initialize variables
      let x = [...initialPoint];
      let fx = f(x);
      let bestX = [...x];
      let bestFx = fx;
      let temp = initialTemp;
      let iter = 0;
      let iterSinceImprovement = 0;
      let moveSizes = Array(x.length).fill(moveSize);

      // Track history if requested
      const history = options.trackHistory
        ? [
            {
              iteration: 0,
              x: [...x],
              fx,
              temperature: temp,
              accepted: true,
              improvement: false,
            },
          ]
        : null;

      // Main optimization loop
      while (iter < maxIterations && temp > finalTemp) {
        // Generate a random neighbor
        const neighbor = [...x];
        for (let i = 0; i < neighbor.length; i++) {
          // Random perturbation scaled by temperature and move size
          const rand = 2 * Math.random() - 1; // Random number in [-1, 1]
          neighbor[i] += (rand * moveSizes[i] * temp) / initialTemp;
        }

        // Evaluate neighbor
        const neighborFx = f(neighbor);

        // Metropolis acceptance criterion
        let acceptance = 0;
        let accepted = false;
        let improvement = false;

        if (neighborFx <= fx) {
          // Accept better solution
          accepted = true;
          acceptance = 1;

          // Check if this is the best solution found so far
          if (neighborFx < bestFx) {
            bestX = [...neighbor];
            bestFx = neighborFx;
            improvement = true;
            iterSinceImprovement = 0;
          }
        } else {
          // Probabilistic acceptance of worse solutions
          const delta = neighborFx - fx;
          acceptance = Math.exp(-delta / temp);
          accepted = Math.random() < acceptance;
        }

        // Update current solution if accepted
        if (accepted) {
          x = [...neighbor];
          fx = neighborFx;
        }

        // Adaptive move size adjustment
        if (adaptiveMove && iter > 0 && iter % 50 === 0) {
          for (let i = 0; i < moveSizes.length; i++) {
            // If acceptance rate is too high, increase move size
            // If acceptance rate is too low, decrease move size
            const acceptanceRate =
              iter > 0
                ? history
                    .slice(Math.max(0, iter - 50), iter)
                    .filter((h) => h.accepted).length / Math.min(50, iter)
                : 0.5;

            if (acceptanceRate > 0.6) {
              moveSizes[i] *= 1.1; // Increase move size
            } else if (acceptanceRate < 0.3) {
              moveSizes[i] *= 0.9; // Decrease move size
            }

            // Ensure move size stays in reasonable bounds
            moveSizes[i] = Math.max(1e-6, Math.min(10, moveSizes[i]));
          }
        }

        // Update temperature with cooling schedule
        temp *= coolingRate;

        // Track iterations since last improvement
        iterSinceImprovement++;

        // Reheat if stuck in a local minimum
        if (reheating && iterSinceImprovement > maxIterations / 10) {
          temp = initialTemp * 0.5;
          iterSinceImprovement = 0;
        }

        // Save history if tracking is enabled
        if (history) {
          history.push({
            iteration: iter + 1,
            x: [...x],
            fx,
            temperature: temp,
            accepted,
            improvement,
            acceptanceProbability: acceptance,
          });
        }

        iter++;
      }

      return {
        minimizer: bestX,
        minimum: bestFx,
        iterations: iter,
        finalTemperature: temp,
        history: history || undefined,
        evaluations: iter + 1, // Initial point + all neighbors
      };
    },
  },

  /**
   * Linear algebra operations
   */
  LinearAlgebra: {
    // Add any specialized linear algebra operations not covered by Matrix or Vector
  },

  /**
   * Statistics and probability functions
   */
  Statistics: {
    /**
     * Calculate the mean of an array of values
     * @param {Array<number>} values - Input values
     * @returns {number} Mean value
     */
    mean: function (values) {
      if (!Array.isArray(values) || values.length === 0) {
        throw new Prime.ValidationError(
          "Mean requires a non-empty array of numbers",
          {
            context: {
              module: "StandardizedMath",
              method: "Statistics.mean",
              actualType: typeof values,
            },
          },
        );
      }

      return MathUtils.kahanSum(values).sum / values.length;
    },

    /**
     * Calculate the variance of an array of values
     * @param {Array<number>} values - Input values
     * @param {boolean} [sample=false] - If true, calculate sample variance
     * @returns {number} Variance
     */
    variance: function (values, sample = false) {
      if (!Array.isArray(values) || values.length === 0) {
        throw new Prime.ValidationError(
          "Variance requires a non-empty array of numbers",
          {
            context: {
              module: "StandardizedMath",
              method: "Statistics.variance",
              actualType: typeof values,
            },
          },
        );
      }

      const mean = this.mean(values);
      const squaredDiffs = values.map((x) => Math.pow(x - mean, 2));
      const divisor = sample ? Math.max(1, values.length - 1) : values.length;

      return MathUtils.kahanSum(squaredDiffs).sum / divisor;
    },

    /**
     * Calculate the standard deviation of an array of values
     * @param {Array<number>} values - Input values
     * @param {boolean} [sample=false] - If true, calculate sample standard deviation
     * @returns {number} Standard deviation
     */
    standardDeviation: function (values, sample = false) {
      return Math.sqrt(this.variance(values, sample));
    },

    /**
     * Generate a normally distributed random number
     * @param {number} [mean=0] - Mean of the distribution
     * @param {number} [stdDev=1] - Standard deviation
     * @returns {number} Random number
     */
    randomNormal: PrimeMath.randomNormal,
  },
};

// Export the StandardizedMath module and error context helper
module.exports = {
  ...StandardizedMath,
  ErrorContext: MathErrorContext,
};
