/**
 * PrimeOS JavaScript Library - Vector Math
 * Vector operations and utilities
 *
 * This file serves as the main entry point for vector operations,
 * importing functionality from the modular components while maintaining
 * backward compatibility.
 */

// Import the Prime object first
const Prime = require("../core");

// Import the modular vector components - only explicitly require core
// Let the others be loaded lazily through Prime.Math
require("./vector-core");

// Ensure the Math namespace exists
Prime.Math = Prime.Math || {};

// Create a Vector object that maintains the original API
(function () {
  // Don't strictly require components to be already loaded
  // Instead, use getters to access them with lazy loading handled by math/index.js

  // Define helper function to safely get module reference
  const getVectorModule = function (moduleName) {
    if (!Prime.Math[moduleName]) {
      // If not loaded, try to load it via the getter in math/index.js
      if (moduleName === "VectorAdvanced") {
        require("./vector-advanced");
      } else if (moduleName === "VectorValidation") {
        require("./vector-validation");
      }
    }
    return Prime.Math[moduleName] || {};
  };

  // Get references to the modular components - using our helper function
  const VectorCore = Prime.Math.VectorCore || {};

  /**
   * Vector operations for mathematical computations
   * Combines core, advanced, and validation functionality
   * while maintaining backward compatibility
   */
  const Vector = {
    /**
     * Create a new vector with specified dimensions
     * @param {number} dimensions - Number of dimensions
     * @param {number} [initialValue=0] - Initial value for all elements
     * @returns {Array} - New vector with specified dimensions
     */
    create: function (dimensions, initialValue = 0) {
      return VectorCore.create(dimensions, initialValue);
    },

    /**
     * Create a vector of zeros with specified dimensions
     * @param {number} dimensions - Number of dimensions
     * @returns {Array} - Vector filled with zeros
     */
    zeros: function (dimensions) {
      return this.create(dimensions, 0);
    },

    /**
     * Create a vector of ones with specified dimensions
     * @param {number} dimensions - Number of dimensions
     * @returns {Array} - Vector filled with ones
     */
    ones: function (dimensions) {
      return this.create(dimensions, 1);
    },

    /**
     * Create a vector filled with a specific value
     * @param {number} dimensions - Number of dimensions
     * @param {number} value - Value to fill the vector with
     * @returns {Array} - Filled vector
     */
    fill: function (dimensions, value) {
      return this.create(dimensions, value);
    },

    /**
     * Create a vector using TypedArray for improved memory efficiency
     * @param {number} dimensions - Number of dimensions
     * @param {number} initialValue - Initial value for all elements
     * @param {string} arrayType - Type of TypedArray ('float64', 'float32', etc.)
     * @returns {TypedArray} - New vector with specified dimensions
     */
    createTyped: function (dimensions, initialValue, arrayType) {
      return VectorCore.create(dimensions, initialValue, {
        useTypedArray: true,
        arrayType: arrayType || "float64",
      });
    },

    /**
     * Add two vectors element-wise
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {Array} - Result of addition
     */
    add: function (a, b) {
      return VectorCore.add(a, b);
    },

    /**
     * Subtract vector b from vector a element-wise
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {Array} - Result of subtraction
     */
    subtract: function (a, b) {
      return VectorCore.subtract(a, b);
    },

    /**
     * Calculate the dot product of two vectors
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {number} - Dot product
     */
    dot: function (a, b) {
      return VectorCore.dot(a, b);
    },

    /**
     * Scale a vector by a scalar
     * @param {Array} vector - Vector to scale
     * @param {number} scalar - Scaling factor
     * @returns {Array} - Scaled vector
     */
    scale: function (vector, scalar) {
      return VectorCore.scale(vector, scalar);
    },

    /**
     * Calculate the magnitude (norm) of a vector
     * @param {Array} vector - Input vector
     * @returns {number} - Vector magnitude
     */
    magnitude: function (vector) {
      // Use Kahan summation for better precision
      let sum = 0;
      let compensation = 0;

      for (let i = 0; i < vector.length; i++) {
        const squared = vector[i] * vector[i];
        const y = squared - compensation;
        const t = sum + y;
        compensation = t - sum - y;
        sum = t;
      }

      return Math.sqrt(sum);
    },

    /**
     * Normalize a vector (create a unit vector in the same direction)
     * @param {Array} vector - Input vector
     * @returns {Array} - Normalized vector
     */
    normalize: function (vector) {
      const mag = this.magnitude(vector);

      // Check for zero magnitude to avoid division by zero
      if (mag < Number.EPSILON) {
        throw new Error("Cannot normalize a zero vector");
      }

      return this.scale(vector, 1 / mag);
    },

    /**
     * Calculate the cross product of two 3D vectors
     * @param {Array} a - First 3D vector
     * @param {Array} b - Second 3D vector
     * @returns {Array} - Cross product vector
     */
    cross: function (a, b) {
      // Ensure vectors are 3D
      if (a.length !== 3 || b.length !== 3) {
        throw new Error("Cross product requires 3D vectors");
      }

      return [
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
      ];
    },

    /**
     * Calculate the angle between two vectors in radians
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {number} - Angle in radians
     */
    angle: function (a, b) {
      const magA = this.magnitude(a);
      const magB = this.magnitude(b);

      // Check for zero vectors
      if (magA < Number.EPSILON || magB < Number.EPSILON) {
        throw new Error("Cannot calculate angle with zero vector");
      }

      const dotProduct = this.dot(a, b);
      // Clamp the value to avoid numerical precision issues
      const cosAngle = Math.max(-1, Math.min(1, dotProduct / (magA * magB)));

      return Math.acos(cosAngle);
    },

    /**
     * Project vector a onto vector b
     * @param {Array} a - Vector to project
     * @param {Array} b - Vector to project onto
     * @returns {Array} - Projection of a onto b
     */
    project: function (a, b) {
      const magBSquared = this.dot(b, b);

      if (magBSquared < Number.EPSILON) {
        throw new Error("Cannot project onto a zero vector");
      }

      const scalar = this.dot(a, b) / magBSquared;
      return this.scale(b, scalar);
    },

    /**
     * Calculate the Euclidean distance between two vectors
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {number} - Euclidean distance
     */
    distance: function (a, b) {
      if (a.length !== b.length) {
        throw new Error("Vectors must have the same dimensions");
      }

      // Create a difference vector and calculate its magnitude
      const diff = this.subtract(a, b);
      return this.magnitude(diff);
    },

    /**
     * Calculate the Manhattan distance (L1 norm) between two vectors
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {number} - Manhattan distance
     */
    manhattanDistance: function (a, b) {
      if (a.length !== b.length) {
        throw new Error("Vectors must have the same dimensions");
      }

      let sum = 0;
      for (let i = 0; i < a.length; i++) {
        sum += Math.abs(a[i] - b[i]);
      }

      return sum;
    },

    /**
     * Elementwise multiplication of two vectors (Hadamard product)
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {Array} - Result of elementwise multiplication
     */
    elementWiseMultiply: function (a, b) {
      if (a.length !== b.length) {
        throw new Error("Vectors must have the same dimensions");
      }

      const result = new Array(a.length);
      for (let i = 0; i < a.length; i++) {
        result[i] = a[i] * b[i];
      }

      return result;
    },

    /**
     * Check if a value is a vector
     * @param {*} value - Value to check
     * @returns {boolean} - True if the value is a vector
     */
    isVector: function (value) {
      return Array.isArray(value);
    },

    /**
     * Check if two vectors have the same dimensions
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {boolean} - True if vectors have the same dimensions
     */
    sameDimensions: function (a, b) {
      return a.length === b.length;
    },

    /**
     * Calculate the outer product of two vectors
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {Array} - Matrix result of outer product
     */
    outerProduct: function (a, b) {
      const result = new Array(a.length);

      for (let i = 0; i < a.length; i++) {
        result[i] = new Array(b.length);
        for (let j = 0; j < b.length; j++) {
          result[i][j] = a[i] * b[j];
        }
      }

      return result;
    },
  };

  // Add Vector to the Prime.Math namespace
  Prime.Math = Prime.Math || {};
  Prime.Math.Vector = Vector;
})();

// Export the enhanced Prime object
module.exports = Prime;
