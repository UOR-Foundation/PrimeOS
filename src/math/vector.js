/**
 * PrimeOS JavaScript Library - Vector Math
 * Vector operations and utilities
 */

// Import the Prime object
const Prime = require("../core");

// Create the Vector module using IIFE
(function () {
  /**
   * Vector operations for mathematical computations
   */
  const Vector = {
    /**
     * Create a new vector with specified dimensions
     * @param {number} dimensions - Number of dimensions
     * @param {number} [initialValue=0] - Initial value for all elements
     * @returns {Array} - New vector with specified dimensions
     */
    create: function (dimensions, initialValue = 0) {
      if (
        !Prime.Utils.isNumber(dimensions) ||
        dimensions <= 0 ||
        !Number.isInteger(dimensions)
      ) {
        throw new Prime.ValidationError(
          "Dimensions must be a positive integer",
        );
      }

      return new Array(dimensions).fill(initialValue);
    },

    /**
     * Add two vectors element-wise
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {Array} - Result of addition
     */
    add: function (a, b) {
      if (!Array.isArray(a) || !Array.isArray(b)) {
        throw new Prime.ValidationError("Vectors must be arrays");
      }

      if (a.length !== b.length) {
        throw new Prime.ValidationError(
          "Vectors must have the same dimensions",
        );
      }

      return a.map((val, i) => val + b[i]);
    },

    /**
     * Subtract vector b from vector a element-wise
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {Array} - Result of subtraction
     */
    subtract: function (a, b) {
      if (!Array.isArray(a) || !Array.isArray(b)) {
        throw new Prime.ValidationError("Vectors must be arrays");
      }

      if (a.length !== b.length) {
        throw new Prime.ValidationError(
          "Vectors must have the same dimensions",
        );
      }

      return a.map((val, i) => val - b[i]);
    },

    /**
     * Calculate the dot product of two vectors
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {number} - Dot product
     */
    dot: function (a, b) {
      if (!Array.isArray(a) || !Array.isArray(b)) {
        throw new Prime.ValidationError("Vectors must be arrays");
      }

      if (a.length !== b.length) {
        throw new Prime.ValidationError(
          "Vectors must have the same dimensions",
        );
      }

      return a.reduce((sum, val, i) => sum + val * b[i], 0);
    },

    /**
     * Scale a vector by a scalar
     * @param {Array} vector - Vector to scale
     * @param {number} scalar - Scaling factor
     * @returns {Array} - Scaled vector
     */
    scale: function (vector, scalar) {
      if (!Array.isArray(vector)) {
        throw new Prime.ValidationError("Vector must be an array");
      }

      if (!Prime.Utils.isNumber(scalar)) {
        throw new Prime.ValidationError("Scalar must be a number");
      }

      return vector.map((val) => val * scalar);
    },

    /**
     * Calculate the magnitude (norm) of a vector
     * @param {Array} vector - Input vector
     * @returns {number} - Vector magnitude
     */
    magnitude: function (vector) {
      if (!Array.isArray(vector)) {
        throw new Prime.ValidationError("Vector must be an array");
      }

      const sumOfSquares = vector.reduce((sum, val) => sum + val * val, 0);
      return Math.sqrt(sumOfSquares);
    },

    /**
     * Normalize a vector to unit length
     * @param {Array} vector - Vector to normalize
     * @returns {Array} - Normalized vector
     */
    normalize: function (vector) {
      if (!Array.isArray(vector)) {
        throw new Prime.ValidationError("Vector must be an array");
      }

      const mag = this.magnitude(vector);

      if (mag === 0) {
        throw new Prime.MathematicalError("Cannot normalize a zero vector");
      }

      return vector.map((val) => val / mag);
    },

    /**
     * Calculate the cross product of two 3D vectors
     * @param {Array} a - First 3D vector
     * @param {Array} b - Second 3D vector
     * @returns {Array} - Cross product
     */
    cross: function (a, b) {
      if (!Array.isArray(a) || !Array.isArray(b)) {
        throw new Prime.ValidationError("Vectors must be arrays");
      }

      if (a.length !== 3 || b.length !== 3) {
        throw new Prime.ValidationError(
          "Cross product is only defined for 3D vectors",
        );
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
      if (!Array.isArray(a) || !Array.isArray(b)) {
        throw new Prime.ValidationError("Vectors must be arrays");
      }

      if (a.length !== b.length) {
        throw new Prime.ValidationError(
          "Vectors must have the same dimensions",
        );
      }

      const magA = this.magnitude(a);
      const magB = this.magnitude(b);

      if (magA === 0 || magB === 0) {
        throw new Prime.MathematicalError(
          "Cannot calculate angle with zero vector",
        );
      }

      const dotProduct = this.dot(a, b);
      const cosTheta = dotProduct / (magA * magB);

      // Handle floating point precision issues
      if (cosTheta > 1) return 0;
      if (cosTheta < -1) return Math.PI;

      return Math.acos(cosTheta);
    },

    /**
     * Project vector a onto vector b
     * @param {Array} a - Vector to project
     * @param {Array} b - Vector to project onto
     * @returns {Array} - Projection result
     */
    project: function (a, b) {
      if (!Array.isArray(a) || !Array.isArray(b)) {
        throw new Prime.ValidationError("Vectors must be arrays");
      }

      if (a.length !== b.length) {
        throw new Prime.ValidationError(
          "Vectors must have the same dimensions",
        );
      }

      const magBSquared = this.dot(b, b);

      if (magBSquared === 0) {
        throw new Prime.MathematicalError("Cannot project onto a zero vector");
      }

      const scalar = this.dot(a, b) / magBSquared;
      return this.scale(b, scalar);
    },

    /**
     * Calculate the distance between two vectors
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {number} - Distance between vectors
     */
    distance: function (a, b) {
      if (!Array.isArray(a) || !Array.isArray(b)) {
        throw new Prime.ValidationError("Vectors must be arrays");
      }

      if (a.length !== b.length) {
        throw new Prime.ValidationError(
          "Vectors must have the same dimensions",
        );
      }

      const difference = this.subtract(a, b);
      return this.magnitude(difference);
    },
  };

  // Add Vector to the Prime.Math namespace
  Prime.Math = Prime.Math || {};
  Prime.Math.Vector = Vector;
})();

// Export the enhanced Prime object
module.exports = Prime;
