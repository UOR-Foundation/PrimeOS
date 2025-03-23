/**
 * PrimeOS JavaScript Library - Manifold Mock
 * Simple implementation for testing
 */

// Import the Prime object from core
const Prime = require("../../core/prime.js");

/**
 * Manifold - Simple implementation for tests
 */
class Manifold {
  /**
   * Create a new manifold
   * @param {Object} config - Configuration object
   * @param {number} config.dimensions - Number of dimensions
   * @param {Array[][]} config.metric - Metric tensor
   */
  constructor(config = {}) {
    this.dimensions = config.dimensions || 3;
    // Check if Math module is available, otherwise create an identity matrix manually
    if (Prime.Math && Prime.Math.Matrix && Prime.Math.Matrix.identity) {
      this.metric =
        config.metric || Prime.Math.Matrix.identity(this.dimensions);
    } else {
      // Create a simple identity matrix manually
      this.metric =
        config.metric || this._createIdentityMatrix(this.dimensions);
    }
    this.name = config.name || "Euclidean";
  }

  /**
   * Create a simple identity matrix when Math module isn't available
   * @private
   * @param {number} size - Matrix size
   * @returns {Array[][]} Identity matrix
   */
  _createIdentityMatrix(size) {
    const matrix = [];
    for (let i = 0; i < size; i++) {
      const row = [];
      for (let j = 0; j < size; j++) {
        row.push(i === j ? 1 : 0);
      }
      matrix.push(row);
    }
    return matrix;
  }

  /**
   * Compute a geodesic on the manifold
   * @param {Array} point - Starting point
   * @param {Array} direction - Direction vector
   * @returns {Object} Geodesic curve information
   */
  computeGeodesic(point, direction) {
    // Simple implementation that just returns a line
    return {
      startPoint: [...point],
      direction: [...direction],
      length: this._vectorMagnitude(direction),
      type: "line",
    };
  }

  /**
   * Get the metric tensor at a point
   * @param {Array} point - Point on the manifold
   * @returns {Array[][]} Metric tensor at the point
   */
  getMetricAt(point) {
    // Return a copy of the metric
    return this._cloneMatrix(this.metric);
  }

  /**
   * Calculate distance between two points
   * @param {Array} point1 - First point
   * @param {Array} point2 - Second point
   * @returns {number} Distance between points
   */
  distance(point1, point2) {
    // In Euclidean space, this is just the standard distance
    if (Prime.Math && Prime.Math.Vector && Prime.Math.Vector.distance) {
      return Prime.Math.Vector.distance(point1, point2);
    } else {
      return this._euclideanDistance(point1, point2);
    }
  }

  /**
   * Calculate vector magnitude when Math module isn't available
   * @private
   * @param {Array} vector - The vector
   * @returns {number} Magnitude of the vector
   */
  _vectorMagnitude(vector) {
    if (Prime.Math && Prime.Math.Vector && Prime.Math.Vector.magnitude) {
      return Prime.Math.Vector.magnitude(vector);
    }

    let sumOfSquares = 0;
    for (let i = 0; i < vector.length; i++) {
      sumOfSquares += vector[i] * vector[i];
    }
    return Math.sqrt(sumOfSquares);
  }

  /**
   * Clone a matrix when Math module isn't available
   * @private
   * @param {Array[][]} matrix - The matrix to clone
   * @returns {Array[][]} Cloned matrix
   */
  _cloneMatrix(matrix) {
    if (Prime.Math && Prime.Math.Matrix && Prime.Math.Matrix.clone) {
      return Prime.Math.Matrix.clone(matrix);
    }

    return matrix.map((row) => [...row]);
  }

  /**
   * Calculate Euclidean distance when Math module isn't available
   * @private
   * @param {Array} point1 - First point
   * @param {Array} point2 - Second point
   * @returns {number} Euclidean distance
   */
  _euclideanDistance(point1, point2) {
    if (point1.length !== point2.length) {
      throw new Error("Points must have the same dimension");
    }

    let sumOfSquares = 0;
    for (let i = 0; i < point1.length; i++) {
      const diff = point1[i] - point2[i];
      sumOfSquares += diff * diff;
    }
    return Math.sqrt(sumOfSquares);
  }
}

// Add Manifold class to Prime.Base0 namespace
Prime.Base0 = Prime.Base0 || {};
Prime.Base0.Manifold = Manifold;

// Also add a helper function to create manifolds
Prime.Base0.createManifold = (config) => {
  return new Prime.Base0.Manifold(config);
};

// Export the enhanced Prime object
module.exports = Prime;
