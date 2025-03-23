/**
 * PrimeOS JavaScript Library - Manifold Mock
 * Simple implementation for testing
 */

// Import the Prime object from core
const Prime = require('../../core');

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
    this.metric = config.metric || Prime.Math.Matrix.identity(this.dimensions);
    this.name = config.name || 'Euclidean';
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
      length: Prime.Math.Vector.magnitude(direction),
      type: 'line'
    };
  }
  
  /**
   * Get the metric tensor at a point
   * @param {Array} point - Point on the manifold
   * @returns {Array[][]} Metric tensor at the point
   */
  getMetricAt(point) {
    // Return a copy of the metric
    return Prime.Math.Matrix.clone(this.metric);
  }
  
  /**
   * Calculate distance between two points
   * @param {Array} point1 - First point
   * @param {Array} point2 - Second point
   * @returns {number} Distance between points
   */
  distance(point1, point2) {
    // In Euclidean space, this is just the standard distance
    return Prime.Math.Vector.distance(point1, point2);
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