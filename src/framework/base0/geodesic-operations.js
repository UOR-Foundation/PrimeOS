/**
 * PrimeOS JavaScript Library - Framework
 * Base 0: Geodesic Operations
 * Operations related to calculating geodesics between manifolds
 */

// Import core
const Prime = require('../../core.js');
const MathUtils = require('../math');
const { Manifold } = require('./manifold.js');

/**
 * GeodesicOperations - Operations for computing geodesics on manifolds
 */
const GeodesicOperations = {
  /**
   * Calculate geodesic between two manifolds
   * @param {Manifold} source - Source manifold
   * @param {Manifold} target - Target manifold
   * @param {Object} options - Options for geodesic calculation
   * @returns {Object} Geodesic information
   */
  computeGeodesic: function (source, target, options = {}) {
    if (!(source instanceof Manifold) || !(target instanceof Manifold)) {
      throw new Prime.ValidationError('Source and target must be manifolds');
    }

    // Check if manifolds exist in compatible spaces
    const commonSpaces = source
      .getSpaces()
      .filter((space) => target.getSpaces().includes(space));

    if (commonSpaces.length === 0) {
      throw new Prime.InvalidOperationError(
        'Manifolds must share at least one space for geodesic calculation',
      );
    }

    const space = commonSpaces[0];
    const steps = options.steps || 10;
    const method = options.method || 'linear';
    const metric = options.metric || 'euclidean';

    // Get source and target points (simplified implementation)
    const sourcePoint = MathUtils.vector.normalizeSimple(
      Object.values(source.getVariant()),
    );
    const targetPoint = MathUtils.vector.normalizeSimple(
      Object.values(target.getVariant()),
    );

    // Calculate geodesic based on the method
    if (method === 'linear') {
      // Linear interpolation for flat manifolds
      const path = [];
      for (let i = 0; i <= steps; i++) {
        const t = i / steps;
        const point = MathUtils.vector.lerp(sourcePoint, targetPoint, t);
        path.push({
          t,
          point: MathUtils.vector.normalizeSimple(point),
        });
      }

      // Calculate geodesic length
      let length = 0;
      for (let i = 1; i < path.length; i++) {
        length += MathUtils.vector.distance(
          path[i - 1].point,
          path[i].point,
        ).distance;
      }

      return {
        source: sourcePoint,
        target: targetPoint,
        path,
        length,
        space,
      };
    } else if (method === 'riemannian') {
      // More complex geodesic calculation on curved manifolds
      // This would use Riemannian geometry operations (simplified implementation)
      const path = [];

      // For curved manifolds, we need to consider the metric tensor
      // and parallal transport along the path
      for (let i = 0; i <= steps; i++) {
        const t = i / steps;

        // In a real implementation, this would use the exponential map
        // and Riemannian metric to compute the geodesic
        const point = MathUtils.vector.lerp(sourcePoint, targetPoint, t);

        // Apply a correction to keep points on the manifold using vector normalization
        const correctedPoint = MathUtils.vector.normalizeSimple(point);

        path.push({
          t,
          point: correctedPoint,
        });
      }

      // For Riemannian geodesics, length calculation should use the
      // metric tensor at each point
      let length = 0;
      for (let i = 1; i < path.length; i++) {
        // This is a simplified version - actual implementation would
        // use the Riemannian metric
        length += MathUtils.vector.distance(
          path[i - 1].point,
          path[i].point,
        ).distance;
      }

      return {
        source: sourcePoint,
        target: targetPoint,
        path,
        length,
        space,
        method: 'riemannian',
      };
    }

    throw new Prime.InvalidOperationError(
      `Geodesic method ${method} not supported`,
    );
  },

  /**
   * Interpolate between manifolds
   * @param {Manifold} source - Source manifold
   * @param {Manifold} target - Target manifold
   * @param {number} t - Interpolation parameter (0-1)
   * @param {Object} options - Interpolation options
   * @returns {Manifold} Interpolated manifold
   */
  interpolate: function (source, target, t, options = {}) {
    if (!(source instanceof Manifold) || !(target instanceof Manifold)) {
      throw new Prime.ValidationError('Source and target must be manifolds');
    }

    if (typeof t !== 'number' || t < 0 || t > 1) {
      throw new Prime.ValidationError(
        'Interpolation parameter t must be a number between 0 and 1',
      );
    }

    // Check if manifolds have compatible types
    if (source.getType() !== target.getType()) {
      throw new Prime.InvalidOperationError(
        'Cannot interpolate between manifolds of different types',
      );
    }

    const method = options.method || 'linear';

    // Create a new manifold with interpolated properties

    // Interpolate meta properties
    const meta = {
      ...source.getMeta(),
      id: `interpolated_${source.getId()}_${target.getId()}_${t}`,
      interpolated: true,
      sourceId: source.getId(),
      targetId: target.getId(),
      interpolationParameter: t,
    };

    // Invariants should be the same for compatible manifolds
    const invariant = source.getInvariant();

    // Interpolate variant properties
    const sourceVariant = source.getVariant();
    const targetVariant = target.getVariant();
    const variant = {};

    // Combine all keys from both variants
    const allKeys = new Set([
      ...Object.keys(sourceVariant),
      ...Object.keys(targetVariant),
    ]);

    for (const key of allKeys) {
      const sourceValue = sourceVariant[key];
      const targetValue = targetVariant[key];

      // If one side doesn't have the property, use the other one's value
      if (sourceValue === undefined) {
        variant[key] = targetValue;
        continue;
      }
      if (targetValue === undefined) {
        variant[key] = sourceValue;
        continue;
      }

      // Interpolate based on value types
      if (typeof sourceValue === 'number' && typeof targetValue === 'number') {
        // Linear interpolation for numbers
        variant[key] = sourceValue * (1 - t) + targetValue * t;
      } else if (Array.isArray(sourceValue) && Array.isArray(targetValue)) {
        // Array interpolation
        if (sourceValue.length === targetValue.length) {
          variant[key] = sourceValue.map((val, i) => {
            return typeof val === 'number' && typeof targetValue[i] === 'number'
              ? val * (1 - t) + targetValue[i] * t
              : t < 0.5
                ? val
                : targetValue[i];
          });
        } else {
          // Different lengths, use whichever is closer based on t
          variant[key] = t < 0.5 ? sourceValue : targetValue;
        }
      } else {
        // For other types, use whichever is closer based on t
        variant[key] = t < 0.5 ? sourceValue : targetValue;
      }
    }

    // Determine spaces for the interpolated manifold
    const spaces = [...new Set([...source.getSpaces(), ...target.getSpaces()])];

    // Create the interpolated manifold
    const interpolated = new Manifold({
      meta,
      invariant,
      variant,
      depth: Math.round(source.getDepth() * (1 - t) + target.getDepth() * t),
      spaces,
    });

    // Establish relations to the source and target
    interpolated.relateTo(source, 'interpolated_from', { t });
    interpolated.relateTo(target, 'interpolated_to', { t });

    return interpolated;
  },

  /**
   * Compute parallel transport along a geodesic
   * @param {Manifold} source - Source manifold
   * @param {Manifold} target - Target manifold
   * @param {Array} vector - Vector to transport
   * @param {Object} options - Transport options
   * @returns {Object} Transport result
   */
  parallelTransport: function (source, target, vector, options = {}) {
    if (!(source instanceof Manifold) || !(target instanceof Manifold)) {
      throw new Prime.ValidationError('Source and target must be manifolds');
    }

    if (!Array.isArray(vector)) {
      throw new Prime.ValidationError('Vector must be an array');
    }

    // Compute the geodesic between source and target
    const geodesic = this.computeGeodesic(source, target, options);
    const steps = geodesic.path.length - 1;

    // Initialize transported vector
    let transportedVector = [...vector];

    // Parallel transport along the geodesic
    // This is a simplified implementation - a complete one would use
    // the connection coefficients of the manifold
    for (let i = 0; i < steps; i++) {
      const currentPoint = geodesic.path[i].point;
      const nextPoint = geodesic.path[i + 1].point;

      // Calculate tangent to the geodesic
      const tangent = [];
      for (let j = 0; j < currentPoint.length; j++) {
        tangent.push(nextPoint[j] - currentPoint[j]);
      }

      // Normalize tangent
      const tangentNorm = Math.sqrt(
        tangent.reduce((sum, val) => sum + val * val, 0),
      );
      const normalizedTangent = tangent.map((val) => val / tangentNorm);

      // Project vector onto tangent
      const dotProduct = transportedVector.reduce(
        (sum, val, idx) => sum + val * normalizedTangent[idx],
        0,
      );

      // Transport the vector (simplified - just keeping it perpendicular to the geodesic)
      for (let j = 0; j < transportedVector.length; j++) {
        transportedVector[j] -= dotProduct * normalizedTangent[j];
      }

      // Renormalize the transported vector to maintain its norm
      const originalNorm = Math.sqrt(
        vector.reduce((sum, val) => sum + val * val, 0),
      );
      const currentNorm = Math.sqrt(
        transportedVector.reduce((sum, val) => sum + val * val, 0),
      );
      transportedVector = transportedVector.map(
        (val) => val * (originalNorm / currentNorm),
      );
    }

    return {
      originalVector: vector,
      transportedVector,
      geodesic,
    };
  },

  /**
   * Compute sectional curvature between two tangent vectors
   * @param {Manifold} manifold - The manifold
   * @param {Array} vector1 - First tangent vector
   * @param {Array} vector2 - Second tangent vector
   * @param {Object} options - Curvature calculation options
   * @returns {Object} Sectional curvature information
   */
  sectionalCurvature: function (manifold, vector1, vector2, options = {}) {
    if (!(manifold instanceof Manifold)) {
      throw new Prime.ValidationError('First argument must be a manifold');
    }

    if (!Array.isArray(vector1) || !Array.isArray(vector2)) {
      throw new Prime.ValidationError('Vectors must be arrays');
    }

    // This is a simplified implementation of sectional curvature
    // A complete implementation would use the Riemann curvature tensor

    // Ensure vectors have the same length
    if (vector1.length !== vector2.length) {
      throw new Prime.ValidationError('Vectors must have the same dimension');
    }

    // Calculate the point on the manifold (use current variant)
    const point = Object.values(manifold.getVariant());

    // Orthogonalize vectors (Gram-Schmidt)
    // First normalize vector1
    const v1Norm = Math.sqrt(vector1.reduce((sum, val) => sum + val * val, 0));
    const v1Normalized = vector1.map((val) => val / v1Norm);

    // Calculate projection of vector2 onto vector1
    const projection = vector2.reduce(
      (sum, val, idx) => sum + val * v1Normalized[idx],
      0,
    );

    // Subtract projection to get orthogonal component
    const v2Orthogonal = vector2.map(
      (val, idx) => val - projection * v1Normalized[idx],
    );

    // Normalize orthogonal component
    const v2Norm = Math.sqrt(
      v2Orthogonal.reduce((sum, val) => sum + val * val, 0),
    );
    const v2Normalized = v2Orthogonal.map((val) => val / v2Norm);

    // In a real implementation, this would compute the sectional curvature
    // K(v1,v2) = <R(v1,v2)v2,v1> where R is the Riemann curvature tensor

    // For this simplified version, we'll use a heuristic based on the manifold's invariants
    const invariants = Object.values(manifold.getInvariant());
    const meanInvariant =
      invariants.length > 0
        ? invariants.reduce(
          (sum, val) => sum + (typeof val === 'number' ? val : 0),
          0,
        ) / invariants.length
        : 0;

    // Calculate a simple curvature value
    const baseCurvature = Math.exp(-Math.abs(meanInvariant) / 10);

    // Vary the curvature based on the vectors
    // This is just a heuristic for demonstration
    const dotProduct = v1Normalized.reduce(
      (sum, val, idx) => sum + val * v2Normalized[idx],
      0,
    );
    const curvatureValue = baseCurvature * (1.0 - Math.abs(dotProduct));

    return {
      point,
      vectors: [v1Normalized, v2Normalized],
      curvature: curvatureValue,
      plane: {
        v1: v1Normalized,
        v2: v2Normalized,
      },
    };
  },
};

module.exports = GeodesicOperations;
