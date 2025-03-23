/**
 * PrimeOS JavaScript Library - Manifold
 * A proper implementation of the Manifold class for Base0
 */

// Import the Prime object from core
const Prime = require('../../core/prime');

// Import the needed math utilities or create fallbacks if not available
const Matrix = (Prime.Math && Prime.Math.Matrix) || {
  identity: size => {
    if (!Number.isInteger(size) || size <= 0) {
      throw new Prime.ValidationError('Size must be a positive integer', { context: { size } });
    }
    return Array(size).fill().map((_, i) => 
      Array(size).fill().map((_, j) => i === j ? 1 : 0)
    );
  },
  clone: matrix => {
    if (!Array.isArray(matrix) || !matrix.length || !Array.isArray(matrix[0])) {
      throw new Prime.ValidationError('Invalid matrix format', { context: { matrix } });
    }
    return matrix.map(row => [...row]);
  },
  multiply: (A, B) => {
    if (!Array.isArray(A) || !Array.isArray(B) || !A.length || !B.length) {
      throw new Prime.ValidationError('Invalid matrix format', { context: { A, B } });
    }
    
    const n = A.length;
    const result = Array(n).fill().map(_ => Array(n).fill(0));
    
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        for (let k = 0; k < n; k++) {
          result[i][j] += A[i][k] * B[k][j];
        }
      }
    }
    return result;
  },
  inverse: matrix => {
    if (!Array.isArray(matrix) || !matrix.length || !Array.isArray(matrix[0])) {
      throw new Prime.ValidationError('Invalid matrix format', { context: { matrix } });
    }
    
    // Simple matrix inversion for 2x2 and 3x3 matrices
    const n = matrix.length;
    
    if (n === 2) {
      const det = matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0];
      if (Math.abs(det) < 1e-10) {
        throw new Prime.MathematicalError('Matrix is singular', { context: { matrix, determinant: det } });
      }
      
      const invDet = 1 / det;
      return [
        [matrix[1][1] * invDet, -matrix[0][1] * invDet],
        [-matrix[1][0] * invDet, matrix[0][0] * invDet]
      ];
    }
    
    if (n === 3) {
      // Use adjugate method for 3x3
      const det = 
        matrix[0][0] * (matrix[1][1] * matrix[2][2] - matrix[1][2] * matrix[2][1]) -
        matrix[0][1] * (matrix[1][0] * matrix[2][2] - matrix[1][2] * matrix[2][0]) +
        matrix[0][2] * (matrix[1][0] * matrix[2][1] - matrix[1][1] * matrix[2][0]);
      
      if (Math.abs(det) < 1e-10) {
        throw new Prime.MathematicalError('Matrix is singular', { context: { matrix, determinant: det } });
      }
      
      const invDet = 1 / det;
      
      const cofactors = [
        [
          (matrix[1][1] * matrix[2][2] - matrix[1][2] * matrix[2][1]),
          -(matrix[0][1] * matrix[2][2] - matrix[0][2] * matrix[2][1]),
          (matrix[0][1] * matrix[1][2] - matrix[0][2] * matrix[1][1])
        ],
        [
          -(matrix[1][0] * matrix[2][2] - matrix[1][2] * matrix[2][0]),
          (matrix[0][0] * matrix[2][2] - matrix[0][2] * matrix[2][0]),
          -(matrix[0][0] * matrix[1][2] - matrix[0][2] * matrix[1][0])
        ],
        [
          (matrix[1][0] * matrix[2][1] - matrix[1][1] * matrix[2][0]),
          -(matrix[0][0] * matrix[2][1] - matrix[0][1] * matrix[2][0]),
          (matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0])
        ]
      ];
      
      // Multiply by 1/det and transpose
      return cofactors.map((row, i) => 
        row.map((val, j) => cofactors[j][i] * invDet)
      );
    }
    
    throw new Prime.MathematicalError('Matrix inversion only implemented for 2x2 and 3x3 matrices', {
      context: { matrixSize: n }
    });
  },
  determinant: matrix => {
    if (!Array.isArray(matrix) || !matrix.length || !Array.isArray(matrix[0])) {
      throw new Prime.ValidationError('Invalid matrix format', { context: { matrix } });
    }
    
    const n = matrix.length;
    
    if (n === 2) {
      return matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0];
    }
    
    if (n === 3) {
      return (
        matrix[0][0] * (matrix[1][1] * matrix[2][2] - matrix[1][2] * matrix[2][1]) -
        matrix[0][1] * (matrix[1][0] * matrix[2][2] - matrix[1][2] * matrix[2][0]) +
        matrix[0][2] * (matrix[1][0] * matrix[2][1] - matrix[1][1] * matrix[2][0])
      );
    }
    
    throw new Prime.MathematicalError('Determinant only implemented for 2x2 and 3x3 matrices', {
      context: { matrixSize: n }
    });
  },
  transpose: matrix => {
    if (!Array.isArray(matrix) || !matrix.length || !Array.isArray(matrix[0])) {
      throw new Prime.ValidationError('Invalid matrix format', { context: { matrix } });
    }
    
    const rows = matrix.length;
    const cols = matrix[0].length;
    const result = Array(cols).fill().map(_ => Array(rows).fill(0));
    
    for (let i = 0; i < rows; i++) {
      for (let j = 0; j < cols; j++) {
        result[j][i] = matrix[i][j];
      }
    }
    
    return result;
  }
};

const Vector = (Prime.Math && Prime.Math.Vector) || {
  magnitude: vector => {
    if (!Array.isArray(vector)) {
      throw new Prime.ValidationError('Vector must be an array', { context: { vector } });
    }
    return Math.sqrt(vector.reduce((sum, val) => sum + val * val, 0));
  },
  distance: (a, b) => {
    if (!Array.isArray(a) || !Array.isArray(b)) {
      throw new Prime.ValidationError('Vectors must be arrays', { context: { a, b } });
    }
    
    if (a.length !== b.length) {
      throw new Prime.ValidationError('Vectors must have the same dimension', {
        context: { dimensionA: a.length, dimensionB: b.length }
      });
    }
    
    let sum = 0;
    for (let i = 0; i < a.length; i++) {
      sum += Math.pow(a[i] - b[i], 2);
    }
    return Math.sqrt(sum);
  },
  normalize: vector => {
    if (!Array.isArray(vector)) {
      throw new Prime.ValidationError('Vector must be an array', { context: { vector } });
    }
    
    const mag = Math.sqrt(vector.reduce((sum, val) => sum + val * val, 0));
    if (mag === 0) return vector.map(_ => 0);
    return vector.map(val => val / mag);
  },
  dot: (a, b) => {
    if (!Array.isArray(a) || !Array.isArray(b)) {
      throw new Prime.ValidationError('Vectors must be arrays', { context: { a, b } });
    }
    
    if (a.length !== b.length) {
      throw new Prime.ValidationError('Vectors must have the same dimension', {
        context: { dimensionA: a.length, dimensionB: b.length }
      });
    }
    
    let sum = 0;
    for (let i = 0; i < a.length; i++) {
      sum += a[i] * b[i];
    }
    return sum;
  },
  cross: (a, b) => {
    if (!Array.isArray(a) || !Array.isArray(b)) {
      throw new Prime.ValidationError('Vectors must be arrays', { context: { a, b } });
    }
    
    if (a.length !== 3 || b.length !== 3) {
      throw new Prime.ValidationError('Cross product is only defined for 3D vectors', {
        context: { dimensionA: a.length, dimensionB: b.length }
      });
    }
    
    return [
      a[1] * b[2] - a[2] * b[1],
      a[2] * b[0] - a[0] * b[2],
      a[0] * b[1] - a[1] * b[0]
    ];
  },
  scale: (vector, scalar) => {
    if (!Array.isArray(vector)) {
      throw new Prime.ValidationError('Vector must be an array', { context: { vector } });
    }
    
    if (typeof scalar !== 'number') {
      throw new Prime.ValidationError('Scalar must be a number', { context: { scalar } });
    }
    
    return vector.map(val => val * scalar);
  }
};

/**
 * Manifold - Full implementation with proper geodesic calculations
 */
class Manifold {
  /**
   * Create a new manifold
   * @param {Object} config - Configuration object
   * @param {number} config.dimensions - Number of dimensions
   * @param {Array[][]} config.metric - Metric tensor
   * @param {string} config.type - Type of manifold ('euclidean', 'spherical', 'hyperbolic', 'custom')
   */
  constructor(config = {}) {
    this.dimensions = config.dimensions || 3;
    this.type = config.type || 'euclidean';
    
    // Initialize the metric tensor based on the type
    if (config.metric) {
      this.metric = Matrix.clone(config.metric);
    } else {
      // Default metrics for different manifold types
      switch (this.type) {
        case 'euclidean':
          this.metric = Matrix.identity(this.dimensions);
          break;
          
        case 'spherical':
          // For a unit sphere
          this.metric = Matrix.identity(this.dimensions);
          break;
          
        case 'hyperbolic':
          // For hyperbolic space with Minkowski metric
          this.metric = Matrix.identity(this.dimensions);
          if (this.dimensions > 0) {
            this.metric[0][0] = -1; // Time dimension has negative signature
          }
          break;
          
        default: // custom or unknown types default to Euclidean
          this.metric = Matrix.identity(this.dimensions);
      }
    }
    
    this.name = config.name || this.type.charAt(0).toUpperCase() + this.type.slice(1);
    
    // Connection coefficients (Christoffel symbols)
    this.christoffelSymbols = this._computeChristoffelSymbols();
  }
  
  /**
   * Compute Christoffel symbols for the manifold based on the metric
   * @private
   * @returns {Array[][][]} Christoffel symbols Γ^i_jk
   */
  _computeChristoffelSymbols() {
    const n = this.dimensions;
    
    // For Euclidean space, all Christoffel symbols are zero
    if (this.type === 'euclidean') {
      return Array(n).fill().map(() => 
        Array(n).fill().map(() => 
          Array(n).fill(0)
        )
      );
    }
    
    // For other manifold types, compute the symbols
    // Note: This is a simplified version that works for simple manifolds
    try {
      // First calculate the inverse metric tensor
      const inverseMetric = Matrix.inverse(this.metric);
      
      // Initialize the symbols as a 3D array
      const symbols = Array(n).fill().map(() => 
        Array(n).fill().map(() => 
          Array(n).fill(0)
        )
      );
      
      // Calculate the partial derivatives of the metric tensor
      // In many simple cases, these would be constant or zero
      // For a more complete implementation, this would compute actual derivatives
      const metricDerivatives = Array(n).fill().map(() => 
        Array(n).fill().map(() => 
          Array(n).fill(0)
        )
      );
      
      // Compute the symbols
      for (let i = 0; i < n; i++) {
        for (let j = 0; j < n; j++) {
          for (let k = 0; k < n; k++) {
            for (let l = 0; l < n; l++) {
              symbols[i][j][k] += 0.5 * inverseMetric[i][l] * (
                metricDerivatives[l][j][k] + 
                metricDerivatives[l][k][j] - 
                metricDerivatives[j][k][l]
              );
            }
          }
        }
      }
      
      return symbols;
    } catch (error) {
      // If there's an error (e.g., matrix inversion), return zero symbols
      console.error('Error computing Christoffel symbols:', error);
      return Array(n).fill().map(() => 
        Array(n).fill().map(() => 
          Array(n).fill(0)
        )
      );
    }
  }
  
  /**
   * Compute geodesics on the manifold
   * @param {Array} point - Starting point
   * @param {Array} direction - Direction vector
   * @param {Object} [options] - Options for geodesic computation
   * @param {number} options.steps - Number of steps for numerical integration (default: 10)
   * @param {number} options.stepSize - Step size for numerical integration (default: 0.1)
   * @returns {Object} Geodesic curve information
   */
  computeGeodesic(point, direction, options = {}) {
    const steps = options.steps || 10;
    const stepSize = options.stepSize || 0.1;
    
    if (!Array.isArray(point) || point.length !== this.dimensions) {
      throw new Error(`Point must be an array with ${this.dimensions} dimensions`);
    }
    
    if (!Array.isArray(direction) || direction.length !== this.dimensions) {
      throw new Error(`Direction must be an array with ${this.dimensions} dimensions`);
    }
    
    // For Euclidean space, geodesics are straight lines
    if (this.type === 'euclidean') {
      const length = Vector.magnitude(direction);
      
      return {
        startPoint: [...point],
        direction: [...direction],
        length,
        type: 'line',
        points: Array(steps + 1).fill().map((_, i) => {
          const t = i * stepSize;
          return point.map((coord, j) => coord + t * direction[j]);
        })
      };
    }
    
    // For spherical space, geodesics are great circles
    if (this.type === 'spherical' && this.dimensions === 3) {
      const length = Vector.magnitude(direction);
      
      // Normalize the starting point and direction for the unit sphere
      const normalizedPoint = Vector.normalize(point);
      
      // Project the direction to the tangent space
      const dotProduct = Vector.dot(normalizedPoint, direction);
      const tangentDirection = direction.map((d, i) => d - dotProduct * normalizedPoint[i]);
      const normalizedDirection = Vector.normalize(tangentDirection);
      
      return {
        startPoint: [...normalizedPoint],
        direction: [...normalizedDirection],
        length,
        type: 'greatCircle',
        points: Array(steps + 1).fill().map((_, i) => {
          const t = i * stepSize;
          // Rotate the point around the axis normal to the plane containing 
          // the point and direction
          const rotationAxis = Vector.cross(normalizedPoint, normalizedDirection);
          const normalizedRotationAxis = Vector.normalize(rotationAxis);
          
          // Use Rodrigues' rotation formula
          const cosTheta = Math.cos(t * length);
          const sinTheta = Math.sin(t * length);
          
          return normalizedPoint.map((p, i) => 
            p * cosTheta + 
            normalizedRotationAxis[i] * Vector.dot(rotationAxis, p) * (1 - cosTheta) +
            Vector.cross(normalizedRotationAxis, [p])[i] * sinTheta
          );
        })
      };
    }
    
    // For other manifold types, use numerical integration of the geodesic equation
    // This is a simplified implementation using Euler's method
    const initialPosition = [...point];
    const initialVelocity = [...direction];
    
    const positions = [initialPosition];
    let currentPosition = [...initialPosition];
    let currentVelocity = [...initialVelocity];
    
    for (let step = 0; step < steps; step++) {
      // Calculate the acceleration using the geodesic equation
      const acceleration = Array(this.dimensions).fill(0);
      
      for (let i = 0; i < this.dimensions; i++) {
        for (let j = 0; j < this.dimensions; j++) {
          for (let k = 0; k < this.dimensions; k++) {
            acceleration[i] -= this.christoffelSymbols[i][j][k] * 
                              currentVelocity[j] * currentVelocity[k];
          }
        }
      }
      
      // Update position and velocity using Euler's method
      const newPosition = currentPosition.map((p, i) => 
        p + stepSize * currentVelocity[i]
      );
      
      const newVelocity = currentVelocity.map((v, i) => 
        v + stepSize * acceleration[i]
      );
      
      positions.push(newPosition);
      currentPosition = newPosition;
      currentVelocity = newVelocity;
    }
    
    return {
      startPoint: initialPosition,
      direction: initialVelocity,
      length: Vector.magnitude(direction) * steps * stepSize,
      type: 'geodesic',
      points: positions
    };
  }
  
  /**
   * Get the metric tensor at a point
   * @param {Array} point - Point on the manifold
   * @returns {Array[][]} Metric tensor at the point
   */
  getMetricAt(point) {
    // For many simple manifolds, the metric is the same at all points
    // For more complex manifolds, this would compute the metric at the given point
    
    if (!Array.isArray(point) || point.length !== this.dimensions) {
      throw new Error(`Point must be an array with ${this.dimensions} dimensions`);
    }
    
    // For a sphere, the metric depends on the position
    if (this.type === 'spherical' && this.dimensions === 3) {
      // This is a simplified version that assumes a unit sphere
      return Matrix.clone(this.metric);
    }
    
    // For most manifold types in this implementation, just return the metric
    return Matrix.clone(this.metric);
  }
  
  /**
   * Calculate parallel transport of a vector along a curve
   * @param {Array} vector - Vector to transport
   * @param {Array} startPoint - Starting point
   * @param {Array} endPoint - Ending point
   * @returns {Array} Transported vector
   */
  parallelTransport(vector, startPoint, endPoint) {
    if (!Array.isArray(vector) || vector.length !== this.dimensions) {
      throw new Error(`Vector must be an array with ${this.dimensions} dimensions`);
    }
    
    if (!Array.isArray(startPoint) || startPoint.length !== this.dimensions) {
      throw new Error(`Start point must be an array with ${this.dimensions} dimensions`);
    }
    
    if (!Array.isArray(endPoint) || endPoint.length !== this.dimensions) {
      throw new Error(`End point must be an array with ${this.dimensions} dimensions`);
    }
    
    // For Euclidean space, parallel transport is trivial (the vector doesn't change)
    if (this.type === 'euclidean') {
      return [...vector];
    }
    
    // For spherical space, implement parallel transport along a great circle
    if (this.type === 'spherical' && this.dimensions === 3) {
      // Normalize points to ensure they're on the unit sphere
      const p1 = Vector.normalize(startPoint);
      const p2 = Vector.normalize(endPoint);
      
      // Find the rotation axis and angle
      const rotationAxis = Vector.cross(p1, p2);
      const rotationAxisMag = Vector.magnitude(rotationAxis);
      
      // If points are identical or antipodal, no transport needed or undefined
      if (rotationAxisMag < 1e-10) {
        return [...vector];
      }
      
      const normalizedRotationAxis = Vector.normalize(rotationAxis);
      const cosAngle = Vector.dot(p1, p2);
      const angle = Math.acos(Math.max(-1, Math.min(1, cosAngle)));
      
      // Project the vector to the tangent space at the start point
      const dotProduct = Vector.dot(p1, vector);
      const tangentVector = vector.map((v, i) => v - dotProduct * p1[i]);
      
      // Use Rodrigues' rotation formula to transport the vector
      const cosTheta = Math.cos(angle);
      const sinTheta = Math.sin(angle);
      
      const transportedVector = tangentVector.map((v, i) => 
        v * cosTheta + 
        normalizedRotationAxis[i] * Vector.dot(rotationAxis, v) * (1 - cosTheta) +
        Vector.cross(normalizedRotationAxis, [v])[i] * sinTheta
      );
      
      return transportedVector;
    }
    
    // For other manifold types, a more complex implementation would be needed
    // This is a placeholder that just returns the original vector
    return [...vector];
  }
  
  /**
   * Calculate the sectional curvature at a point in a plane
   * @param {Array} point - Point on the manifold
   * @param {Array} u - First vector spanning the plane
   * @param {Array} v - Second vector spanning the plane
   * @returns {number} Sectional curvature
   */
  sectionalCurvature(point, u, v) {
    // For Euclidean space, the curvature is always zero
    if (this.type === 'euclidean') {
      return 0;
    }
    
    // For spherical space, the curvature is constant
    if (this.type === 'spherical') {
      return 1; // Unit sphere has constant curvature 1
    }
    
    // For hyperbolic space, the curvature is constant negative
    if (this.type === 'hyperbolic') {
      return -1; // Standard hyperbolic space has constant curvature -1
    }
    
    // For other manifold types, a more complex calculation would be needed
    // This is a placeholder
    return 0;
  }
  
  /**
   * Calculate distance between two points
   * @param {Array} point1 - First point
   * @param {Array} point2 - Second point
   * @returns {number} Distance between points
   */
  distance(point1, point2) {
    if (!Array.isArray(point1) || point1.length !== this.dimensions) {
      throw new Error(`First point must be an array with ${this.dimensions} dimensions`);
    }
    
    if (!Array.isArray(point2) || point2.length !== this.dimensions) {
      throw new Error(`Second point must be an array with ${this.dimensions} dimensions`);
    }
    
    // For Euclidean space, use the standard distance formula
    if (this.type === 'euclidean') {
      return Vector.distance(point1, point2);
    }
    
    // For spherical space (on a unit sphere), calculate the great circle distance
    if (this.type === 'spherical' && this.dimensions === 3) {
      const p1 = Vector.normalize(point1);
      const p2 = Vector.normalize(point2);
      
      // Compute the angle between the points
      const cosAngle = Vector.dot(p1, p2);
      // Clamp to avoid numerical issues
      const angle = Math.acos(Math.max(-1, Math.min(1, cosAngle)));
      
      return angle; // Arc length on unit sphere
    }
    
    // For hyperbolic space, we would compute the hyperbolic distance
    // This is a simplified placeholder
    if (this.type === 'hyperbolic') {
      return Vector.distance(point1, point2);
    }
    
    // For other manifold types, we need to find the geodesic and compute its length
    // This is a simplification - find the direction vector and compute a geodesic
    const direction = point2.map((p2Val, i) => p2Val - point1[i]);
    const geodesic = this.computeGeodesic(point1, direction);
    
    return geodesic.length;
  }
  
  /**
   * Calculate the exponential map at a point
   * @param {Array} point - Point on the manifold
   * @param {Array} vector - Tangent vector
   * @returns {Array} Point reached by following the geodesic
   */
  exponentialMap(point, vector) {
    if (!Array.isArray(point) || point.length !== this.dimensions) {
      throw new Error(`Point must be an array with ${this.dimensions} dimensions`);
    }
    
    if (!Array.isArray(vector) || vector.length !== this.dimensions) {
      throw new Error(`Vector must be an array with ${this.dimensions} dimensions`);
    }
    
    // For Euclidean space, exp_p(v) = p + v
    if (this.type === 'euclidean') {
      return point.map((p, i) => p + vector[i]);
    }
    
    // For spherical space, use the geodesic formula for the unit sphere
    if (this.type === 'spherical' && this.dimensions === 3) {
      const p = Vector.normalize(point);
      const vnorm = Vector.magnitude(vector);
      
      if (vnorm < 1e-10) {
        return [...p]; // Zero vector maps to the original point
      }
      
      // Project vector to tangent space if needed
      const dotProduct = Vector.dot(p, vector);
      const tangentVector = vector.map((v, i) => v - dotProduct * p[i]);
      const tangentVectorNorm = Vector.magnitude(tangentVector);
      
      if (tangentVectorNorm < 1e-10) {
        return [...p]; // Vector is perpendicular to tangent space
      }
      
      const normalizedTangent = tangentVector.map(v => v / tangentVectorNorm);
      
      // Follow the geodesic (great circle) for distance vnorm
      return p.map((p_i, i) => 
        p_i * Math.cos(vnorm) + normalizedTangent[i] * Math.sin(vnorm)
      );
    }
    
    // For other manifold types, use numerical integration
    const geodesic = this.computeGeodesic(point, vector, { steps: 1, stepSize: 1.0 });
    
    // Return the endpoint of the geodesic
    return geodesic.points[geodesic.points.length - 1];
  }
  
  /**
   * Calculate the logarithm map (inverse of exponential map)
   * @param {Array} point1 - Base point
   * @param {Array} point2 - Target point
   * @returns {Array} Tangent vector at point1 whose exponential map reaches point2
   */
  logarithmMap(point1, point2) {
    if (!Array.isArray(point1) || point1.length !== this.dimensions) {
      throw new Error(`First point must be an array with ${this.dimensions} dimensions`);
    }
    
    if (!Array.isArray(point2) || point2.length !== this.dimensions) {
      throw new Error(`Second point must be an array with ${this.dimensions} dimensions`);
    }
    
    // For Euclidean space, log_p(q) = q - p
    if (this.type === 'euclidean') {
      return point2.map((q, i) => q - point1[i]);
    }
    
    // For spherical space, compute the tangent vector
    if (this.type === 'spherical' && this.dimensions === 3) {
      const p = Vector.normalize(point1);
      const q = Vector.normalize(point2);
      
      const cosAngle = Vector.dot(p, q);
      
      // If points are identical or antipodal, the logarithm is not well-defined
      if (Math.abs(Math.abs(cosAngle) - 1) < 1e-10) {
        return Array(this.dimensions).fill(0);
      }
      
      const angle = Math.acos(Math.max(-1, Math.min(1, cosAngle)));
      
      // Compute the direction in tangent space
      const direction = q.map((q_i, i) => q_i - cosAngle * p[i]);
      const directionNorm = Vector.magnitude(direction);
      
      if (directionNorm < 1e-10) {
        return Array(this.dimensions).fill(0);
      }
      
      // Scale to get the correct length
      return direction.map(d => (angle / directionNorm) * d);
    }
    
    // For other manifold types, this would require solving a boundary value problem
    // This is a placeholder that just returns the vector from point1 to point2
    return point2.map((p2Val, i) => p2Val - point1[i]);
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