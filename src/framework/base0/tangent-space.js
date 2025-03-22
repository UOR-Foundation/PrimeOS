/**
 * PrimeOS JavaScript Library - Framework
 * Base 0: Tangent Space
 * Operations related to tangent space calculations
 */

// Import core
const Prime = require("../../core.js");
const MathUtils = require("../math");
const { Manifold } = require("./manifold.js");

/**
 * TangentSpaceOperations - Operations for working with tangent spaces on manifolds
 */
const TangentSpaceOperations = {
  /**
   * Calculate the tangent space at a point on a manifold
   * @param {Manifold} manifold - The manifold
   * @param {Object} point - Point on the manifold
   * @param {Object} options - Options for tangent space calculation
   * @returns {Object} Tangent space information
   */
  calculateTangentSpace: function(manifold, point = null, options = {}) {
    if (!(manifold instanceof Manifold)) {
      throw new Prime.ValidationError("First argument must be a manifold");
    }

    // If no point specified, use the current manifold state
    if (point === null) {
      point = Object.values(manifold.getVariant());
    }

    const dimension = point.length;
    const basisVectors = [];

    // Generate basis vectors for the tangent space
    for (let i = 0; i < dimension; i++) {
      // Create basis vector (simplified implementation - in practice these would be
      // calculated based on the manifold's local geometry)
      const basisVector = Array(dimension).fill(0);
      basisVector[i] = 1;
      
      // In a real implementation, these would be corrected to be tangent to the manifold
      basisVectors.push(basisVector);
    }

    // For curved manifolds, we should apply a projection to ensure
    // the basis vectors are truly tangent to the manifold
    const projectedBasis = basisVectors.map(vector => {
      // This is a simplified implementation - in reality this would use
      // the manifold's structure to project to the tangent space
      return MathUtils.vector.normalizeSimple(vector);
    });

    return {
      point,
      basis: projectedBasis,
      dimension: projectedBasis.length,
      manifold
    };
  },

  /**
   * Calculate the curvature at a point on a manifold
   * @param {Manifold} manifold - The manifold
   * @param {Object} point - Point to calculate curvature at
   * @param {Object} options - Options for curvature calculation
   * @returns {Object} Curvature information
   */
  calculateCurvature: function(manifold, point = null, options = {}) {
    if (!(manifold instanceof Manifold)) {
      throw new Prime.ValidationError("First argument must be a manifold");
    }

    // If no point specified, use the current manifold state
    if (point === null) {
      point = Object.values(manifold.getVariant());
    }

    // For a proper implementation, this would calculate the Riemann curvature tensor
    // Here we provide a simplified implementation
    
    // Get the tangent space at the point
    const tangentSpaceInfo = this.calculateTangentSpace(manifold, point);
    
    // Compute a simplified Ricci curvature scalar using manifold invariants
    // This approach calculates an approximation of the scalar curvature
    // by using manifold properties and tangent space information
    const invariants = Object.values(manifold.getInvariant());
    const meanInvariant = invariants.length > 0 
      ? invariants.reduce((sum, val) => sum + (typeof val === 'number' ? val : 0), 0) / invariants.length 
      : 0;
    
    // Calculate a simplified curvature value
    const curvatureScalar = Math.exp(-Math.abs(meanInvariant) / 10);
    
    // Generate placeholder sectional curvatures
    const sectionalCurvatures = [];
    for (let i = 0; i < tangentSpaceInfo.basis.length - 1; i++) {
      for (let j = i+1; j < tangentSpaceInfo.basis.length; j++) {
        sectionalCurvatures.push({
          plane: [i, j],
          value: curvatureScalar * (1 + 0.1 * (i-j))
        });
      }
    }
    
    return {
      point,
      scalarCurvature: curvatureScalar,
      sectionalCurvatures,
      manifold
    };
  },

  /**
   * Project a vector into the tangent space at a point
   * @param {Manifold} manifold - The manifold
   * @param {Array} vector - Vector to project
   * @param {Array} point - Point on the manifold
   * @param {Object} options - Projection options
   * @returns {Object} Projected vector information
   */
  projectToTangentSpace: function(manifold, vector, point = null, options = {}) {
    if (!(manifold instanceof Manifold)) {
      throw new Prime.ValidationError("First argument must be a manifold");
    }

    if (!Array.isArray(vector)) {
      throw new Prime.ValidationError("Vector must be an array");
    }

    // If no point specified, use the current manifold state
    if (point === null) {
      point = Object.values(manifold.getVariant());
    }

    // Calculate tangent space at the point
    const tangentSpace = this.calculateTangentSpace(manifold, point);
    
    // Project the vector onto the tangent space basis
    const projectionCoefficients = [];
    for (const basisVector of tangentSpace.basis) {
      // Calculate the dot product with the basis vector
      let dotProduct = 0;
      for (let i = 0; i < Math.min(vector.length, basisVector.length); i++) {
        dotProduct += vector[i] * basisVector[i];
      }
      projectionCoefficients.push(dotProduct);
    }
    
    // Reconstruct the projected vector as a linear combination of basis vectors
    const projectedVector = Array(point.length).fill(0);
    for (let i = 0; i < projectionCoefficients.length; i++) {
      const basis = tangentSpace.basis[i];
      for (let j = 0; j < projectedVector.length; j++) {
        projectedVector[j] += projectionCoefficients[i] * basis[j];
      }
    }
    
    return {
      originalVector: vector,
      projectedVector,
      coefficients: projectionCoefficients,
      tangentSpace
    };
  },

  /**
   * Check if a vector is tangent to the manifold at a point
   * @param {Manifold} manifold - The manifold 
   * @param {Array} vector - Vector to check
   * @param {Array} point - Point on the manifold
   * @param {Object} options - Check options
   * @returns {Object} Check result
   */
  isTangentVector: function(manifold, vector, point = null, options = {}) {
    if (!(manifold instanceof Manifold)) {
      throw new Prime.ValidationError("First argument must be a manifold");
    }

    if (!Array.isArray(vector)) {
      throw new Prime.ValidationError("Vector must be an array");
    }

    // If no point specified, use the current manifold state
    if (point === null) {
      point = Object.values(manifold.getVariant());
    }

    // Project the vector to the tangent space
    const projection = this.projectToTangentSpace(manifold, vector, point, options);
    
    // Calculate the difference between the original and projected vectors
    const originalNorm = Math.sqrt(vector.reduce((sum, val) => sum + val * val, 0));
    
    // If original norm is zero, consider it tangent
    if (originalNorm < 1e-10) {
      return {
        isTangent: true,
        error: 0,
        originalVector: vector,
        projectedVector: projection.projectedVector
      };
    }
    
    // Calculate the error as the relative difference
    const difference = [];
    for (let i = 0; i < Math.min(vector.length, projection.projectedVector.length); i++) {
      difference.push(vector[i] - projection.projectedVector[i]);
    }
    
    const diffNorm = Math.sqrt(difference.reduce((sum, val) => sum + val * val, 0));
    const relativeError = diffNorm / originalNorm;
    
    // Determine if it's tangent based on a threshold
    const errorThreshold = options.threshold || 1e-6;
    const isTangent = relativeError < errorThreshold;
    
    return {
      isTangent,
      error: relativeError,
      originalVector: vector,
      projectedVector: projection.projectedVector,
      difference
    };
  },

  /**
   * Calculate the metric tensor at a point
   * @param {Manifold} manifold - The manifold
   * @param {Array} point - Point on the manifold
   * @param {Object} options - Metric calculation options
   * @returns {Object} Metric tensor information
   */
  calculateMetricTensor: function(manifold, point = null, options = {}) {
    if (!(manifold instanceof Manifold)) {
      throw new Prime.ValidationError("First argument must be a manifold");
    }

    // If no point specified, use the current manifold state
    if (point === null) {
      point = Object.values(manifold.getVariant());
    }

    // Calculate tangent space at the point
    const tangentSpace = this.calculateTangentSpace(manifold, point);
    const dimension = tangentSpace.basis.length;
    
    // Create the metric tensor (a symmetric matrix)
    // For simplicity, we'll use a simplistic implementation
    // In general, the metric tensor would be calculated based on the
    // manifold's geometry and parametrization
    const metricTensor = [];
    for (let i = 0; i < dimension; i++) {
      metricTensor.push([]);
      for (let j = 0; j < dimension; j++) {
        // Calculate the inner product between basis vectors
        // In Euclidean space, this is just the dot product
        let innerProduct = 0;
        for (let k = 0; k < tangentSpace.basis[i].length; k++) {
          innerProduct += tangentSpace.basis[i][k] * tangentSpace.basis[j][k];
        }
        
        // In a more general setting, this would use the specific
        // inner product of the manifold
        metricTensor[i].push(innerProduct);
      }
    }
    
    return {
      point,
      metricTensor,
      dimension,
      tangentSpace
    };
  }
};

module.exports = TangentSpaceOperations;