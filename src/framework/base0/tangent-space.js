/**
 * PrimeOS JavaScript Library - Framework
 * Base 0: Tangent Space
 * Operations related to tangent space calculations
 */

// Import core
const Prime = require("../../core/prime.js");
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
  calculateTangentSpace: function (manifold, point = null, options = {}) {
    if (!(manifold instanceof Manifold)) {
      throw new Prime.ValidationError("First argument must be a manifold");
    }

    // If no point specified, use the current manifold state
    if (point === null) {
      point = Object.values(manifold.getVariant());
    }

    const dimension = point.length;
    const basisVectors = [];

    // Generate proper basis vectors for the tangent space that respect
    // the manifold's geometry at the given point

    // First, determine the manifold type and its geometric properties
    const manifoldType = manifold.getType();
    let manifoldGeometry = "euclidean"; // Default assumption

    // Extract additional geometric information from manifold metadata if available
    if (manifold.getMeta() && manifold.getMeta().geometry) {
      manifoldGeometry = manifold.getMeta().geometry;
    } else if (
      manifoldType.includes("sphere") ||
      manifoldType.includes("ellipsoid")
    ) {
      manifoldGeometry = "spherical";
    } else if (
      manifoldType.includes("hyper") ||
      manifoldType.includes("saddle")
    ) {
      manifoldGeometry = "hyperbolic";
    } else if (manifoldType.includes("torus")) {
      manifoldGeometry = "toroidal";
    }

    // For non-Euclidean manifolds, we need to account for the geometry
    // when creating tangent basis vectors
    if (manifoldGeometry === "spherical") {
      // For spherical geometry, tangent vectors must be perpendicular to the position vector

      // First, create an uncorrected set of basis vectors
      const uncorrectedBasis = [];
      for (let i = 0; i < dimension; i++) {
        const basisVector = Array(dimension).fill(0);
        basisVector[i] = 1;
        uncorrectedBasis.push(basisVector);
      }

      // Calculate the position vector norm (distance from origin)
      const pointNorm =
        Math.sqrt(point.reduce((sum, val) => sum + val * val, 0)) || 1;

      // Normalize the position vector
      const normalizedPoint = point.map((val) => val / pointNorm);

      // Project each basis vector to be tangent to the sphere at this point
      for (let i = 0; i < uncorrectedBasis.length; i++) {
        const basisVector = uncorrectedBasis[i];

        // Calculate dot product with the position
        const dotWithPosition = basisVector.reduce(
          (sum, val, idx) => sum + val * normalizedPoint[idx],
          0,
        );

        // Subtract the radial component to get a tangent vector
        const tangentVector = basisVector.map(
          (val, idx) => val - dotWithPosition * normalizedPoint[idx],
        );

        // Normalize the tangent vector
        const tangentNorm =
          Math.sqrt(tangentVector.reduce((sum, val) => sum + val * val, 0)) ||
          1;

        basisVectors.push(tangentVector.map((val) => val / tangentNorm));
      }

      // Remove any linearly dependent vectors
      // (this can happen if a basis vector was parallel to the position)
      const finalBasisVectors = [];
      for (let i = 0; i < basisVectors.length; i++) {
        // Check if this vector is linearly independent from previous ones
        let isIndependent = true;
        const currentVector = basisVectors[i];

        // Skip vectors that are essentially zero
        const vectorNorm = Math.sqrt(
          currentVector.reduce((sum, val) => sum + val * val, 0),
        );
        if (vectorNorm < 1e-10) {
          isIndependent = false;
        } else {
          // Check against previous vectors
          for (let j = 0; j < finalBasisVectors.length && isIndependent; j++) {
            const prevVector = finalBasisVectors[j];

            // Calculate normalized dot product
            const dotProduct = currentVector.reduce(
              (sum, val, idx) => sum + val * prevVector[idx],
              0,
            );

            // If vectors are nearly parallel, they are not independent
            if (Math.abs(dotProduct) > 1 - 1e-10) {
              isIndependent = false;
            }
          }
        }

        if (isIndependent) {
          finalBasisVectors.push(currentVector);
        }
      }

      // Replace original array with the properly constructed basis
      basisVectors = finalBasisVectors;

      // If we don't have enough basis vectors, generate additional ones
      while (basisVectors.length < dimension - 1) {
        // Sphere tangent space is dimension-1
        // Create a random vector
        const randomVector = Array(dimension)
          .fill(0)
          .map(() => Math.random() * 2 - 1);

        // Project to be tangent to sphere and normalize
        const dotWithPosition = randomVector.reduce(
          (sum, val, idx) => sum + val * normalizedPoint[idx],
          0,
        );

        const tangentVector = randomVector.map(
          (val, idx) => val - dotWithPosition * normalizedPoint[idx],
        );

        const tangentNorm =
          Math.sqrt(tangentVector.reduce((sum, val) => sum + val * val, 0)) ||
          1;

        const normalizedTangent = tangentVector.map((val) => val / tangentNorm);

        // Check if this vector is linearly independent from existing ones
        let isIndependent = true;
        for (let j = 0; j < basisVectors.length && isIndependent; j++) {
          const existingVector = basisVectors[j];
          const dotProduct = normalizedTangent.reduce(
            (sum, val, idx) => sum + val * existingVector[idx],
            0,
          );

          if (Math.abs(dotProduct) > 0.9) {
            isIndependent = false;
          }
        }

        if (isIndependent) {
          basisVectors.push(normalizedTangent);
        }
      }
    } else if (manifoldGeometry === "hyperbolic") {
      // For hyperbolic geometry, similar to spherical but with different metric

      // First create standard basis vectors
      for (let i = 0; i < dimension; i++) {
        const basisVector = Array(dimension).fill(0);
        basisVector[i] = 1;

        // For hyperbolic space, the time component (usually first component)
        // needs special treatment
        if (i === 0) {
          // First vector is timelike in hyperbolic space
          basisVector[i] = 1;
        }

        basisVectors.push(basisVector);
      }

      // Apply Gram-Schmidt orthogonalization with hyperbolic metric
      const orthogonalBasis = [];
      for (let i = 0; i < basisVectors.length; i++) {
        const newVector = [...basisVectors[i]];

        // Subtract projections onto previous vectors
        for (let j = 0; j < orthogonalBasis.length; j++) {
          const prevVector = orthogonalBasis[j];

          // Hyperbolic inner product: special treatment for time component
          let innerProduct = -newVector[0] * prevVector[0];
          for (let k = 1; k < dimension; k++) {
            innerProduct += newVector[k] * prevVector[k];
          }

          // Hyperbolic norm squared of previous vector
          let prevNormSquared = -prevVector[0] * prevVector[0];
          for (let k = 1; k < dimension; k++) {
            prevNormSquared += prevVector[k] * prevVector[k];
          }

          // Skip if degenerate
          if (Math.abs(prevNormSquared) < 1e-10) {
            continue;
          }

          // Subtract projection
          const projectionFactor = innerProduct / prevNormSquared;
          for (let k = 0; k < dimension; k++) {
            newVector[k] -= projectionFactor * prevVector[k];
          }
        }

        // Compute norm of new vector
        let newNormSquared = -newVector[0] * newVector[0];
        for (let k = 1; k < dimension; k++) {
          newNormSquared += newVector[k] * newVector[k];
        }

        // Skip if degenerate
        if (Math.abs(newNormSquared) < 1e-10) {
          continue;
        }

        // Normalize the vector
        const newNorm = Math.sqrt(Math.abs(newNormSquared));
        const normalizedVector = newVector.map((val) => val / newNorm);

        orthogonalBasis.push(normalizedVector);
      }

      // Replace with orthogonalized basis
      basisVectors = orthogonalBasis;
    } else if (manifoldGeometry === "toroidal") {
      // For toroidal geometry, the basis depends on the parameterization
      // In a standard parameterization, each pair of coordinates represents a circle

      // Generate standard basis vectors first
      for (let i = 0; i < dimension; i++) {
        const basisVector = Array(dimension).fill(0);
        basisVector[i] = 1;
        basisVectors.push(basisVector);
      }

      // For a torus, we can use the standard basis vectors
      // but we need to normalize them according to the local metric
      // which depends on the radius of each circle

      if (
        manifold.getMeta() &&
        manifold.getMeta().radii &&
        Array.isArray(manifold.getMeta().radii)
      ) {
        // If we have explicit radii information, use it
        const radii = manifold.getMeta().radii;

        for (let i = 0; i < Math.min(dimension, radii.length); i++) {
          // Scale basis vector by the circle radius
          if (radii[i] > 0) {
            basisVectors[i] = basisVectors[i].map((val) => val / radii[i]);
          }
        }
      }
    } else {
      // For Euclidean and other geometries, use standard basis vectors
      for (let i = 0; i < dimension; i++) {
        const basisVector = Array(dimension).fill(0);
        basisVector[i] = 1;
        basisVectors.push(basisVector);
      }
    }

    // For curved manifolds, we should apply a projection to ensure
    // the basis vectors are truly tangent to the manifold
    const projectedBasis = basisVectors.map((vector) => {
      // This is a simplified implementation - in reality this would use
      // the manifold's structure to project to the tangent space
      return MathUtils.vector.normalizeSimple(vector);
    });

    return {
      point,
      basis: projectedBasis,
      dimension: projectedBasis.length,
      manifold,
    };
  },

  /**
   * Calculate the curvature at a point on a manifold
   * @param {Manifold} manifold - The manifold
   * @param {Object} point - Point to calculate curvature at
   * @param {Object} options - Options for curvature calculation
   * @returns {Object} Curvature information
   */
  calculateCurvature: function (manifold, point = null, options = {}) {
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
    const meanInvariant =
      invariants.length > 0
        ? invariants.reduce(
            (sum, val) => sum + (typeof val === "number" ? val : 0),
            0,
          ) / invariants.length
        : 0;

    // Calculate a simplified curvature value
    const curvatureScalar = Math.exp(-Math.abs(meanInvariant) / 10);

    // Generate placeholder sectional curvatures
    const sectionalCurvatures = [];
    for (let i = 0; i < tangentSpaceInfo.basis.length - 1; i++) {
      for (let j = i + 1; j < tangentSpaceInfo.basis.length; j++) {
        sectionalCurvatures.push({
          plane: [i, j],
          value: curvatureScalar * (1 + 0.1 * (i - j)),
        });
      }
    }

    return {
      point,
      scalarCurvature: curvatureScalar,
      sectionalCurvatures,
      manifold,
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
  projectToTangentSpace: function (
    manifold,
    vector,
    point = null,
    options = {},
  ) {
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
      tangentSpace,
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
  isTangentVector: function (manifold, vector, point = null, options = {}) {
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
    const projection = this.projectToTangentSpace(
      manifold,
      vector,
      point,
      options,
    );

    // Calculate the difference between the original and projected vectors
    const originalNorm = Math.sqrt(
      vector.reduce((sum, val) => sum + val * val, 0),
    );

    // If original norm is zero, consider it tangent
    if (originalNorm < 1e-10) {
      return {
        isTangent: true,
        error: 0,
        originalVector: vector,
        projectedVector: projection.projectedVector,
      };
    }

    // Calculate the error as the relative difference
    const difference = [];
    for (
      let i = 0;
      i < Math.min(vector.length, projection.projectedVector.length);
      i++
    ) {
      difference.push(vector[i] - projection.projectedVector[i]);
    }

    const diffNorm = Math.sqrt(
      difference.reduce((sum, val) => sum + val * val, 0),
    );
    const relativeError = diffNorm / originalNorm;

    // Determine if it's tangent based on a threshold
    const errorThreshold = options.threshold || 1e-6;
    const isTangent = relativeError < errorThreshold;

    return {
      isTangent,
      error: relativeError,
      originalVector: vector,
      projectedVector: projection.projectedVector,
      difference,
    };
  },

  /**
   * Calculate the metric tensor at a point
   * @param {Manifold} manifold - The manifold
   * @param {Array} point - Point on the manifold
   * @param {Object} options - Metric calculation options
   * @returns {Object} Metric tensor information
   */
  calculateMetricTensor: function (manifold, point = null, options = {}) {
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
    // Calculate based on the manifold's geometry and parameterization

    // First, determine the manifold type and its geometric properties
    const manifoldType = manifold.getType();
    let manifoldGeometry = "euclidean"; // Default assumption

    // Extract geometric information from manifold metadata
    if (manifold.getMeta() && manifold.getMeta().geometry) {
      manifoldGeometry = manifold.getMeta().geometry;
    } else if (
      manifoldType.includes("sphere") ||
      manifoldType.includes("ellipsoid")
    ) {
      manifoldGeometry = "spherical";
    } else if (
      manifoldType.includes("hyper") ||
      manifoldType.includes("saddle")
    ) {
      manifoldGeometry = "hyperbolic";
    } else if (manifoldType.includes("torus")) {
      manifoldGeometry = "toroidal";
    }

    const metricTensor = [];

    // Calculate the appropriate metric tensor based on geometry
    if (manifoldGeometry === "spherical") {
      // For spherical geometry, the metric is induced from the embedding space
      // Get the radius if available, otherwise use the point norm
      let radius = 1.0;
      if (manifold.getMeta() && manifold.getMeta().radius) {
        radius = manifold.getMeta().radius;
      } else {
        // Estimate radius from the point
        radius =
          Math.sqrt(point.reduce((sum, val) => sum + val * val, 0)) || 1.0;
      }

      // Initialize metric tensor
      for (let i = 0; i < dimension; i++) {
        metricTensor.push([]);
        for (let j = 0; j < dimension; j++) {
          // Base inner product between basis vectors
          let innerProduct = 0;
          for (let k = 0; k < tangentSpace.basis[i].length; k++) {
            innerProduct += tangentSpace.basis[i][k] * tangentSpace.basis[j][k];
          }

          // Scale by the square of the radius for spherical geometry
          metricTensor[i].push(radius * radius * innerProduct);
        }
      }
    } else if (manifoldGeometry === "hyperbolic") {
      // For hyperbolic geometry, the metric has a Minkowski signature (-,+,+,+,...)

      // Initialize metric tensor with Minkowski metric
      for (let i = 0; i < dimension; i++) {
        metricTensor.push([]);
        for (let j = 0; j < dimension; j++) {
          if (i === j) {
            // Diagonal elements have specific signs
            if (i === 0) {
              // Time dimension has negative sign
              metricTensor[i].push(-1);
            } else {
              // Space dimensions have positive sign
              metricTensor[i].push(1);
            }
          } else {
            // Off-diagonal elements are zero
            metricTensor[i].push(0);
          }
        }
      }

      // Get the hyperbolic radius if available
      let radius = 1.0;
      if (manifold.getMeta() && manifold.getMeta().radius) {
        radius = manifold.getMeta().radius;
      }

      // Scale by the square of the radius
      for (let i = 0; i < dimension; i++) {
        for (let j = 0; j < dimension; j++) {
          metricTensor[i][j] *= radius * radius;
        }
      }
    } else if (manifoldGeometry === "toroidal") {
      // For toroidal geometry, the metric depends on the circles' radii

      // Get radii if available
      let majorRadius = 1.0;
      let minorRadius = 0.25;
      if (manifold.getMeta() && manifold.getMeta().majorRadius) {
        majorRadius = manifold.getMeta().majorRadius;
      }
      if (manifold.getMeta() && manifold.getMeta().minorRadius) {
        minorRadius = manifold.getMeta().minorRadius;
      }

      // Angular coordinates for the torus (from the point or given directly)
      let theta = 0,
        phi = 0;
      if (manifold.getMeta() && manifold.getMeta().coordinates) {
        theta = manifold.getMeta().coordinates.theta || 0;
        phi = manifold.getMeta().coordinates.phi || 0;
      } else if (point.length >= 2) {
        // Estimate angular coordinates from the point (simplified)
        theta = Math.atan2(point[1], point[0]) || 0;
        phi = point.length >= 4 ? Math.atan2(point[3], point[2]) : 0;
      }

      // Initialize metric tensor for the standard parameterization of a torus
      for (let i = 0; i < dimension; i++) {
        metricTensor.push([]);
        for (let j = 0; j < dimension; j++) {
          // Default to zero for off-diagonal elements
          let metricValue = 0;

          // For a torus, diagonal elements depend on position
          if (i === j) {
            if (i === 0) {
              // First coordinate is around major circumference
              metricValue = majorRadius * majorRadius;
            } else if (i === 1) {
              // Second coordinate is around minor circumference
              metricValue = minorRadius * minorRadius;
            } else if (i >= 2 && i < dimension) {
              // For higher dimensions, use appropriate scaling
              metricValue = 1.0;
            }
          }

          metricTensor[i].push(metricValue);
        }
      }
    } else if (manifoldGeometry === "product") {
      // For product manifolds, the metric is a block diagonal matrix
      // of the metrics of the factor manifolds

      // Get the factor dimensions if available
      let factorDimensions = [];
      if (
        manifold.getMeta() &&
        manifold.getMeta().factorDimensions &&
        Array.isArray(manifold.getMeta().factorDimensions)
      ) {
        factorDimensions = manifold.getMeta().factorDimensions;
      } else {
        // Default assumption: all factors have equal dimension
        const numFactors = manifold.getMeta()?.numFactors || 2;
        const factorDim = Math.floor(dimension / numFactors);
        for (let i = 0; i < numFactors; i++) {
          factorDimensions.push(factorDim);
        }
      }

      // Initialize metric tensor with zeros
      for (let i = 0; i < dimension; i++) {
        metricTensor.push(Array(dimension).fill(0));
      }

      // Fill in diagonal blocks for each factor
      let startIndex = 0;
      for (const factorDim of factorDimensions) {
        // Each factor contributes a diagonal block to the metric
        for (let i = 0; i < factorDim; i++) {
          for (let j = 0; j < factorDim; j++) {
            if (i === j) {
              // Diagonal elements are 1 (assuming Euclidean factors)
              metricTensor[startIndex + i][startIndex + j] = 1;
            }
          }
        }
        startIndex += factorDim;
      }
    } else {
      // For Euclidean and other generic geometries, use standard inner product
      for (let i = 0; i < dimension; i++) {
        metricTensor.push([]);
        for (let j = 0; j < dimension; j++) {
          // Calculate the inner product between basis vectors
          let innerProduct = 0;
          for (let k = 0; k < tangentSpace.basis[i].length; k++) {
            innerProduct += tangentSpace.basis[i][k] * tangentSpace.basis[j][k];
          }

          metricTensor[i].push(innerProduct);
        }
      }
    }

    return {
      point,
      metricTensor,
      dimension,
      tangentSpace,
    };
  },
};

module.exports = TangentSpaceOperations;
