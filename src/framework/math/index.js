/**
 * Mathematical utilities for the Prime Framework
 * Enhanced with numerical stability improvements and precision controls
 */

// Import core if available
let Prime;
try {
  Prime = require("../../core.js");
} catch (e) {
  // Handle case where core isn't available yet
  Prime = {};
}

/**
 * Constants for numerical operations
 */
const CONSTANTS = {
  // Base precision value, equivalent to 2^-52 (standard double precision epsilon)
  EPSILON: 2.220446049250313e-16,

  // Slightly larger epsilon for general comparisons to handle accumulated errors
  EPSILON_GENERAL: 1e-10,

  // Specific tolerances for different contexts
  TOLERANCES: {
    vector: 1e-12,
    matrix: 1e-12,
    integration: 1e-10,
    optimization: 1e-8,
    eigenvalue: 1e-14,
  },

  // Maximum iterations for various iterative algorithms
  MAX_ITERATIONS: {
    optimization: 1000,
    integration: 500,
    eigen: 100,
    quadrature: 50,
  },
};

/**
 * Adaptive precision control that scales with magnitude of inputs
 *
 * @param {number} magnitude - Characteristic magnitude of the calculation
 * @param {string} context - Context of the calculation (e.g., 'vector', 'matrix')
 * @returns {number} Appropriate epsilon value scaled to the magnitude
 */
function adaptiveEpsilon(magnitude, context = "general") {
  // Get base tolerance for the context
  const baseTolerance =
    CONSTANTS.TOLERANCES[context] || CONSTANTS.EPSILON_GENERAL;

  // Scale epsilon with magnitude
  if (magnitude === 0) return baseTolerance;

  const absValue = Math.abs(magnitude);
  // For very small values, use a more relaxed tolerance
  if (absValue < 1e-8) {
    return Math.max(baseTolerance, CONSTANTS.EPSILON * absValue * 10);
  }
  // For very large values, scale tolerance to avoid underflow
  if (absValue > 1e8) {
    return Math.max(baseTolerance, CONSTANTS.EPSILON * absValue);
  }

  return baseTolerance;
}

/**
 * Enhanced Kahan summation algorithm with magnitude tracking
 *
 * @param {Array} values - Array of values to sum
 * @returns {Object} Sum and error estimates
 */
function kahanSum(values) {
  if (!Array.isArray(values)) {
    throw new TypeError("Expected an array of values");
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
    precision: Math.log10(
      1 / (CONSTANTS.EPSILON * conditionNumber || CONSTANTS.EPSILON),
    ),
  };
}

/**
 * Vector operations with enhanced numerical stability
 */
const vector = {
  /**
   * Calculate Euclidean distance between vectors with enhanced precision
   *
   * @param {Array} a - First vector
   * @param {Array} b - Second vector
   * @param {Object} options - Calculation options
   * @returns {Object} Distance result with error estimation
   */
  distance: function (a, b, options = {}) {
    // Validate inputs
    if (!Array.isArray(a) || !Array.isArray(b)) {
      throw new TypeError("Vectors must be arrays");
    }

    const maxLength = Math.max(a.length, b.length);
    const sqDiffs = new Array(maxLength);

    // Calculate squared differences
    for (let i = 0; i < maxLength; i++) {
      const aVal = i < a.length ? a[i] : 0;
      const bVal = i < b.length ? b[i] : 0;
      const diff = aVal - bVal;
      sqDiffs[i] = diff * diff;
    }

    // Use Kahan summation for numerical stability
    const sumResult = kahanSum(sqDiffs);

    // Prevent negative value due to floating point errors
    const sum = Math.max(0, sumResult.sum);

    // Apply high-precision square root
    const distance = Math.sqrt(sum);

    // Calculate relative error estimate based on condition number
    const relativeError =
      distance > 0
        ? (CONSTANTS.EPSILON * sumResult.conditionNumber) / (2 * distance)
        : 0;

    return {
      distance,
      relativeError,
      absoluteError: distance * relativeError,
      conditionNumber: sumResult.conditionNumber,
    };
  },

  /**
   * Calculate cosine similarity with enhanced stability and edge case handling
   *
   * @param {Array} a - First vector
   * @param {Array} b - Second vector
   * @param {Object} options - Calculation options
   * @returns {Object} Similarity result with error estimation
   */
  cosineSimilarity: function (a, b, options = {}) {
    // Validate inputs
    if (!Array.isArray(a) || !Array.isArray(b)) {
      throw new TypeError("Vectors must be arrays");
    }

    const maxLength = Math.max(a.length, b.length);
    const dotTerms = new Array(maxLength);
    const aSquareTerms = new Array(maxLength);
    const bSquareTerms = new Array(maxLength);

    // Calculate terms for dot product and norms
    for (let i = 0; i < maxLength; i++) {
      const aVal = i < a.length ? a[i] : 0;
      const bVal = i < b.length ? b[i] : 0;

      dotTerms[i] = aVal * bVal;
      aSquareTerms[i] = aVal * aVal;
      bSquareTerms[i] = bVal * bVal;
    }

    // Use Kahan summation for all three sums
    const dotResult = kahanSum(dotTerms);
    const aNormResult = kahanSum(aSquareTerms);
    const bNormResult = kahanSum(bSquareTerms);

    // Protect against negative values due to floating point errors
    const aNorm = Math.sqrt(Math.max(0, aNormResult.sum));
    const bNorm = Math.sqrt(Math.max(0, bNormResult.sum));
    const dotProduct = dotResult.sum;

    // Calculate adaptive epsilon based on vector magnitudes
    const adaptiveEps = adaptiveEpsilon(Math.max(aNorm, bNorm), "vector");

    // Mathematically principled handling of zero or near-zero vectors
    if (aNorm < adaptiveEps || bNorm < adaptiveEps) {
      // If both vectors are effectively zero
      if (aNorm < adaptiveEps && bNorm < adaptiveEps) {
        return {
          similarity: 1, // By convention, zero vectors are considered parallel
          distance: 0,
          relativeError: 0,
          absoluteError: 0,
          reason: "Both vectors are effectively zero",
        };
      }

      // One vector is zero, the other isn't
      return {
        similarity: 0,
        distance: 1,
        relativeError: 0,
        absoluteError: 0,
        reason: "One vector is effectively zero",
      };
    }

    // Calculate similarity with proper bound checking
    let similarity = dotProduct / (aNorm * bNorm);

    // Ensure value is within valid range [-1, 1]
    // This is mathematically justified because cosine cannot exceed these bounds
    if (similarity > 1) {
      // If very close to 1, it's likely a floating point error
      if (similarity < 1 + adaptiveEps) {
        similarity = 1;
      }
    } else if (similarity < -1) {
      // If very close to -1, it's likely a floating point error
      if (similarity > -1 - adaptiveEps) {
        similarity = -1;
      }
    }

    // Final bound enforcement with explanation
    similarity = Math.max(-1, Math.min(1, similarity));

    // Calculate error estimates
    const dotProductRelError =
      dotProduct !== 0
        ? (CONSTANTS.EPSILON * dotResult.conditionNumber) / Math.abs(dotProduct)
        : 0;
    const normRelError =
      (CONSTANTS.EPSILON *
        Math.max(aNormResult.conditionNumber, bNormResult.conditionNumber)) /
      2;

    // Combined relative error using error propagation formula
    const relativeError = dotProductRelError + 2 * normRelError;
    const absoluteError = Math.abs(similarity) * relativeError;

    return {
      similarity,
      distance: 1 - similarity,
      relativeError,
      absoluteError,
      conditionNumber: Math.max(
        dotResult.conditionNumber,
        aNormResult.conditionNumber,
        bNormResult.conditionNumber,
      ),
    };
  },

  /**
   * Calculate Manhattan distance with enhanced stability
   *
   * @param {Array} a - First vector
   * @param {Array} b - Second vector
   * @returns {Object} Distance result with error estimation
   */
  manhattanDistance: function (a, b) {
    // Validate inputs
    if (!Array.isArray(a) || !Array.isArray(b)) {
      throw new TypeError("Vectors must be arrays");
    }

    const maxLength = Math.max(a.length, b.length);
    const terms = new Array(maxLength);

    // Calculate absolute differences
    for (let i = 0; i < maxLength; i++) {
      const aVal = i < a.length ? a[i] : 0;
      const bVal = i < b.length ? b[i] : 0;
      terms[i] = Math.abs(aVal - bVal);
    }

    // Use Kahan summation for numerical stability
    const sumResult = kahanSum(terms);

    return {
      distance: sumResult.sum,
      relativeError: CONSTANTS.EPSILON * sumResult.conditionNumber,
      absoluteError:
        CONSTANTS.EPSILON * sumResult.conditionNumber * sumResult.sum,
      conditionNumber: sumResult.conditionNumber,
    };
  },

  /**
   * Calculate Chebyshev distance (maximum norm)
   *
   * @param {Array} a - First vector
   * @param {Array} b - Second vector
   * @returns {Object} Distance result
   */
  chebyshevDistance: function (a, b) {
    // Validate inputs
    if (!Array.isArray(a) || !Array.isArray(b)) {
      throw new TypeError("Vectors must be arrays");
    }

    const maxLength = Math.max(a.length, b.length);
    let maxDiff = 0;
    let maxDiffIndex = -1;

    // Find maximum absolute difference
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
      maxDiffIndex,
      relativeError: maxDiff > 0 ? CONSTANTS.EPSILON : 0,
      absoluteError: CONSTANTS.EPSILON * maxDiff,
    };
  },

  /**
   * Normalize a vector with enhanced numerical stability
   *
   * @param {Array} v - Vector to normalize
   * @param {Object} options - Normalization options
   * @returns {Object} Normalized vector and metadata
   */
  normalize: function (v, options = {}) {
    if (!Array.isArray(v)) {
      throw new TypeError("Vector must be an array");
    }

    // Calculate vector norm using Kahan summation for better precision
    const squareTerms = v.map((val) => val * val);
    const sumResult = kahanSum(squareTerms);

    // Protect against negative values due to floating point errors
    const norm = Math.sqrt(Math.max(0, sumResult.sum));

    // Handle zero or near-zero vectors
    const eps = options.epsilon || adaptiveEpsilon(norm, "vector");
    if (norm < eps) {
      return {
        vector: Array(v.length).fill(0),
        norm: 0,
        relativeError: 0,
        isZero: true,
        message: "Vector is effectively zero; returned zero vector",
      };
    }

    // Normalize the vector
    const normalized = v.map((val) => val / norm);

    // Calculate error estimate
    const relativeError =
      CONSTANTS.EPSILON * (1 + sumResult.conditionNumber / 2);

    return {
      vector: normalized,
      norm,
      relativeError,
      absoluteError: relativeError * norm,
      conditionNumber: sumResult.conditionNumber,
    };
  },

  /**
   * Generate an orthogonal basis for a set of vectors
   *
   * @param {Array} vectors - Array of vectors
   * @param {Object} options - Orthogonalization options
   * @returns {Array} Orthogonal basis vectors
   */
  gramSchmidt: function (vectors, options = {}) {
    if (!Array.isArray(vectors) || vectors.length === 0) {
      throw new TypeError("Expected non-empty array of vectors");
    }

    // Extract configuration options
    const reorthogonalize = options.reorthogonalize !== false;
    const normalize = options.normalize !== false;
    const tolerance = options.tolerance || adaptiveEpsilon(0, "vector");

    const n = vectors.length;
    const dim = vectors[0].length;
    const basis = [];

    for (let i = 0; i < n; i++) {
      // Start with the original vector
      let q = vectors[i].slice();

      // Modified Gram-Schmidt process
      for (let j = 0; j < basis.length; j++) {
        // Project q onto basis[j]
        const dotProduct = this.dotProduct(q, basis[j].vector);

        // Subtract the projection
        for (let k = 0; k < dim; k++) {
          q[k] -= dotProduct * basis[j].vector[k];
        }

        // Reorthogonalize for better numerical stability
        if (reorthogonalize) {
          const dotProduct2 = this.dotProduct(q, basis[j].vector);
          for (let k = 0; k < dim; k++) {
            q[k] -= dotProduct2 * basis[j].vector[k];
          }
        }
      }

      // Normalize the resulting vector
      const normResult = this.normalize(q);

      // Check if the resulting vector is non-zero
      if (normResult.norm > tolerance) {
        basis.push(normResult);
      }
    }

    return basis;
  },

  /**
   * Calculate dot product with enhanced numerical stability
   *
   * @param {Array} a - First vector
   * @param {Array} b - Second vector
   * @returns {number} Dot product result
   */
  dotProduct: function (a, b) {
    if (!Array.isArray(a) || !Array.isArray(b)) {
      throw new TypeError("Vectors must be arrays");
    }

    const maxLength = Math.max(a.length, b.length);
    const terms = new Array(maxLength);

    // Calculate terms for dot product
    for (let i = 0; i < maxLength; i++) {
      const aVal = i < a.length ? a[i] : 0;
      const bVal = i < b.length ? b[i] : 0;
      terms[i] = aVal * bVal;
    }

    // Use Kahan summation for numerical stability
    return kahanSum(terms).sum;
  },
};

/**
 * Matrix operations with enhanced numerical stability
 */
const matrix = {
  /**
   * Multiply two matrices with enhanced precision
   *
   * @param {Array} a - First matrix (array of arrays)
   * @param {Array} b - Second matrix (array of arrays)
   * @returns {Object} Result matrix and error metrics
   */
  multiply: function (a, b) {
    // Validate inputs
    if (
      !Array.isArray(a) ||
      !a.every(Array.isArray) ||
      !Array.isArray(b) ||
      !b.every(Array.isArray)
    ) {
      throw new TypeError("Matrices must be arrays of arrays");
    }

    const aRows = a.length;
    const aCols = a[0].length;
    const bRows = b.length;
    const bCols = b[0].length;

    // Check matrix dimensions
    if (aCols !== bRows) {
      throw new Error(
        `Matrix dimensions mismatch: ${aRows}x${aCols} * ${bRows}x${bCols}`,
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
          CONSTANTS.EPSILON *
          sumResult.conditionNumber *
          Math.abs(sumResult.sum);
      }
    }

    return {
      matrix: result,
      maxRelativeError: CONSTANTS.EPSILON * maxConditionNumber,
      elementErrors: maxErrors,
      conditionNumber: maxConditionNumber,
    };
  },

  /**
   * Calculate matrix determinant with numerical stability enhancements
   *
   * @param {Array} matrix - Input matrix
   * @returns {Object} Determinant and error estimation
   */
  determinant: function (matrix) {
    if (!Array.isArray(matrix) || !matrix.every(Array.isArray)) {
      throw new TypeError("Matrix must be an array of arrays");
    }

    const n = matrix.length;

    // Check if matrix is square
    if (!matrix.every((row) => row.length === n)) {
      throw new Error("Matrix must be square");
    }

    // Handle special cases
    if (n === 1) {
      return {
        determinant: matrix[0][0],
        relativeError: CONSTANTS.EPSILON,
        absoluteError: CONSTANTS.EPSILON * Math.abs(matrix[0][0]),
      };
    }

    if (n === 2) {
      const det = matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0];
      return {
        determinant: det,
        relativeError: 2 * CONSTANTS.EPSILON,
        absoluteError: 2 * CONSTANTS.EPSILON * Math.abs(det),
      };
    }

    // For larger matrices, use LU decomposition for better numerical stability
    try {
      const lu = this.luDecomposition(matrix);
      let det = lu.pivot.sign;

      // Determinant is the product of diagonal elements
      let maxLog = 0;
      const logs = new Array(n);

      // Use logarithmic approach to avoid overflow/underflow
      for (let i = 0; i < n; i++) {
        const val = Math.abs(lu.LU[i][i]);
        if (val === 0) {
          return {
            determinant: 0,
            relativeError: 0,
            absoluteError: 0,
            isSingular: true,
          };
        }

        logs[i] = Math.log(val);
        maxLog = Math.max(maxLog, Math.abs(logs[i]));

        // Track sign
        if (lu.LU[i][i] < 0) {
          det = -det;
        }
      }

      // Sum logs to get log(abs(det))
      const logSum = logs.reduce((sum, log) => sum + log, 0);

      // Exponentiate to get abs(det)
      const absDet = Math.exp(logSum);

      // Apply sign
      const result = det * absDet;

      // Estimate error based on condition number and matrix size
      const relativeError = lu.conditionEstimate
        ? n * CONSTANTS.EPSILON * lu.conditionEstimate
        : n * CONSTANTS.EPSILON;

      return {
        determinant: result,
        relativeError,
        absoluteError: relativeError * Math.abs(result),
        conditionEstimate: lu.conditionEstimate,
      };
    } catch (e) {
      // Fallback to simpler but less stable method
      let det = 0;
      let sign = 1;

      // Basic cofactor expansion
      for (let j = 0; j < n; j++) {
        // Create submatrix
        const submatrix = [];
        for (let i = 1; i < n; i++) {
          submatrix.push([]);
          for (let k = 0; k < n; k++) {
            if (k !== j) {
              submatrix[i - 1].push(matrix[i][k]);
            }
          }
        }

        // Recursively compute determinant
        const subDet = this.determinant(submatrix);
        det += sign * matrix[0][j] * subDet.determinant;
        sign = -sign;
      }

      return {
        determinant: det,
        relativeError: n * n * CONSTANTS.EPSILON, // Higher error for naive method
        absoluteError: n * n * CONSTANTS.EPSILON * Math.abs(det),
        method: "cofactor expansion",
        warning:
          "Used less numerically stable method, result may have larger errors",
      };
    }
  },

  /**
   * LU Decomposition with partial pivoting for enhanced numerical stability
   *
   * @param {Array} matrix - Input matrix
   * @returns {Object} LU decomposition and pivot information
   */
  luDecomposition: function (matrix) {
    if (!Array.isArray(matrix) || !matrix.every(Array.isArray)) {
      throw new TypeError("Matrix must be an array of arrays");
    }

    const n = matrix.length;

    // Check if matrix is square
    if (!matrix.every((row) => row.length === n)) {
      throw new Error("Matrix must be square");
    }

    // Create a copy of the matrix
    const LU = matrix.map((row) => [...row]);

    // Create pivot vector and sign tracker
    const pivots = Array(n)
      .fill()
      .map((_, i) => i);
    let pivotSign = 1;

    // Track matrix norms for condition number estimate
    let maxNorm = 0;
    let minPivot = Infinity;

    // Compute row sums for implicit scaling
    const implicitScaling = new Array(n);
    for (let i = 0; i < n; i++) {
      let rowMax = 0;
      for (let j = 0; j < n; j++) {
        rowMax = Math.max(rowMax, Math.abs(LU[i][j]));
      }

      if (rowMax === 0) {
        throw new Error("Matrix is singular");
      }

      implicitScaling[i] = 1.0 / rowMax;
    }

    // Outer loop over columns
    for (let k = 0; k < n; k++) {
      // Find pivot row
      let pivotRow = k;
      let maxScaledElement = 0;

      for (let i = k; i < n; i++) {
        const scaledElement = implicitScaling[i] * Math.abs(LU[i][k]);
        if (scaledElement > maxScaledElement) {
          maxScaledElement = scaledElement;
          pivotRow = i;
        }
      }

      // Swap rows if needed
      if (pivotRow !== k) {
        for (let j = 0; j < n; j++) {
          const temp = LU[pivotRow][j];
          LU[pivotRow][j] = LU[k][j];
          LU[k][j] = temp;
        }

        // Update pivot tracking
        const temp = pivots[pivotRow];
        pivots[pivotRow] = pivots[k];
        pivots[k] = temp;

        // Update implicit scaling
        const tempScale = implicitScaling[pivotRow];
        implicitScaling[pivotRow] = implicitScaling[k];
        implicitScaling[k] = tempScale;

        // Track sign changes for determinant
        pivotSign = -pivotSign;
      }

      // Check for singularity
      const pivot = LU[k][k];
      if (Math.abs(pivot) < CONSTANTS.EPSILON) {
        return {
          LU,
          pivot: { indices: pivots, sign: pivotSign },
          isSingular: true,
          singularityIndex: k,
        };
      }

      // Track condition number components
      maxNorm = Math.max(maxNorm, Math.abs(pivot));
      minPivot = Math.min(minPivot, Math.abs(pivot));

      // Compute multipliers and eliminate below
      for (let i = k + 1; i < n; i++) {
        LU[i][k] /= pivot;

        // Update the remaining submatrix
        for (let j = k + 1; j < n; j++) {
          LU[i][j] -= LU[i][k] * LU[k][j];
        }
      }
    }

    // Estimate condition number based on pivot values
    const conditionEstimate = maxNorm / Math.min(CONSTANTS.EPSILON, minPivot);

    return {
      LU,
      pivot: { indices: pivots, sign: pivotSign },
      conditionEstimate,
      isSingular: false,
    };
  },
};

/**
 * Advanced optimization algorithms with enhanced numerical stability
 */
const optimization = {
  /**
   * Find minimum of a function using gradient descent with adaptive step sizing
   *
   * @param {Function} f - Function to minimize
   * @param {Array} initialPoint - Starting point
   * @param {Object} options - Optimization options
   * @returns {Object} Optimization result
   */
  gradientDescent: function (f, initialPoint, options = {}) {
    if (typeof f !== "function") {
      throw new TypeError("First argument must be a function");
    }

    if (!Array.isArray(initialPoint)) {
      throw new TypeError("Initial point must be an array");
    }

    // Configuration options with defaults
    const maxIterations =
      options.maxIterations || CONSTANTS.MAX_ITERATIONS.optimization;
    const tolerance = options.tolerance || CONSTANTS.TOLERANCES.optimization;
    const learningRate = options.learningRate || 0.01;
    const adaptiveLR = options.adaptiveLearningRate !== false;
    const momentum = options.momentum || 0;

    // Initialize variables
    let x = [...initialPoint];
    let fx = f(x);
    let iter = 0;
    let converged = false;
    let stepSize = learningRate;
    let previousGradient = null;
    let velocity = Array(x.length).fill(0);

    // Track iteration history if requested
    const history = options.trackHistory
      ? [
          {
            iteration: 0,
            x: [...x],
            fx,
            stepSize,
          },
        ]
      : null;

    // Optimization loop
    while (iter < maxIterations && !converged) {
      // Calculate gradient
      const gradient = this._computeGradient(f, x, {
        method: options.gradientMethod || "central",
        epsilon: options.gradientEpsilon,
      });

      // Check for convergence based on gradient norm
      const gradientNorm = vector.normalize(gradient);
      if (gradientNorm.norm < tolerance) {
        converged = true;
        break;
      }

      // Apply momentum if enabled
      if (momentum > 0) {
        for (let i = 0; i < x.length; i++) {
          velocity[i] = momentum * velocity[i] - stepSize * gradient.vector[i];
          x[i] += velocity[i];
        }
      } else {
        // Standard gradient descent step
        for (let i = 0; i < x.length; i++) {
          x[i] -= stepSize * gradient.vector[i];
        }
      }

      // Evaluate function at new point
      const newFx = f(x);

      // Adaptive learning rate
      if (adaptiveLR) {
        if (newFx < fx) {
          // Successful step, increase step size slightly
          stepSize *= 1.1;
          fx = newFx;
        } else {
          // Unsuccessful step, reduce step size and revert
          stepSize *= 0.5;

          // Revert the step
          if (momentum > 0) {
            for (let i = 0; i < x.length; i++) {
              x[i] -= velocity[i];
              velocity[i] = 0; // Reset velocity after backtrack
            }
          } else {
            for (let i = 0; i < x.length; i++) {
              x[i] += stepSize * gradient.vector[i];
            }
          }

          // Recalculate function value
          fx = f(x);
        }
      } else {
        fx = newFx;
      }

      // Track history if requested
      if (history) {
        history.push({
          iteration: iter + 1,
          x: [...x],
          fx,
          stepSize,
          gradientNorm: gradientNorm.norm,
        });
      }

      // Store gradient for next iteration
      previousGradient = gradient;

      // Increment iteration counter
      iter++;
    }

    return {
      minimum: x,
      value: fx,
      iterations: iter,
      converged,
      gradientNorm: this._computeGradient(f, x).norm,
      history,
    };
  },

  /**
   * Compute gradient of a function with enhanced numerical accuracy
   *
   * @param {Function} f - Function to differentiate
   * @param {Array} x - Point at which to compute gradient
   * @param {Object} options - Differentiation options
   * @returns {Object} Gradient vector and metadata
   */
  _computeGradient: function (f, x, options = {}) {
    if (typeof f !== "function") {
      throw new TypeError("First argument must be a function");
    }

    if (!Array.isArray(x)) {
      throw new TypeError("Point must be an array");
    }

    // Configure differentiation method
    const method = options.method || "central";
    const epsilon =
      options.epsilon || adaptiveEpsilon(Math.abs(f(x)), "optimization");

    const n = x.length;
    const gradient = new Array(n);

    // Compute gradient components
    for (let i = 0; i < n; i++) {
      // Create points for numerical differentiation
      const xPlus = [...x];
      const xMinus = [...x];
      const xPlus2 = [...x];
      const xMinus2 = [...x];

      switch (method) {
        case "forward":
          // Forward difference: (f(x+h) - f(x)) / h
          xPlus[i] += epsilon;
          gradient[i] = (f(xPlus) - f(x)) / epsilon;
          break;

        case "central":
          // Central difference: (f(x+h) - f(x-h)) / (2h)
          xPlus[i] += epsilon;
          xMinus[i] -= epsilon;
          gradient[i] = (f(xPlus) - f(xMinus)) / (2 * epsilon);
          break;

        case "high-order":
          // 5-point stencil for higher accuracy:
          // (-f(x+2h) + 8f(x+h) - 8f(x-h) + f(x-2h)) / (12h)
          xPlus[i] += epsilon;
          xMinus[i] -= epsilon;
          xPlus2[i] += 2 * epsilon;
          xMinus2[i] -= 2 * epsilon;

          gradient[i] =
            (-f(xPlus2) + 8 * f(xPlus) - 8 * f(xMinus) + f(xMinus2)) /
            (12 * epsilon);
          break;

        case "adaptive":
          // Richardson extrapolation with adaptive step sizes
          const h1 = epsilon;
          const h2 = 0.5 * epsilon;

          // Compute central differences at two step sizes
          xPlus[i] += h1;
          xMinus[i] -= h1;
          const deriv1 = (f(xPlus) - f(xMinus)) / (2 * h1);

          // Reset and compute with smaller step
          xPlus[i] = x[i] + h2;
          xMinus[i] = x[i] - h2;
          const deriv2 = (f(xPlus) - f(xMinus)) / (2 * h2);

          // Richardson extrapolation to improve accuracy
          // For central differences, error is O(h²), so extrapolation formula is:
          // (4*deriv2 - deriv1) / 3
          gradient[i] = (4 * deriv2 - deriv1) / 3;
          break;

        default:
          throw new Error(`Unknown differentiation method: ${method}`);
      }
    }

    // Calculate gradient norm and return enhanced result
    return vector.normalize(gradient);
  },

  /**
   * Enhanced simulated annealing with adaptive temperature and constraints
   *
   * @param {Function} f - Function to minimize
   * @param {Array} initialPoint - Starting point
   * @param {Object} options - Annealing options
   * @returns {Object} Optimization result
   */
  simulatedAnnealing: function (f, initialPoint, options = {}) {
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
    const constraints = options.constraints || [];
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

    // Helper function to check constraints
    const satisfiesConstraints = (point) => {
      for (const constraint of constraints) {
        if (typeof constraint === "function" && !constraint(point)) {
          return false;
        }
      }
      return true;
    };

    // Generate a move with adaptive sizes
    const generateMove = () => {
      const newX = [...x];

      for (let i = 0; i < x.length; i++) {
        // Generate random move with current move size
        const delta = (Math.random() * 2 - 1) * moveSizes[i];
        newX[i] += delta;
      }

      // Apply constraints if any
      if (constraints.length > 0 && !satisfiesConstraints(newX)) {
        // If move violates constraints, try projection
        this._projectToFeasible(newX, constraints, x);
      }

      return newX;
    };

    // Main annealing loop
    while (iter < maxIterations && temp > finalTemp) {
      // Generate new solution
      const newX = generateMove();
      const newFx = f(newX);

      // Decide whether to accept the new solution
      let accept = false;
      let improvement = false;

      if (newFx <= fx) {
        // Always accept better solutions
        accept = true;

        // Check if this is the best solution found so far
        if (newFx < bestFx) {
          bestX = [...newX];
          bestFx = newFx;
          improvement = true;
          iterSinceImprovement = 0;
        }
      } else {
        // Accept worse solutions with some probability
        const delta = newFx - fx;
        const acceptanceProbability = Math.exp(-delta / temp);

        if (Math.random() < acceptanceProbability) {
          accept = true;
        }
      }

      // Update current solution if move was accepted
      if (accept) {
        x = [...newX];
        fx = newFx;

        // Adapt move sizes if enabled
        if (adaptiveMove && improvement) {
          // Increase move size in dimensions that led to improvement
          for (let i = 0; i < x.length; i++) {
            if (Math.abs(x[i] - bestX[i]) > 0.1 * moveSizes[i]) {
              moveSizes[i] *= 1.1;
            }
          }
        }
      } else {
        // Reduce move sizes in dimensions that frequently fail
        if (adaptiveMove) {
          for (let i = 0; i < x.length; i++) {
            moveSizes[i] *= 0.98;
          }
        }
      }

      // Track history if requested
      if (history) {
        history.push({
          iteration: iter + 1,
          x: accept ? [...x] : [...x], // Current position
          fx: accept ? fx : fx,
          bestX: [...bestX],
          bestFx,
          temperature: temp,
          accepted: accept,
          improvement,
        });
      }

      // Update temperature according to cooling schedule
      temp *= coolingRate;

      // Implement reheating if enabled and stuck
      iterSinceImprovement++;
      if (reheating && iterSinceImprovement > maxIterations / 10) {
        temp = Math.min(initialTemp * 0.5, temp * 5);
        iterSinceImprovement = 0;

        // Also reset move sizes
        moveSizes = Array(x.length).fill(moveSize);
      }

      iter++;
    }

    return {
      minimum: bestX,
      value: bestFx,
      iterations: iter,
      temperature: temp,
      history,
    };
  },

  /**
   * Project a point to the feasible region defined by constraints
   *
   * @param {Array} point - Point to project
   * @param {Array} constraints - Constraint functions
   * @param {Array} fallback - Fallback point if projection fails
   * @returns {boolean} Projection success
   */
  _projectToFeasible: function (point, constraints, fallback) {
    // Simple projection method:
    // For each violated constraint, move along constraint gradient
    let feasible = false;
    let attempts = 0;
    const maxAttempts = 10;

    // Helper function to check constraints
    const satisfiesConstraints = (pt) => {
      for (const constraint of constraints) {
        if (typeof constraint === "function" && !constraint(pt)) {
          return false;
        }
      }
      return true;
    };

    // Already feasible
    if (satisfiesConstraints(point)) {
      return true;
    }

    while (!feasible && attempts < maxAttempts) {
      let projected = true;

      for (const constraint of constraints) {
        if (typeof constraint === "function" && !constraint(point)) {
          // If constraint provides a projection method, use it
          if (typeof constraint.project === "function") {
            constraint.project(point);
          } else if (typeof constraint.gradient === "function") {
            // If gradient is available, move along gradient
            const gradient = constraint.gradient(point);
            const stepSize = 0.1 / (attempts + 1);

            for (let i = 0; i < point.length; i++) {
              point[i] += stepSize * gradient[i];
            }
          } else {
            // Without projection or gradient, use random perturbation
            for (let i = 0; i < point.length; i++) {
              point[i] = 0.8 * point[i] + 0.2 * fallback[i];
            }
          }

          projected = false;
          break;
        }
      }

      // Check if we've reached feasibility
      feasible = satisfiesConstraints(point);

      // If not projected, we're still feasible
      if (projected) {
        break;
      }

      attempts++;
    }

    // If failed, reset to fallback point
    if (!feasible) {
      for (let i = 0; i < point.length; i++) {
        point[i] = fallback[i];
      }
      return false;
    }

    return true;
  },
};

/**
 * Numerical integration with enhanced mathematical precision
 */
const integration = {
  /**
   * Adaptive numerical integration using Gauss-Kronrod quadrature
   *
   * @param {Function} f - Function to integrate
   * @param {number} a - Lower bound
   * @param {number} b - Upper bound
   * @param {Object} options - Integration options
   * @returns {Object} Integration result and error estimation
   */
  adaptiveQuadrature: function (f, a, b, options = {}) {
    if (typeof f !== "function") {
      throw new TypeError("First argument must be a function");
    }

    if (typeof a !== "number" || typeof b !== "number") {
      throw new TypeError("Integration bounds must be numbers");
    }

    // Configure integration options
    const tolerance = options.tolerance || CONSTANTS.TOLERANCES.integration;
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
      -0.7415311855993944, 0.9491079123427585, -0.9491079123427585, 0, 0, 0, 0,
      0, 0, 0, 0,
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

    // Split into initial intervals if requested
    if (initialIntervals > 1) {
      const intervalSize = (b - a) / initialIntervals;
      for (let i = 0; i < initialIntervals; i++) {
        const intervalStart = a + i * intervalSize;
        const intervalEnd = intervalStart + intervalSize;

        const intervalResult = adaptiveIntegrate(intervalStart, intervalEnd, 0);

        result += intervalResult.integral;
        error += intervalResult.error;
      }
    } else {
      // Direct integration of entire interval
      const fullResult = adaptiveIntegrate(a, b, 0);
      result = fullResult.integral;
      error = fullResult.error;
    }

    return {
      integral: result,
      error,
      relativeError:
        Math.abs(result) > 1e-10 ? error / Math.abs(result) : error,
      evaluations,
    };
  },
};

// Import additional math modules if available
let patternRecognition;
try {
  patternRecognition = require('./patternRecognition.js');
} catch (e) {
  patternRecognition = {};
}

let spectral;
try {
  spectral = require('./spectral.js');
} catch (e) {
  spectral = {};
}

let coherence;
try {
  coherence = require('./coherence.js');
} catch (e) {
  coherence = {};
}

// Import linear algebra module
let linalg;
try {
  linalg = require('./linalg.js');
} catch (e) {
  linalg = {};
}

// Import Prime.math module
let primeMath;
try {
  primeMath = require('./prime-math.js');
} catch (e) {
  primeMath = {};
}

// Export the math utilities
module.exports = {
  CONSTANTS,
  adaptiveEpsilon,
  kahanSum,
  vector,
  matrix,
  optimization,
  integration,
  patternRecognition,
  spectral,
  coherence,
  linalg,
  primeMath
};
