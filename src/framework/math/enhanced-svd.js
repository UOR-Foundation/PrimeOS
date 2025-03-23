/**
 * PrimeOS Enhanced SVD Implementation
 * Provides a robust Singular Value Decomposition algorithm optimized for numerical
 * stability with extreme values (very large >1e100 or very small <1e-100)
 */

// Import Prime directly from core/prime
const Prime = require("../../core/prime.js");

// Import specialized error classes directly from core/error.js
const CoreErrors = require("../../core/error.js");

/**
 * Computes the Singular Value Decomposition (SVD) of a matrix using a hybrid algorithm
 * that adapts to different matrix characteristics for optimal numerical stability.
 *
 * @param {Array<Array<number>>} matrix - Input matrix
 * @param {Object} [options={}] - Algorithm options
 * @param {string} [options.algorithm='auto'] - Algorithm to use ('jacobi', 'qr', 'powerIteration', 'auto')
 * @param {boolean} [options.useScaling=true] - Whether to use matrix scaling for extreme values
 * @param {number} [options.maxIterations=150] - Maximum number of iterations
 * @param {number} [options.tolerance=1e-14] - Convergence tolerance
 * @param {boolean} [options.thin=false] - Whether to compute thin SVD
 * @returns {Object} - Object containing U, S, and V matrices
 */
function computeSVD(matrix, options = {}) {
  // Default options
  const algorithm = options.algorithm || "auto";
  const useScaling = options.useScaling !== false;
  const maxIterations = options.maxIterations || 150;
  const tolerance = options.tolerance || 1e-14;
  const thin = options.thin || false;

  // Simple matrix validation function
  function isValidMatrix(m) {
    if (!Array.isArray(m) || m.length === 0) return false;
    if (!Array.isArray(m[0])) return false;

    const cols = m[0].length;
    if (cols === 0) return false;

    // Check all rows have same length
    for (let i = 1; i < m.length; i++) {
      if (!Array.isArray(m[i]) || m[i].length !== cols) return false;
    }

    return true;
  }

  // Check for NaN or Infinity values
  function hasInvalidValues(m) {
    for (let i = 0; i < m.length; i++) {
      for (let j = 0; j < m[i].length; j++) {
        if (!Number.isFinite(m[i][j])) return true;
      }
    }
    return false;
  }

  // Validate input matrix
  if (!isValidMatrix(matrix)) {
    throw new CoreErrors.Errors.ValidationError("Input must be a valid matrix");
  }

  // Check for NaN/Infinity
  if (hasInvalidValues(matrix)) {
    throw new CoreErrors.Errors.ValidationError(
      "Matrix contains invalid values (NaN or Infinity)",
    );
  }

  // Get matrix dimensions
  const rows = matrix.length;
  const cols = matrix[0].length;
  const dimensions = { rows, cols };

  // Check matrix dimensions
  if (rows === 0 || cols === 0) {
    throw new Prime.ValidationError("Matrix dimensions must be non-zero");
  }

  // Special case for 1x1 matrix
  if (rows === 1 && cols === 1) {
    const value = matrix[0][0];
    const absValue = Math.abs(value);
    const sign = value >= 0 ? 1 : -1;

    // Create result matrices
    const U = [[sign]];
    const S = [[absValue]];
    const V = [[1]];

    return { U, S, V, dimensions };
  }

  // Special case for matrices with extremely small values
  const isExtremelySmall = analyzeIfExtremelySmall(matrix);
  if (isExtremelySmall) {
    console.log(
      "Matrix contains extremely small values, using specialized handling",
    );
    return handleExtremelySmallMatrix(matrix);
  }

  // Analyze matrix for extreme values and condition number
  const { maxAbs, minNonZero, dynamicRange, needsScaling, scaleFactor } =
    analyzeMatrix(matrix, useScaling);

  // Check for invalid condition based on analysis
  if (maxAbs === 0) {
    throw new CoreErrors.Errors.MatrixSingularityError(
      "Zero matrix has no valid SVD decomposition",
    );
  }

  if (minNonZero > 0 && dynamicRange > 1e308) {
    throw new CoreErrors.Errors.NumericalInstabilityError(
      `Matrix condition number exceeds representable range (${dynamicRange.toExponential(2)})`,
      { operation: "SVD", dynamicRange, maxAbs, minNonZero },
    );
  }

  // Apply scaling if needed
  let workingMatrix = matrix;
  if (needsScaling) {
    console.log(
      `Scaling matrix for SVD with factor ${scaleFactor.toExponential(2)}`,
    );
    workingMatrix = applyScaling(matrix, scaleFactor);
  }

  // Store algorithm metadata for result
  let algorithmUsed;

  // Choose algorithm based on matrix characteristics
  let selectedAlgorithm = algorithm;
  if (algorithm === "auto") {
    selectedAlgorithm = chooseAlgorithm(dimensions, dynamicRange);
  }

  // Compute SVD using selected algorithm
  let result;
  try {
    algorithmUsed = selectedAlgorithm;
    switch (selectedAlgorithm) {
      case "jacobi":
        result = jacobiSVD(workingMatrix, { maxIterations, tolerance });
        break;
      case "qr":
        result = qrSVD(workingMatrix, { maxIterations, tolerance });
        break;
      case "powerIteration":
        result = powerIterationSVD(workingMatrix, { maxIterations, tolerance });
        break;
      default:
        throw new CoreErrors.Errors.ValidationError(
          `Unknown SVD algorithm: ${selectedAlgorithm}`,
        );
    }
  } catch (error) {
    // If the primary algorithm fails, try fallback methods
    console.error(
      `SVD ${selectedAlgorithm} algorithm failed: ${error.message}. Trying fallbacks.`,
    );

    try {
      algorithmUsed = "jacobi-fallback";
      result = jacobiSVD(workingMatrix, {
        maxIterations: maxIterations * 2,
        tolerance: tolerance * 10,
      });
    } catch (fallbackError) {
      try {
        algorithmUsed = "powerIteration-fallback";
        result = powerIterationSVD(workingMatrix, {
          maxIterations: maxIterations * 2,
          tolerance: tolerance * 10,
        });
      } catch (lastFallbackError) {
        // Last resort: create identity-based approximation
        console.error(`All SVD algorithms failed. Creating minimal result.`);
        algorithmUsed = "emergency-fallback";

        // Create detailed error context for diagnostics
        const errorContext = {
          operation: "SVD",
          algorithm: selectedAlgorithm,
          attemptedFallbacks: ["jacobi", "powerIteration"],
          dimensions: dimensions,
          dynamicRange: dynamicRange,
          maxAbsValue: maxAbs,
          minNonZeroValue: minNonZero === Infinity ? 0 : minNonZero,
          needsScaling: needsScaling,
          scaleFactor: scaleFactor,
          primaryError: error.message,
          fallbackError: fallbackError.message,
          lastFallbackError: lastFallbackError.message,
        };

        // Before using emergency fallback, check if we should throw instead
        if (options.throwOnFallbackFailure === true) {
          throw new CoreErrors.Errors.NumericalInstabilityError(
            "SVD computation failed in all algorithms, fallback unavailable",
            errorContext,
          );
        }

        return {
          ...createEmergencyFallbackSVD(matrix),
          algorithm: algorithmUsed,
          errorContext: errorContext,
        };
      }
    }
  }

  // Unpack result
  let { U, S, V } = result;

  // Scale back singular values if needed
  if (needsScaling && scaleFactor !== 1) {
    for (let i = 0; i < Math.min(rows, cols); i++) {
      if (Array.isArray(S) && Array.isArray(S[0])) {
        S[i][i] /= scaleFactor;
      } else if (Array.isArray(S)) {
        S[i] /= scaleFactor;
      }
    }
  }

  // Convert to thin SVD if requested
  if (thin && rows > cols) {
    const minDim = cols;
    const thinU = [];

    for (let i = 0; i < rows; i++) {
      thinU[i] = [];
      for (let j = 0; j < minDim; j++) {
        thinU[i][j] = U[i][j];
      }
    }

    U = thinU;
  }

  return {
    U,
    S,
    V,
    dimensions,
    algorithm: algorithmUsed,
    metadata: {
      dynamicRange,
      needsScaling,
      scaleFactor: needsScaling ? scaleFactor : 1,
      maxAbsValue: maxAbs,
      minNonZeroValue: minNonZero === Infinity ? 0 : minNonZero,
      estimatedConditionNumber: dynamicRange,
    },
  };
}

/**
 * Analyzes a matrix to determine if scaling is needed for numerical stability
 * @param {Array<Array<number>>} matrix - Input matrix
 * @param {boolean} useScaling - Whether scaling should be considered
 * @returns {Object} - Analysis results
 */
function analyzeMatrix(matrix, useScaling) {
  const rows = matrix.length;
  const cols = matrix[0].length;

  let maxAbs = 0;
  let minNonZero = Infinity;

  // Find maximum absolute value and minimum non-zero absolute value
  for (let i = 0; i < rows; i++) {
    for (let j = 0; j < cols; j++) {
      const absVal = Math.abs(matrix[i][j]);
      if (absVal > 0) {
        maxAbs = Math.max(maxAbs, absVal);
        minNonZero = Math.min(minNonZero, absVal);
      }
    }
  }

  // Calculate dynamic range
  const dynamicRange =
    maxAbs > 0 && minNonZero < Infinity ? maxAbs / minNonZero : 0;

  // Determine if scaling is needed
  const needsScaling =
    useScaling &&
    (maxAbs > 1e100 || minNonZero < 1e-100 || dynamicRange > 1e200);

  // Calculate appropriate scaling factor
  let scaleFactor = 1;

  if (needsScaling) {
    if (maxAbs > 1e100) {
      // Scale down for very large values
      scaleFactor = 1 / maxAbs;
    } else if (minNonZero < 1e-100 && minNonZero > 0) {
      // Scale up for very small values
      scaleFactor = 1 / minNonZero;
    } else if (dynamicRange > 1e200) {
      // Balance the extreme values using logarithmic center
      const logMax = Math.log10(maxAbs);
      const logMin = Math.log10(minNonZero > 0 ? minNonZero : 1e-300);
      const centerLog = (logMax + logMin) / 2;
      scaleFactor = Math.pow(10, -centerLog);
    }
  }

  return { maxAbs, minNonZero, dynamicRange, needsScaling, scaleFactor };
}

/**
 * Applies scaling to a matrix
 * @param {Array<Array<number>>} matrix - Input matrix
 * @param {number} scaleFactor - Scaling factor
 * @returns {Array<Array<number>>} - Scaled matrix
 */
function applyScaling(matrix, scaleFactor) {
  const rows = matrix.length;
  const cols = matrix[0].length;
  const result = [];

  for (let i = 0; i < rows; i++) {
    result[i] = [];
    for (let j = 0; j < cols; j++) {
      result[i][j] = matrix[i][j] * scaleFactor;
    }
  }

  return result;
}

/**
 * Chooses the best SVD algorithm based on matrix characteristics
 * @param {Object} dimensions - Matrix dimensions {rows, cols}
 * @param {number} dynamicRange - Ratio of largest to smallest non-zero values
 * @returns {string} - Selected algorithm name
 */
function chooseAlgorithm(dimensions, dynamicRange) {
  const { rows, cols } = dimensions;
  const size = Math.max(rows, cols);

  // For small matrices, Jacobi is most stable
  if (size <= 32) {
    return "jacobi";
  }

  // For matrices with extreme dynamic range, use power iteration
  if (dynamicRange > 1e10) {
    return "powerIteration";
  }

  // For mid-sized matrices with moderate condition, QR is fastest
  if (size <= 128 && dynamicRange < 1e8) {
    return "qr";
  }

  // Default to Jacobi for largest matrices or undetermined cases
  return "jacobi";
}

/**
 * SVD implementation using two-sided Jacobi rotations
 * This algorithm is slower but more numerically stable
 * @param {Array<Array<number>>} matrix - Input matrix
 * @param {Object} options - Algorithm options
 * @returns {Object} - SVD decomposition {U, S, V}
 */
function jacobiSVD(matrix, options) {
  const { maxIterations, tolerance } = options;
  const m = matrix.length;
  const n = matrix[0].length;

  // Create initial matrices
  let U = createIdentityMatrix(m);
  let V = createIdentityMatrix(n);
  let S = cloneMatrix(matrix);

  // Analyze matrix to find maximum value for convergence detection
  let maxElement = 0;
  for (let i = 0; i < m; i++) {
    for (let j = 0; j < n; j++) {
      maxElement = Math.max(maxElement, Math.abs(S[i][j]));
    }
  }

  // Use adaptive tolerance based on matrix size and magnitude
  const adaptiveTolerance = tolerance * maxElement * Math.max(m, n);

  // Helper function for SVD step using Jacobi rotations
  const svdStep = () => {
    let totalChange = 0;

    // Process all possible pairs of columns
    for (let p = 0; p < n - 1; p++) {
      for (let q = p + 1; q < n; q++) {
        // Calculate parameters for Jacobi rotation
        let sqSum = 0;
        let spSum = 0;

        for (let i = 0; i < m; i++) {
          const spVal = S[i][p];
          const sqVal = S[i][q];
          spSum += spVal * spVal;
          sqSum += sqVal * sqVal;
        }

        if (Math.sqrt(spSum * sqSum) < adaptiveTolerance) {
          continue; // Skip if columns are effectively zero
        }

        // Compute off-diagonal sum with Kahan summation for stability
        let spq = 0;
        let compensation = 0;

        for (let i = 0; i < m; i++) {
          // Kahan summation to reduce floating-point errors
          const y = S[i][p] * S[i][q] - compensation;
          const t = spq + y;
          compensation = t - spq - y;
          spq = t;
        }

        // Check if rotation is needed
        if (Math.abs(spq) <= tolerance * Math.sqrt(spSum * sqSum)) {
          continue;
        }

        // Compute Jacobi rotation parameters
        const theta = 0.5 * Math.atan2(2 * spq, spSum - sqSum);
        const cosTheta = Math.cos(theta);
        const sinTheta = Math.sin(theta);

        // Apply rotation to S
        for (let i = 0; i < m; i++) {
          const Sip = S[i][p];
          const Siq = S[i][q];
          S[i][p] = Sip * cosTheta + Siq * sinTheta;
          S[i][q] = -Sip * sinTheta + Siq * cosTheta;
        }

        // Apply rotation to V
        for (let i = 0; i < n; i++) {
          const Vip = V[i][p];
          const Viq = V[i][q];
          V[i][p] = Vip * cosTheta + Viq * sinTheta;
          V[i][q] = -Vip * sinTheta + Viq * cosTheta;
        }

        totalChange += Math.abs(spq);
      }
    }

    return totalChange;
  };

  // Iterate until convergence or max iterations
  let iter = 0;
  let totalChange = 0;

  do {
    totalChange = svdStep();
    iter++;
  } while (totalChange > adaptiveTolerance && iter < maxIterations);

  // Compute U and singular values from S
  const singularValues = [];
  const columnNorms = [];

  // Calculate column norms
  for (let j = 0; j < n; j++) {
    let colNorm = 0;
    let compensation = 0;

    for (let i = 0; i < m; i++) {
      // Use Kahan summation for better precision with small values
      const val = S[i][j];
      const y = val * val - compensation;
      const t = colNorm + y;
      compensation = t - colNorm - y;
      colNorm = t;
    }

    columnNorms[j] = Math.sqrt(colNorm);
    singularValues[j] = columnNorms[j];
  }

  // Sort singular values and rearrange matrices
  const indices = singularValues.map((_, i) => i);
  indices.sort((a, b) => singularValues[b] - singularValues[a]);

  // Create sorted matrices
  const sortedS = createZeroMatrix(m, n);
  const sortedU = createZeroMatrix(m, m);
  const sortedV = createZeroMatrix(n, n);

  for (let j = 0; j < n; j++) {
    if (j < Math.min(m, n)) {
      sortedS[j][j] = singularValues[indices[j]];
    }

    // Rearrange V columns
    for (let i = 0; i < n; i++) {
      sortedV[i][j] = V[i][indices[j]];
    }

    // Create U columns from normalized S columns
    if (columnNorms[indices[j]] > adaptiveTolerance) {
      for (let i = 0; i < m; i++) {
        sortedU[i][j] = S[i][indices[j]] / columnNorms[indices[j]];
      }
    } else {
      // Handle numerically zero singular values
      if (j < m) {
        sortedU[j][j] = 1;
      }
    }
  }

  // Complete orthogonalization of U if needed
  for (let j = n; j < m; j++) {
    // Find a vector orthogonal to all existing columns
    let tempCol = new Array(m).fill(0);
    tempCol[j % m] = 1;

    // Orthogonalize against existing columns
    for (let k = 0; k < j; k++) {
      let dotProd = 0;
      for (let i = 0; i < m; i++) {
        dotProd += tempCol[i] * sortedU[i][k];
      }

      for (let i = 0; i < m; i++) {
        tempCol[i] -= dotProd * sortedU[i][k];
      }
    }

    // Normalize
    let norm = 0;
    for (let i = 0; i < m; i++) {
      norm += tempCol[i] * tempCol[i];
    }
    norm = Math.sqrt(norm);

    if (norm > adaptiveTolerance) {
      for (let i = 0; i < m; i++) {
        sortedU[i][j] = tempCol[i] / norm;
      }
    } else {
      // Fallback for numerical stability
      sortedU[j][j] = 1;
    }
  }

  return { U: sortedU, S: sortedS, V: sortedV };
}

/**
 * SVD implementation using QR iterations
 * This algorithm is faster for well-conditioned matrices
 * @param {Array<Array<number>>} matrix - Input matrix
 * @param {Object} options - Algorithm options
 * @returns {Object} - SVD decomposition {U, S, V}
 */
function qrSVD(matrix, options) {
  const { maxIterations, tolerance } = options;
  const m = matrix.length;
  const n = matrix[0].length;

  // Form A^T * A for eigenvalue decomposition
  const AtA = multiplyMatrixTranspose(matrix, matrix);

  // Perform eigendecomposition of AtA
  const { eigenvalues, eigenvectors } = eigenDecomposition(AtA, {
    maxIterations,
    tolerance,
  });

  // Sort eigenvalues and eigenvectors
  const indices = eigenvalues.map((_, i) => i);
  indices.sort((a, b) => eigenvalues[b] - eigenvalues[a]);

  // Create sorted V and singular values
  const V = createZeroMatrix(n, n);
  const singularValues = [];

  for (let j = 0; j < n; j++) {
    const idx = indices[j];
    const eigenvalue = eigenvalues[idx];

    // Eigenvalues of A^T*A are squares of singular values
    singularValues[j] = eigenvalue >= 0 ? Math.sqrt(eigenvalue) : 0;

    // Copy eigenvectors to V
    for (let i = 0; i < n; i++) {
      V[i][j] = eigenvectors[i][idx];
    }
  }

  // Calculate U using A*V/sigma
  const U = createZeroMatrix(m, m);
  const S = createZeroMatrix(m, n);

  // Fill diagonal of S with singular values
  const minDim = Math.min(m, n);
  for (let i = 0; i < minDim; i++) {
    S[i][i] = singularValues[i];
  }

  // Compute U columns from normalized AV
  for (let j = 0; j < minDim; j++) {
    if (singularValues[j] > tolerance) {
      // u_j = Av_j / sigma_j
      for (let i = 0; i < m; i++) {
        let sum = 0;
        for (let k = 0; k < n; k++) {
          sum += matrix[i][k] * V[k][j];
        }
        U[i][j] = sum / singularValues[j];
      }
    } else {
      // For zero singular values, set a unit vector
      U[j % m][j] = 1;
    }
  }

  // Complete U with orthogonal basis if m > n
  if (m > n) {
    for (let j = n; j < m; j++) {
      // Create orthogonal vector
      let v = new Array(m).fill(0);
      v[j] = 1;

      // Orthogonalize against existing columns
      for (let k = 0; k < j; k++) {
        let dot = 0;
        for (let i = 0; i < m; i++) {
          dot += v[i] * U[i][k];
        }

        for (let i = 0; i < m; i++) {
          v[i] -= dot * U[i][k];
        }
      }

      // Normalize
      let norm = 0;
      for (let i = 0; i < m; i++) {
        norm += v[i] * v[i];
      }
      norm = Math.sqrt(norm);

      if (norm > tolerance) {
        for (let i = 0; i < m; i++) {
          U[i][j] = v[i] / norm;
        }
      } else {
        // Fallback
        U[j][j] = 1;
      }
    }
  }

  return { U, S, V };
}

/**
 * SVD implementation using power iteration method
 * This algorithm is more robust for ill-conditioned matrices
 * @param {Array<Array<number>>} matrix - Input matrix
 * @param {Object} options - Algorithm options
 * @returns {Object} - SVD decomposition {U, S, V}
 */
function powerIterationSVD(matrix, options) {
  const { maxIterations, tolerance } = options;
  const m = matrix.length;
  const n = matrix[0].length;
  const minDim = Math.min(m, n);

  // Initialize result matrices
  const U = createZeroMatrix(m, m);
  const S = createZeroMatrix(m, n);
  const V = createZeroMatrix(n, n);

  // Clone the matrix for deflation
  let A = cloneMatrix(matrix);

  // Arrays to store singular values and vectors
  const singularValues = new Array(minDim).fill(0);
  const uVectors = new Array(minDim);
  const vVectors = new Array(minDim);

  // Compute each singular value/vector pair using power iteration
  for (let i = 0; i < minDim; i++) {
    // Start with a random unit vector
    let v = new Array(n).fill(0);
    v[i % n] = 1; // Use standard basis vectors for better convergence

    // Normalize v
    let vNorm = 0;
    for (let j = 0; j < n; j++) {
      vNorm += v[j] * v[j];
    }
    vNorm = Math.sqrt(vNorm);
    for (let j = 0; j < n; j++) {
      v[j] /= vNorm;
    }

    // Power iteration to find dominant singular value/vectors
    let prevSingularValue = 0;
    let singularValue = 0;
    let iter = 0;

    do {
      prevSingularValue = singularValue;

      // Calculate u = Av / |Av|
      let u = new Array(m).fill(0);

      // Compute u = A*v with Kahan summation
      for (let j = 0; j < m; j++) {
        let sum = 0;
        let compensation = 0;

        for (let k = 0; k < n; k++) {
          // Kahan summation
          const y = A[j][k] * v[k] - compensation;
          const t = sum + y;
          compensation = t - sum - y;
          sum = t;
        }

        u[j] = sum;
      }

      // Calculate |u|
      let uNorm = 0;
      for (let j = 0; j < m; j++) {
        uNorm += u[j] * u[j];
      }
      uNorm = Math.sqrt(uNorm);

      // Normalize u
      if (uNorm > tolerance) {
        for (let j = 0; j < m; j++) {
          u[j] /= uNorm;
        }
      } else {
        // Handle zero case
        if (i < m) u[i] = 1;
        uNorm = 1;
      }

      // Calculate v = A^T u / |A^T u|
      const newV = new Array(n).fill(0);

      // Compute v = A^T * u with Kahan summation
      for (let j = 0; j < n; j++) {
        let sum = 0;
        let compensation = 0;

        for (let k = 0; k < m; k++) {
          // Kahan summation
          const y = A[k][j] * u[k] - compensation;
          const t = sum + y;
          compensation = t - sum - y;
          sum = t;
        }

        newV[j] = sum;
      }

      // Calculate |v|
      let newVNorm = 0;
      for (let j = 0; j < n; j++) {
        newVNorm += newV[j] * newV[j];
      }
      newVNorm = Math.sqrt(newVNorm);

      // Singular value is |A^T u|
      singularValue = newVNorm;

      // Normalize v
      if (newVNorm > tolerance) {
        for (let j = 0; j < n; j++) {
          v[j] = newV[j] / newVNorm;
        }
      } else {
        // Handle zero case
        if (i < n) v[i] = 1;
      }

      // Check convergence with relative error
      const relError =
        Math.abs(singularValue - prevSingularValue) /
        (singularValue > tolerance ? singularValue : 1);

      if (relError < tolerance) {
        break;
      }

      iter++;
    } while (iter < maxIterations);

    // Store singular value and vectors
    singularValues[i] = singularValue;
    uVectors[i] = new Array(m);
    vVectors[i] = new Array(n);

    for (let j = 0; j < m; j++) {
      uVectors[i][j] = u[j];
    }

    for (let j = 0; j < n; j++) {
      vVectors[i][j] = v[j];
    }

    // Deflate the matrix by removing the component sigma * u * v^T
    for (let j = 0; j < m; j++) {
      for (let k = 0; k < n; k++) {
        A[j][k] -= singularValue * u[j] * v[k];
      }
    }
  }

  // Sort singular values and vectors by decreasing value
  const indices = new Array(minDim).fill(0).map((_, i) => i);
  indices.sort((a, b) => singularValues[b] - singularValues[a]);

  // Fill S, U, V matrices
  for (let i = 0; i < minDim; i++) {
    const idx = indices[i];
    S[i][i] = singularValues[idx];

    for (let j = 0; j < m; j++) {
      U[j][i] = uVectors[idx][j];
    }

    for (let j = 0; j < n; j++) {
      V[j][i] = vVectors[idx][j];
    }
  }

  // Complete U with orthogonal basis if m > minDim
  if (m > minDim) {
    for (let i = minDim; i < m; i++) {
      // Generate vector orthogonal to all existing columns
      const vec = new Array(m).fill(0);
      vec[i % m] = 1;

      // Gram-Schmidt orthogonalization
      for (let j = 0; j < i; j++) {
        let dot = 0;
        for (let k = 0; k < m; k++) {
          dot += vec[k] * U[k][j];
        }

        for (let k = 0; k < m; k++) {
          vec[k] -= dot * U[k][j];
        }
      }

      // Normalize
      let norm = 0;
      for (let j = 0; j < m; j++) {
        norm += vec[j] * vec[j];
      }
      norm = Math.sqrt(norm);

      if (norm > tolerance) {
        for (let j = 0; j < m; j++) {
          U[j][i] = vec[j] / norm;
        }
      } else {
        // Fallback if orthogonalization failed
        U[i][i] = 1;
      }
    }
  }

  // Complete V with orthogonal basis if n > minDim
  if (n > minDim) {
    for (let i = minDim; i < n; i++) {
      // Generate vector orthogonal to all existing columns
      const vec = new Array(n).fill(0);
      vec[i % n] = 1;

      // Gram-Schmidt orthogonalization
      for (let j = 0; j < i; j++) {
        let dot = 0;
        for (let k = 0; k < n; k++) {
          dot += vec[k] * V[k][j];
        }

        for (let k = 0; k < n; k++) {
          vec[k] -= dot * V[k][j];
        }
      }

      // Normalize
      let norm = 0;
      for (let j = 0; j < n; j++) {
        norm += vec[j] * vec[j];
      }
      norm = Math.sqrt(norm);

      if (norm > tolerance) {
        for (let j = 0; j < n; j++) {
          V[j][i] = vec[j] / norm;
        }
      } else {
        // Fallback if orthogonalization failed
        V[i][i] = 1;
      }
    }
  }

  return { U, S, V };
}

/**
 * Creates an identity matrix of specified size
 * @param {number} size - Matrix size
 * @returns {Array<Array<number>>} - Identity matrix
 */
function createIdentityMatrix(size) {
  const result = [];

  for (let i = 0; i < size; i++) {
    result[i] = [];
    for (let j = 0; j < size; j++) {
      result[i][j] = i === j ? 1 : 0;
    }
  }

  return result;
}

/**
 * Creates a zero matrix of specified dimensions
 * @param {number} rows - Number of rows
 * @param {number} cols - Number of columns
 * @returns {Array<Array<number>>} - Zero matrix
 */
function createZeroMatrix(rows, cols) {
  const result = [];

  for (let i = 0; i < rows; i++) {
    result[i] = new Array(cols).fill(0);
  }

  return result;
}

/**
 * Creates a deep copy of a matrix
 * @param {Array<Array<number>>} matrix - Input matrix
 * @returns {Array<Array<number>>} - Cloned matrix
 */
function cloneMatrix(matrix) {
  const rows = matrix.length;
  const cols = matrix[0].length;
  const result = [];

  for (let i = 0; i < rows; i++) {
    result[i] = matrix[i].slice();
  }

  return result;
}

/**
 * Multiplies matrix transposed by another matrix: A^T * B
 * @param {Array<Array<number>>} a - First matrix
 * @param {Array<Array<number>>} b - Second matrix
 * @returns {Array<Array<number>>} - Result matrix
 */
function multiplyMatrixTranspose(a, b) {
  const rowsA = a.length;
  const colsA = a[0].length;
  const colsB = b[0].length;
  const result = [];

  for (let i = 0; i < colsA; i++) {
    result[i] = [];
    for (let j = 0; j < colsB; j++) {
      let sum = 0;
      let compensation = 0;

      // Kahan summation for better precision
      for (let k = 0; k < rowsA; k++) {
        const y = a[k][i] * b[k][j] - compensation;
        const t = sum + y;
        compensation = t - sum - y;
        sum = t;
      }

      result[i][j] = sum;
    }
  }

  return result;
}

/**
 * Computes eigenvalues and eigenvectors of a symmetric matrix
 * Uses QR algorithm with implicit shifts for numerical stability
 * @param {Array<Array<number>>} matrix - Symmetric matrix
 * @param {Object} options - Algorithm options
 * @returns {Object} - Eigenvalues and eigenvectors
 */
function eigenDecomposition(matrix, options = {}) {
  const { maxIterations = 100, tolerance = 1e-10 } = options;
  const n = matrix.length;

  // Check if matrix is symmetric
  for (let i = 0; i < n; i++) {
    for (let j = i + 1; j < n; j++) {
      if (Math.abs(matrix[i][j] - matrix[j][i]) > tolerance) {
        throw new Error("Eigendecomposition requires a symmetric matrix");
      }
    }
  }

  // Create a copy of the input matrix
  let H = cloneMatrix(matrix);
  let V = createIdentityMatrix(n);

  // Tridiagonalize the matrix using Householder transformations
  tridiagonalize(H, V);

  // Perform QR algorithm on the tridiagonal matrix
  const numIterations = qrAlgorithm(H, V, { maxIterations, tolerance });

  // Extract eigenvalues and eigenvectors
  const eigenvalues = [];
  const eigenvectors = [];

  for (let i = 0; i < n; i++) {
    eigenvalues[i] = H[i][i];
    eigenvectors[i] = [];

    for (let j = 0; j < n; j++) {
      eigenvectors[i][j] = V[i][j];
    }
  }

  return { eigenvalues, eigenvectors, iterations: numIterations };
}

/**
 * Tridiagonalizes a symmetric matrix using Householder transformations
 * @param {Array<Array<number>>} matrix - Input/output matrix
 * @param {Array<Array<number>>} V - Eigenvector matrix
 */
function tridiagonalize(matrix, V) {
  const n = matrix.length;

  for (let k = 0; k < n - 2; k++) {
    let scale = 0;

    // Compute scale to avoid underflow/overflow
    for (let i = k + 1; i < n; i++) {
      scale += Math.abs(matrix[i][k]);
    }

    if (scale === 0) continue;

    // Compute Householder vector
    let h = 0;
    for (let i = k + 1; i < n; i++) {
      matrix[i][k] /= scale;
      h += matrix[i][k] * matrix[i][k];
    }

    let f = matrix[k + 1][k];
    let g = f >= 0 ? -Math.sqrt(h) : Math.sqrt(h);

    h = h - f * g;
    matrix[k + 1][k] = f - g;

    // Temporary storage for Householder vector
    const temp = new Array(n - k - 1).fill(0);

    // Compute A * u
    for (let j = k + 1; j < n; j++) {
      let sum = 0;
      for (let i = k + 1; i < n; i++) {
        sum += matrix[i][k] * matrix[i][j];
      }

      f = sum / h;

      // Compute p = f * u
      for (let i = k + 1; i < n; i++) {
        temp[i - k - 1] = f * matrix[i][k];
      }

      // Compute q = A * p
      for (let i = k + 1; i < n; i++) {
        for (let j = k + 1; j <= i; j++) {
          matrix[i][j] -=
            matrix[i][k] * temp[j - k - 1] + matrix[j][k] * temp[i - k - 1];
          matrix[j][i] = matrix[i][j];
        }
      }
    }

    // Apply Householder transformation to eigenvector matrix
    for (let i = 0; i < n; i++) {
      let sum = 0;
      for (let j = k + 1; j < n; j++) {
        sum += V[i][j] * matrix[j][k];
      }

      sum /= h;

      for (let j = k + 1; j < n; j++) {
        V[i][j] -= sum * matrix[j][k];
      }
    }

    // Scale back
    for (let i = k + 1; i < n; i++) {
      matrix[i][k] *= scale;
    }
  }
}

/**
 * Performs QR algorithm on a tridiagonal matrix
 * @param {Array<Array<number>>} H - Tridiagonal matrix
 * @param {Array<Array<number>>} V - Eigenvector matrix
 * @param {Object} options - Algorithm options
 * @returns {number} - Number of iterations
 */
function qrAlgorithm(H, V, options) {
  const { maxIterations, tolerance } = options;
  const n = H.length;

  let iterations = 0;
  let m = n;

  while (m > 1 && iterations < maxIterations) {
    let h, g, p, r, f, q, s;

    // Look for a single small subdiagonal element to split the matrix
    for (let i = m - 2; i >= 0; i--) {
      const test1 = Math.abs(H[i][i]) + Math.abs(H[i + 1][i + 1]);
      const test2 = test1 + Math.abs(H[i + 1][i]);

      if (Math.abs(H[i + 1][i]) < tolerance * test2) {
        // Found a negligible off-diagonal element
        H[i + 1][i] = 0;
        break;
      }
    }

    // Check if matrix can be split
    let l = 0;
    for (let i = m - 2; i >= 0; i--) {
      if (Math.abs(H[i + 1][i]) < tolerance) {
        l = i + 1;
        break;
      }
    }

    if (l === m - 1) {
      // 1x1 block, eigenvalue found
      m--;
    } else if (l === m - 2) {
      // 2x2 block, solve quadratic for eigenvalues
      const a = H[m - 2][m - 2];
      const b = H[m - 2][m - 1];
      const c = H[m - 1][m - 2];
      const d = H[m - 1][m - 1];

      const trace = a + d;
      const det = a * d - b * c;
      const discriminant = trace * trace - 4 * det;

      if (discriminant >= 0) {
        // Real eigenvalues
        const sqrtDisc = Math.sqrt(discriminant);
        const lambda1 = (trace + sqrtDisc) / 2;
        const lambda2 = (trace - sqrtDisc) / 2;

        H[m - 2][m - 2] = lambda1;
        H[m - 1][m - 1] = lambda2;
        H[m - 2][m - 1] = 0;
        H[m - 1][m - 2] = 0;
      } else {
        // Complex eigenvalues, not used in SVD (should not happen for symmetric matrices)
        H[m - 2][m - 2] = a;
        H[m - 1][m - 1] = d;
      }

      // Update eigenvectors
      for (let i = 0; i < n; i++) {
        // Complex operation for real 2x2 block
        const vi1 = V[i][m - 2];
        const vi2 = V[i][m - 1];

        V[i][m - 2] = vi1 * a + vi2 * c;
        V[i][m - 1] = vi1 * b + vi2 * d;
      }

      m -= 2;
    } else {
      // Perform QR step on [l:m, l:m] submatrix

      // Calculate Wilkinson shift
      const a = H[m - 2][m - 2];
      const b = H[m - 2][m - 1];
      const c = H[m - 1][m - 2];
      const d = H[m - 1][m - 1];

      const trace = a + d;
      const det = a * d - b * c;
      const shift = (a - d) / 2;
      const sign = shift >= 0 ? 1 : -1;
      const discriminant = shift * shift + b * c;

      let mu;
      if (discriminant > 0) {
        mu = d - (c * b) / (shift + sign * Math.sqrt(discriminant));
      } else {
        mu = d;
      }

      // Initialize first column of implicit Q
      let x = H[l][l] - mu;
      let z = H[l + 1][l];

      // Perform implicit Q*R with Givens rotations
      for (let k = l; k < m - 1; k++) {
        // Calculate Givens rotation
        const [cs, sn] = givensRotation(x, z);

        // Apply rotation to H
        for (let j = k; j < m; j++) {
          const p = H[k][j];
          const q = H[k + 1][j];
          H[k][j] = cs * p + sn * q;
          H[k + 1][j] = -sn * p + cs * q;
        }

        for (let i = 0; i <= Math.min(k + 2, m - 1); i++) {
          const p = H[i][k];
          const q = H[i][k + 1];
          H[i][k] = cs * p + sn * q;
          H[i][k + 1] = -sn * p + cs * q;
        }

        // Apply rotation to eigenvector matrix
        for (let i = 0; i < n; i++) {
          const p = V[i][k];
          const q = V[i][k + 1];
          V[i][k] = cs * p + sn * q;
          V[i][k + 1] = -sn * p + cs * q;
        }

        // Prepare for next rotation
        if (k < m - 2) {
          x = H[k + 1][k];
          z = H[k + 2][k];
        }
      }

      iterations++;
    }
  }

  return iterations;
}

/**
 * Computes Givens rotation for a pair of values
 * @param {number} a - First value
 * @param {number} b - Second value
 * @returns {Array<number>} - [cos, sin] for rotation
 */
function givensRotation(a, b) {
  const denominator = Math.sqrt(a * a + b * b);

  if (denominator === 0) {
    return [1, 0];
  }

  const cs = a / denominator;
  const sn = b / denominator;

  return [cs, sn];
}

/**
 * Creates a fallback SVD result for emergency cases
 * @param {Array<Array<number>>} matrix - Original matrix
 * @returns {Object} - Minimal SVD result
 */
function createEmergencyFallbackSVD(matrix) {
  const m = matrix.length;
  const n = matrix[0].length;
  const U = createIdentityMatrix(m);
  const V = createIdentityMatrix(n);
  const S = createZeroMatrix(m, n);

  // Estimate diagonal values
  const minDim = Math.min(m, n);

  // Calculate Frobenius norm as a rough estimate
  let frobNorm = 0;
  for (let i = 0; i < m; i++) {
    for (let j = 0; j < n; j++) {
      frobNorm += matrix[i][j] * matrix[i][j];
    }
  }
  frobNorm = Math.sqrt(frobNorm);

  // Set singular values to reasonable defaults
  // The first singular value is set to the Frobenius norm
  // Additional singular values decrease geometrically
  if (minDim > 0) {
    S[0][0] = frobNorm;

    for (let i = 1; i < minDim; i++) {
      S[i][i] = S[i - 1][i - 1] / 10;
    }
  }

  return { U, S, V, dimensions: { rows: m, cols: n } };
}

/**
 * Determines if a matrix contains exclusively extremely small values
 * @param {Array<Array<number>>} matrix - Input matrix
 * @returns {boolean} - True if matrix has only extremely small values
 */
function analyzeIfExtremelySmall(matrix) {
  const rows = matrix.length;
  const cols = matrix[0].length;

  let maxAbs = 0;

  for (let i = 0; i < rows; i++) {
    for (let j = 0; j < cols; j++) {
      const absVal = Math.abs(matrix[i][j]);
      maxAbs = Math.max(maxAbs, absVal);

      // If we find any value that's not extremely small, return false
      if (absVal > 1e-10) {
        return false;
      }
    }
  }

  // If all values are very small, return true
  return maxAbs > 0 && maxAbs < 1e-10;
}

/**
 * Special handler for matrices with extremely small values
 * @param {Array<Array<number>>} matrix - Input matrix with small values
 * @returns {Object} - SVD decomposition {U, S, V}
 */
function handleExtremelySmallMatrix(matrix) {
  const rows = matrix.length;
  const cols = matrix[0].length;
  const minDim = Math.min(rows, cols);

  // Create a scaled matrix for computation
  const scaledMatrix = [];

  // Apply aggressive scaling to bring values to normal range
  const scaleFactor = 1e15;
  for (let i = 0; i < rows; i++) {
    scaledMatrix[i] = [];
    for (let j = 0; j < cols; j++) {
      scaledMatrix[i][j] = matrix[i][j] * scaleFactor;
    }
  }

  // Use Jacobi algorithm which is most stable for small values
  const { U, S, V } = jacobiSVD(scaledMatrix, {
    maxIterations: 200,
    tolerance: 1e-14,
  });

  // Scale back the singular values
  for (let i = 0; i < minDim; i++) {
    S[i][i] /= scaleFactor;
  }

  // Ensure all basis vectors are actually orthogonal
  // This is critical for extremely small values

  // Orthogonalize U
  for (let i = 0; i < rows; i++) {
    // First normalize
    let norm = 0;
    for (let j = 0; j < rows; j++) {
      norm += U[j][i] * U[j][i];
    }
    norm = Math.sqrt(norm);

    if (norm > 1e-14) {
      for (let j = 0; j < rows; j++) {
        U[j][i] /= norm;
      }
    } else {
      // For zero vectors, set a unit vector
      for (let j = 0; j < rows; j++) {
        U[j][i] = j === i ? 1 : 0;
      }
    }

    // Then orthogonalize against all previous vectors
    for (let k = 0; k < i; k++) {
      let dot = 0;
      for (let j = 0; j < rows; j++) {
        dot += U[j][i] * U[j][k];
      }

      for (let j = 0; j < rows; j++) {
        U[j][i] -= dot * U[j][k];
      }

      // Renormalize after orthogonalization
      norm = 0;
      for (let j = 0; j < rows; j++) {
        norm += U[j][i] * U[j][i];
      }
      norm = Math.sqrt(norm);

      if (norm > 1e-14) {
        for (let j = 0; j < rows; j++) {
          U[j][i] /= norm;
        }
      } else {
        // If vector becomes zero during orthogonalization,
        // create a unit vector orthogonal to all previous ones
        let found = false;
        for (let j = 0; j < rows && !found; j++) {
          let isOrthogonal = true;
          for (let l = 0; l < i && isOrthogonal; l++) {
            if (Math.abs(U[j][l]) > 1e-14) {
              isOrthogonal = false;
            }
          }

          if (isOrthogonal) {
            for (let m = 0; m < rows; m++) {
              U[m][i] = m === j ? 1 : 0;
            }
            found = true;
          }
        }

        // If we couldn't find an orthogonal unit vector, create a random one and orthogonalize
        if (!found) {
          for (let j = 0; j < rows; j++) {
            U[j][i] = j === i ? 1 : 0;
          }

          for (let k = 0; k < i; k++) {
            let dot = 0;
            for (let j = 0; j < rows; j++) {
              dot += U[j][i] * U[j][k];
            }

            for (let j = 0; j < rows; j++) {
              U[j][i] -= dot * U[j][k];
            }
          }

          // Normalize again
          norm = 0;
          for (let j = 0; j < rows; j++) {
            norm += U[j][i] * U[j][i];
          }
          norm = Math.sqrt(norm);

          if (norm > 1e-14) {
            for (let j = 0; j < rows; j++) {
              U[j][i] /= norm;
            }
          } else {
            // Last resort fallback
            for (let j = 0; j < rows; j++) {
              U[j][i] = j === i ? 1 : 0;
            }
          }
        }
      }
    }
  }

  // Same process for V
  for (let i = 0; i < cols; i++) {
    // First normalize
    let norm = 0;
    for (let j = 0; j < cols; j++) {
      norm += V[j][i] * V[j][i];
    }
    norm = Math.sqrt(norm);

    if (norm > 1e-14) {
      for (let j = 0; j < cols; j++) {
        V[j][i] /= norm;
      }
    } else {
      // For zero vectors, set a unit vector
      for (let j = 0; j < cols; j++) {
        V[j][i] = j === i ? 1 : 0;
      }
    }

    // Then orthogonalize against all previous vectors
    for (let k = 0; k < i; k++) {
      let dot = 0;
      for (let j = 0; j < cols; j++) {
        dot += V[j][i] * V[j][k];
      }

      for (let j = 0; j < cols; j++) {
        V[j][i] -= dot * V[j][k];
      }

      // Renormalize after orthogonalization
      norm = 0;
      for (let j = 0; j < cols; j++) {
        norm += V[j][i] * V[j][i];
      }
      norm = Math.sqrt(norm);

      if (norm > 1e-14) {
        for (let j = 0; j < cols; j++) {
          V[j][i] /= norm;
        }
      } else {
        // If vector becomes zero during orthogonalization,
        // create a unit vector orthogonal to all previous ones
        let found = false;
        for (let j = 0; j < cols && !found; j++) {
          let isOrthogonal = true;
          for (let l = 0; l < i && isOrthogonal; l++) {
            if (Math.abs(V[j][l]) > 1e-14) {
              isOrthogonal = false;
            }
          }

          if (isOrthogonal) {
            for (let m = 0; m < cols; m++) {
              V[m][i] = m === j ? 1 : 0;
            }
            found = true;
          }
        }

        // If we couldn't find an orthogonal unit vector, create a random one and orthogonalize
        if (!found) {
          for (let j = 0; j < cols; j++) {
            V[j][i] = j === i ? 1 : 0;
          }

          for (let k = 0; k < i; k++) {
            let dot = 0;
            for (let j = 0; j < cols; j++) {
              dot += V[j][i] * V[j][k];
            }

            for (let j = 0; j < cols; j++) {
              V[j][i] -= dot * V[j][k];
            }
          }

          // Normalize again
          norm = 0;
          for (let j = 0; j < cols; j++) {
            norm += V[j][i] * V[j][i];
          }
          norm = Math.sqrt(norm);

          if (norm > 1e-14) {
            for (let j = 0; j < cols; j++) {
              V[j][i] /= norm;
            }
          } else {
            // Last resort fallback
            for (let j = 0; j < cols; j++) {
              V[j][i] = j === i ? 1 : 0;
            }
          }
        }
      }
    }
  }

  return { U, S, V };
}

// Export the SVD implementation
module.exports = computeSVD;
