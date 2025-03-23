/**
 * PrimeOS JavaScript Library - Math
 * Matrix Error Handling
 * Error recovery strategies for matrix operations
 */

// Import the Prime object
const Prime = require("../core");

/**
 * Matrix error handling utilities with recovery strategies
 */
const MatrixErrorHandling = {
  /**
   * Attempt to recover from singular or ill-conditioned matrix errors
   * @param {function} operation - The matrix operation function to execute
   * @param {Array} args - Arguments to pass to the operation
   * @param {Object} options - Recovery options
   * @returns {*} - Result of operation or recovered alternative
   * @throws {Error} - Improved error with recovery suggestions if recovery fails
   */
  recoverFromSingularity: function (operation, args, options = {}) {
    try {
      // Try the original operation
      return operation.apply(null, args);
    } catch (error) {
      if (
        error.message.includes("singular") ||
        error.message.includes("condition")
      ) {
        const strategy = options.strategy || "pseudoinverse";
        const MatrixCore = Prime.Math.MatrixCore;

        // Matrix that caused the error
        const matrix = args[0];

        switch (strategy) {
          case "pseudoinverse":
            // Compute pseudoinverse using SVD if available
            if (Prime.Math.Matrix.pseudoInverse) {
              return Prime.Math.Matrix.pseudoInverse(matrix);
            }
            break;

          case "regularize":
            // Add a small value to the diagonal (Tikhonov regularization)
            const epsilon = options.epsilon || 1e-10;
            const regularized = MatrixCore.clone(matrix);
            const n = regularized.length;

            for (let i = 0; i < n; i++) {
              regularized[i][i] += epsilon;
            }

            // Try operation with regularized matrix
            args[0] = regularized;
            return operation.apply(null, args);

          case "truncate":
            // Use truncated SVD if available
            if (Prime.Math.Matrix.truncatedSVD) {
              const rank = options.rank || Math.floor(matrix.length / 2);
              return Prime.Math.Matrix.truncatedSVD(matrix, rank);
            }
            break;
        }

        // If no recovery succeeded, throw enhanced error
        throw new Prime.MathematicalError(
          `Matrix operation failed due to singularity or poor conditioning: ${error.message}. ` +
            `Try scaling the matrix, adding regularization, or using pseudoinverse.`,
        );
      }

      // For other types of errors, just rethrow
      throw error;
    }
  },

  /**
   * Handle numerical stability issues from extreme values with proper scaling and recovery
   * @param {function} operation - The matrix operation function to execute
   * @param {Array} args - Arguments to pass to the operation
   * @param {Object} options - Recovery options
   * @returns {*} - Result of operation with numerically stable approach
   * @throws {Error} - Enhanced error with suggestions if recovery fails
   */
  handleExtremeValues: function (operation, args, options = {}) {
    const MatrixCore = Prime.Math.MatrixCore;
    const MatrixValidation = Prime.Math.MatrixValidation;

    // Extract the matrix from arguments
    const matrix = args[0];

    // Input validation
    if (!MatrixValidation.isMatrix(matrix)) {
      throw new Prime.ValidationError("Input must be a valid matrix");
    }

    // Check for NaN and Infinity values
    if (MatrixValidation.hasInvalidValues(matrix)) {
      throw new Prime.ValidationError(
        "Matrix contains NaN or Infinity values which cannot be processed",
      );
    }

    // Analyze matrix properties for potential numerical issues
    const dims = MatrixCore.dimensions(matrix);
    const rows = dims.rows;
    const cols = dims.cols;

    // Calculate matrix statistics for scaling decisions
    let maxAbs = 0;
    let minNonZero = Infinity;
    let sumOfSquares = 0;

    for (let i = 0; i < rows; i++) {
      for (let j = 0; j < cols; j++) {
        const value = matrix[i][j];
        const absValue = Math.abs(value);

        // Track extremes
        if (absValue > maxAbs) {
          maxAbs = absValue;
        }
        if (absValue > 0 && absValue < minNonZero) {
          minNonZero = absValue;
        }

        // Accumulate sum of squares for Frobenius norm
        sumOfSquares += absValue * absValue;
      }
    }

    // Check for matrices with extreme value range that may cause numerical instability
    const valueRatio =
      maxAbs > 0 && minNonZero < Infinity ? maxAbs / minNonZero : 0;

    const needsScaling =
      maxAbs > 1e100 || minNonZero < 1e-100 || valueRatio > 1e200;

    if (needsScaling) {
      // Choose appropriate scaling factor based on matrix properties
      let scaleFactor;
      if (maxAbs > 1e100) {
        // Scale down for very large values
        scaleFactor = 1.0 / Math.pow(10, Math.floor(Math.log10(maxAbs)) - 10);
      } else if (minNonZero < 1e-100) {
        // Scale up for very small values
        scaleFactor = Math.pow(
          10,
          Math.abs(Math.floor(Math.log10(minNonZero))) - 10,
        );
      } else {
        // Balance the range
        const logMax = Math.log10(maxAbs);
        const logMin = Math.log10(minNonZero);
        const targetLog = (logMax + logMin) / 2;
        scaleFactor = Math.pow(10, -targetLog);
      }

      try {
        // Apply scaling to create numerically stable matrix
        const scaledMatrix = MatrixCore.scale(matrix, scaleFactor);

        // Replace original matrix with scaled version in arguments
        const newArgs = [...args];
        newArgs[0] = scaledMatrix;

        // Execute operation on scaled matrix
        const result = operation.apply(null, newArgs);

        // Apply inverse scaling based on operation type
        const operationName = operation.name || "";

        // Different operations require different unscaling approaches
        if (typeof result === "number") {
          // For scalar results like determinant
          const power =
            operationName.toLowerCase() === "determinant" ? rows : 1;
          return result * Math.pow(1 / scaleFactor, power);
        } else if (result && typeof result === "object") {
          // Handle special return types from matrix decompositions
          if (result.L && result.U) {
            // LU decomposition
            result.L = MatrixCore.clone(result.L);
            result.U = MatrixCore.scale(result.U, 1 / scaleFactor);
            return result;
          } else if (result.Q && result.R) {
            // QR decomposition
            result.R = MatrixCore.scale(result.R, 1 / scaleFactor);
            return result;
          } else if (result.eigenvalues) {
            // Eigenvalue decomposition
            const scaledEigenvalues = result.eigenvalues.map(
              (v) => v / scaleFactor,
            );
            return {
              eigenvalues: scaledEigenvalues,
              eigenvectors: result.eigenvectors,
            };
          }
          // Default matrix result
          return MatrixCore.scale(result, 1 / scaleFactor);
        }

        // Default for other types of results
        return result;
      } catch (error) {
        // If scaling fails, provide helpful diagnostic information
        throw new Prime.MathematicalError(
          `Matrix operation failed despite applying scaling: ${error.message}. ` +
            `Matrix has extreme values (max=${maxAbs.toExponential(5)}, min non-zero=${minNonZero.toExponential(5)}, ` +
            `condition estimate=${valueRatio.toExponential(5)}). ` +
            `Consider using an alternative algorithm or preprocessing the data.`,
        );
      }
    }

    // For matrices in normal range, just execute the operation
    try {
      return operation.apply(null, args);
    } catch (error) {
      // Enhance error message with useful diagnostic information
      const normFrobenius = Math.sqrt(sumOfSquares);
      const meanValue = sumOfSquares / (rows * cols);

      throw new Prime.MathematicalError(
        `Matrix operation failed: ${error.message}. ` +
          `Matrix properties: size=${rows}x${cols}, Frobenius norm=${normFrobenius.toExponential(5)}, ` +
          `RMS value=${Math.sqrt(meanValue).toExponential(5)}. ` +
          `Try checking matrix conditioning or using regularization techniques.`,
      );
    }
  },

  /**
   * Compute pseudoinverse using SVD for ill-conditioned or singular matrices
   * @param {Array|TypedArray} matrix - Matrix to compute pseudoinverse for
   * @param {number} [tolerance=1e-10] - Singular value threshold (relative to max)
   * @returns {Array|TypedArray} - Pseudoinverse of the matrix
   */
  pseudoInverse: function (matrix, tolerance = 1e-10) {
    const MatrixCore = Prime.Math.MatrixCore;
    const MatrixValidation = Prime.Math.MatrixValidation;

    // Input validation
    if (!MatrixCore.isMatrix(matrix)) {
      throw new Prime.ValidationError("Matrix must be valid");
    }

    if (MatrixValidation.hasInvalidValues(matrix)) {
      throw new Prime.ValidationError("Matrix contains NaN or Infinity values");
    }

    const dim = MatrixCore.dimensions(matrix);
    const rows = dim.rows;
    const cols = dim.cols;
    const useTypedArray = matrix._isTypedArray;
    const arrayType = matrix._arrayType;

    // Calculate matrix statistics for adaptive tolerance
    let maxAbs = 0;
    for (let i = 0; i < rows; i++) {
      for (let j = 0; j < cols; j++) {
        const absVal = Math.abs(matrix[i][j]);
        if (absVal > maxAbs) {
          maxAbs = absVal;
        }
      }
    }

    // Adjust tolerance based on matrix magnitude
    const adaptiveTolerance = tolerance * (1 + maxAbs * Number.EPSILON * 100);

    try {
      // Import PrimeMath for SVD
      const PrimeMath = require("../framework/math/prime-math.js");

      if (!PrimeMath || !PrimeMath.svd) {
        throw new Prime.ValidationError(
          "SVD implementation required for pseudoinverse",
        );
      }

      // Decide if scaling is necessary
      let scaleFactor = 1;
      let scaledMatrix = matrix;

      if (maxAbs > 1e100) {
        // Scale down for numerical stability
        scaleFactor = 1e-100;
        scaledMatrix = MatrixCore.scale(matrix, scaleFactor);
      } else if (maxAbs < 1e-100 && maxAbs > 0) {
        // Scale up for numerical stability
        scaleFactor = 1e100;
        scaledMatrix = MatrixCore.scale(matrix, scaleFactor);
      }

      // Create a matrix object and perform SVD
      const matObj = PrimeMath.createMatrix(scaledMatrix);
      const { U, S, V } = PrimeMath.svd(matObj);

      // Find the maximum singular value
      let maxSingularValue = 0;
      for (let i = 0; i < Math.min(S.rows, S.cols); i++) {
        if (S.values[i][i] > maxSingularValue) {
          maxSingularValue = S.values[i][i];
        }
      }

      // Handle the case where all singular values are essentially zero
      if (maxSingularValue < adaptiveTolerance) {
        // Return zero matrix for the case where matrix is effectively zero
        return MatrixCore.create(cols, rows, 0, {
          useTypedArray,
          arrayType,
        });
      }

      // Compute threshold for zeroing small singular values
      const threshold = maxSingularValue * adaptiveTolerance;

      // Create inverse of S with filtering of small values (Tikhonov regularization)
      const SInv = PrimeMath.createMatrix(S.cols, S.rows);
      for (let i = 0; i < Math.min(S.rows, S.cols); i++) {
        if (S.values[i][i] > threshold) {
          // Standard pseudoinverse for well-behaved singular values
          SInv.values[i][i] = 1 / S.values[i][i];
        } else if (S.values[i][i] > 0) {
          // Tikhonov regularization for small singular values
          // This prevents division by very small numbers
          SInv.values[i][i] =
            S.values[i][i] /
            (S.values[i][i] * S.values[i][i] + threshold * threshold);
        }
        // Values below numerical precision are left as zero
      }

      // Compute pseudoinverse: V * S^+ * U^T
      const UT = PrimeMath.transposeMatrix(U);
      const VS = PrimeMath.multiplyMatrices(V, SInv);
      const pseudoInv = PrimeMath.multiplyMatrices(VS, UT);

      // Adjust for scaling factor
      let resultMatrix;
      if (scaleFactor !== 1) {
        // Need to scale the result to account for input scaling
        const scaledPseudoInv = PrimeMath.createMatrix(
          pseudoInv.rows,
          pseudoInv.cols,
        );
        const scaleAdjustment = 1 / scaleFactor;

        for (let i = 0; i < pseudoInv.rows; i++) {
          for (let j = 0; j < pseudoInv.cols; j++) {
            scaledPseudoInv.values[i][j] =
              pseudoInv.values[i][j] * scaleAdjustment;
          }
        }
        resultMatrix = scaledPseudoInv;
      } else {
        resultMatrix = pseudoInv;
      }

      // Convert back to the original matrix format
      const result = MatrixCore.create(
        resultMatrix.rows,
        resultMatrix.cols,
        0,
        {
          useTypedArray,
          arrayType,
        },
      );

      for (let i = 0; i < resultMatrix.rows; i++) {
        for (let j = 0; j < resultMatrix.cols; j++) {
          result[i][j] = resultMatrix.values[i][j];
        }
      }

      return result;
    } catch (error) {
      // Provide informative error for failed pseudoinverse computation
      throw new Prime.MathematicalError(
        `Failed to compute pseudoinverse: ${error.message}. ` +
          `Matrix is ${rows}x${cols} with largest value ${maxAbs.toExponential(5)}. ` +
          `Consider preprocessing or using alternative factorization methods.`,
      );
    }
  },

  /**
   * Compute a truncated SVD approximation of a matrix
   * @param {Array|TypedArray} matrix - Matrix to approximate
   * @param {number} rank - Rank to truncate to
   * @returns {Array|TypedArray} - Low-rank approximation of the matrix
   */
  truncatedSVD: function (matrix, rank) {
    const MatrixCore = Prime.Math.MatrixCore;

    if (!MatrixCore.isMatrix(matrix)) {
      throw new Prime.ValidationError("Matrix must be valid");
    }

    const dim = MatrixCore.dimensions(matrix);
    rank = Math.min(rank, Math.min(dim.rows, dim.cols));

    // Import PrimeMath for SVD
    const PrimeMath = require("../framework/math/prime-math.js");

    if (!PrimeMath || !PrimeMath.svd) {
      throw new Prime.ValidationError(
        "SVD implementation required for truncated SVD",
      );
    }

    // Create a matrix object and perform SVD
    const matObj = PrimeMath.createMatrix(matrix);
    const { U, S, V } = PrimeMath.svd(matObj);

    // Truncate the singular values
    const ST = PrimeMath.createMatrix(rank, rank);
    for (let i = 0; i < rank; i++) {
      ST.values[i][i] = S.values[i][i];
    }

    // Truncate U and V
    const UT = PrimeMath.createMatrix(U.rows, rank);
    for (let i = 0; i < U.rows; i++) {
      for (let j = 0; j < rank; j++) {
        UT.values[i][j] = U.values[i][j];
      }
    }

    const VT = PrimeMath.createMatrix(V.rows, rank);
    for (let i = 0; i < V.rows; i++) {
      for (let j = 0; j < rank; j++) {
        VT.values[i][j] = V.values[i][j];
      }
    }

    // Compute low-rank approximation: U_r * S_r * V_r^T
    const SVT = PrimeMath.multiplyMatrices(ST, PrimeMath.transposeMatrix(VT));
    const approx = PrimeMath.multiplyMatrices(UT, SVT);

    // Convert back to the original matrix format
    const result = MatrixCore.create(dim.rows, dim.cols, 0, {
      useTypedArray: matrix._isTypedArray,
      arrayType: matrix._arrayType,
    });

    for (let i = 0; i < dim.rows; i++) {
      for (let j = 0; j < dim.cols; j++) {
        result[i][j] = approx.values[i][j];
      }
    }

    return result;
  },

  /**
   * Validate inputs for matrix operations with enhanced error messages
   * @param {string} operation - Operation name
   * @param {Array} matrices - Array of matrices to validate
   * @returns {void}
   * @throws {Error} - Detailed error explaining the validation failure
   */
  validateWithDetails: function (operation, matrices) {
    const MatrixValidation = Prime.Math.MatrixValidation;
    const result = MatrixValidation.validateOperation(operation, matrices);

    if (!result.isValid) {
      // Check for specific common issues to provide more helpful messages
      if (matrices.length > 0) {
        // Check for NaN or Infinity values
        for (let i = 0; i < matrices.length; i++) {
          if (MatrixValidation.hasInvalidValues(matrices[i])) {
            throw new Prime.ValidationError(
              `Matrix ${i + 1} contains NaN or Infinity values which cannot be processed. ` +
                `Check for division by zero or overflow in previous calculations.`,
            );
          }
        }

        // For operations requiring square matrices
        const squareOps = [
          "determinant",
          "inverse",
          "eigenvalues",
          "choleskydecomposition",
          "ludecomposition",
          "qrdecomposition",
        ];
        if (
          squareOps.includes(operation.toLowerCase()) &&
          matrices[0].length !== matrices[0][0].length
        ) {
          throw new Prime.ValidationError(
            `The ${operation} operation requires a square matrix. ` +
              `Current dimensions: ${matrices[0].length}x${matrices[0][0].length}.`,
          );
        }

        // For multiplication
        if (operation.toLowerCase() === "multiply" && matrices.length === 2) {
          throw new Prime.ValidationError(
            `Matrix multiplication dimension mismatch. ` +
              `First matrix: ${matrices[0].length}x${matrices[0][0].length}, ` +
              `Second matrix: ${matrices[1].length}x${matrices[1][0].length}. ` +
              `The column count of the first matrix must match the row count of the second.`,
          );
        }
      }

      // If no specific error was thrown, fall back to the generic message
      throw new Prime.ValidationError(result.error);
    }
  },
};

// Add pseudoInverse and truncatedSVD to Matrix module
Prime.Math = Prime.Math || {};
Prime.Math.Matrix = Prime.Math.Matrix || {};
Prime.Math.Matrix.pseudoInverse = MatrixErrorHandling.pseudoInverse;
Prime.Math.Matrix.truncatedSVD = MatrixErrorHandling.truncatedSVD;

// Export the MatrixErrorHandling module
if (
  Object.getOwnPropertyDescriptor(Prime.Math, "MatrixErrorHandling") &&
  Object.getOwnPropertyDescriptor(Prime.Math, "MatrixErrorHandling").get
) {
  // Use a more careful approach to update the property
  const descriptor = Object.getOwnPropertyDescriptor(
    Prime.Math,
    "MatrixErrorHandling",
  );
  const originalGetter = descriptor.get;

  Object.defineProperty(Prime.Math, "MatrixErrorHandling", {
    get: function () {
      const result = originalGetter.call(this);
      // If result is an empty object (placeholder), return our implementation
      if (Object.keys(result).length === 0) {
        return MatrixErrorHandling;
      }
      // Otherwise, preserve what's already there
      return result;
    },
    configurable: true,
  });
} else {
  // Direct assignment if no getter exists
  Prime.Math.MatrixErrorHandling = MatrixErrorHandling;
}

// Export the enhanced Prime object
module.exports = Prime;
