/**
 * PrimeOS Enhanced SVD Integration
 * Integrates the enhanced SVD implementation with the StandardizedMath interface
 * and adds comprehensive error handling with context
 */

// Import direct dependencies
const Prime = require("../../core/prime.js");

// Import specialized error classes directly from core/error.js
const CoreErrors = require("../../core/error.js");

// Import ErrorContext from StandardizedMath
const { ErrorContext } = require("./standardized-math.js");
const enhancedSVD = require("./enhanced-svd.js");

/**
 * Computes the Singular Value Decomposition (SVD) of a matrix with enhanced
 * error handling and context information for debugging
 *
 * @param {Array<Array<number>>} matrix - Input matrix
 * @param {Object} [options={}] - Algorithm options
 * @returns {Object} SVD decomposition {U, S, V} with additional metadata
 */
function computeSVDWithErrorContext(matrix, options = {}) {
  // Validate input
  if (!Array.isArray(matrix) || !matrix.length || !Array.isArray(matrix[0])) {
    const context = ErrorContext.create(
      "StandardizedMath.Matrix.svdWithMetrics",
      { matrix },
    );
    throw new CoreErrors.Errors.ValidationError(
      "Matrix must be a 2D array",
      context,
    );
  }

  try {
    // Dynamically try loading PrimeMath
    const PrimeMath = require("../../../src/mathematics.js").Math;
    if (
      PrimeMath &&
      PrimeMath.MatrixValidation &&
      PrimeMath.MatrixValidation.isMatrix
    ) {
      if (!PrimeMath.MatrixValidation.isMatrix(matrix)) {
        const context = ErrorContext.create(
          "StandardizedMath.Matrix.svdWithMetrics",
          { matrix },
        );
        throw new CoreErrors.Errors.ValidationError(
          "Matrix does not pass PrimeMath validation",
          context,
        );
      }
    }
  } catch (e) {
    // Ignore errors from trying to load PrimeMath - we'll use our fallback validation
  }

  // Analyze the matrix for potential numerical issues
  const analysis = analyzeMatrixForSVD(matrix);

  // Add the analysis to options for enhanced SVD
  const enhancedOptions = {
    ...options,
    analysisMetadata: analysis,
  };

  try {
    // Compute SVD using the enhanced implementation
    const result = enhancedSVD(matrix, enhancedOptions);

    // Append analysis metadata to the result
    return {
      ...result,
      metadata: {
        ...analysis,
        successMethod: result.algorithm || enhancedOptions.algorithm || "auto",
      },
    };
  } catch (error) {
    // Capture the error context for better diagnostics
    const errorContext = ErrorContext.create(
      "StandardizedMath.Matrix.svdWithMetrics",
      { matrix },
      {
        ...analysis,
        attemptedAlgorithm: enhancedOptions.algorithm || "auto",
        originalError: error.message,
      },
    );

    // Map the error to appropriate specialized error class
    if (
      error.message.includes("singular") ||
      error.message.includes("Singular")
    ) {
      throw new CoreErrors.Errors.MatrixSingularityError(
        "Matrix is singular or near-singular for SVD computation",
        errorContext,
      );
    } else if (
      error.message.includes("convergence") ||
      error.message.includes("iterations")
    ) {
      throw new CoreErrors.Errors.ConvergenceError(
        "SVD algorithm failed to converge within the allowed iterations",
        errorContext,
      );
    } else if (
      error.message.includes("overflow") ||
      error.message.includes("underflow") ||
      error.message.includes("NaN")
    ) {
      throw new CoreErrors.Errors.NumericOverflowError(
        "Numeric overflow/underflow encountered during SVD computation",
        errorContext,
      );
    } else if (error.message.includes("dimension")) {
      throw new CoreErrors.Errors.DimensionMismatchError(
        "Invalid matrix dimensions for SVD computation",
        errorContext,
      );
    } else {
      // For unrecognized errors, wrap in NumericalInstabilityError
      throw new CoreErrors.Errors.NumericalInstabilityError(
        `SVD computation failed: ${error.message}`,
        errorContext,
      );
    }
  }
}

/**
 * Analyzes a matrix to detect potential numerical issues for SVD
 * @param {Array<Array<number>>} matrix - Input matrix
 * @returns {Object} Matrix analysis results
 */
function analyzeMatrixForSVD(matrix) {
  const rows = matrix.length;
  const cols = matrix[0].length;

  let maxAbs = 0;
  let minNonZero = Infinity;
  let sumSquares = 0;
  let hasZeroRows = false;
  let hasZeroCols = false;
  let zeroRowsCount = 0;
  let zeroColsCount = 0;

  // Analyze row sums to detect zero rows
  const rowSums = new Array(rows).fill(0);
  const colSums = new Array(cols).fill(0);

  // First pass: find max/min values and row/column sums
  for (let i = 0; i < rows; i++) {
    for (let j = 0; j < cols; j++) {
      const value = matrix[i][j];
      const absValue = Math.abs(value);

      // Track max and min non-zero absolute values
      if (absValue > 0) {
        maxAbs = Math.max(maxAbs, absValue);
        minNonZero = Math.min(minNonZero, absValue);
      }

      // Accumulate to Frobenius norm calculation
      sumSquares += value * value;

      // Accumulate to row and column sums for zero detection
      rowSums[i] += absValue;
      colSums[j] += absValue;
    }
  }

  // Check for zero rows and columns
  for (let i = 0; i < rows; i++) {
    if (rowSums[i] === 0) {
      hasZeroRows = true;
      zeroRowsCount++;
    }
  }

  for (let j = 0; j < cols; j++) {
    if (colSums[j] === 0) {
      hasZeroCols = true;
      zeroColsCount++;
    }
  }

  // Calculate Frobenius norm and other metrics
  const frobeniusNorm = Math.sqrt(sumSquares);
  const dynamicRange =
    minNonZero < Infinity ? maxAbs / minNonZero : maxAbs > 0 ? Infinity : 0;
  const rank = Math.min(rows, cols) - Math.max(zeroRowsCount, zeroColsCount);

  // Estimate condition number based on dynamic range (rough approximation)
  const estimatedConditionNumber = dynamicRange;

  // Determine if the matrix has extreme values
  const hasExtremeValues =
    maxAbs > 1e100 || (minNonZero < 1e-100 && minNonZero > 0);
  const isExtremelySmall = maxAbs > 0 && maxAbs < 1e-100;
  const isExtremelyLarge = minNonZero > 1e100;

  // Estimate numerical stability risk based on values
  let numericalStabilityRisk = "low";
  if (hasExtremeValues || estimatedConditionNumber > 1e12) {
    numericalStabilityRisk = "high";
  } else if (estimatedConditionNumber > 1e8) {
    numericalStabilityRisk = "medium";
  }

  return {
    dimensions: { rows, cols },
    maxAbsValue: maxAbs,
    minNonZeroValue: minNonZero === Infinity ? 0 : minNonZero,
    frobeniusNorm,
    dynamicRange,
    estimatedRank: rank,
    hasZeroRows,
    hasZeroCols,
    zeroRowsCount,
    zeroColsCount,
    hasExtremeValues,
    isExtremelySmall,
    isExtremelyLarge,
    estimatedConditionNumber,
    numericalStabilityRisk,
  };
}

/**
 * Returns SVD implementation based on a matrix analysis for StandardizedMath
 * Wraps the enhanced SVD with additional error handling and diagnostics
 */
module.exports = {
  computeSVDWithErrorContext,
  analyzeMatrixForSVD,
};
