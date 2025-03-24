/**
 * PrimeOS SVD Integration Module
 * Provides integration between the enhanced SVD implementation and the main PrimeMath module
 * Makes the enhanced SVD the default implementation for all SVD operations
 */

// Import the enhanced SVD implementation
const enhancedSVD = require('./enhanced-svd.js');
const enhancedSVDContext = require('./enhanced-svd-integration.js');
const Prime = require('../../core/prime.js');
const StandardizedMath = require('./standardized-math.js');
const TypeValidation = require('./type-validation.js');

/**
 * Make enhanced SVD the default implementation for PrimeMath
 * @param {Object} PrimeMath - The PrimeMath module to enhance
 * @returns {Object} - Enhanced PrimeMath module with better SVD
 */
function integrateEnhancedSVD(PrimeMath) {
  if (!PrimeMath) {
    // Try importing PrimeMath if not provided
    try {
      PrimeMath = require('./prime-math.js');
    } catch (error) {
      console.error('Failed to import PrimeMath module:', error.message);
      return null;
    }
  }

  if (!PrimeMath) {
    console.error('PrimeMath module is not available');
    return null;
  }

  // Create an SVD wrapper that correctly adapts inputs and outputs
  // to match the expected interfaces
  const originalSVD = PrimeMath.svd || function() { 
    throw new Error('SVD implementation not available in PrimeMath');
  };

  /**
   * Enhanced SVD function that uses the more robust implementation
   * but maintains the same interface as the original
   * 
   * @param {Matrix|Array<Array<number>>} matrix - Matrix to decompose
   * @param {Object} [options={}] - SVD options
   * @returns {Object} - SVD decomposition {U, S, V}
   */
  PrimeMath.svd = function(matrix, options = {}) {
    // Handle both native matrix objects and 2D arrays
    let values;
    let isMatrixObject = false;
    let rows, cols;

    try {
      // Check if input is a Matrix object or 2D array
      if (matrix && typeof matrix === 'object' && 'values' in matrix) {
        // It's a PrimeMath Matrix object
        values = matrix.values;
        rows = matrix.rows;
        cols = matrix.cols;
        isMatrixObject = true;
      } else if (Array.isArray(matrix)) {
        if (Array.isArray(matrix[0])) {
          // It's a 2D array
          values = matrix;
          rows = matrix.length;
          cols = matrix[0].length;
        } else {
          // It might be a 1D array that needs to be converted to a column vector
          values = matrix.map(val => [val]);
          rows = matrix.length;
          cols = 1;
        }
      } else {
        throw new Prime.ValidationError('Matrix must be a Matrix object or 2D array');
      }

      // Validate the matrix values
      TypeValidation.assertMatrix(values, 'matrix', { operation: 'svd' });

      // Prepare enhanced SVD options
      const enhancedOptions = {
        algorithm: options.algorithm || 'auto',
        useScaling: options.useScaling !== false,
        maxIterations: options.maxIterations || 150,
        tolerance: options.tolerance || 1e-14,
        thin: options.thin || false
      };

      // Use the enhanced SVD implementation with error context
      const result = enhancedSVDContext.computeSVDWithErrorContext(values, enhancedOptions);

      if (isMatrixObject) {
        // If input was a Matrix object, return result as Matrix objects
        return {
          U: PrimeMath.createMatrix(result.U),
          S: createDiagonalMatrixFromS(result.S, rows, cols, PrimeMath),
          V: PrimeMath.createMatrix(result.V)
        };
      } else {
        // For 2D array input, return 2D arrays
        return {
          U: result.U,
          S: result.S,
          V: result.V
        };
      }
    } catch (error) {
      // If enhanced SVD fails, try using the original implementation
      console.warn(`Enhanced SVD failed: ${error.message}. Trying original implementation.`);
      
      try {
        return originalSVD.call(PrimeMath, matrix, options);
      } catch (fallbackError) {
        // If both implementations fail, provide detailed error information
        const errorContext = {
          operation: 'svd',
          matrixShape: isMatrixObject ? [rows, cols] : (Array.isArray(matrix) ? 
            [matrix.length, Array.isArray(matrix[0]) ? matrix[0].length : 1] : 'unknown'),
          enhancedSVDError: error.message,
          originalSVDError: fallbackError.message
        };
        
        throw new Prime.MathematicalError(
          `SVD computation failed in all implementations: ${error.message}`, 
          errorContext
        );
      }
    }
  };

  // Add the enhanced SVD directly to the PrimeMath interface
  PrimeMath.enhancedSVD = enhancedSVD;
  
  // Add the SVD with metrics and error context
  PrimeMath.svdWithMetrics = enhancedSVDContext.computeSVDWithErrorContext;

  return PrimeMath;
}

/**
 * Helper function to create a diagonal matrix from singular values
 * @private
 */
function createDiagonalMatrixFromS(S, rows, cols, PrimeMath) {
  // If S is already a 2D array, use it directly
  if (Array.isArray(S) && Array.isArray(S[0])) {
    return PrimeMath.createMatrix(S);
  }
  
  // Otherwise, create a diagonal matrix from the singular values
  const minDim = Math.min(rows, cols);
  const sMatrix = PrimeMath.createMatrix(rows, cols);
  
  // Fill the diagonal with singular values
  for (let i = 0; i < minDim; i++) {
    if (Array.isArray(S)) {
      sMatrix.values[i][i] = S[i];
    } else {
      // Handle case where S is a single value
      sMatrix.values[0][0] = S;
    }
  }
  
  return sMatrix;
}

// Export the integration function and enhanced SVD
module.exports = {
  integrateEnhancedSVD,
  enhancedSVD,
  svdWithMetrics: enhancedSVDContext.computeSVDWithErrorContext
};

// Automatically integrate if possible
try {
  const PrimeMath = require('./prime-math.js');
  integrateEnhancedSVD(PrimeMath);
} catch (error) {
  console.log('Auto-integration of enhanced SVD failed:', error.message);
}