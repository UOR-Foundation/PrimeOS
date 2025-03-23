/**
 * PrimeOS JavaScript Library - Matrix Math
 * Matrix operations and utilities
 * This module serves as a facade for specialized matrix operation modules
 */

// Import the Prime object
const Prime = require('../core');

// Ensure required modules are loaded
require('./matrix-core');
require('./matrix-advanced');
require('./matrix-validation');

// Create the Matrix module using IIFE
(function () {
  /**
   * Matrix operations for mathematical computations
   * Provides a unified interface to specialized matrix modules
   */
  const Matrix = {
    /**
     * Create a new matrix with specified dimensions
     * @param {number} rows - Number of rows
     * @param {number} cols - Number of columns
     * @param {number} [initialValue=0] - Initial value for all elements
     * @param {Object} [options={}] - Additional options
     * @returns {Array|TypedArray} - New matrix with specified dimensions
     */
    create: function (rows, cols, initialValue = 0, options = {}) {
      return Prime.Math.MatrixCore.create(rows, cols, initialValue, options);
    },

    /**
     * Create an identity matrix of specified size
     * @param {number} size - Size of the identity matrix
     * @param {Object} [options={}] - Additional options
     * @returns {Array|TypedArray} - Identity matrix
     */
    identity: function (size, options = {}) {
      return Prime.Math.MatrixCore.identity(size, options);
    },

    /**
     * Check if a value is a matrix (array of arrays or typed matrix)
     * @param {*} value - Value to check
     * @returns {boolean} - True if the value is a matrix
     */
    isMatrix: function (value) {
      return Prime.Math.MatrixValidation.isMatrix(value);
    },

    /**
     * Get the dimensions of a matrix
     * @param {Array|TypedArray} matrix - Matrix to get dimensions of
     * @returns {Object} - Object with rows and cols properties
     */
    dimensions: function (matrix) {
      return Prime.Math.MatrixCore.dimensions(matrix);
    },

    /**
     * Add two matrices element-wise
     * @param {Array|TypedArray} a - First matrix
     * @param {Array|TypedArray} b - Second matrix
     * @param {Array|TypedArray} [result] - Optional result matrix (for in-place operations)
     * @returns {Array|TypedArray} - Result of addition
     */
    add: function (a, b, result) {
      return Prime.Math.MatrixCore.add(a, b, result);
    },

    /**
     * Subtract matrix b from matrix a element-wise
     * @param {Array|TypedArray} a - First matrix
     * @param {Array|TypedArray} b - Second matrix
     * @param {Array|TypedArray} [result] - Optional result matrix (for in-place operations)
     * @returns {Array|TypedArray} - Result of subtraction
     */
    subtract: function (a, b, result) {
      return Prime.Math.MatrixCore.subtract(a, b, result);
    },

    /**
     * Multiply two matrices
     * @param {Array|TypedArray} a - First matrix
     * @param {Array|TypedArray} b - Second matrix
     * @param {Array|TypedArray} [result] - Optional result matrix (for in-place operations)
     * @returns {Array|TypedArray} - Result of multiplication
     */
    multiply: function (a, b, result) {
      return Prime.Math.MatrixCore.multiply(a, b, result);
    },

    /**
     * Scale a matrix by a scalar
     * @param {Array|TypedArray} matrix - Matrix to scale
     * @param {number} scalar - Scaling factor
     * @param {Array|TypedArray} [result] - Optional result matrix (for in-place operations)
     * @returns {Array|TypedArray} - Scaled matrix
     */
    scale: function (matrix, scalar, result) {
      return Prime.Math.MatrixCore.scale(matrix, scalar, result);
    },

    /**
     * Transpose a matrix
     * @param {Array|TypedArray} matrix - Matrix to transpose
     * @param {Array|TypedArray} [result] - Optional result matrix (for in-place operations)
     * @returns {Array|TypedArray} - Transposed matrix
     */
    transpose: function (matrix, result) {
      return Prime.Math.MatrixCore.transpose(matrix, result);
    },

    /**
     * Calculate the determinant of a square matrix
     * @param {Array|TypedArray} matrix - Square matrix
     * @returns {number} - Determinant
     */
    determinant: function (matrix) {
      return Prime.Math.MatrixAdvanced.determinant(matrix);
    },

    /**
     * Calculate the cofactor of a matrix element
     * @private
     * @param {Array|TypedArray} matrix - Original matrix
     * @param {number} row - Row index
     * @param {number} col - Column index
     * @returns {number} - Cofactor
     */
    cofactor: function (matrix, row, col) {
      return Prime.Math.MatrixAdvanced.cofactor(matrix, row, col);
    },

    /**
     * Calculate the minor of a matrix element
     * @private
     * @param {Array|TypedArray} matrix - Original matrix
     * @param {number} row - Row index to exclude
     * @param {number} col - Column index to exclude
     * @returns {Array|TypedArray} - Minor matrix
     */
    minor: function (matrix, row, col) {
      return Prime.Math.MatrixAdvanced.minor(matrix, row, col);
    },

    /**
     * Calculate the inverse of a matrix
     * @param {Array|TypedArray} matrix - Matrix to invert
     * @returns {Array|TypedArray} - Inverted matrix
     */
    inverse: function (matrix) {
      return Prime.Math.MatrixAdvanced.inverse(matrix);
    },

    /**
     * Solve a system of linear equations Ax = b
     * @param {Array|TypedArray} A - Coefficient matrix
     * @param {Array} b - Right-hand side vector
     * @returns {Array} - Solution vector
     */
    solve: function (A, b) {
      return Prime.Math.MatrixAdvanced.solve(A, b);
    },

    /**
     * Create a deep copy of a matrix
     * @param {Array|TypedArray} matrix - Matrix to clone
     * @returns {Array|TypedArray} - New copy of the matrix
     */
    clone: function (matrix) {
      return Prime.Math.MatrixCore.clone(matrix);
    },

    /**
     * Copy values from one matrix to another
     * @param {Array|TypedArray} source - Source matrix
     * @param {Array|TypedArray} destination - Destination matrix
     * @returns {Array|TypedArray} - Destination matrix (modified in-place)
     */
    copy: function (source, destination) {
      return Prime.Math.MatrixCore.copy(source, destination);
    },

    /**
     * Element-wise multiplication of two matrices (Hadamard product)
     * @param {Array|TypedArray} a - First matrix
     * @param {Array|TypedArray} b - Second matrix
     * @param {Array|TypedArray} [result] - Optional result matrix (for in-place operations)
     * @returns {Array|TypedArray} - Result of element-wise multiplication
     */
    elementWiseMultiply: function (a, b, result) {
      return Prime.Math.MatrixCore.elementWiseMultiply(a, b, result);
    },

    /**
     * Calculate LU decomposition of a matrix
     * @param {Array|TypedArray} matrix - Matrix to decompose
     * @returns {Object} - Object containing L and U matrices
     */
    luDecomposition: function (matrix) {
      return Prime.Math.MatrixAdvanced.luDecomposition(matrix);
    },

    /**
     * Compute QR decomposition using Gram-Schmidt process
     * @param {Array|TypedArray} matrix - Matrix to decompose
     * @returns {Object} - Object containing Q and R matrices
     */
    qrDecomposition: function (matrix) {
      return Prime.Math.MatrixAdvanced.qrDecomposition(matrix);
    },

    /**
     * Compute eigenvalues and eigenvectors of a symmetric matrix
     * @param {Array|TypedArray} matrix - Symmetric matrix
     * @param {Object} [options={}] - Options
     * @returns {Object} - Object containing eigenvalues and eigenvectors
     */
    eigenvalues: function (matrix, options = {}) {
      return Prime.Math.MatrixAdvanced.eigenvalues(matrix, options);
    },

    /**
     * Compute Cholesky decomposition of a positive-definite matrix
     * @param {Array|TypedArray} matrix - Positive-definite matrix
     * @returns {Array|TypedArray} - Lower triangular matrix L where matrix = L * L^T
     */
    choleskyDecomposition: function (matrix) {
      return Prime.Math.MatrixAdvanced.choleskyDecomposition(matrix);
    },

    /**
     * Calculate the matrix trace (sum of diagonal elements)
     * @param {Array|TypedArray} matrix - Matrix
     * @returns {number} - Trace
     */
    trace: function (matrix) {
      return Prime.Math.MatrixAdvanced.trace(matrix);
    },

    /**
     * Calculate the matrix rank using Gaussian elimination
     * @param {Array|TypedArray} matrix - Matrix
     * @param {number} [tolerance=1e-10] - Numerical tolerance for zero
     * @returns {number} - Rank of the matrix
     */
    rank: function (matrix, tolerance = 1e-10) {
      return Prime.Math.MatrixAdvanced.rank(matrix, tolerance);
    },

    /**
     * Check if a matrix is square (has the same number of rows and columns)
     * @param {Array|TypedArray} matrix - Matrix to check
     * @returns {boolean} - True if the matrix is square
     */
    isSquare: function (matrix) {
      return Prime.Math.MatrixValidation.isSquare(matrix);
    },

    /**
     * Check if a matrix is symmetric (equal to its transpose)
     * @param {Array|TypedArray} matrix - Matrix to check
     * @param {number} [tolerance=1e-10] - Tolerance for floating-point comparisons
     * @returns {boolean} - True if the matrix is symmetric
     */
    isSymmetric: function (matrix, tolerance = 1e-10) {
      return Prime.Math.MatrixValidation.isSymmetric(matrix, tolerance);
    },

    /**
     * Check if a matrix is invertible (non-singular)
     * @param {Array|TypedArray} matrix - Matrix to check
     * @param {number} [tolerance=1e-10] - Tolerance for determinant near zero
     * @returns {boolean} - True if the matrix is invertible
     */
    isInvertible: function (matrix, tolerance = 1e-10) {
      return Prime.Math.MatrixValidation.isInvertible(matrix, tolerance);
    },

    /**
     * Check if a matrix is orthogonal (its transpose equals its inverse)
     * @param {Array|TypedArray} matrix - Matrix to check
     * @param {number} [tolerance=1e-10] - Tolerance for floating-point comparisons
     * @returns {boolean} - True if the matrix is orthogonal
     */
    isOrthogonal: function (matrix, tolerance = 1e-10) {
      return Prime.Math.MatrixValidation.isOrthogonal(matrix, tolerance);
    },

    /**
     * Fill a matrix with a specific value
     * @param {Array|TypedArray} matrix - Matrix to fill
     * @param {number} value - Value to fill the matrix with
     * @returns {Array|TypedArray} - Filled matrix (modified in-place)
     */
    fill: function (matrix, value) {
      return Prime.Math.MatrixCore.fill(matrix, value);
    },
  };

  // Add Matrix to the Prime.Math namespace
  Prime.Math = Prime.Math || {};

  // Check if Matrix already has a getter defined, if so, use it
  if (
    Object.getOwnPropertyDescriptor(Prime.Math, 'Matrix') &&
    Object.getOwnPropertyDescriptor(Prime.Math, 'Matrix').get
  ) {
    // Use a more careful approach to update the property
    const descriptor = Object.getOwnPropertyDescriptor(Prime.Math, 'Matrix');
    const originalGetter = descriptor.get;

    Object.defineProperty(Prime.Math, 'Matrix', {
      get: function () {
        const result = originalGetter.call(this);
        // If result is an empty object (placeholder), return our implementation
        if (Object.keys(result).length === 0) {
          return Matrix;
        }
        // Otherwise, preserve what's already there
        return result;
      },
      configurable: true,
    });
  } else {
    // Direct assignment if no getter exists
    Prime.Math.Matrix = Matrix;
  }
})();

// Export the enhanced Prime object
module.exports = Prime;
