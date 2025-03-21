/**
 * PrimeOS JavaScript Library - Matrix Math
 * Matrix operations and utilities
 */

// Import the Prime object
const Prime = require("../core");

// Create the Matrix module using IIFE
(function () {
  /**
   * Matrix operations for mathematical computations
   */
  const Matrix = {
    /**
     * Create a new matrix with specified dimensions
     * @param {number} rows - Number of rows
     * @param {number} cols - Number of columns
     * @param {number} [initialValue=0] - Initial value for all elements
     * @returns {Array} - New matrix with specified dimensions
     */
    create: function (rows, cols, initialValue = 0) {
      if (
        !Prime.Utils.isNumber(rows) ||
        rows <= 0 ||
        !Number.isInteger(rows) ||
        !Prime.Utils.isNumber(cols) ||
        cols <= 0 ||
        !Number.isInteger(cols)
      ) {
        throw new Prime.ValidationError("Dimensions must be positive integers");
      }

      return Array(rows)
        .fill()
        .map(() => Array(cols).fill(initialValue));
    },

    /**
     * Create an identity matrix of specified size
     * @param {number} size - Size of the identity matrix
     * @returns {Array} - Identity matrix
     */
    identity: function (size) {
      if (!Prime.Utils.isNumber(size) || size <= 0 || !Number.isInteger(size)) {
        throw new Prime.ValidationError("Size must be a positive integer");
      }

      const result = this.create(size, size, 0);
      for (let i = 0; i < size; i++) {
        result[i][i] = 1;
      }

      return result;
    },

    /**
     * Add two matrices element-wise
     * @param {Array} a - First matrix
     * @param {Array} b - Second matrix
     * @returns {Array} - Result of addition
     */
    add: function (a, b) {
      if (
        !Array.isArray(a) ||
        !Array.isArray(b) ||
        !a.every((row) => Array.isArray(row)) ||
        !b.every((row) => Array.isArray(row))
      ) {
        throw new Prime.ValidationError("Matrices must be 2D arrays");
      }

      const aRows = a.length;
      const aCols = a[0].length;
      const bRows = b.length;
      const bCols = b[0].length;

      if (aRows !== bRows || aCols !== bCols) {
        throw new Prime.ValidationError(
          "Matrices must have the same dimensions",
        );
      }

      const result = this.create(aRows, aCols);
      for (let i = 0; i < aRows; i++) {
        for (let j = 0; j < aCols; j++) {
          result[i][j] = a[i][j] + b[i][j];
        }
      }

      return result;
    },

    /**
     * Subtract matrix b from matrix a element-wise
     * @param {Array} a - First matrix
     * @param {Array} b - Second matrix
     * @returns {Array} - Result of subtraction
     */
    subtract: function (a, b) {
      if (
        !Array.isArray(a) ||
        !Array.isArray(b) ||
        !a.every((row) => Array.isArray(row)) ||
        !b.every((row) => Array.isArray(row))
      ) {
        throw new Prime.ValidationError("Matrices must be 2D arrays");
      }

      const aRows = a.length;
      const aCols = a[0].length;
      const bRows = b.length;
      const bCols = b[0].length;

      if (aRows !== bRows || aCols !== bCols) {
        throw new Prime.ValidationError(
          "Matrices must have the same dimensions",
        );
      }

      const result = this.create(aRows, aCols);
      for (let i = 0; i < aRows; i++) {
        for (let j = 0; j < aCols; j++) {
          result[i][j] = a[i][j] - b[i][j];
        }
      }

      return result;
    },

    /**
     * Multiply two matrices
     * @param {Array} a - First matrix
     * @param {Array} b - Second matrix
     * @returns {Array} - Result of multiplication
     */
    multiply: function (a, b) {
      if (
        !Array.isArray(a) ||
        !Array.isArray(b) ||
        !a.every((row) => Array.isArray(row)) ||
        !b.every((row) => Array.isArray(row))
      ) {
        throw new Prime.ValidationError("Matrices must be 2D arrays");
      }

      const aRows = a.length;
      const aCols = a[0].length;
      const bRows = b.length;
      const bCols = b[0].length;

      if (aCols !== bRows) {
        throw new Prime.ValidationError(
          "First matrix column count must match second matrix row count",
        );
      }

      const result = this.create(aRows, bCols);
      for (let i = 0; i < aRows; i++) {
        for (let j = 0; j < bCols; j++) {
          let sum = 0;
          for (let k = 0; k < aCols; k++) {
            sum += a[i][k] * b[k][j];
          }
          result[i][j] = sum;
        }
      }

      return result;
    },

    /**
     * Scale a matrix by a scalar
     * @param {Array} matrix - Matrix to scale
     * @param {number} scalar - Scaling factor
     * @returns {Array} - Scaled matrix
     */
    scale: function (matrix, scalar) {
      if (
        !Array.isArray(matrix) ||
        !matrix.every((row) => Array.isArray(row))
      ) {
        throw new Prime.ValidationError("Matrix must be a 2D array");
      }

      if (!Prime.Utils.isNumber(scalar)) {
        throw new Prime.ValidationError("Scalar must be a number");
      }

      const rows = matrix.length;
      const cols = matrix[0].length;
      const result = this.create(rows, cols);

      for (let i = 0; i < rows; i++) {
        for (let j = 0; j < cols; j++) {
          result[i][j] = matrix[i][j] * scalar;
        }
      }

      return result;
    },

    /**
     * Transpose a matrix
     * @param {Array} matrix - Matrix to transpose
     * @returns {Array} - Transposed matrix
     */
    transpose: function (matrix) {
      if (
        !Array.isArray(matrix) ||
        !matrix.every((row) => Array.isArray(row))
      ) {
        throw new Prime.ValidationError("Matrix must be a 2D array");
      }

      const rows = matrix.length;
      const cols = matrix[0].length;
      const result = this.create(cols, rows);

      for (let i = 0; i < rows; i++) {
        for (let j = 0; j < cols; j++) {
          result[j][i] = matrix[i][j];
        }
      }

      return result;
    },

    /**
     * Calculate the determinant of a square matrix
     * @param {Array} matrix - Square matrix
     * @returns {number} - Determinant
     */
    determinant: function (matrix) {
      if (
        !Array.isArray(matrix) ||
        !matrix.every((row) => Array.isArray(row))
      ) {
        throw new Prime.ValidationError("Matrix must be a 2D array");
      }

      const rows = matrix.length;
      const cols = matrix[0].length;

      if (rows !== cols) {
        throw new Prime.ValidationError("Matrix must be square");
      }

      // Base case for 1x1 matrix
      if (rows === 1) {
        return matrix[0][0];
      }

      // Base case for 2x2 matrix
      if (rows === 2) {
        return matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0];
      }

      // Recursive case for larger matrices
      let det = 0;
      const sign = 1;

      for (let j = 0; j < cols; j++) {
        det += sign * matrix[0][j] * this.cofactor(matrix, 0, j);
        // Toggle sign for next iteration
      }

      return det;
    },

    /**
     * Calculate the cofactor of a matrix element
     * @private
     * @param {Array} matrix - Original matrix
     * @param {number} row - Row index
     * @param {number} col - Column index
     * @returns {number} - Cofactor
     */
    cofactor: function (matrix, row, col) {
      const minor = this.minor(matrix, row, col);
      return ((row + col) % 2 === 0 ? 1 : -1) * this.determinant(minor);
    },

    /**
     * Calculate the minor of a matrix element
     * @private
     * @param {Array} matrix - Original matrix
     * @param {number} row - Row index to exclude
     * @param {number} col - Column index to exclude
     * @returns {Array} - Minor matrix
     */
    minor: function (matrix, row, col) {
      const rows = matrix.length;
      const minor = [];

      for (let i = 0; i < rows; i++) {
        if (i === row) continue;

        const minorRow = [];
        for (let j = 0; j < rows; j++) {
          if (j === col) continue;
          minorRow.push(matrix[i][j]);
        }

        minor.push(minorRow);
      }

      return minor;
    },

    /**
     * Calculate the inverse of a matrix
     * @param {Array} matrix - Matrix to invert
     * @returns {Array} - Inverted matrix
     */
    inverse: function (matrix) {
      if (
        !Array.isArray(matrix) ||
        !matrix.every((row) => Array.isArray(row))
      ) {
        throw new Prime.ValidationError("Matrix must be a 2D array");
      }

      const rows = matrix.length;
      const cols = matrix[0].length;

      if (rows !== cols) {
        throw new Prime.ValidationError("Matrix must be square");
      }

      const det = this.determinant(matrix);

      if (Math.abs(det) < 1e-10) {
        throw new Prime.MathematicalError(
          "Matrix is singular and cannot be inverted",
        );
      }

      // For 2x2 matrices, use direct formula for efficiency
      if (rows === 2) {
        const result = this.create(2, 2);
        const invDet = 1 / det;

        result[0][0] = matrix[1][1] * invDet;
        result[0][1] = -matrix[0][1] * invDet;
        result[1][0] = -matrix[1][0] * invDet;
        result[1][1] = matrix[0][0] * invDet;

        return result;
      }

      // For larger matrices, calculate adjugate and scale
      const adjugate = this.create(rows, cols);

      for (let i = 0; i < rows; i++) {
        for (let j = 0; j < cols; j++) {
          adjugate[j][i] = this.cofactor(matrix, i, j);
        }
      }

      return this.scale(adjugate, 1 / det);
    },

    /**
     * Solve a system of linear equations Ax = b
     * @param {Array} A - Coefficient matrix
     * @param {Array} b - Right-hand side vector
     * @returns {Array} - Solution vector
     */
    solve: function (A, b) {
      if (!Array.isArray(A) || !A.every((row) => Array.isArray(row))) {
        throw new Prime.ValidationError(
          "Coefficient matrix must be a 2D array",
        );
      }

      if (!Array.isArray(b) || b.some((item) => Array.isArray(item))) {
        throw new Prime.ValidationError("Right-hand side must be a 1D array");
      }

      const rows = A.length;
      const cols = A[0].length;

      if (rows !== cols) {
        throw new Prime.ValidationError("Coefficient matrix must be square");
      }

      if (rows !== b.length) {
        throw new Prime.ValidationError("Matrix rows must match vector length");
      }

      // Create a column vector from b
      const bVector = b.map((val) => [val]);

      // Solve by multiplying the inverse of A with b
      const inverse = this.inverse(A);
      const result = this.multiply(inverse, bVector);

      // Flatten the result to a 1D array
      return result.map((row) => row[0]);
    },
  };

  // Add Matrix to the Prime.Math namespace
  Prime.Math = Prime.Math || {};
  Prime.Math.Matrix = Matrix;
})();

// Export the enhanced Prime object
module.exports = Prime;
