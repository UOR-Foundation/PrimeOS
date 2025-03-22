/**
 * PrimeOS JavaScript Library - Math
 * Matrix Validation
 * Validation utilities for matrix operations
 */

// Import the Prime object
const Prime = require("../core");

/**
 * Matrix validation utilities
 */
const MatrixValidation = {
  /**
   * Check if a value is a valid matrix (2D array or typed matrix)
   * @param {*} value - Value to check
   * @returns {boolean} - True if the value is a valid matrix
   */
  isMatrix: function (value) {
    const MatrixCore = Prime.Math.MatrixCore;
    return MatrixCore && MatrixCore.isMatrix ? MatrixCore.isMatrix(value) : 
      (Array.isArray(value) && 
       value.length > 0 && 
       Array.isArray(value[0]));
  },
  
  /**
   * Check if a matrix is square (has the same number of rows and columns)
   * @param {Array|TypedArray} matrix - Matrix to check
   * @returns {boolean} - True if the matrix is square
   */
  isSquare: function (matrix) {
    if (!this.isMatrix(matrix)) {
      return false;
    }
    
    const MatrixCore = Prime.Math.MatrixCore;
    const dim = MatrixCore ? MatrixCore.dimensions(matrix) : 
      { rows: matrix.length, cols: matrix[0].length };
    
    return dim.rows === dim.cols;
  },
  
  /**
   * Check if matrix dimensions are valid (non-negative integers)
   * @param {number} rows - Number of rows
   * @param {number} cols - Number of columns
   * @returns {boolean} - True if the dimensions are valid
   */
  isValidDimensions: function (rows, cols) {
    return (
      Prime.Utils.isNumber(rows) &&
      rows >= 0 &&
      Number.isInteger(rows) &&
      Prime.Utils.isNumber(cols) &&
      cols >= 0 &&
      Number.isInteger(cols)
    );
  },
  
  /**
   * Check if two matrices have the same dimensions
   * @param {Array|TypedArray} a - First matrix
   * @param {Array|TypedArray} b - Second matrix
   * @returns {boolean} - True if matrices have the same dimensions
   */
  haveSameDimensions: function (a, b) {
    if (!this.isMatrix(a) || !this.isMatrix(b)) {
      return false;
    }
    
    const MatrixCore = Prime.Math.MatrixCore;
    
    if (MatrixCore && MatrixCore.dimensions) {
      const aDim = MatrixCore.dimensions(a);
      const bDim = MatrixCore.dimensions(b);
      return aDim.rows === bDim.rows && aDim.cols === bDim.cols;
    }
    
    // Fallback calculation
    return a.length === b.length && a[0].length === b[0].length;
  },
  
  /**
   * Check if matrices are compatible for multiplication (a.cols === b.rows)
   * @param {Array|TypedArray} a - First matrix
   * @param {Array|TypedArray} b - Second matrix
   * @returns {boolean} - True if matrices are compatible for multiplication
   */
  areMultiplicable: function (a, b) {
    if (!this.isMatrix(a) || !this.isMatrix(b)) {
      return false;
    }
    
    const MatrixCore = Prime.Math.MatrixCore;
    
    if (MatrixCore && MatrixCore.dimensions) {
      const aDim = MatrixCore.dimensions(a);
      const bDim = MatrixCore.dimensions(b);
      return aDim.cols === bDim.rows;
    }
    
    // Fallback calculation
    return a[0].length === b.length;
  },
  
  /**
   * Check if a matrix is symmetric (equal to its transpose)
   * @param {Array|TypedArray} matrix - Matrix to check
   * @param {number} [tolerance=1e-10] - Tolerance for floating-point comparisons
   * @returns {boolean} - True if the matrix is symmetric
   */
  isSymmetric: function (matrix, tolerance = 1e-10) {
    if (!this.isSquare(matrix)) {
      return false;
    }
    
    const MatrixCore = Prime.Math.MatrixCore;
    const n = MatrixCore ? MatrixCore.dimensions(matrix).rows : matrix.length;
    
    for (let i = 0; i < n; i++) {
      for (let j = i + 1; j < n; j++) {
        if (Math.abs(matrix[i][j] - matrix[j][i]) > tolerance) {
          return false;
        }
      }
    }
    
    return true;
  },
  
  /**
   * Check if a matrix is diagonal (all non-diagonal elements are zero)
   * @param {Array|TypedArray} matrix - Matrix to check
   * @param {number} [tolerance=1e-10] - Tolerance for floating-point comparisons
   * @returns {boolean} - True if the matrix is diagonal
   */
  isDiagonal: function (matrix, tolerance = 1e-10) {
    if (!this.isSquare(matrix)) {
      return false;
    }
    
    const MatrixCore = Prime.Math.MatrixCore;
    const n = MatrixCore ? MatrixCore.dimensions(matrix).rows : matrix.length;
    
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        if (i !== j && Math.abs(matrix[i][j]) > tolerance) {
          return false;
        }
      }
    }
    
    return true;
  },
  
  /**
   * Check if a matrix is an identity matrix
   * @param {Array|TypedArray} matrix - Matrix to check
   * @param {number} [tolerance=1e-10] - Tolerance for floating-point comparisons
   * @returns {boolean} - True if the matrix is an identity matrix
   */
  isIdentity: function (matrix, tolerance = 1e-10) {
    if (!this.isSquare(matrix)) {
      return false;
    }
    
    const MatrixCore = Prime.Math.MatrixCore;
    const n = MatrixCore ? MatrixCore.dimensions(matrix).rows : matrix.length;
    
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        const expected = i === j ? 1 : 0;
        if (Math.abs(matrix[i][j] - expected) > tolerance) {
          return false;
        }
      }
    }
    
    return true;
  },
  
  /**
   * Check if a matrix is invertible (non-singular)
   * @param {Array|TypedArray} matrix - Matrix to check
   * @param {number} [tolerance=1e-10] - Tolerance for determinant near zero
   * @returns {boolean} - True if the matrix is invertible
   */
  isInvertible: function (matrix, tolerance = 1e-10) {
    if (!this.isSquare(matrix)) {
      return false;
    }
    
    try {
      const MatrixAdvanced = Prime.Math.MatrixAdvanced;
      const det = MatrixAdvanced.determinant(matrix);
      return Math.abs(det) > tolerance;
    } catch (error) {
      return false;
    }
  },
  
  /**
   * Check if a matrix has all positive eigenvalues (positive-definite)
   * @param {Array|TypedArray} matrix - Matrix to check
   * @param {number} [tolerance=1e-10] - Tolerance for eigenvalue positivity
   * @returns {boolean} - True if the matrix is positive-definite
   */
  isPositiveDefinite: function (matrix, tolerance = 1e-10) {
    if (!this.isSquare(matrix) || !this.isSymmetric(matrix)) {
      return false;
    }
    
    try {
      // Try Cholesky decomposition (only works for positive-definite matrices)
      const MatrixAdvanced = Prime.Math.MatrixAdvanced;
      MatrixAdvanced.choleskyDecomposition(matrix);
      return true;
    } catch (error) {
      return false;
    }
  },
  
  /**
   * Check if a matrix is orthogonal (its transpose equals its inverse)
   * @param {Array|TypedArray} matrix - Matrix to check
   * @param {number} [tolerance=1e-10] - Tolerance for floating-point comparisons
   * @returns {boolean} - True if the matrix is orthogonal
   */
  isOrthogonal: function (matrix, tolerance = 1e-10) {
    if (!this.isSquare(matrix)) {
      return false;
    }
    
    const MatrixCore = Prime.Math.MatrixCore;
    
    if (MatrixCore) {
      // Multiply matrix by its transpose, should be identity
      const transpose = MatrixCore.transpose(matrix);
      const product = MatrixCore.multiply(matrix, transpose);
      
      // Check if product is identity
      return this.isIdentity(product, tolerance);
    }
    
    return false;
  },
  
  /**
   * Validate that an operation can be performed with the given matrices
   * @param {string} operation - Operation name ('add', 'multiply', etc.)
   * @param {Array<Array|TypedArray>} matrices - Matrices to validate
   * @returns {Object} - Object with isValid flag and error message
   */
  validateOperation: function (operation, matrices) {
    if (!Array.isArray(matrices) || matrices.length === 0) {
      return { isValid: false, error: "No matrices provided" };
    }
    
    // First check that all inputs are matrices
    for (let i = 0; i < matrices.length; i++) {
      if (!this.isMatrix(matrices[i])) {
        return { isValid: false, error: `Input ${i + 1} is not a valid matrix` };
      }
    }
    
    // Operation-specific validations
    switch (operation.toLowerCase()) {
      case 'add':
      case 'subtract':
        if (matrices.length !== 2) {
          return { isValid: false, error: `${operation} requires exactly 2 matrices` };
        }
        
        if (!this.haveSameDimensions(matrices[0], matrices[1])) {
          return { isValid: false, error: "Matrices must have the same dimensions" };
        }
        
        break;
        
      case 'multiply':
        if (matrices.length !== 2) {
          return { isValid: false, error: "Multiply requires exactly 2 matrices" };
        }
        
        if (!this.areMultiplicable(matrices[0], matrices[1])) {
          return { isValid: false, error: "First matrix column count must match second matrix row count" };
        }
        
        break;
        
      case 'determinant':
      case 'inverse':
      case 'eigenvalues':
        if (matrices.length !== 1) {
          return { isValid: false, error: `${operation} requires exactly 1 matrix` };
        }
        
        if (!this.isSquare(matrices[0])) {
          return { isValid: false, error: "Matrix must be square" };
        }
        
        break;
        
      case 'choleskydecomposition':
        if (matrices.length !== 1) {
          return { isValid: false, error: "Cholesky decomposition requires exactly 1 matrix" };
        }
        
        if (!this.isSquare(matrices[0])) {
          return { isValid: false, error: "Matrix must be square" };
        }
        
        if (!this.isSymmetric(matrices[0])) {
          return { isValid: false, error: "Matrix must be symmetric" };
        }
        
        if (!this.isPositiveDefinite(matrices[0])) {
          return { isValid: false, error: "Matrix must be positive-definite" };
        }
        
        break;
        
      case 'transpose':
      case 'scale':
      case 'trace':
      case 'rank':
        if (matrices.length !== 1) {
          return { isValid: false, error: `${operation} requires exactly 1 matrix` };
        }
        
        break;
        
      default:
        return { isValid: false, error: `Unknown operation: ${operation}` };
    }
    
    return { isValid: true, error: null };
  },
  
  /**
   * Check if a matrix contains NaN or Infinity values
   * @param {Array|TypedArray} matrix - Matrix to check
   * @returns {boolean} - True if the matrix contains invalid numerical values
   */
  hasInvalidValues: function (matrix) {
    if (!this.isMatrix(matrix)) {
      return true;
    }
    
    const MatrixCore = Prime.Math.MatrixCore;
    const dim = MatrixCore ? MatrixCore.dimensions(matrix) : 
      { rows: matrix.length, cols: matrix[0].length };
    
    for (let i = 0; i < dim.rows; i++) {
      for (let j = 0; j < dim.cols; j++) {
        const value = matrix[i][j];
        if (isNaN(value) || !isFinite(value)) {
          return true;
        }
      }
    }
    
    return false;
  },
  
  /**
   * Check if a matrix is close to being singular
   * @param {Array|TypedArray} matrix - Matrix to check
   * @param {number} [tolerance=1e-10] - Tolerance for determinant near zero
   * @returns {boolean} - True if the matrix is nearly singular
   */
  isNearlySingular: function (matrix, tolerance = 1e-10) {
    if (!this.isSquare(matrix)) {
      return true;
    }
    
    try {
      const MatrixAdvanced = Prime.Math.MatrixAdvanced;
      
      // Check condition number if available
      if (MatrixAdvanced.conditionNumber) {
        const condition = MatrixAdvanced.conditionNumber(matrix);
        return condition > 1e14 || !isFinite(condition);
      }
      
      // Fallback to determinant
      const det = MatrixAdvanced.determinant(matrix);
      return Math.abs(det) < tolerance;
    } catch (error) {
      return true;
    }
  },
  
  /**
   * Verify that all sizes in an array of matrices are compatible for chained operations
   * @param {Array<Array|TypedArray>} matrices - Array of matrices to verify
   * @returns {boolean} - True if all matrices are compatible
   */
  areChainMultiplicable: function (matrices) {
    if (!Array.isArray(matrices) || matrices.length < 2) {
      return false;
    }
    
    for (let i = 0; i < matrices.length - 1; i++) {
      if (!this.isMatrix(matrices[i]) || !this.isMatrix(matrices[i + 1])) {
        return false;
      }
      
      if (!this.areMultiplicable(matrices[i], matrices[i + 1])) {
        return false;
      }
    }
    
    return true;
  }
};

// Export the MatrixValidation module
Prime.Math = Prime.Math || {};
Prime.Math.MatrixValidation = MatrixValidation;

// Export the enhanced Prime object
module.exports = Prime;