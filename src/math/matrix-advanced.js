/**
 * PrimeOS JavaScript Library - Math
 * Matrix Advanced Operations
 * Advanced matrix operations with memory optimization and performance enhancements
 */

// Import the Prime object
const Prime = require("../core");

/**
 * Advanced matrix operations with optimized implementations
 */
const MatrixAdvanced = {
  /**
   * Calculate the determinant of a square matrix
   * @param {Array|TypedArray} matrix - Square matrix
   * @returns {number} - Determinant
   */
  determinant: function (matrix) {
    const MatrixCore = Prime.Math.MatrixCore;
    
    if (!MatrixCore.isMatrix(matrix)) {
      throw new Prime.ValidationError("Matrix must be valid");
    }

    const dim = MatrixCore.dimensions(matrix);
    
    if (dim.rows !== dim.cols) {
      throw new Prime.ValidationError("Matrix must be square");
    }

    // Base case for 1x1 matrix
    if (dim.rows === 1) {
      return matrix[0][0];
    }

    // Base case for 2x2 matrix (optimized)
    if (dim.rows === 2) {
      return matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0];
    }

    // Base case for 3x3 matrix (optimized)
    if (dim.rows === 3) {
      return (
        matrix[0][0] * (matrix[1][1] * matrix[2][2] - matrix[1][2] * matrix[2][1]) -
        matrix[0][1] * (matrix[1][0] * matrix[2][2] - matrix[1][2] * matrix[2][0]) +
        matrix[0][2] * (matrix[1][0] * matrix[2][1] - matrix[1][1] * matrix[2][0])
      );
    }

    // Recursive case for larger matrices using cofactor expansion
    let det = 0;
    for (let j = 0; j < dim.cols; j++) {
      const sign = j % 2 === 0 ? 1 : -1;
      det += sign * matrix[0][j] * this.cofactor(matrix, 0, j);
    }

    return det;
  },

  /**
   * Calculate the cofactor of a matrix element
   * @param {Array|TypedArray} matrix - Original matrix
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
   * @param {Array|TypedArray} matrix - Original matrix
   * @param {number} row - Row index to exclude
   * @param {number} col - Column index to exclude
   * @returns {Array|TypedArray} - Minor matrix
   */
  minor: function (matrix, row, col) {
    const MatrixCore = Prime.Math.MatrixCore;
    const dim = MatrixCore.dimensions(matrix);
    
    // Create a new matrix with dimensions reduced by 1
    const useTypedArray = matrix._isTypedArray;
    const arrayType = matrix._arrayType;
    
    const minor = MatrixCore.create(dim.rows - 1, dim.cols - 1, 0, {
      useTypedArray,
      arrayType
    });
    
    // Fill the minor with values, excluding the specified row and column
    let minorRow = 0;
    for (let i = 0; i < dim.rows; i++) {
      if (i === row) continue;
      
      let minorCol = 0;
      for (let j = 0; j < dim.cols; j++) {
        if (j === col) continue;
        minor[minorRow][minorCol] = matrix[i][j];
        minorCol++;
      }
      
      minorRow++;
    }
    
    return minor;
  },

  /**
   * Calculate the adjugate (adjoint) of a matrix
   * @param {Array|TypedArray} matrix - Matrix to calculate adjugate for
   * @returns {Array|TypedArray} - Adjugate matrix
   */
  adjugate: function (matrix) {
    const MatrixCore = Prime.Math.MatrixCore;
    
    if (!MatrixCore.isMatrix(matrix)) {
      throw new Prime.ValidationError("Matrix must be valid");
    }
    
    const dim = MatrixCore.dimensions(matrix);
    
    if (dim.rows !== dim.cols) {
      throw new Prime.ValidationError("Matrix must be square");
    }
    
    // Create adjugate matrix with the same type as input
    const useTypedArray = matrix._isTypedArray;
    const arrayType = matrix._arrayType;
    
    const adjugate = MatrixCore.create(dim.rows, dim.cols, 0, {
      useTypedArray,
      arrayType
    });
    
    // For 2x2 matrix, use direct formula for efficiency
    if (dim.rows === 2) {
      adjugate[0][0] = matrix[1][1];
      adjugate[0][1] = -matrix[0][1];
      adjugate[1][0] = -matrix[1][0];
      adjugate[1][1] = matrix[0][0];
      return adjugate;
    }
    
    // Calculate each cofactor
    for (let i = 0; i < dim.rows; i++) {
      for (let j = 0; j < dim.cols; j++) {
        // Note the transpose in the assignment (j, i instead of i, j)
        adjugate[j][i] = this.cofactor(matrix, i, j);
      }
    }
    
    return adjugate;
  },

  /**
   * Calculate the inverse of a matrix
   * @param {Array|TypedArray} matrix - Matrix to invert
   * @returns {Array|TypedArray} - Inverted matrix
   */
  inverse: function (matrix) {
    const MatrixCore = Prime.Math.MatrixCore;
    
    if (!MatrixCore.isMatrix(matrix)) {
      throw new Prime.ValidationError("Matrix must be valid");
    }
    
    const dim = MatrixCore.dimensions(matrix);
    
    if (dim.rows !== dim.cols) {
      throw new Prime.ValidationError("Matrix must be square");
    }
    
    const det = this.determinant(matrix);
    
    if (Math.abs(det) < 1e-10) {
      throw new Prime.MathematicalError(
        "Matrix is singular and cannot be inverted"
      );
    }
    
    // For 2x2 matrices, use direct formula for efficiency
    if (dim.rows === 2) {
      const useTypedArray = matrix._isTypedArray;
      const arrayType = matrix._arrayType;
      
      const result = MatrixCore.create(2, 2, 0, {
        useTypedArray,
        arrayType
      });
      
      const invDet = 1 / det;
      
      result[0][0] = matrix[1][1] * invDet;
      result[0][1] = -matrix[0][1] * invDet;
      result[1][0] = -matrix[1][0] * invDet;
      result[1][1] = matrix[0][0] * invDet;
      
      return result;
    }
    
    // For larger matrices, calculate adjugate and scale
    const adjugate = this.adjugate(matrix);
    return MatrixCore.scale(adjugate, 1 / det);
  },

  /**
   * Solve a system of linear equations Ax = b
   * @param {Array|TypedArray} A - Coefficient matrix
   * @param {Array} b - Right-hand side vector
   * @returns {Array} - Solution vector
   */
  solve: function (A, b) {
    const MatrixCore = Prime.Math.MatrixCore;
    
    if (!MatrixCore.isMatrix(A)) {
      throw new Prime.ValidationError("Coefficient matrix must be valid");
    }
    
    if (!Array.isArray(b)) {
      throw new Prime.ValidationError("Right-hand side must be an array");
    }
    
    const dim = MatrixCore.dimensions(A);
    
    if (dim.rows !== dim.cols) {
      throw new Prime.ValidationError("Coefficient matrix must be square");
    }
    
    if (dim.rows !== b.length) {
      throw new Prime.ValidationError("Matrix rows must match vector length");
    }
    
    // Create column vector from b
    const useTypedArray = A._isTypedArray;
    const arrayType = A._arrayType;
    
    const bVector = MatrixCore.create(dim.rows, 1, 0, {
      useTypedArray,
      arrayType
    });
    
    for (let i = 0; i < dim.rows; i++) {
      bVector[i][0] = b[i];
    }
    
    // Solve by multiplying the inverse of A with b
    const inverse = this.inverse(A);
    const result = MatrixCore.multiply(inverse, bVector);
    
    // Convert result back to a regular array for compatibility
    const solutionVector = new Array(dim.rows);
    for (let i = 0; i < dim.rows; i++) {
      solutionVector[i] = result[i][0];
    }
    
    return solutionVector;
  },

  /**
   * Calculate LU decomposition of a matrix
   * @param {Array|TypedArray} matrix - Matrix to decompose
   * @returns {Object} - Object containing L and U matrices
   */
  luDecomposition: function (matrix) {
    const MatrixCore = Prime.Math.MatrixCore;
    
    if (!MatrixCore.isMatrix(matrix)) {
      throw new Prime.ValidationError("Matrix must be valid");
    }
    
    const dim = MatrixCore.dimensions(matrix);
    
    if (dim.rows !== dim.cols) {
      throw new Prime.ValidationError("Matrix must be square");
    }
    
    const n = dim.rows;
    const useTypedArray = matrix._isTypedArray;
    const arrayType = matrix._arrayType;
    
    // Create L and U matrices
    const L = MatrixCore.create(n, n, 0, {
      useTypedArray,
      arrayType
    });
    
    const U = MatrixCore.clone(matrix);
    
    // Perform LU decomposition
    for (let k = 0; k < n; k++) {
      // Set diagonal element of L to 1
      L[k][k] = 1;
      
      for (let i = k + 1; i < n; i++) {
        // Skip if pivot is effectively zero
        if (Math.abs(U[k][k]) < 1e-10) {
          continue;
        }
        
        // Calculate multiplier
        const factor = U[i][k] / U[k][k];
        L[i][k] = factor;
        
        // Update U matrix
        for (let j = k; j < n; j++) {
          U[i][j] -= factor * U[k][j];
        }
      }
    }
    
    return { L, U };
  },

  /**
   * Compute QR decomposition using Gram-Schmidt process
   * @param {Array|TypedArray} matrix - Matrix to decompose
   * @returns {Object} - Object containing Q and R matrices
   */
  qrDecomposition: function (matrix) {
    const MatrixCore = Prime.Math.MatrixCore;
    const VectorCore = Prime.Math.VectorCore;
    
    if (!MatrixCore.isMatrix(matrix)) {
      throw new Prime.ValidationError("Matrix must be valid");
    }
    
    const dim = MatrixCore.dimensions(matrix);
    const m = dim.rows;
    const n = dim.cols;
    
    if (m < n) {
      throw new Prime.ValidationError("Matrix must have at least as many rows as columns");
    }
    
    const useTypedArray = matrix._isTypedArray;
    const arrayType = matrix._arrayType;
    
    // Create Q and R matrices
    const Q = MatrixCore.create(m, n, 0, {
      useTypedArray,
      arrayType
    });
    
    const R = MatrixCore.create(n, n, 0, {
      useTypedArray,
      arrayType
    });
    
    // Extract columns of A
    const A = new Array(n);
    for (let j = 0; j < n; j++) {
      A[j] = new Array(m);
      for (let i = 0; i < m; i++) {
        A[j][i] = matrix[i][j];
      }
    }
    
    // Gram-Schmidt process
    const Q_cols = new Array(n);
    
    for (let j = 0; j < n; j++) {
      // Start with the original column
      let q = A[j].slice();
      
      // Subtract projections onto previous orthonormal vectors
      for (let i = 0; i < j; i++) {
        // Compute dot product
        let dot = 0;
        for (let k = 0; k < m; k++) {
          dot += A[j][k] * Q_cols[i][k];
        }
        
        // Set R value
        R[i][j] = dot;
        
        // Subtract projection
        for (let k = 0; k < m; k++) {
          q[k] -= dot * Q_cols[i][k];
        }
      }
      
      // Compute the norm of q
      let norm = 0;
      for (let i = 0; i < m; i++) {
        norm += q[i] * q[i];
      }
      norm = Math.sqrt(norm);
      
      // Check for linear dependence
      if (norm < 1e-10) {
        throw new Prime.MathematicalError("Matrix columns are linearly dependent");
      }
      
      // Normalize q
      for (let i = 0; i < m; i++) {
        q[i] /= norm;
      }
      
      // Store normalized vector in Q_cols and in R diagonal
      Q_cols[j] = q;
      R[j][j] = norm;
      
      // Store in Q matrix
      for (let i = 0; i < m; i++) {
        Q[i][j] = q[i];
      }
    }
    
    return { Q, R };
  },

  /**
   * Compute eigenvalues and eigenvectors of a symmetric matrix using power iteration
   * @param {Array|TypedArray} matrix - Symmetric matrix
   * @param {Object} [options={}] - Options
   * @param {number} [options.maxIterations=100] - Maximum number of iterations
   * @param {number} [options.tolerance=1e-10] - Convergence tolerance
   * @param {number} [options.numEigenvalues=1] - Number of eigenvalues to compute
   * @returns {Object} - Object containing eigenvalues and eigenvectors
   */
  eigenvalues: function (matrix, options = {}) {
    const MatrixCore = Prime.Math.MatrixCore;
    
    if (!MatrixCore.isMatrix(matrix)) {
      throw new Prime.ValidationError("Matrix must be valid");
    }
    
    const dim = MatrixCore.dimensions(matrix);
    
    if (dim.rows !== dim.cols) {
      throw new Prime.ValidationError("Matrix must be square");
    }
    
    const n = dim.rows;
    const maxIterations = options.maxIterations || 100;
    const tolerance = options.tolerance || 1e-10;
    const numEigenvalues = Math.min(options.numEigenvalues || 1, n);
    
    const useTypedArray = matrix._isTypedArray;
    const arrayType = matrix._arrayType;
    
    // Arrays to store results
    const eigenvalues = new Array(numEigenvalues);
    const eigenvectors = MatrixCore.create(n, numEigenvalues, 0, {
      useTypedArray,
      arrayType
    });
    
    // Create a working copy of the matrix
    let A = MatrixCore.clone(matrix);
    
    for (let k = 0; k < numEigenvalues; k++) {
      // Start with a random vector
      let vector = new Array(n);
      for (let i = 0; i < n; i++) {
        vector[i] = Math.random();
      }
      
      // Normalize the vector
      let norm = 0;
      for (let i = 0; i < n; i++) {
        norm += vector[i] * vector[i];
      }
      norm = Math.sqrt(norm);
      
      for (let i = 0; i < n; i++) {
        vector[i] /= norm;
      }
      
      let eigenvalue = 0;
      let lastEigenvalue = 0;
      
      // Power iteration
      for (let iter = 0; iter < maxIterations; iter++) {
        // Multiply matrix by vector
        const Av = new Array(n).fill(0);
        
        for (let i = 0; i < n; i++) {
          for (let j = 0; j < n; j++) {
            Av[i] += A[i][j] * vector[j];
          }
        }
        
        // Find largest component
        eigenvalue = 0;
        for (let i = 0; i < n; i++) {
          eigenvalue += vector[i] * Av[i];
        }
        
        // Check for convergence
        if (Math.abs(eigenvalue - lastEigenvalue) < tolerance) {
          break;
        }
        
        lastEigenvalue = eigenvalue;
        
        // Normalize the resulting vector
        norm = 0;
        for (let i = 0; i < n; i++) {
          norm += Av[i] * Av[i];
        }
        norm = Math.sqrt(norm);
        
        for (let i = 0; i < n; i++) {
          vector[i] = Av[i] / norm;
        }
      }
      
      // Store results
      eigenvalues[k] = eigenvalue;
      for (let i = 0; i < n; i++) {
        eigenvectors[i][k] = vector[i];
      }
      
      // Deflate the matrix to find next eigenvalue
      if (k < numEigenvalues - 1) {
        // A = A - eigenvalue * vector * vector^T
        for (let i = 0; i < n; i++) {
          for (let j = 0; j < n; j++) {
            A[i][j] -= eigenvalue * vector[i] * vector[j];
          }
        }
      }
    }
    
    return { eigenvalues, eigenvectors };
  },

  /**
   * Compute Cholesky decomposition of a positive-definite matrix
   * @param {Array|TypedArray} matrix - Positive-definite matrix
   * @returns {Array|TypedArray} - Lower triangular matrix L where matrix = L * L^T
   */
  choleskyDecomposition: function (matrix) {
    const MatrixCore = Prime.Math.MatrixCore;
    
    if (!MatrixCore.isMatrix(matrix)) {
      throw new Prime.ValidationError("Matrix must be valid");
    }
    
    const dim = MatrixCore.dimensions(matrix);
    
    if (dim.rows !== dim.cols) {
      throw new Prime.ValidationError("Matrix must be square");
    }
    
    const n = dim.rows;
    const useTypedArray = matrix._isTypedArray;
    const arrayType = matrix._arrayType;
    
    // Create result matrix
    const L = MatrixCore.create(n, n, 0, {
      useTypedArray,
      arrayType
    });
    
    // Perform Cholesky decomposition
    for (let i = 0; i < n; i++) {
      for (let j = 0; j <= i; j++) {
        let sum = 0;
        
        if (j === i) {
          // Diagonal elements
          for (let k = 0; k < j; k++) {
            sum += L[j][k] * L[j][k];
          }
          
          const value = matrix[j][j] - sum;
          
          if (value <= 0) {
            throw new Prime.MathematicalError("Matrix is not positive-definite");
          }
          
          L[j][j] = Math.sqrt(value);
        } else {
          // Off-diagonal elements
          for (let k = 0; k < j; k++) {
            sum += L[i][k] * L[j][k];
          }
          
          L[i][j] = (matrix[i][j] - sum) / L[j][j];
        }
      }
    }
    
    return L;
  },

  /**
   * Calculate the matrix trace (sum of diagonal elements)
   * @param {Array|TypedArray} matrix - Matrix
   * @returns {number} - Trace
   */
  trace: function (matrix) {
    const MatrixCore = Prime.Math.MatrixCore;
    
    if (!MatrixCore.isMatrix(matrix)) {
      throw new Prime.ValidationError("Matrix must be valid");
    }
    
    const dim = MatrixCore.dimensions(matrix);
    
    // For non-square matrices, take the min of rows and cols
    const size = Math.min(dim.rows, dim.cols);
    
    let trace = 0;
    for (let i = 0; i < size; i++) {
      trace += matrix[i][i];
    }
    
    return trace;
  },

  /**
   * Calculate the matrix rank using Gaussian elimination
   * @param {Array|TypedArray} matrix - Matrix
   * @param {number} [tolerance=1e-10] - Numerical tolerance for zero
   * @returns {number} - Rank of the matrix
   */
  rank: function (matrix, tolerance = 1e-10) {
    const MatrixCore = Prime.Math.MatrixCore;
    
    if (!MatrixCore.isMatrix(matrix)) {
      throw new Prime.ValidationError("Matrix must be valid");
    }
    
    const dim = MatrixCore.dimensions(matrix);
    const m = dim.rows;
    const n = dim.cols;
    
    // Create a copy of the matrix to work with
    const A = MatrixCore.clone(matrix);
    
    let rank = 0;
    const rows = new Array(m).fill(false); // Track processed rows
    
    for (let j = 0; j < n; j++) {
      // Find pivot row
      let pivot = -1;
      let maxValue = tolerance;
      
      for (let i = 0; i < m; i++) {
        if (!rows[i] && Math.abs(A[i][j]) > maxValue) {
          maxValue = Math.abs(A[i][j]);
          pivot = i;
        }
      }
      
      if (pivot >= 0) {
        rank++;
        rows[pivot] = true; // Mark row as processed
        
        // Normalize pivot row
        const pivotValue = A[pivot][j];
        for (let k = j; k < n; k++) {
          A[pivot][k] /= pivotValue;
        }
        
        // Eliminate this column from other rows
        for (let i = 0; i < m; i++) {
          if (i !== pivot) {
            const factor = A[i][j];
            for (let k = j; k < n; k++) {
              A[i][k] -= factor * A[pivot][k];
            }
          }
        }
      }
    }
    
    return rank;
  },

  /**
   * Calculate the condition number of a matrix
   * @param {Array|TypedArray} matrix - Matrix
   * @returns {number} - Condition number (infinity if singular)
   */
  conditionNumber: function (matrix) {
    // Estimate condition number using the largest and smallest eigenvalues
    try {
      // Get eigenvalues (all of them)
      const dim = Prime.Math.MatrixCore.dimensions(matrix);
      const { eigenvalues } = this.eigenvalues(matrix, { numEigenvalues: dim.rows });
      
      // Find largest and smallest absolute eigenvalues
      let maxEigenvalue = 0;
      let minEigenvalue = Infinity;
      
      for (let i = 0; i < eigenvalues.length; i++) {
        const absValue = Math.abs(eigenvalues[i]);
        if (absValue > maxEigenvalue) {
          maxEigenvalue = absValue;
        }
        if (absValue < minEigenvalue && absValue > 1e-10) {
          minEigenvalue = absValue;
        }
      }
      
      if (minEigenvalue === Infinity || minEigenvalue < 1e-10) {
        return Infinity; // Matrix is singular or nearly singular
      }
      
      return maxEigenvalue / minEigenvalue;
    } catch (error) {
      // If eigenvalue computation fails, return infinity
      return Infinity;
    }
  }
};

// Export the MatrixAdvanced module
Prime.Math = Prime.Math || {};
Prime.Math.MatrixAdvanced = MatrixAdvanced;

// Export the enhanced Prime object
module.exports = Prime;