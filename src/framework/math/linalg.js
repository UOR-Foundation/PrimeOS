/**
 * Linear Algebra Module for PrimeOS
 * Implements vector and matrix operations with mathematical precision guarantees
 * Extends the Prime.math namespace
 */

// Import Prime directly from core/prime to avoid circular dependencies
const Prime = require("../../core/prime.js");

// Import standardized math interface
const StandardMath = require("./index.js").Standard;

/**
 * Vector operations with enhanced numerical stability
 */
class Vector {
  /**
   * Create a new vector
   * @param {Array<number>|number} values - Array of values or dimension for zero vector
   */
  constructor(values) {
    if (Array.isArray(values)) {
      this.values = [...values];
    } else if (typeof values === "number" && values >= 0) {
      this.values = new Array(values).fill(0);
    } else {
      throw new Prime.ValidationError(
        "Vector constructor requires array or positive dimension",
      );
    }
  }

  /**
   * Get the dimension of the vector
   * @returns {number} Dimension
   */
  get dimension() {
    return this.values.length;
  }

  /**
   * Get a copy of the vector values
   * @returns {Array<number>} Copy of vector values
   */
  toArray() {
    return [...this.values];
  }

  /**
   * Create a vector from an array
   * @param {Array<number>} array - Input array
   * @returns {Vector} New vector
   */
  static fromArray(array) {
    return new Vector(array);
  }

  /**
   * Create a zero vector of given dimension
   * @param {number} dimension - Vector dimension
   * @returns {Vector} Zero vector
   */
  static zeros(dimension) {
    return new Vector(dimension);
  }

  /**
   * Create a vector of ones
   * @param {number} dimension - Vector dimension
   * @returns {Vector} Vector of ones
   */
  static ones(dimension) {
    return new Vector(new Array(dimension).fill(1));
  }

  /**
   * Create a vector with elements from start to end (inclusive)
   * @param {number} start - Start value
   * @param {number} end - End value
   * @param {number} [step=1] - Step size
   * @returns {Vector} Range vector
   */
  static range(start, end, step = 1) {
    const values = [];
    for (let i = start; i <= end; i += step) {
      values.push(i);
    }
    return new Vector(values);
  }

  /**
   * Add another vector to this one
   * @param {Vector|Array<number>} other - Vector to add
   * @returns {Vector} Result of addition
   */
  add(other) {
    const otherValues = other instanceof Vector ? other.values : other;

    if (otherValues.length !== this.dimension) {
      throw new Prime.MathematicalError(
        "Vectors must have the same dimension for addition",
      );
    }

    // Use StandardMath for vector addition
    const result = StandardMath.Vector.add(this.values, otherValues);

    return new Vector(result);
  }

  /**
   * Subtract another vector from this one
   * @param {Vector|Array<number>} other - Vector to subtract
   * @returns {Vector} Result of subtraction
   */
  subtract(other) {
    const otherValues = other instanceof Vector ? other.values : other;

    if (otherValues.length !== this.dimension) {
      throw new Prime.MathematicalError(
        "Vectors must have the same dimension for subtraction",
      );
    }

    // Use StandardMath for vector subtraction
    const result = StandardMath.Vector.subtract(this.values, otherValues);

    return new Vector(result);
  }

  /**
   * Multiply vector by a scalar
   * @param {number} scalar - Scalar value
   * @returns {Vector} Scaled vector
   */
  scale(scalar) {
    if (typeof scalar !== "number") {
      throw new Prime.ValidationError("Scale factor must be a number");
    }

    // Use StandardMath for vector scaling
    const result = StandardMath.Vector.scale(this.values, scalar);
    return new Vector(result);
  }

  /**
   * Calculate the dot product with another vector
   * @param {Vector|Array<number>} other - Other vector
   * @returns {number} Dot product
   */
  dot(other) {
    const otherValues = other instanceof Vector ? other.values : other;

    if (otherValues.length !== this.dimension) {
      throw new Prime.MathematicalError(
        "Vectors must have the same dimension for dot product",
      );
    }

    // Use the standardized math interface with enhanced precision
    return StandardMath.Vector.dot(this.values, otherValues);
  }

  /**
   * Calculate the cross product with another vector (3D only)
   * @param {Vector|Array<number>} other - Other vector
   * @returns {Vector} Cross product
   */
  cross(other) {
    const otherValues = other instanceof Vector ? other.values : other;

    if (this.dimension !== 3 || otherValues.length !== 3) {
      throw new Prime.MathematicalError("Cross product requires 3D vectors");
    }

    // Use StandardMath for cross product
    const result = StandardMath.Vector.cross(this.values, otherValues);

    return new Vector(result);
  }

  /**
   * Calculate the angle between this vector and another
   * @param {Vector|Array<number>} other - Other vector
   * @returns {number} Angle in radians
   */
  angleBetween(other) {
    const otherValues = other instanceof Vector ? other.values : other;

    // Use StandardMath for calculating the angle
    try {
      return StandardMath.Vector.angle(this.values, otherValues);
    } catch (error) {
      throw new Prime.MathematicalError(
        "Cannot compute angle with zero vectors",
      );
    }
  }

  /**
   * Project this vector onto another vector
   * @param {Vector|Array<number>} other - Vector to project onto
   * @returns {Vector} Projection vector
   */
  projectOnto(other) {
    const otherValues = other instanceof Vector ? other.values : other;

    try {
      // Use StandardMath for vector projection
      const result = StandardMath.Vector.project(this.values, otherValues);
      return new Vector(result);
    } catch (error) {
      throw new Prime.MathematicalError("Cannot project onto zero vector");
    }
  }

  /**
   * Calculate the norm (magnitude) of the vector
   * @param {number} [p=2] - The order of the norm (1 for L1, 2 for L2, etc.)
   * @returns {number} Vector norm
   */
  norm(p = 2) {
    // Use standardized math interface for vector norm
    return StandardMath.Vector.norm(this.values, { order: p });
  }

  /**
   * Normalize the vector to unit length
   * @returns {Vector} Normalized vector
   */
  normalize() {
    // Use standardized math interface for vector normalization
    try {
      const normalizedValues = StandardMath.Vector.normalize(this.values);
      return new Vector(normalizedValues);
    } catch (error) {
      throw new Prime.MathematicalError("Cannot normalize zero vector");
    }
  }

  /**
   * Calculate the distance to another vector
   * @param {Vector|Array<number>} other - Other vector
   * @param {number} [p=2] - The order of the norm (1 for L1, 2 for L2, etc.)
   * @returns {number} Distance
   */
  distance(other, p = 2) {
    const otherValues = other instanceof Vector ? other.values : other;

    // Use StandardMath for vector distance
    return StandardMath.Vector.distance(this.values, otherValues, { order: p });
  }

  /**
   * Check if this vector equals another vector
   * @param {Vector|Array<number>} other - Other vector
   * @param {number} [epsilon=Number.EPSILON] - Tolerance for floating-point comparison
   * @returns {boolean} True if vectors are equal
   */
  equals(other, epsilon = Number.EPSILON) {
    const otherValues = other instanceof Vector ? other.values : other;

    if (this.dimension !== otherValues.length) {
      return false;
    }

    for (let i = 0; i < this.dimension; i++) {
      if (Math.abs(this.values[i] - otherValues[i]) > epsilon) {
        return false;
      }
    }

    return true;
  }

  /**
   * Apply a function to each element of the vector
   * @param {Function} fn - Function to apply
   * @returns {Vector} New vector with applied function
   */
  map(fn) {
    return new Vector(this.values.map(fn));
  }

  /**
   * Create a string representation of the vector
   * @returns {string} String representation
   */
  toString() {
    return `[${this.values.join(", ")}]`;
  }

  /**
   * Alias for norm() to maintain compatibility with integration tests
   * @returns {number} Vector magnitude (Euclidean norm)
   */
  magnitude() {
    return this.norm(2);
  }
}

/**
 * Matrix operations with enhanced numerical stability
 */
class Matrix {
  /**
   * Create a new matrix
   * @param {Array<Array<number>>|number[]|number} values - Matrix values, dimensions, or flat array
   * @param {number} [rows] - Number of rows (if values is flat array)
   * @param {number} [cols] - Number of columns (if values is flat array)
   */
  constructor(values, rows, cols) {
    if (Array.isArray(values) && Array.isArray(values[0])) {
      // 2D array
      this.rows = values.length;
      this.cols = values[0].length;

      // Validate all rows have the same length
      for (let i = 1; i < this.rows; i++) {
        if (!Array.isArray(values[i]) || values[i].length !== this.cols) {
          throw new Prime.ValidationError("All rows must have the same length");
        }
      }

      // Deep copy the values
      this.values = values.map((row) => [...row]);
    } else if (
      Array.isArray(values) &&
      typeof rows === "number" &&
      typeof cols === "number"
    ) {
      // Flat array with dimensions
      if (values.length !== rows * cols) {
        throw new Prime.ValidationError("Invalid dimensions for flat array");
      }

      this.rows = rows;
      this.cols = cols;
      this.values = [];

      // Convert flat array to 2D array
      for (let i = 0; i < rows; i++) {
        const row = [];
        for (let j = 0; j < cols; j++) {
          row.push(values[i * cols + j]);
        }
        this.values.push(row);
      }
    } else if (typeof values === "number" && typeof rows === "number") {
      // Create matrix with dimensions and default value 0
      this.rows = values;
      this.cols = rows;
      this.values = Array(this.rows)
        .fill()
        .map(() => Array(this.cols).fill(0));
    } else {
      throw new Prime.ValidationError("Invalid matrix constructor arguments");
    }
  }

  /**
   * Get the shape of the matrix
   * @returns {number[]} [rows, cols]
   */
  get shape() {
    return [this.rows, this.cols];
  }

  /**
   * Get a specific element
   * @param {number} i - Row index
   * @param {number} j - Column index
   * @returns {number} Matrix element value
   */
  get(i, j) {
    this._validateIndices(i, j);
    return this.values[i][j];
  }

  /**
   * Set a specific element
   * @param {number} i - Row index
   * @param {number} j - Column index
   * @param {number} value - New value
   */
  set(i, j, value) {
    this._validateIndices(i, j);
    this.values[i][j] = value;
  }

  /**
   * Validate indices
   * @private
   * @param {number} i - Row index
   * @param {number} j - Column index
   */
  _validateIndices(i, j) {
    if (i < 0 || i >= this.rows || j < 0 || j >= this.cols) {
      throw new Prime.MathematicalError(`Indices out of range: (${i}, ${j})`);
    }
  }

  /**
   * Get a deep copy of the matrix values
   * @returns {Array<Array<number>>} Matrix values
   */
  toArray() {
    return this.values.map((row) => [...row]);
  }

  /**
   * Get a flat array of the matrix values (row-major order)
   * @returns {Array<number>} Flat array
   */
  toFlatArray() {
    const result = [];
    for (let i = 0; i < this.rows; i++) {
      for (let j = 0; j < this.cols; j++) {
        result.push(this.values[i][j]);
      }
    }
    return result;
  }

  /**
   * Create a matrix from a 2D array
   * @param {Array<Array<number>>} array - 2D array
   * @returns {Matrix} New matrix
   */
  static fromArray(array) {
    return new Matrix(array);
  }

  /**
   * Create a matrix from a flat array
   * @param {Array<number>} array - Flat array
   * @param {number} rows - Number of rows
   * @param {number} cols - Number of columns
   * @returns {Matrix} New matrix
   */
  static fromFlatArray(array, rows, cols) {
    return new Matrix(array, rows, cols);
  }

  /**
   * Create a zero matrix
   * @param {number} rows - Number of rows
   * @param {number} cols - Number of columns
   * @returns {Matrix} Zero matrix
   */
  static zeros(rows, cols) {
    return new Matrix(rows, cols);
  }

  /**
   * Create a matrix of ones
   * @param {number} rows - Number of rows
   * @param {number} cols - Number of columns
   * @returns {Matrix} Matrix of ones
   */
  static ones(rows, cols) {
    const values = Array(rows)
      .fill()
      .map(() => Array(cols).fill(1));
    return new Matrix(values);
  }

  /**
   * Create an identity matrix
   * @param {number} size - Matrix size
   * @returns {Matrix} Identity matrix
   */
  static identity(size) {
    const values = Array(size)
      .fill()
      .map((_, i) =>
        Array(size)
          .fill(0)
          .map((_, j) => (i === j ? 1 : 0)),
      );
    return new Matrix(values);
  }

  /**
   * Create a diagonal matrix
   * @param {Array<number>|Vector} diagonal - Diagonal elements
   * @returns {Matrix} Diagonal matrix
   */
  static diagonal(diagonal) {
    const diag = diagonal instanceof Vector ? diagonal.values : diagonal;
    const size = diag.length;

    const values = Array(size)
      .fill()
      .map((_, i) =>
        Array(size)
          .fill(0)
          .map((_, j) => (i === j ? diag[i] : 0)),
      );

    return new Matrix(values);
  }

  /**
   * Alias for diagonal. Create a diagonal matrix or extract diagonal from a matrix
   * @param {Array<number>|Vector|Matrix} input - Diagonal elements or matrix
   * @returns {Matrix|Array} Diagonal matrix or vector of diagonal elements
   */
  static diag(input) {
    // Check if input is a matrix
    if (input instanceof Matrix) {
      // Extract diagonal elements from matrix
      const n = Math.min(input.rows, input.cols);
      const diag = new Array(n);

      for (let i = 0; i < n; i++) {
        diag[i] = input.get(i, i);
      }

      return diag;
    } else {
      // Create a diagonal matrix (reuse the diagonal method)
      return this.diagonal(input);
    }
  }

  /**
   * Add another matrix to this one
   * @param {Matrix|Array<Array<number>>} other - Matrix to add
   * @returns {Matrix} Result of addition
   */
  add(other) {
    const otherMatrix = other instanceof Matrix ? other : new Matrix(other);

    if (this.rows !== otherMatrix.rows || this.cols !== otherMatrix.cols) {
      throw new Prime.MathematicalError(
        "Matrices must have the same shape for addition",
      );
    }

    // Use StandardMath for matrix addition
    const result = StandardMath.Matrix.add(this.values, otherMatrix.values);

    return new Matrix(result);
  }

  /**
   * Subtract another matrix from this one
   * @param {Matrix|Array<Array<number>>} other - Matrix to subtract
   * @returns {Matrix} Result of subtraction
   */
  subtract(other) {
    const otherMatrix = other instanceof Matrix ? other : new Matrix(other);

    if (this.rows !== otherMatrix.rows || this.cols !== otherMatrix.cols) {
      throw new Prime.MathematicalError(
        "Matrices must have the same shape for subtraction",
      );
    }

    // Use StandardMath for matrix subtraction
    const result = StandardMath.Matrix.subtract(
      this.values,
      otherMatrix.values,
    );

    return new Matrix(result);
  }

  /**
   * Multiply matrix by a scalar
   * @param {number} scalar - Scalar value
   * @returns {Matrix} Scaled matrix
   */
  scale(scalar) {
    if (typeof scalar !== "number") {
      throw new Prime.ValidationError("Scale factor must be a number");
    }

    // Use StandardMath for matrix scaling
    const result = StandardMath.Matrix.scale(this.values, scalar);

    return new Matrix(result);
  }

  /**
   * Multiply matrix by another matrix or vector
   * @param {Matrix|Vector|Array<Array<number>>|Array<number>} other - Matrix or vector to multiply
   * @returns {Matrix|Vector} Result of multiplication
   */
  multiply(other) {
    if (other instanceof Vector) {
      return this._multiplyVector(other);
    }

    const otherMatrix = other instanceof Matrix ? other : new Matrix(other);

    // Check dimensions compatibility for matrix multiplication
    if (this.cols !== otherMatrix.rows) {
      throw new Prime.MathematicalError(
        `Matrix dimensions incompatible for multiplication: ${this.rows}x${this.cols} and ${otherMatrix.rows}x${otherMatrix.cols}`,
      );
    }

    // Use StandardMath for matrix multiplication with enhanced numerical stability
    try {
      const { matrix } = StandardMath.Matrix.multiplyWithMetrics(
        this.values,
        otherMatrix.values,
      );
      return new Matrix(matrix);
    } catch (error) {
      // Fallback to standard multiplication if multiplyWithMetrics fails
      const result = StandardMath.Matrix.multiply(
        this.values,
        otherMatrix.values,
      );
      return new Matrix(result);
    }
  }

  /**
   * Multiply matrix by a vector
   * @private
   * @param {Vector} vector - Vector to multiply
   * @returns {Vector} Result of multiplication
   */
  _multiplyVector(vector) {
    if (this.cols !== vector.dimension) {
      throw new Prime.MathematicalError(
        "Matrix and vector dimensions incompatible for multiplication",
      );
    }

    // Use StandardMath for matrix-vector multiplication
    try {
      const result = StandardMath.Matrix.multiply(this.values, vector.values);
      return new Vector(result);
    } catch (error) {
      throw new Prime.MathematicalError(
        "Failed to multiply matrix and vector: " + error.message,
      );
    }
  }

  /**
   * Calculate the transpose of the matrix
   * @returns {Matrix} Transposed matrix
   */
  transpose() {
    // Use StandardMath for matrix transpose
    const result = StandardMath.Matrix.transpose(this.values);

    return new Matrix(result);
  }

  /**
   * Calculate the trace of the matrix
   * @returns {number} Trace (sum of diagonal elements)
   */
  trace() {
    if (this.rows !== this.cols) {
      throw new Prime.MathematicalError("Trace requires a square matrix");
    }

    // Use StandardMath for matrix trace
    return StandardMath.Matrix.trace(this.values);
  }

  /**
   * Calculate the determinant of the matrix
   * @returns {number} Determinant
   */
  determinant() {
    if (this.rows !== this.cols) {
      throw new Prime.MathematicalError("Determinant requires a square matrix");
    }

    // Use StandardMath for matrix determinant with enhanced numerical stability
    try {
      const { determinant } = StandardMath.Matrix.determinantWithMetrics(
        this.values,
      );
      return determinant;
    } catch (error) {
      // Fallback to standard determinant if determinantWithMetrics fails
      return StandardMath.Matrix.determinant(this.values);
    }
  }

  /**
   * Perform LU decomposition with partial pivoting
   * @returns {Object} Object with L, U, P matrices and exchanges count
   */
  luDecomposition() {
    if (this.rows !== this.cols) {
      throw new Prime.MathematicalError(
        "LU decomposition requires a square matrix",
      );
    }

    // Use StandardMath for LU decomposition
    try {
      const result = StandardMath.Matrix.luDecomposition(this.values);

      // Convert arrays to Matrix objects
      return {
        L: new Matrix(result.L),
        U: new Matrix(result.U),
        P: new Matrix(result.P),
        exchanges: result.exchanges,
      };
    } catch (error) {
      throw new Prime.MathematicalError(
        "LU decomposition failed: " + error.message,
      );
    }
  }

  /**
   * Calculate the inverse of the matrix
   * @returns {Matrix} Inverse matrix
   */
  inverse() {
    if (this.rows !== this.cols) {
      throw new Prime.MathematicalError("Inverse requires a square matrix");
    }

    // Use StandardMath for matrix inverse
    try {
      const result = StandardMath.Matrix.inverse(this.values);
      return new Matrix(result);
    } catch (error) {
      throw new Prime.MathematicalError(
        "Matrix is singular, cannot compute inverse",
      );
    }
  }

  /**
   * Solve system of linear equations Ax = b
   * @param {Vector|Array<number>} b - Right-hand side vector
   * @returns {Vector} Solution vector
   */
  solve(b) {
    const bVector = b instanceof Vector ? b : new Vector(b);

    if (this.rows !== this.cols) {
      throw new Prime.MathematicalError("System matrix must be square");
    }

    if (this.rows !== bVector.dimension) {
      throw new Prime.MathematicalError(
        "Vector dimension must match matrix size",
      );
    }

    // Use StandardMath for solving linear systems
    try {
      const result = StandardMath.Matrix.solve(this.values, bVector.values);
      return new Vector(result);
    } catch (error) {
      throw new Prime.MathematicalError(
        "Failed to solve linear system: " + error.message,
      );
    }
  }

  /**
   * Calculate the eigenvalues and eigenvectors of the matrix
   * @returns {Object} Object with eigenvalues and eigenvectors
   */
  eigen() {
    if (this.rows !== this.cols) {
      throw new Prime.MathematicalError(
        "Eigendecomposition requires a square matrix",
      );
    }

    // Use StandardMath for eigendecomposition
    try {
      const result = StandardMath.Matrix.eigen(this.values);

      // Convert eigenvectors to Vector objects if they aren't already
      const eigenvectors = result.vectors.map((v) =>
        v instanceof Vector ? v : new Vector(v),
      );

      return {
        values: result.values,
        vectors: eigenvectors,
      };
    } catch (error) {
      throw new Prime.MathematicalError(
        "Eigendecomposition failed: " + error.message,
      );
    }
  }

  /**
   * Perform QR decomposition
   * @returns {Object} Object with Q and R matrices
   */
  qrDecomposition() {
    if (this.rows < this.cols) {
      throw new Prime.MathematicalError(
        "QR decomposition requires rows >= columns",
      );
    }

    // Use StandardMath for QR decomposition
    try {
      const result = StandardMath.Matrix.qrDecomposition(this.values);

      // Convert to Matrix objects
      return {
        Q: new Matrix(result.Q),
        R: new Matrix(result.R),
      };
    } catch (error) {
      throw new Prime.MathematicalError(
        "QR decomposition failed: " + error.message,
      );
    }
  }

  /**
   * Calculate the singular value decomposition (SVD) with enhanced numerical stability for extreme values
   * @param {Object} [options={}] - SVD computation options
   * @param {number} [options.tolerance=1e-10] - Base tolerance for convergence
   * @param {number} [options.maxIterations=100] - Maximum number of iterations for the algorithm
   * @returns {Object} Object with U, S, and V matrices
   */
  svd(options = {}) {
    // Use StandardMath for SVD
    try {
      const result = StandardMath.Matrix.svd(this.values, options);

      // Convert to Matrix objects if needed
      return {
        U: result.U instanceof Matrix ? result.U : new Matrix(result.U),
        S: result.S instanceof Matrix ? result.S : new Matrix(result.S),
        V: result.V instanceof Matrix ? result.V : new Matrix(result.V),
      };
    } catch (error) {
      throw new Prime.MathematicalError(
        "SVD decomposition failed: " + error.message,
      );
    }
  }

  /**
   * Calculate the condition number of the matrix
   * @returns {number} Condition number
   */
  conditionNumber() {
    // Use StandardMath for condition number
    try {
      return StandardMath.Matrix.conditionNumber(this.values);
    } catch (error) {
      throw new Prime.MathematicalError(
        "Failed to calculate condition number: " + error.message,
      );
    }
  }

  /**
   * Calculate the rank of the matrix
   * @param {number} [tolerance=1e-10] - Tolerance for singular values
   * @returns {number} Rank
   */
  rank(tolerance = 1e-10) {
    // Use StandardMath for matrix rank
    try {
      return StandardMath.Matrix.rank(this.values, tolerance);
    } catch (error) {
      throw new Prime.MathematicalError(
        "Failed to calculate rank: " + error.message,
      );
    }
  }

  /**
   * Calculate the Frobenius norm of the matrix
   * @returns {number} Frobenius norm
   */
  norm() {
    // Use StandardMath for matrix norm
    return StandardMath.Matrix.norm(this.values);
  }

  /**
   * Check if this matrix equals another matrix
   * @param {Matrix|Array<Array<number>>} other - Other matrix
   * @param {number} [epsilon=Number.EPSILON] - Tolerance for floating-point comparison
   * @returns {boolean} True if matrices are equal
   */
  equals(other, epsilon = Number.EPSILON) {
    const otherMatrix = other instanceof Matrix ? other : new Matrix(other);

    if (this.rows !== otherMatrix.rows || this.cols !== otherMatrix.cols) {
      return false;
    }

    for (let i = 0; i < this.rows; i++) {
      for (let j = 0; j < this.cols; j++) {
        if (Math.abs(this.values[i][j] - otherMatrix.values[i][j]) > epsilon) {
          return false;
        }
      }
    }

    return true;
  }

  /**
   * Apply a function to each element of the matrix
   * @param {Function} fn - Function to apply
   * @returns {Matrix} New matrix with applied function
   */
  map(fn) {
    const result = Array(this.rows)
      .fill()
      .map((_, i) =>
        Array(this.cols)
          .fill(0)
          .map((_, j) => fn(this.values[i][j], i, j)),
      );

    return new Matrix(result);
  }

  /**
   * Create a string representation of the matrix
   * @returns {string} String representation
   */
  toString() {
    return this.values.map((row) => `[${row.join(", ")}]`).join("\n");
  }
}

/**
 * Export module
 */
module.exports = {
  Vector,
  Matrix,
};
