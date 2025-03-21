/**
 * Linear Algebra Module for PrimeOS
 * Implements vector and matrix operations with mathematical precision guarantees
 * Extends the Prime.math namespace
 */

// Import required modules
const Prime = require('../../mathematics.js');

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
    } else if (typeof values === 'number' && values >= 0) {
      this.values = new Array(values).fill(0);
    } else {
      throw new Prime.ValidationError('Vector constructor requires array or positive dimension');
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
      throw new Prime.MathematicalError('Vectors must have the same dimension for addition');
    }
    
    // Use compensated summation for precision
    const result = new Array(this.dimension);
    for (let i = 0; i < this.dimension; i++) {
      result[i] = this.values[i] + otherValues[i];
    }
    
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
      throw new Prime.MathematicalError('Vectors must have the same dimension for subtraction');
    }
    
    const result = new Array(this.dimension);
    for (let i = 0; i < this.dimension; i++) {
      result[i] = this.values[i] - otherValues[i];
    }
    
    return new Vector(result);
  }

  /**
   * Multiply vector by a scalar
   * @param {number} scalar - Scalar value
   * @returns {Vector} Scaled vector
   */
  scale(scalar) {
    if (typeof scalar !== 'number') {
      throw new Prime.ValidationError('Scale factor must be a number');
    }
    
    const result = this.values.map(v => v * scalar);
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
      throw new Prime.MathematicalError('Vectors must have the same dimension for dot product');
    }
    
    // Use either ExtremePrecision module or calculate directly
    if (Prime.ExtremePrecision && Prime.ExtremePrecision.dotProduct) {
      return Prime.ExtremePrecision.dotProduct(this.values, otherValues);
    } else {
      // Direct calculation with Kahan summation for precision
      let sum = 0;
      let compensation = 0;
      
      for (let i = 0; i < this.dimension; i++) {
        const y = this.values[i] * otherValues[i] - compensation;
        const t = sum + y;
        compensation = (t - sum) - y;
        sum = t;
      }
      
      return sum;
    }
  }

  /**
   * Calculate the cross product with another vector (3D only)
   * @param {Vector|Array<number>} other - Other vector
   * @returns {Vector} Cross product
   */
  cross(other) {
    const otherValues = other instanceof Vector ? other.values : other;
    
    if (this.dimension !== 3 || otherValues.length !== 3) {
      throw new Prime.MathematicalError('Cross product requires 3D vectors');
    }
    
    const [a1, a2, a3] = this.values;
    const [b1, b2, b3] = otherValues;
    
    return new Vector([
      a2 * b3 - a3 * b2,
      a3 * b1 - a1 * b3,
      a1 * b2 - a2 * b1
    ]);
  }

  /**
   * Calculate the angle between this vector and another
   * @param {Vector|Array<number>} other - Other vector
   * @returns {number} Angle in radians
   */
  angleBetween(other) {
    const otherValues = other instanceof Vector ? other.values : other;
    
    const dotProduct = this.dot(otherValues);
    
    // Calculate norm for the other vector
    let otherNorm;
    if (Prime.ExtremePrecision && Prime.ExtremePrecision.norm) {
      otherNorm = Prime.ExtremePrecision.norm(otherValues);
    } else {
      // Calculate the norm directly
      const otherVec = other instanceof Vector ? other : new Vector(otherValues);
      otherNorm = otherVec.norm();
    }
    
    const normProduct = this.norm() * otherNorm;
    
    // Handle numerical stability for angles
    if (Math.abs(normProduct) < Number.EPSILON) {
      throw new Prime.MathematicalError('Cannot compute angle with zero vectors');
    }
    
    const cosTheta = dotProduct / normProduct;
    
    // Numerical stability - clamp cosTheta to [-1, 1]
    const clampedCosTheta = Math.max(-1, Math.min(1, cosTheta));
    
    return Math.acos(clampedCosTheta);
  }

  /**
   * Project this vector onto another vector
   * @param {Vector|Array<number>} other - Vector to project onto
   * @returns {Vector} Projection vector
   */
  projectOnto(other) {
    const otherValues = other instanceof Vector ? other.values : other;
    
    const otherDot = Prime.ExtremePrecision.dotProduct(otherValues, otherValues);
    if (Math.abs(otherDot) < Number.EPSILON) {
      throw new Prime.MathematicalError('Cannot project onto zero vector');
    }
    
    const scalar = this.dot(otherValues) / otherDot;
    
    return new Vector(otherValues).scale(scalar);
  }

  /**
   * Calculate the norm (magnitude) of the vector
   * @param {number} [p=2] - The order of the norm (1 for L1, 2 for L2, etc.)
   * @returns {number} Vector norm
   */
  norm(p = 2) {
    if (Prime.ExtremePrecision && Prime.ExtremePrecision.norm) {
      return Prime.ExtremePrecision.norm(this.values, p);
    } else {
      // Calculate norm directly
      if (p === 2) {
        // Euclidean norm (L2)
        let sum = 0;
        let compensation = 0;
        
        // Use Kahan summation for better precision
        for (let i = 0; i < this.dimension; i++) {
          const squared = this.values[i] * this.values[i];
          const y = squared - compensation;
          const t = sum + y;
          compensation = (t - sum) - y;
          sum = t;
        }
        
        return Math.sqrt(Math.max(0, sum));
      } else if (p === 1) {
        // Manhattan norm (L1)
        let sum = 0;
        
        for (let i = 0; i < this.dimension; i++) {
          sum += Math.abs(this.values[i]);
        }
        
        return sum;
      } else if (p === Infinity || p === 'inf') {
        // Maximum norm (L∞)
        let max = 0;
        
        for (let i = 0; i < this.dimension; i++) {
          const abs = Math.abs(this.values[i]);
          if (abs > max) {
            max = abs;
          }
        }
        
        return max;
      } else {
        // General case (Lp)
        let sum = 0;
        
        for (let i = 0; i < this.dimension; i++) {
          sum += Math.pow(Math.abs(this.values[i]), p);
        }
        
        return Math.pow(sum, 1 / p);
      }
    }
  }

  /**
   * Normalize the vector to unit length
   * @returns {Vector} Normalized vector
   */
  normalize() {
    const magnitude = this.norm();
    
    if (magnitude < Number.EPSILON) {
      throw new Prime.MathematicalError('Cannot normalize zero vector');
    }
    
    return this.scale(1 / magnitude);
  }

  /**
   * Calculate the distance to another vector
   * @param {Vector|Array<number>} other - Other vector
   * @param {number} [p=2] - The order of the norm (1 for L1, 2 for L2, etc.)
   * @returns {number} Distance
   */
  distance(other, p = 2) {
    const diff = this.subtract(other);
    return diff.norm(p);
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
    return `[${this.values.join(', ')}]`;
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
          throw new Prime.ValidationError('All rows must have the same length');
        }
      }
      
      // Deep copy the values
      this.values = values.map(row => [...row]);
    } else if (Array.isArray(values) && typeof rows === 'number' && typeof cols === 'number') {
      // Flat array with dimensions
      if (values.length !== rows * cols) {
        throw new Prime.ValidationError('Invalid dimensions for flat array');
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
    } else if (typeof values === 'number' && typeof rows === 'number') {
      // Create matrix with dimensions and default value 0
      this.rows = values;
      this.cols = rows;
      this.values = Array(this.rows).fill().map(() => Array(this.cols).fill(0));
    } else {
      throw new Prime.ValidationError('Invalid matrix constructor arguments');
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
    return this.values.map(row => [...row]);
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
    const values = Array(rows).fill().map(() => Array(cols).fill(1));
    return new Matrix(values);
  }

  /**
   * Create an identity matrix
   * @param {number} size - Matrix size
   * @returns {Matrix} Identity matrix
   */
  static identity(size) {
    const values = Array(size).fill().map((_, i) => 
      Array(size).fill(0).map((_, j) => i === j ? 1 : 0)
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
    
    const values = Array(size).fill().map((_, i) => 
      Array(size).fill(0).map((_, j) => i === j ? diag[i] : 0)
    );
    
    return new Matrix(values);
  }

  /**
   * Add another matrix to this one
   * @param {Matrix|Array<Array<number>>} other - Matrix to add
   * @returns {Matrix} Result of addition
   */
  add(other) {
    const otherMatrix = other instanceof Matrix ? other : new Matrix(other);
    
    if (this.rows !== otherMatrix.rows || this.cols !== otherMatrix.cols) {
      throw new Prime.MathematicalError('Matrices must have the same shape for addition');
    }
    
    const result = Array(this.rows).fill().map((_, i) => 
      Array(this.cols).fill(0).map((_, j) => 
        this.values[i][j] + otherMatrix.values[i][j]
      )
    );
    
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
      throw new Prime.MathematicalError('Matrices must have the same shape for subtraction');
    }
    
    const result = Array(this.rows).fill().map((_, i) => 
      Array(this.cols).fill(0).map((_, j) => 
        this.values[i][j] - otherMatrix.values[i][j]
      )
    );
    
    return new Matrix(result);
  }

  /**
   * Multiply matrix by a scalar
   * @param {number} scalar - Scalar value
   * @returns {Matrix} Scaled matrix
   */
  scale(scalar) {
    if (typeof scalar !== 'number') {
      throw new Prime.ValidationError('Scale factor must be a number');
    }
    
    const result = this.values.map(row => row.map(v => v * scalar));
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
    this._checkMultiplyDimensions(otherMatrix);
    
    const result = Array(this.rows).fill().map(() => Array(otherMatrix.cols).fill(0));
    
    // Efficient matrix multiplication with cache-friendly order
    for (let i = 0; i < this.rows; i++) {
      for (let k = 0; k < this.cols; k++) {
        const aik = this.values[i][k];
        for (let j = 0; j < otherMatrix.cols; j++) {
          result[i][j] += aik * otherMatrix.values[k][j];
        }
      }
    }
    
    return new Matrix(result);
  }

  /**
   * Multiply matrix by a vector
   * @private
   * @param {Vector} vector - Vector to multiply
   * @returns {Vector} Result of multiplication
   */
  _multiplyVector(vector) {
    if (this.cols !== vector.dimension) {
      throw new Prime.MathematicalError('Matrix and vector dimensions incompatible for multiplication');
    }
    
    const result = new Array(this.rows).fill(0);
    
    for (let i = 0; i < this.rows; i++) {
      // Use compensated summation for precision
      let sum = 0;
      let compensation = 0;
      
      for (let j = 0; j < this.cols; j++) {
        const val = this.values[i][j] * vector.values[j];
        const y = val - compensation;
        const t = sum + y;
        compensation = (t - sum) - y;
        sum = t;
      }
      
      result[i] = sum;
    }
    
    return new Vector(result);
  }
  
  /**
   * Check if the dimensions are compatible for matrix multiplication
   * @private
   * @param {Matrix} otherMatrix - Matrix to multiply with
   */
  _checkMultiplyDimensions(otherMatrix) {
    if (this.cols !== otherMatrix.rows) {
      if (Prime.MathematicalError) {
        throw new Prime.MathematicalError(
          `Matrix dimensions incompatible for multiplication: ${this.rows}x${this.cols} and ${otherMatrix.rows}x${otherMatrix.cols}`
        );
      } else {
        throw new Error(
          `Matrix dimensions incompatible for multiplication: ${this.rows}x${this.cols} and ${otherMatrix.rows}x${otherMatrix.cols}`
        );
      }
    }
  }

  /**
   * Calculate the transpose of the matrix
   * @returns {Matrix} Transposed matrix
   */
  transpose() {
    const result = Array(this.cols).fill().map(() => Array(this.rows).fill(0));
    
    for (let i = 0; i < this.rows; i++) {
      for (let j = 0; j < this.cols; j++) {
        result[j][i] = this.values[i][j];
      }
    }
    
    return new Matrix(result);
  }

  /**
   * Calculate the trace of the matrix
   * @returns {number} Trace (sum of diagonal elements)
   */
  trace() {
    if (this.rows !== this.cols) {
      throw new Prime.MathematicalError('Trace requires a square matrix');
    }
    
    let sum = 0;
    for (let i = 0; i < this.rows; i++) {
      sum += this.values[i][i];
    }
    
    return sum;
  }

  /**
   * Calculate the determinant of the matrix
   * @returns {number} Determinant
   */
  determinant() {
    if (this.rows !== this.cols) {
      throw new Prime.MathematicalError('Determinant requires a square matrix');
    }
    
    // Handle special cases for efficiency
    if (this.rows === 1) {
      return this.values[0][0];
    }
    
    if (this.rows === 2) {
      return this.values[0][0] * this.values[1][1] - this.values[0][1] * this.values[1][0];
    }
    
    if (this.rows === 3) {
      const [a, b, c] = this.values[0];
      const [d, e, f] = this.values[1];
      const [g, h, i] = this.values[2];
      
      return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g);
    }
    
    // For larger matrices, use LU decomposition
    return this._determinantLU();
  }

  /**
   * Calculate determinant using LU decomposition
   * @private
   * @returns {number} Determinant
   */
  _determinantLU() {
    const { L, U, P, exchanges } = this.luDecomposition();
    
    // Determinant of triangular matrices is the product of diagonal elements
    let detL = 1;
    let detU = 1;
    
    for (let i = 0; i < this.rows; i++) {
      detL *= L.values[i][i];
      detU *= U.values[i][i];
    }
    
    // Determinant is det(L) * det(U) * (-1)^exchanges
    const sign = exchanges % 2 === 0 ? 1 : -1;
    return sign * detL * detU;
  }

  /**
   * Perform LU decomposition with partial pivoting
   * @returns {Object} Object with L, U, P matrices and exchanges count
   */
  luDecomposition() {
    if (this.rows !== this.cols) {
      throw new Prime.MathematicalError('LU decomposition requires a square matrix');
    }
    
    const n = this.rows;
    const L = Matrix.zeros(n, n);
    const U = Matrix.zeros(n, n);
    const P = Matrix.identity(n);
    
    // Create a copy of the matrix to work with
    const A = this.toArray();
    let exchanges = 0;
    
    // Perform decomposition
    for (let k = 0; k < n; k++) {
      // Find pivot
      let pivot = k;
      let maxVal = Math.abs(A[k][k]);
      
      for (let i = k + 1; i < n; i++) {
        const absValue = Math.abs(A[i][k]);
        if (absValue > maxVal) {
          maxVal = absValue;
          pivot = i;
        }
      }
      
      // Check for singularity
      if (Math.abs(A[pivot][k]) < Number.EPSILON) {
        throw new Prime.MathematicalError('Matrix is singular, LU decomposition failed');
      }
      
      // Swap rows if necessary
      if (pivot !== k) {
        [A[k], A[pivot]] = [A[pivot], A[k]];
        [P.values[k], P.values[pivot]] = [P.values[pivot], P.values[k]];
        exchanges++;
      }
      
      // Compute multipliers and eliminate
      for (let i = k + 1; i < n; i++) {
        A[i][k] = A[i][k] / A[k][k];
        
        for (let j = k + 1; j < n; j++) {
          A[i][j] -= A[i][k] * A[k][j];
        }
      }
    }
    
    // Extract L and U from A
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        if (i > j) {
          // Lower triangular part (below diagonal)
          L.values[i][j] = A[i][j];
        } else if (i === j) {
          // Diagonal of L is 1
          L.values[i][j] = 1;
          // Diagonal of U
          U.values[i][j] = A[i][j];
        } else {
          // Upper triangular part (above diagonal)
          U.values[i][j] = A[i][j];
        }
      }
    }
    
    return { L, U, P, exchanges };
  }

  /**
   * Calculate the inverse of the matrix
   * @returns {Matrix} Inverse matrix
   */
  inverse() {
    if (this.rows !== this.cols) {
      throw new Prime.MathematicalError('Inverse requires a square matrix');
    }
    
    const n = this.rows;
    
    // Handle 1x1 and 2x2 matrices directly for efficiency
    if (n === 1) {
      const det = this.values[0][0];
      if (Math.abs(det) < Number.EPSILON) {
        throw new Prime.MathematicalError('Matrix is singular, cannot compute inverse');
      }
      return new Matrix([[1 / det]]);
    }
    
    if (n === 2) {
      const det = this.determinant();
      if (Math.abs(det) < Number.EPSILON) {
        throw new Prime.MathematicalError('Matrix is singular, cannot compute inverse');
      }
      
      const [a, b] = this.values[0];
      const [c, d] = this.values[1];
      
      return new Matrix([
        [d / det, -b / det],
        [-c / det, a / det]
      ]);
    }
    
    // For larger matrices, use LU decomposition
    return this._inverseLU();
  }

  /**
   * Calculate inverse using LU decomposition
   * @private
   * @returns {Matrix} Inverse matrix
   */
  _inverseLU() {
    const n = this.rows;
    const { L, U, P } = this.luDecomposition();
    const result = Matrix.zeros(n, n);
    
    // Solve for each column of the inverse
    for (let j = 0; j < n; j++) {
      // Create the j-th unit vector of P
      const e = new Array(n).fill(0);
      for (let i = 0; i < n; i++) {
        e[i] = P.values[i][j];
      }
      
      // Solve L * y = e by forward substitution
      const y = new Array(n).fill(0);
      for (let i = 0; i < n; i++) {
        let sum = 0;
        for (let k = 0; k < i; k++) {
          sum += L.values[i][k] * y[k];
        }
        y[i] = e[i] - sum;
      }
      
      // Solve U * x = y by back substitution
      for (let i = n - 1; i >= 0; i--) {
        let sum = 0;
        for (let k = i + 1; k < n; k++) {
          sum += U.values[i][k] * result.values[k][j];
        }
        
        if (Math.abs(U.values[i][i]) < Number.EPSILON) {
          throw new Prime.MathematicalError('Matrix is singular, cannot compute inverse');
        }
        
        result.values[i][j] = (y[i] - sum) / U.values[i][i];
      }
    }
    
    return result;
  }

  /**
   * Solve system of linear equations Ax = b
   * @param {Vector|Array<number>} b - Right-hand side vector
   * @returns {Vector} Solution vector
   */
  solve(b) {
    const bVector = b instanceof Vector ? b : new Vector(b);
    
    if (this.rows !== this.cols) {
      throw new Prime.MathematicalError('System matrix must be square');
    }
    
    if (this.rows !== bVector.dimension) {
      throw new Prime.MathematicalError('Vector dimension must match matrix size');
    }
    
    // Use LU decomposition to solve the system
    const { L, U, P } = this.luDecomposition();
    const n = this.rows;
    
    // Apply the permutation matrix to the right-hand side
    const pb = new Array(n);
    for (let i = 0; i < n; i++) {
      let sum = 0;
      for (let j = 0; j < n; j++) {
        sum += P.values[i][j] * bVector.values[j];
      }
      pb[i] = sum;
    }
    
    // Solve Ly = Pb by forward substitution
    const y = new Array(n);
    for (let i = 0; i < n; i++) {
      let sum = 0;
      for (let j = 0; j < i; j++) {
        sum += L.values[i][j] * y[j];
      }
      y[i] = pb[i] - sum; // Since L has 1's on the diagonal
    }
    
    // Solve Ux = y by back substitution
    const x = new Array(n);
    for (let i = n - 1; i >= 0; i--) {
      let sum = 0;
      for (let j = i + 1; j < n; j++) {
        sum += U.values[i][j] * x[j];
      }
      
      if (Math.abs(U.values[i][i]) < Number.EPSILON) {
        throw new Prime.MathematicalError('Matrix is singular, cannot solve system');
      }
      
      x[i] = (y[i] - sum) / U.values[i][i];
    }
    
    return new Vector(x);
  }

  /**
   * Calculate the eigenvalues and eigenvectors of the matrix
   * @returns {Object} Object with eigenvalues and eigenvectors
   */
  eigen() {
    if (this.rows !== this.cols) {
      throw new Prime.MathematicalError('Eigendecomposition requires a square matrix');
    }
    
    // Check if we can use ExtremePrecision
    if (Prime.ExtremePrecision && Prime.ExtremePrecision.eigen) {
      const result = Prime.ExtremePrecision.eigen(this.values);
      
      // Convert eigenvectors to Vector objects
      const eigenvectors = result.vectors.map(v => new Vector(v));
      
      return {
        values: result.values,
        vectors: eigenvectors
      };
    }
    
    // Basic implementation for 2x2 matrices
    if (this.rows === 2) {
      return this._eigen2x2();
    }
    
    // For symmetric matrices, use QR iteration
    // Check if matrix is symmetric
    const isSymmetric = this._isSymmetric();
    
    if (isSymmetric) {
      return this._eigenSymmetric();
    }
    
    // For non-symmetric matrices, use power iteration for dominant eigenpair
    // and deflation for subsequent ones
    return this._eigenPowerMethod();
  }
  
  /**
   * Check if matrix is symmetric
   * @private
   * @returns {boolean} True if symmetric
   */
  _isSymmetric() {
    if (this.rows !== this.cols) {
      return false;
    }
    
    const n = this.rows;
    const epsilon = 1e-10;
    
    for (let i = 0; i < n; i++) {
      for (let j = i + 1; j < n; j++) {
        if (Math.abs(this.values[i][j] - this.values[j][i]) > epsilon) {
          return false;
        }
      }
    }
    
    return true;
  }
  
  /**
   * Eigendecomposition for 2x2 matrices
   * @private
   * @returns {Object} Eigenvalues and eigenvectors
   */
  _eigen2x2() {
    const [[a, b], [c, d]] = this.values;
    
    // Calculate eigenvalues
    const trace = a + d;
    const det = a * d - b * c;
    
    // Discriminant
    const discriminant = trace * trace - 4 * det;
    
    if (discriminant < 0) {
      // Complex eigenvalues, not implemented
      throw new Prime.MathematicalError('Complex eigenvalues not implemented');
    }
    
    const sqrtDiscriminant = Math.sqrt(discriminant);
    const lambda1 = (trace + sqrtDiscriminant) / 2;
    const lambda2 = (trace - sqrtDiscriminant) / 2;
    
    // Calculate eigenvectors
    let v1, v2;
    
    if (Math.abs(b) > 1e-10) {
      v1 = new Vector([b, lambda1 - a]).normalize();
      v2 = new Vector([b, lambda2 - a]).normalize();
    } else if (Math.abs(c) > 1e-10) {
      v1 = new Vector([lambda1 - d, c]).normalize();
      v2 = new Vector([lambda2 - d, c]).normalize();
    } else {
      // Diagonal matrix
      v1 = new Vector([1, 0]);
      v2 = new Vector([0, 1]);
    }
    
    return {
      values: [lambda1, lambda2],
      vectors: [v1, v2]
    };
  }
  
  /**
   * Eigendecomposition for symmetric matrices using QR iteration
   * @private
   * @returns {Object} Eigenvalues and eigenvectors
   */
  _eigenSymmetric() {
    const n = this.rows;
    let A = this.toArray();
    let Q = Matrix.identity(n).values;
    
    const maxIterations = 100;
    const epsilon = 1e-10;
    
    // QR iteration
    for (let iter = 0; iter < maxIterations; iter++) {
      // Check if A is nearly diagonal
      let isNearlyDiagonal = true;
      for (let i = 0; i < n; i++) {
        for (let j = 0; j < n; j++) {
          if (i !== j && Math.abs(A[i][j]) > epsilon) {
            isNearlyDiagonal = false;
            break;
          }
        }
        if (!isNearlyDiagonal) break;
      }
      
      if (isNearlyDiagonal) break;
      
      // QR decomposition using Gram-Schmidt
      let R = Array(n).fill().map(() => Array(n).fill(0));
      let Qi = Array(n).fill().map(() => Array(n).fill(0));
      
      // Get matrix columns
      let columns = [];
      for (let j = 0; j < n; j++) {
        columns.push(Array(n).fill(0).map((_, i) => A[i][j]));
      }
      
      // Gram-Schmidt process
      for (let j = 0; j < n; j++) {
        let q = [...columns[j]];
        
        for (let i = 0; i < j; i++) {
          // Calculate dot product
          let dot = 0;
          for (let k = 0; k < n; k++) {
            dot += q[k] * Qi[k][i];
          }
          
          R[i][j] = dot;
          
          // Subtract projection
          for (let k = 0; k < n; k++) {
            q[k] -= dot * Qi[k][i];
          }
        }
        
        // Normalize
        let norm = 0;
        for (let i = 0; i < n; i++) {
          norm += q[i] * q[i];
        }
        norm = Math.sqrt(norm);
        
        if (norm < epsilon) {
          // Linearly dependent
          throw new Prime.MathematicalError('QR decomposition failed for eigendecomposition');
        }
        
        for (let i = 0; i < n; i++) {
          Qi[i][j] = q[i] / norm;
        }
        
        R[j][j] = norm;
      }
      
      // Update A = R * Q
      let newA = Array(n).fill().map(() => Array(n).fill(0));
      for (let i = 0; i < n; i++) {
        for (let j = 0; j < n; j++) {
          for (let k = 0; k < n; k++) {
            newA[i][j] += R[i][k] * Qi[j][k];
          }
        }
      }
      A = newA;
      
      // Update Q matrix (eigenvectors)
      let newQ = Array(n).fill().map(() => Array(n).fill(0));
      for (let i = 0; i < n; i++) {
        for (let j = 0; j < n; j++) {
          for (let k = 0; k < n; k++) {
            newQ[i][j] += Q[i][k] * Qi[j][k];
          }
        }
      }
      Q = newQ;
    }
    
    // Extract eigenvalues from diagonal
    const eigenvalues = [];
    for (let i = 0; i < n; i++) {
      eigenvalues.push(A[i][i]);
    }
    
    // Sort eigenvalues and eigenvectors by decreasing eigenvalue
    const indices = Array(n).fill().map((_, i) => i);
    indices.sort((a, b) => Math.abs(eigenvalues[b]) - Math.abs(eigenvalues[a]));
    
    const sortedValues = indices.map(i => eigenvalues[i]);
    const sortedVectors = indices.map(i => {
      const vector = Array(n);
      for (let j = 0; j < n; j++) {
        vector[j] = Q[j][i];
      }
      return new Vector(vector);
    });
    
    return {
      values: sortedValues,
      vectors: sortedVectors
    };
  }
  
  /**
   * Eigendecomposition using power method for non-symmetric matrices
   * @private
   * @returns {Object} Eigenvalues and eigenvectors
   */
  _eigenPowerMethod() {
    const n = this.rows;
    const maxIterations = 100;
    const epsilon = 1e-10;
    
    // Create a copy of the matrix
    let A = this.toArray();
    
    // Storage for eigenvalues and eigenvectors
    const eigenvalues = [];
    const eigenvectors = [];
    
    // Power iteration for each eigenvalue
    for (let eigenIndex = 0; eigenIndex < n; eigenIndex++) {
      // Start with a random vector
      let v = Array(n).fill(0);
      v[eigenIndex % n] = 1; // Try different starting vectors
      
      let lambda = 0;
      let prevLambda = 0;
      
      // Power iteration
      for (let iter = 0; iter < maxIterations; iter++) {
        // Multiply A * v
        let Av = Array(n).fill(0);
        for (let i = 0; i < n; i++) {
          for (let j = 0; j < n; j++) {
            Av[i] += A[i][j] * v[j];
          }
        }
        
        // Find the largest component
        let maxAbs = 0;
        let maxIndex = 0;
        for (let i = 0; i < n; i++) {
          const abs = Math.abs(Av[i]);
          if (abs > maxAbs) {
            maxAbs = abs;
            maxIndex = i;
          }
        }
        
        // Normalize with respect to the largest element
        lambda = Av[maxIndex];
        
        // Check for convergence
        if (Math.abs(lambda - prevLambda) < epsilon * Math.abs(lambda)) {
          break;
        }
        
        prevLambda = lambda;
        
        // Normalize v
        for (let i = 0; i < n; i++) {
          v[i] = Av[i] / lambda;
        }
      }
      
      // Store eigenvalue and eigenvector
      eigenvalues.push(lambda);
      eigenvectors.push(new Vector(v));
      
      // Deflation: remove this eigenvalue's contribution
      for (let i = 0; i < n; i++) {
        for (let j = 0; j < n; j++) {
          A[i][j] -= lambda * v[i] * v[j];
        }
      }
    }
    
    return {
      values: eigenvalues,
      vectors: eigenvectors
    };
  }

  /**
   * Perform QR decomposition
   * @returns {Object} Object with Q and R matrices
   */
  qrDecomposition() {
    if (this.rows < this.cols) {
      throw new Prime.MathematicalError('QR decomposition requires rows >= columns');
    }
    
    const m = this.rows;
    const n = this.cols;
    
    // Initialize Q and R
    const Q = Matrix.zeros(m, m);
    const R = Matrix.zeros(m, n);
    
    // Extract columns of original matrix
    const columns = [];
    for (let j = 0; j < n; j++) {
      const col = new Array(m);
      for (let i = 0; i < m; i++) {
        col[i] = this.values[i][j];
      }
      columns.push(col);
    }
    
    // Modified Gram-Schmidt process
    const orthogonalBasis = [];
    
    for (let j = 0; j < n; j++) {
      let q = new Vector(columns[j]);
      
      // Orthogonalize against previous vectors
      for (let i = 0; i < j; i++) {
        const qi = orthogonalBasis[i];
        const projection = q.dot(qi);
        R.values[i][j] = projection;
        
        // Subtract projection
        q = q.subtract(qi.scale(projection));
      }
      
      // Normalize
      const norm = q.norm();
      
      // Handle potential linear dependence
      if (norm < 1e-10) {
        // Column is linearly dependent
        R.values[j][j] = 0;
        orthogonalBasis.push(new Vector(m).scale(0));
      } else {
        const normalized = q.scale(1 / norm);
        R.values[j][j] = norm;
        orthogonalBasis.push(normalized);
        
        // Store in Q
        for (let i = 0; i < m; i++) {
          Q.values[i][j] = normalized.values[i];
        }
      }
    }
    
    // Complete Q with orthogonal basis for null space (if m > n)
    if (m > n) {
      // Find additional orthogonal vectors to complete the basis
      for (let j = n; j < m; j++) {
        // Start with canonical basis vector e_j
        const e = new Array(m).fill(0);
        e[j] = 1;
        let q = new Vector(e);
        
        // Orthogonalize against previous vectors
        for (let i = 0; i < j; i++) {
          const qi = i < n ? orthogonalBasis[i] : new Vector(Q.values.map(row => row[i]));
          const projection = q.dot(qi);
          
          // Subtract projection
          q = q.subtract(qi.scale(projection));
        }
        
        // Normalize
        const norm = q.norm();
        
        if (norm < 1e-10) {
          // Try a different vector
          e.fill(0);
          e[(j + 1) % m] = 1;
          q = new Vector(e);
          
          // Orthogonalize and normalize again
          for (let i = 0; i < j; i++) {
            const qi = i < n ? orthogonalBasis[i] : new Vector(Q.values.map(row => row[i]));
            q = q.subtract(qi.scale(q.dot(qi)));
          }
          
          const newNorm = q.norm();
          if (newNorm < 1e-10) {
            throw new Prime.MathematicalError('QR decomposition failed to find orthogonal basis');
          }
          
          const normalized = q.scale(1 / newNorm);
          
          // Store in Q
          for (let i = 0; i < m; i++) {
            Q.values[i][j] = normalized.values[i];
          }
        } else {
          const normalized = q.scale(1 / norm);
          
          // Store in Q
          for (let i = 0; i < m; i++) {
            Q.values[i][j] = normalized.values[i];
          }
        }
      }
    }
    
    return { Q, R: new Matrix(R.values.slice(0, n)) };
  }

  /**
   * Calculate the singular value decomposition (SVD)
   * @returns {Object} Object with U, S, and V matrices
   */
  svd() {
    // For small matrices, use direct approach
    if (this.rows <= 3 && this.cols <= 3) {
      return this._svdDirect();
    }
    
    // For larger matrices, use QR iteration
    const A = this.toArray();
    const m = this.rows;
    const n = this.cols;
    
    // Compute A^T A or AA^T (whichever is smaller)
    let useTranspose = m > n;
    let B;
    
    if (useTranspose) {
      // Compute A^T A (n x n matrix)
      B = Array(n).fill().map(() => Array(n).fill(0));
      
      for (let i = 0; i < n; i++) {
        for (let j = 0; j < n; j++) {
          for (let k = 0; k < m; k++) {
            B[i][j] += A[k][i] * A[k][j];
          }
        }
      }
    } else {
      // Compute AA^T (m x m matrix)
      B = Array(m).fill().map(() => Array(m).fill(0));
      
      for (let i = 0; i < m; i++) {
        for (let j = 0; j < m; j++) {
          for (let k = 0; k < n; k++) {
            B[i][j] += A[i][k] * A[j][k];
          }
        }
      }
    }
    
    // Compute eigendecomposition of B
    const bMatrix = new Matrix(B);
    const { values: eigenvalues, vectors: eigenvectors } = bMatrix.eigen();
    
    // The singular values are the square roots of the eigenvalues
    const singularValues = eigenvalues.map(v => Math.sqrt(Math.abs(v)));
    
    // Organize singular values in descending order
    const indices = Array(singularValues.length).fill().map((_, i) => i);
    indices.sort((a, b) => singularValues[b] - singularValues[a]);
    
    const sortedSingularValues = indices.map(i => singularValues[i]);
    const sortedEigenvectors = indices.map(i => eigenvectors[i]);
    
    // For a non-square matrix, we need to compute the other set of singular vectors
    let U, V;
    const r = Math.min(m, n);
    
    if (useTranspose) {
      // V comes from eigenvectors of A^T A
      V = Matrix.fromArray(sortedEigenvectors.map(v => v.values));
      
      // U from U = AV/sigma
      U = Matrix.zeros(m, r);
      
      for (let i = 0; i < r; i++) {
        // Skip near-zero singular values
        if (sortedSingularValues[i] < 1e-10) continue;
        
        const v = sortedEigenvectors[i].values;
        const sigma = sortedSingularValues[i];
        
        for (let j = 0; j < m; j++) {
          let sum = 0;
          for (let k = 0; k < n; k++) {
            sum += A[j][k] * v[k];
          }
          U.values[j][i] = sum / sigma;
        }
      }
    } else {
      // U comes from eigenvectors of AA^T
      U = Matrix.fromArray(sortedEigenvectors.map(v => v.values));
      
      // V from V = A^T U/sigma
      V = Matrix.zeros(n, r);
      
      for (let i = 0; i < r; i++) {
        // Skip near-zero singular values
        if (sortedSingularValues[i] < 1e-10) continue;
        
        const u = sortedEigenvectors[i].values;
        const sigma = sortedSingularValues[i];
        
        for (let j = 0; j < n; j++) {
          let sum = 0;
          for (let k = 0; k < m; k++) {
            sum += A[k][j] * u[k];
          }
          V.values[j][i] = sum / sigma;
        }
      }
    }
    
    // Create diagonal matrix S
    const S = Matrix.zeros(r, r);
    for (let i = 0; i < r; i++) {
      S.values[i][i] = sortedSingularValues[i];
    }
    
    // Complete U and V if needed
    if (useTranspose) {
      // Complete U with orthogonal basis
      if (m > r) {
        const { Q } = U.qrDecomposition();
        U = Q;
      }
    } else {
      // Complete V with orthogonal basis
      if (n > r) {
        const { Q } = V.qrDecomposition();
        V = Q;
      }
    }
    
    return { U, S, V: V.transpose() };
  }

  /**
   * Direct SVD for small matrices
   * @private
   * @returns {Object} Object with U, S, and V matrices
   */
  _svdDirect() {
    const m = this.rows;
    const n = this.cols;
    const r = Math.min(m, n);
    
    // For 1x1 matrix
    if (m === 1 && n === 1) {
      const a = this.values[0][0];
      const s = Math.abs(a);
      const sign = a >= 0 ? 1 : -1;
      
      return {
        U: new Matrix([[sign]]),
        S: new Matrix([[s]]),
        V: new Matrix([[1]])
      };
    }
    
    // For 2x2 matrix, use direct formulation
    if (m === 2 && n === 2) {
      const [[a, b], [c, d]] = this.values;
      
      // Compute elements of A^T A
      const e = a*a + c*c;
      const f = a*b + c*d;
      const g = f;
      const h = b*b + d*d;
      
      // Compute eigenvalues of A^T A
      const trace = e + h;
      const det = e*h - f*g;
      
      const discriminant = Math.sqrt(trace*trace - 4*det);
      const lambda1 = (trace + discriminant) / 2;
      const lambda2 = (trace - discriminant) / 2;
      
      const s1 = Math.sqrt(Math.abs(lambda1));
      const s2 = Math.sqrt(Math.abs(lambda2));
      
      // Compute eigenvectors of A^T A for V
      let v1, v2;
      
      if (Math.abs(f) > 1e-10) {
        v1 = new Vector([f, lambda1 - e]).normalize().values;
        v2 = new Vector([f, lambda2 - e]).normalize().values;
      } else if (Math.abs(g) > 1e-10) {
        v1 = new Vector([lambda1 - h, g]).normalize().values;
        v2 = new Vector([lambda2 - h, g]).normalize().values;
      } else {
        // A^T A is diagonal, eigenvectors are standard basis
        v1 = e >= h ? [1, 0] : [0, 1];
        v2 = e >= h ? [0, 1] : [1, 0];
      }
      
      // Compute U from A*V/s
      const u1 = [
        (a*v1[0] + b*v1[1]) / s1,
        (c*v1[0] + d*v1[1]) / s1
      ];
      
      const u2 = [
        (a*v2[0] + b*v2[1]) / s2,
        (c*v2[0] + d*v2[1]) / s2
      ];
      
      // Normalize U vectors
      const norm1 = Math.sqrt(u1[0]*u1[0] + u1[1]*u1[1]);
      const norm2 = Math.sqrt(u2[0]*u2[0] + u2[1]*u2[1]);
      
      u1[0] /= norm1;
      u1[1] /= norm1;
      u2[0] /= norm2;
      u2[1] /= norm2;
      
      return {
        U: new Matrix([u1, u2]),
        S: new Matrix([[s1, 0], [0, s2]]),
        V: new Matrix([v1, v2])
      };
    }
    
    // For other small matrices, revert to the general algorithm
    // but with higher precision requirements
    const A = this.toArray();
    const useTranspose = m > n;
    let B;
    
    if (useTranspose) {
      // Compute A^T A (n x n matrix)
      B = Array(n).fill().map(() => Array(n).fill(0));
      
      for (let i = 0; i < n; i++) {
        for (let j = 0; j < n; j++) {
          for (let k = 0; k < m; k++) {
            B[i][j] += A[k][i] * A[k][j];
          }
        }
      }
    } else {
      // Compute AA^T (m x m matrix)
      B = Array(m).fill().map(() => Array(m).fill(0));
      
      for (let i = 0; i < m; i++) {
        for (let j = 0; j < m; j++) {
          for (let k = 0; k < n; k++) {
            B[i][j] += A[i][k] * A[j][k];
          }
        }
      }
    }
    
    // Compute eigendecomposition with higher precision
    const result = Prime.ExtremePrecision.eigen(B, { maxIterations: 200 });
    
    // Extract and sort singular values and vectors
    const singularValues = result.values.map(v => Math.sqrt(Math.abs(v)));
    
    // Organize singular values in descending order
    const indices = Array(singularValues.length).fill().map((_, i) => i);
    indices.sort((a, b) => singularValues[b] - singularValues[a]);
    
    const sortedSingularValues = indices.map(i => singularValues[i]);
    const sortedEigenvectors = indices.map(i => result.vectors[i]);
    
    let U, V;
    
    if (useTranspose) {
      // V comes from eigenvectors of A^T A
      V = new Matrix(sortedEigenvectors);
      
      // U from U = AV/sigma
      U = Matrix.zeros(m, r);
      
      for (let i = 0; i < r; i++) {
        if (sortedSingularValues[i] < 1e-10) continue;
        
        const v = sortedEigenvectors[i];
        const sigma = sortedSingularValues[i];
        
        for (let j = 0; j < m; j++) {
          let sum = 0;
          for (let k = 0; k < n; k++) {
            sum += A[j][k] * v[k];
          }
          U.values[j][i] = sum / sigma;
        }
      }
    } else {
      // U comes from eigenvectors of AA^T
      U = new Matrix(sortedEigenvectors);
      
      // V from V = A^T U/sigma
      V = Matrix.zeros(n, r);
      
      for (let i = 0; i < r; i++) {
        if (sortedSingularValues[i] < 1e-10) continue;
        
        const u = sortedEigenvectors[i];
        const sigma = sortedSingularValues[i];
        
        for (let j = 0; j < n; j++) {
          let sum = 0;
          for (let k = 0; k < m; k++) {
            sum += A[k][j] * u[k];
          }
          V.values[j][i] = sum / sigma;
        }
      }
    }
    
    // Create diagonal matrix S
    const S = Matrix.zeros(r, r);
    for (let i = 0; i < r; i++) {
      S.values[i][i] = sortedSingularValues[i];
    }
    
    return { U, S, V: V.transpose() };
  }

  /**
   * Calculate the condition number of the matrix
   * @returns {number} Condition number
   */
  conditionNumber() {
    const { S } = this.svd();
    
    // Condition number is the ratio of largest to smallest singular value
    const singularValues = [];
    for (let i = 0; i < Math.min(S.rows, S.cols); i++) {
      const s = S.values[i][i];
      if (s > 1e-12) {
        singularValues.push(s);
      }
    }
    
    if (singularValues.length === 0) {
      return Infinity;
    }
    
    const maxSingularValue = Math.max(...singularValues);
    const minSingularValue = Math.min(...singularValues);
    
    return maxSingularValue / minSingularValue;
  }

  /**
   * Calculate the rank of the matrix
   * @param {number} [tolerance=1e-10] - Tolerance for singular values
   * @returns {number} Rank
   */
  rank(tolerance = 1e-10) {
    const { S } = this.svd();
    
    let r = 0;
    for (let i = 0; i < Math.min(S.rows, S.cols); i++) {
      if (S.values[i][i] > tolerance) {
        r++;
      }
    }
    
    return r;
  }

  /**
   * Calculate the Frobenius norm of the matrix
   * @returns {number} Frobenius norm
   */
  norm() {
    let sumSquares = 0;
    
    for (let i = 0; i < this.rows; i++) {
      for (let j = 0; j < this.cols; j++) {
        sumSquares += this.values[i][j] * this.values[i][j];
      }
    }
    
    return Math.sqrt(sumSquares);
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
    const result = Array(this.rows).fill().map((_, i) => 
      Array(this.cols).fill(0).map((_, j) => fn(this.values[i][j], i, j))
    );
    
    return new Matrix(result);
  }

  /**
   * Create a string representation of the matrix
   * @returns {string} String representation
   */
  toString() {
    return this.values.map(row => `[${row.join(', ')}]`).join('\n');
  }
}

/**
 * Export module
 */
module.exports = {
  Vector,
  Matrix
};