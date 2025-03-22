/**
 * PrimeOS Math Module
 * Provides high-precision mathematical operations for vectors and matrices
 * Integrates with other PrimeOS mathematical components
 */

// Import dependencies
const Prime = require("../../mathematics.js");
const { Vector, Matrix } = require("./linalg.js");

// Define isNumber function if not available
function isNumber(value) {
  return typeof value === "number" && !isNaN(value) && isFinite(value);
}

// Define clamp function if not available
function clamp(value, min, max) {
  return Math.max(min, Math.min(max, value));
}

// Define lerp function if not available
function lerp(a, b, t) {
  return a * (1 - t) + b * t;
}

/**
 * Math module for PrimeOS.
 * Exports a comprehensive set of mathematical functions
 * and utilities with enhanced precision guarantees.
 */
const PrimeMath = {
  /**
   * Constants with high precision
   */
  constants: {
    PI: Math.PI,
    E: Math.E,
    PHI: (1 + Math.sqrt(5)) / 2, // Golden ratio
    SQRT2: Math.SQRT2,
    EPSILON: Number.EPSILON,
    MACHINE_EPSILON: 2.220446049250313e-16, // Double precision machine epsilon
    SQRT_EPSILON: Math.sqrt(Number.EPSILON),
  },

  /**
   * Vector operations
   */
  Vector: Vector,

  /**
   * Create a new vector
   * @param {Array<number>|number} values - Vector values or dimension
   * @returns {Vector} New vector
   */
  createVector: function (values) {
    return new Vector(values);
  },

  /**
   * Create a vector from an array
   * @param {Array<number>} array - Input array
   * @returns {Vector} New vector
   */
  vectorFromArray: function (array) {
    return Vector.fromArray(array);
  },

  /**
   * Create a zero vector
   * @param {number} dimension - Vector dimension
   * @returns {Vector} Zero vector
   */
  zeroVector: function (dimension) {
    return Vector.zeros(dimension);
  },

  /**
   * Create a vector of ones
   * @param {number} dimension - Vector dimension
   * @returns {Vector} Vector of ones
   */
  onesVector: function (dimension) {
    return Vector.ones(dimension);
  },

  /**
   * Create a vector with elements from start to end (inclusive)
   * @param {number} start - Start value
   * @param {number} end - End value
   * @param {number} [step=1] - Step size
   * @returns {Vector} Range vector
   */
  rangeVector: function (start, end, step = 1) {
    return Vector.range(start, end, step);
  },

  /**
   * Add two vectors
   * @param {Vector|Array<number>} v1 - First vector
   * @param {Vector|Array<number>} v2 - Second vector
   * @returns {Vector} Result of addition
   */
  addVectors: function (v1, v2) {
    const vec1 = v1 instanceof Vector ? v1 : new Vector(v1);
    return vec1.add(v2);
  },

  /**
   * Subtract two vectors
   * @param {Vector|Array<number>} v1 - First vector
   * @param {Vector|Array<number>} v2 - Second vector
   * @returns {Vector} Result of subtraction
   */
  subtractVectors: function (v1, v2) {
    const vec1 = v1 instanceof Vector ? v1 : new Vector(v1);
    return vec1.subtract(v2);
  },

  /**
   * Scale a vector by a scalar
   * @param {Vector|Array<number>} v - Vector
   * @param {number} scalar - Scalar value
   * @returns {Vector} Scaled vector
   */
  scaleVector: function (v, scalar) {
    const vec = v instanceof Vector ? v : new Vector(v);
    return vec.scale(scalar);
  },

  /**
   * Calculate the dot product of two vectors
   * @param {Vector|Array<number>} v1 - First vector
   * @param {Vector|Array<number>} v2 - Second vector
   * @returns {number} Dot product
   */
  dotProduct: function (v1, v2) {
    const vec1 = v1 instanceof Vector ? v1 : new Vector(v1);
    return vec1.dot(v2);
  },

  /**
   * Calculate the cross product of two 3D vectors
   * @param {Vector|Array<number>} v1 - First vector
   * @param {Vector|Array<number>} v2 - Second vector
   * @returns {Vector} Cross product
   */
  crossProduct: function (v1, v2) {
    const vec1 = v1 instanceof Vector ? v1 : new Vector(v1);
    return vec1.cross(v2);
  },

  /**
   * Calculate the norm (magnitude) of a vector
   * @param {Vector|Array<number>} v - Vector
   * @param {number} [p=2] - Norm order (1=L1, 2=L2/Euclidean)
   * @returns {number} Vector norm
   */
  vectorNorm: function (v, p = 2) {
    const vec = v instanceof Vector ? v : new Vector(v);
    return vec.norm(p);
  },

  /**
   * Normalize a vector to unit length
   * @param {Vector|Array<number>} v - Vector
   * @returns {Vector} Normalized vector
   */
  normalizeVector: function (v) {
    const vec = v instanceof Vector ? v : new Vector(v);
    return vec.normalize();
  },

  /**
   * Calculate the distance between two vectors
   * @param {Vector|Array<number>} v1 - First vector
   * @param {Vector|Array<number>} v2 - Second vector
   * @param {number} [p=2] - Norm order (1=L1, 2=L2/Euclidean)
   * @returns {number} Distance
   */
  vectorDistance: function (v1, v2, p = 2) {
    const vec1 = v1 instanceof Vector ? v1 : new Vector(v1);
    return vec1.distance(v2, p);
  },

  /**
   * Calculate the angle between two vectors
   * @param {Vector|Array<number>} v1 - First vector
   * @param {Vector|Array<number>} v2 - Second vector
   * @returns {number} Angle in radians
   */
  angleBetweenVectors: function (v1, v2) {
    const vec1 = v1 instanceof Vector ? v1 : new Vector(v1);
    return vec1.angleBetween(v2);
  },

  /**
   * Project one vector onto another
   * @param {Vector|Array<number>} v1 - Vector to project
   * @param {Vector|Array<number>} v2 - Vector to project onto
   * @returns {Vector} Projection vector
   */
  projectVector: function (v1, v2) {
    const vec1 = v1 instanceof Vector ? v1 : new Vector(v1);
    return vec1.projectOnto(v2);
  },

  /**
   * Apply Gram-Schmidt orthogonalization to a set of vectors
   * @param {Array<Vector>|Array<Array<number>>} vectors - Array of vectors
   * @returns {Array<Vector>} Orthogonalized vectors
   */
  gramSchmidt: function (vectors) {
    // Convert to Vector objects if needed
    const vecs = vectors.map((v) => (v instanceof Vector ? v : new Vector(v)));

    const result = [];

    for (let i = 0; i < vecs.length; i++) {
      let v = vecs[i];

      // Orthogonalize against previous vectors
      for (let j = 0; j < result.length; j++) {
        const projection = v.projectOnto(result[j]);
        v = v.subtract(projection);
      }

      // Check if the vector is linearly independent
      const norm = v.norm();
      if (norm > 1e-10) {
        // Normalize and add to result
        result.push(v.scale(1 / norm));
      }
    }

    return result;
  },

  /**
   * Matrix operations
   */
  Matrix: Matrix,

  /**
   * Create a new matrix
   * @param {Array<Array<number>>|number[]|number} values - Matrix values or dimensions
   * @param {number} [rows] - Number of rows (if values is flat array)
   * @param {number} [cols] - Number of columns (if values is flat array)
   * @returns {Matrix} New matrix
   */
  createMatrix: function (values, rows, cols) {
    // Ensure we're using the correct Matrix constructor from linalg
    const { Matrix } = require("./linalg.js");
    return new Matrix(values, rows, cols);
  },

  /**
   * Create a matrix from a 2D array
   * @param {Array<Array<number>>} array - 2D array
   * @returns {Matrix} New matrix
   */
  matrixFromArray: function (array) {
    return Matrix.fromArray(array);
  },

  /**
   * Create a matrix from a flat array
   * @param {Array<number>} array - Flat array
   * @param {number} rows - Number of rows
   * @param {number} cols - Number of columns
   * @returns {Matrix} New matrix
   */
  matrixFromFlatArray: function (array, rows, cols) {
    return Matrix.fromFlatArray(array, rows, cols);
  },

  /**
   * Create a zero matrix
   * @param {number} rows - Number of rows
   * @param {number} cols - Number of columns
   * @returns {Matrix} Zero matrix
   */
  zeroMatrix: function (rows, cols) {
    return Matrix.zeros(rows, cols);
  },

  /**
   * Create a matrix of ones
   * @param {number} rows - Number of rows
   * @param {number} cols - Number of columns
   * @returns {Matrix} Matrix of ones
   */
  onesMatrix: function (rows, cols) {
    return Matrix.ones(rows, cols);
  },

  /**
   * Create an identity matrix
   * @param {number} size - Matrix size
   * @returns {Matrix} Identity matrix
   */
  identityMatrix: function (size) {
    return Matrix.identity(size);
  },

  /**
   * Create a diagonal matrix
   * @param {Array<number>|Vector} diagonal - Diagonal elements
   * @returns {Matrix} Diagonal matrix
   */
  diagonalMatrix: function (diagonal) {
    return Matrix.diagonal(diagonal);
  },

  /**
   * Add two matrices
   * @param {Matrix|Array<Array<number>>} m1 - First matrix
   * @param {Matrix|Array<Array<number>>} m2 - Second matrix
   * @returns {Matrix} Result of addition
   */
  addMatrices: function (m1, m2) {
    const mat1 = m1 instanceof Matrix ? m1 : new Matrix(m1);
    return mat1.add(m2);
  },

  /**
   * Subtract two matrices
   * @param {Matrix|Array<Array<number>>} m1 - First matrix
   * @param {Matrix|Array<Array<number>>} m2 - Second matrix
   * @returns {Matrix} Result of subtraction
   */
  subtractMatrices: function (m1, m2) {
    const mat1 = m1 instanceof Matrix ? m1 : new Matrix(m1);
    return mat1.subtract(m2);
  },

  /**
   * Scale a matrix by a scalar
   * @param {Matrix|Array<Array<number>>} m - Matrix
   * @param {number} scalar - Scalar value
   * @returns {Matrix} Scaled matrix
   */
  scaleMatrix: function (m, scalar) {
    const mat = m instanceof Matrix ? m : new Matrix(m);
    return mat.scale(scalar);
  },

  /**
   * Multiply two matrices or a matrix and a vector
   * @param {Matrix|Array<Array<number>>} m1 - First matrix
   * @param {Matrix|Vector|Array<Array<number>>|Array<number>} m2 - Second matrix or vector
   * @returns {Matrix|Vector} Result of multiplication
   */
  multiplyMatrices: function (m1, m2) {
    const mat1 = m1 instanceof Matrix ? m1 : new Matrix(m1);
    return mat1.multiply(m2);
  },

  /**
   * Calculate the transpose of a matrix
   * @param {Matrix|Array<Array<number>>} m - Matrix
   * @returns {Matrix} Transposed matrix
   */
  transposeMatrix: function (m) {
    const mat = m instanceof Matrix ? m : new Matrix(m);
    return mat.transpose();
  },

  /**
   * Calculate the trace of a matrix
   * @param {Matrix|Array<Array<number>>} m - Matrix
   * @returns {number} Trace
   */
  matrixTrace: function (m) {
    const mat = m instanceof Matrix ? m : new Matrix(m);
    return mat.trace();
  },

  /**
   * Calculate the determinant of a matrix
   * @param {Matrix|Array<Array<number>>} m - Matrix
   * @returns {number} Determinant
   */
  matrixDeterminant: function (m) {
    const mat = m instanceof Matrix ? m : new Matrix(m);
    return mat.determinant();
  },

  /**
   * Perform LU decomposition of a matrix
   * @param {Matrix|Array<Array<number>>} m - Matrix
   * @returns {Object} Object with L, U, P matrices and exchanges count
   */
  luDecomposition: function (m) {
    const mat = m instanceof Matrix ? m : new Matrix(m);
    return mat.luDecomposition();
  },

  /**
   * Calculate the inverse of a matrix
   * @param {Matrix|Array<Array<number>>} m - Matrix
   * @returns {Matrix} Inverse matrix
   */
  inverseMatrix: function (m) {
    const mat = m instanceof Matrix ? m : new Matrix(m);
    return mat.inverse();
  },

  /**
   * Solve a system of linear equations Ax = b
   * @param {Matrix|Array<Array<number>>} A - Coefficient matrix
   * @param {Vector|Array<number>} b - Right-hand side vector
   * @returns {Vector} Solution vector
   */
  solveSystem: function (A, b) {
    const matA = A instanceof Matrix ? A : new Matrix(A);
    return matA.solve(b);
  },

  /**
   * Calculate the eigenvalues and eigenvectors of a matrix
   * @param {Matrix|Array<Array<number>>} m - Matrix
   * @returns {Object} Object with eigenvalues and eigenvectors
   */
  eigendecomposition: function (m) {
    const mat = m instanceof Matrix ? m : new Matrix(m);
    return mat.eigen();
  },

  /**
   * Perform QR decomposition of a matrix
   * @param {Matrix|Array<Array<number>>} m - Matrix
   * @returns {Object} Object with Q and R matrices
   */
  qrDecomposition: function (m) {
    const mat = m instanceof Matrix ? m : new Matrix(m);
    return mat.qrDecomposition();
  },

  /**
   * Calculate the singular value decomposition (SVD) of a matrix
   * @param {Matrix|Array<Array<number>>} m - Matrix
   * @returns {Object} Object with U, S, and V matrices
   */
  svd: function (m) {
    const mat = m instanceof Matrix ? m : new Matrix(m);
    return mat.svd();
  },

  /**
   * Calculate the condition number of a matrix
   * @param {Matrix|Array<Array<number>>} m - Matrix
   * @returns {number} Condition number
   */
  conditionNumber: function (m) {
    const mat = m instanceof Matrix ? m : new Matrix(m);
    return mat.conditionNumber();
  },

  /**
   * Calculate the rank of a matrix
   * @param {Matrix|Array<Array<number>>} m - Matrix
   * @param {number} [tolerance=1e-10] - Tolerance for singular values
   * @returns {number} Rank
   */
  matrixRank: function (m, tolerance = 1e-10) {
    const mat = m instanceof Matrix ? m : new Matrix(m);
    return mat.rank(tolerance);
  },

  /**
   * Calculate the Frobenius norm of a matrix
   * @param {Matrix|Array<Array<number>>} m - Matrix
   * @returns {number} Frobenius norm
   */
  matrixNorm: function (m) {
    const mat = m instanceof Matrix ? m : new Matrix(m);
    return mat.norm();
  },

  /**
   * Enhanced precision scalar functions
   */

  /**
   * Calculate the square root with enhanced precision
   * @param {number} x - Input value
   * @returns {number} Square root
   */
  sqrt: function (x) {
    if (!isNumber(x) || x < 0) {
      throw new Prime.MathematicalError(
        "Square root requires a non-negative number",
      );
    }

    // For values close to zero, use enhanced precision
    if (x < 1e-10) {
      // Use a Taylor series approximation for better precision
      const halfX = x / 2;
      return Math.sqrt(x) * (1 + halfX / 4 - (halfX * halfX) / 8);
    }

    return Math.sqrt(x);
  },

  /**
   * Calculate the power with enhanced precision
   * @param {number} base - Base value
   * @param {number} exponent - Exponent value
   * @returns {number} Result of base raised to exponent
   */
  pow: function (base, exponent) {
    if (!isNumber(base) || !isNumber(exponent)) {
      throw new Prime.ValidationError("Power requires numeric values");
    }

    // Handle special cases for enhanced precision
    if (Math.abs(exponent) < 1e-10) {
      return 1; // Any number to the power of 0 is 1
    }

    if (Math.abs(base - 1) < 1e-10) {
      return 1; // 1 to any power is 1
    }

    if (Math.abs(base) < 1e-10) {
      return exponent > 0 ? 0 : Infinity; // 0^positive = 0, 0^negative = infinity
    }

    // For integer exponents, use a more precise algorithm
    if (Number.isInteger(exponent)) {
      if (exponent >= 0) {
        return this._powInt(base, exponent);
      } else {
        return 1 / this._powInt(base, -exponent);
      }
    }

    return Math.pow(base, exponent);
  },

  /**
   * Helper function for integer powers
   * @private
   * @param {number} base - Base value
   * @param {number} exponent - Integer exponent
   * @returns {number} Result
   */
  _powInt: function (base, exponent) {
    // Use exponentiation by squaring for efficiency
    if (exponent === 0) {
      return 1;
    }

    if (exponent === 1) {
      return base;
    }

    if (exponent % 2 === 0) {
      return this._powInt(base * base, exponent / 2);
    } else {
      return base * this._powInt(base, exponent - 1);
    }
  },

  /**
   * Calculate the exponential function (e^x) with enhanced precision
   * @param {number} x - Exponent
   * @returns {number} e^x
   */
  exp: function (x) {
    if (!isNumber(x)) {
      throw new Prime.ValidationError("Exp requires a numeric value");
    }

    // For values close to zero, use a Taylor series for better precision
    if (Math.abs(x) < 1e-5) {
      // e^x ≈ 1 + x + x^2/2! + x^3/3! + ...
      return 1 + x + (x * x) / 2 + (x * x * x) / 6 + (x * x * x * x) / 24;
    }

    return Math.exp(x);
  },

  /**
   * Calculate the natural logarithm with enhanced precision
   * @param {number} x - Input value
   * @returns {number} Natural logarithm
   */
  log: function (x) {
    if (!isNumber(x) || x <= 0) {
      throw new Prime.MathematicalError("Logarithm requires a positive number");
    }

    // For values close to 1, use a Taylor series for better precision
    if (Math.abs(x - 1) < 1e-5) {
      // ln(1+y) ≈ y - y^2/2 + y^3/3 - ...
      const y = x - 1;
      return y - (y * y) / 2 + (y * y * y) / 3 - (y * y * y * y) / 4;
    }

    return Math.log(x);
  },

  /**
   * Calculate sine with enhanced precision
   * @param {number} x - Angle in radians
   * @returns {number} Sine value
   */
  sin: function (x) {
    if (!isNumber(x)) {
      throw new Prime.ValidationError("Sine requires a numeric value");
    }

    // Normalize angle to [0, 2π)
    const normalized = x % (2 * Math.PI);

    // For values close to 0 or π, use a Taylor series for better precision
    if (Math.abs(normalized) < 1e-5 || Math.abs(normalized - Math.PI) < 1e-5) {
      // sin(x) ≈ x - x^3/3! + x^5/5! - ...
      return Math.sin(normalized);
    }

    return Math.sin(x);
  },

  /**
   * Calculate cosine with enhanced precision
   * @param {number} x - Angle in radians
   * @returns {number} Cosine value
   */
  cos: function (x) {
    if (!isNumber(x)) {
      throw new Prime.ValidationError("Cosine requires a numeric value");
    }

    // Normalize angle to [0, 2π)
    const normalized = x % (2 * Math.PI);

    // For values close to π/2 or 3π/2, use a Taylor series for better precision
    if (
      Math.abs(normalized - Math.PI / 2) < 1e-5 ||
      Math.abs(normalized - (3 * Math.PI) / 2) < 1e-5
    ) {
      // cos(x) ≈ 1 - x^2/2! + x^4/4! - ...
      return Math.cos(normalized);
    }

    return Math.cos(x);
  },

  /**
   * Calculate tangent with enhanced precision
   * @param {number} x - Angle in radians
   * @returns {number} Tangent value
   */
  tan: function (x) {
    if (!isNumber(x)) {
      throw new Prime.ValidationError("Tangent requires a numeric value");
    }

    // Check for values close to singularities (π/2 + nπ)
    const normalized = x % Math.PI;
    if (Math.abs(normalized - Math.PI / 2) < 1e-10) {
      throw new Prime.MathematicalError("Tangent is undefined at π/2 + nπ");
    }

    // For better precision, use the ratio of sine and cosine
    return this.sin(x) / this.cos(x);
  },

  /**
   * Enhanced numerical algorithms
   */

  /**
   * Calculate the numeric derivative of a function at a point
   * @param {Function} f - Function to differentiate
   * @param {number} x - Point at which to calculate derivative
   * @param {number} [h=1e-8] - Step size for finite difference
   * @returns {number} Derivative value
   */
  derivative: function (f, x, h = 1e-8) {
    if (typeof f !== "function") {
      throw new Prime.ValidationError("Derivative requires a function");
    }

    if (!isNumber(x)) {
      throw new Prime.ValidationError("Derivative requires a numeric point");
    }

    // Use central difference for better accuracy
    const fxph = f(x + h);
    const fxmh = f(x - h);

    return (fxph - fxmh) / (2 * h);
  },

  /**
   * Calculate a numerical integral of a function over an interval
   * @param {Function} f - Function to integrate
   * @param {number} a - Lower bound
   * @param {number} b - Upper bound
   * @param {Object} [options={}] - Integration options
   * @returns {number} Definite integral value
   */
  integrate: function (f, a, b, options = {}) {
    if (Prime.ExtremePrecision && Prime.ExtremePrecision.integrate) {
      return Prime.ExtremePrecision.integrate(f, a, b, options);
    }

    // Adaptive Simpson's rule integration
    const tolerance = options.tolerance || 1e-10;
    const maxDepth = options.maxDepth || 20;

    // Simpson's rule for a single interval
    const simpsonRule = (a, b) => {
      const h = (b - a) / 2;
      const c = a + h;
      return (h / 3) * (f(a) + 4 * f(c) + f(b));
    };

    // Recursive adaptive integration
    const adaptiveIntegrate = (a, b, fa, fb, depth) => {
      const h = (b - a) / 2;
      const c = a + h;
      const fc = f(c);

      const whole = simpsonRule(a, b);
      const left = simpsonRule(a, c);
      const right = simpsonRule(c, b);

      const error = Math.abs(left + right - whole);

      if (error < tolerance || depth >= maxDepth) {
        return left + right + error / 15; // Error correction
      }

      return (
        adaptiveIntegrate(a, c, fa, fc, depth + 1) +
        adaptiveIntegrate(c, b, fc, fb, depth + 1)
      );
    };

    const fa = f(a);
    const fb = f(b);
    return adaptiveIntegrate(a, b, fa, fb, 0);
  },

  /**
   * Solve a nonlinear equation f(x) = 0 using Newton's method
   * @param {Function} f - Function
   * @param {Function} df - Derivative of f
   * @param {number} x0 - Initial guess
   * @param {Object} [options={}] - Solution options
   * @returns {number} Root of the equation
   */
  solveNewton: function (f, df, x0, options = {}) {
    if (typeof f !== "function" || typeof df !== "function") {
      throw new Prime.ValidationError(
        "Newton method requires function and derivative",
      );
    }

    if (!isNumber(x0)) {
      throw new Prime.ValidationError("Initial guess must be a number");
    }

    const tolerance = options.tolerance || 1e-10;
    const maxIterations = options.maxIterations || 100;

    let x = x0;

    for (let i = 0; i < maxIterations; i++) {
      const fx = f(x);

      // Check if we've found a root
      if (Math.abs(fx) < tolerance) {
        return x;
      }

      const dfx = df(x);

      // Check for division by zero
      if (Math.abs(dfx) < 1e-14) {
        throw new Prime.MathematicalError(
          "Derivative near zero, Newton method failed",
        );
      }

      // Update estimate
      const newX = x - fx / dfx;

      // Check for convergence
      if (Math.abs(newX - x) < tolerance) {
        return newX;
      }

      x = newX;
    }

    throw new Prime.MathematicalError("Newton method failed to converge");
  },

  /**
   * Solve an optimization problem using gradient descent
   * @param {Function} f - Function to minimize
   * @param {Array<number>|Vector} initialGuess - Initial point
   * @param {Object} [options={}] - Optimization options
   * @returns {Object} Optimization result
   */
  minimizeGradient: function (f, initialGuess, options = {}) {
    if (Prime.ExtremePrecision && Prime.ExtremePrecision.gradientDescent) {
      return Prime.ExtremePrecision.gradientDescent(
        f,
        initialGuess instanceof Vector ? initialGuess.values : initialGuess,
        options,
      );
    }

    // Basic gradient descent implementation
    const tolerance = options.tolerance || 1e-8;
    const maxIterations = options.maxIterations || 1000;
    const learningRate = options.learningRate || 0.01;

    const x =
      initialGuess instanceof Vector
        ? initialGuess.values.slice()
        : initialGuess.slice();

    const n = x.length;
    let iter = 0;
    let fx = f(x);

    // Helper for numerical gradient calculation
    const computeGradient = (point) => {
      const h = 1e-8;
      const grad = new Array(n);

      for (let i = 0; i < n; i++) {
        const x1 = point.slice();
        const x2 = point.slice();
        x1[i] += h;
        x2[i] -= h;

        grad[i] = (f(x1) - f(x2)) / (2 * h);
      }

      return grad;
    };

    // Optimization loop
    while (iter < maxIterations) {
      // Compute gradient
      const gradient = computeGradient(x);

      // Check convergence
      let gradNorm = 0;
      for (let i = 0; i < n; i++) {
        gradNorm += gradient[i] * gradient[i];
      }
      gradNorm = Math.sqrt(gradNorm);

      if (gradNorm < tolerance) {
        break;
      }

      // Update parameters
      for (let i = 0; i < n; i++) {
        x[i] -= learningRate * gradient[i];
      }

      // Evaluate new function value
      const newFx = f(x);

      // Line search (optional)
      if (newFx > fx) {
        // If function value increased, reduce step size
        for (let i = 0; i < n; i++) {
          x[i] += learningRate * gradient[i]; // Undo step
        }

        // Try with smaller step size
        for (let i = 0; i < n; i++) {
          x[i] -= 0.1 * learningRate * gradient[i];
        }
      }

      fx = f(x);
      iter++;
    }

    return {
      params: x,
      cost: fx,
      iterations: iter,
      converged: iter < maxIterations,
    };
  },

  /**
   * Interpolate between values
   * @param {number} a - First value
   * @param {number} b - Second value
   * @param {number} t - Interpolation parameter (0-1)
   * @returns {number} Interpolated value
   */
  lerp: function (a, b, t) {
    if (!isNumber(a) || !isNumber(b) || !isNumber(t)) {
      throw new Prime.ValidationError("Lerp requires numeric values");
    }

    // Clamp t to [0, 1]
    const tClamped = Math.max(0, Math.min(1, t));

    // Use a more precise interpolation formula
    return a * (1 - tClamped) + b * tClamped;
  },

  /**
   * Clamp a value between a minimum and maximum
   * @param {number} value - Value to clamp
   * @param {number} min - Minimum value
   * @param {number} max - Maximum value
   * @returns {number} Clamped value
   */
  clamp: function (value, min, max) {
    if (!isNumber(value) || !isNumber(min) || !isNumber(max)) {
      throw new Prime.ValidationError("Clamp requires numeric values");
    }

    return Math.max(min, Math.min(max, value));
  },

  /**
   * Utility functions
   */

  /**
   * Check if two numbers are approximately equal
   * @param {number} a - First number
   * @param {number} b - Second number
   * @param {number} [epsilon=Number.EPSILON] - Tolerance
   * @returns {boolean} True if numbers are approximately equal
   */
  approxEqual: function (a, b, epsilon = Number.EPSILON) {
    if (!isNumber(a) || !isNumber(b)) {
      throw new Prime.ValidationError(
        "Approximate equality requires numeric values",
      );
    }

    // Special cases
    if (a === b) return true;
    if (isNaN(a) && isNaN(b)) return true;

    // Absolute and relative error check
    const diff = Math.abs(a - b);
    const absA = Math.abs(a);
    const absB = Math.abs(b);

    // When both values are very small
    if (absA < 1e-10 && absB < 1e-10) {
      return diff < epsilon;
    }

    // When values are larger, use relative error
    return diff <= epsilon * Math.max(absA, absB);
  },

  /**
   * Check if a value is a power of 2
   * @param {number} n - Value to check
   * @returns {boolean} True if value is a power of 2
   */
  isPowerOfTwo: function (n) {
    if (!Number.isInteger(n) || n <= 0) {
      return false;
    }

    return (n & (n - 1)) === 0;
  },

  /**
   * Generate a random number within a range
   * @param {number} min - Minimum value
   * @param {number} max - Maximum value
   * @returns {number} Random number
   */
  random: function (min = 0, max = 1) {
    if (!isNumber(min) || !isNumber(max)) {
      throw new Prime.ValidationError("Random range requires numeric values");
    }

    return min + Math.random() * (max - min);
  },

  /**
   * Generate a normally distributed random number
   * @param {number} [mean=0] - Mean of the distribution
   * @param {number} [stdDev=1] - Standard deviation
   * @returns {number} Random number
   */
  randomNormal: function (mean = 0, stdDev = 1) {
    if (!isNumber(mean) || !isNumber(stdDev)) {
      throw new Prime.ValidationError(
        "Normal distribution requires numeric parameters",
      );
    }

    // Box-Muller transform
    const u1 = Math.random();
    const u2 = Math.random();

    const z0 = Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math.PI * u2);

    return mean + z0 * stdDev;
  },

  /**
   * Convert between degrees and radians
   * @param {number} degrees - Angle in degrees
   * @returns {number} Angle in radians
   */
  toRadians: function (degrees) {
    if (!isNumber(degrees)) {
      throw new Prime.ValidationError("Degrees must be a number");
    }

    return (degrees * Math.PI) / 180;
  },

  /**
   * Convert between radians and degrees
   * @param {number} radians - Angle in radians
   * @returns {number} Angle in degrees
   */
  toDegrees: function (radians) {
    if (!isNumber(radians)) {
      throw new Prime.ValidationError("Radians must be a number");
    }

    return (radians * 180) / Math.PI;
  },
};

module.exports = PrimeMath;
