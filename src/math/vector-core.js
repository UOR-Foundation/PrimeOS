/**
 * PrimeOS JavaScript Library - Math
 * Vector Core Operations
 * Core vector operations with memory optimization and performance enhancements
 */

// Import the Prime object
const Prime = require('../core');

/**
 * Core vector operations with optimized implementations
 */
const VectorCore = {
  /**
   * Create a new vector with specified dimensions
   * @param {number} dimensions - Number of dimensions
   * @param {number} [initialValue=0] - Initial value for all elements
   * @param {Object} [options={}] - Additional options
   * @param {boolean} [options.useTypedArray=false] - Use TypedArray for memory efficiency
   * @param {string} [options.arrayType='float64'] - Type of TypedArray ('float64', 'float32', etc.)
   * @returns {Array|TypedArray} - New vector with specified dimensions
   */
  create: function (dimensions, initialValue = 0, options = {}) {
    if (
      !Prime.Utils.isNumber(dimensions) ||
      dimensions <= 0 ||
      !Number.isInteger(dimensions)
    ) {
      throw new Prime.ValidationError('Dimensions must be a positive integer');
    }

    // Use TypedArray if specified in options
    if (options.useTypedArray) {
      let typedArray;

      switch (options.arrayType) {
        case 'float32':
          typedArray = new Float32Array(dimensions);
          break;
        case 'int32':
          typedArray = new Int32Array(dimensions);
          break;
        case 'int16':
          typedArray = new Int16Array(dimensions);
          break;
        case 'uint8':
          typedArray = new Uint8Array(dimensions);
          break;
        case 'float64':
        default:
          typedArray = new Float64Array(dimensions);
      }

      if (initialValue !== 0) {
        typedArray.fill(initialValue);
      }

      return typedArray;
    }

    // Otherwise use standard JavaScript array
    return new Array(dimensions).fill(initialValue);
  },

  /**
   * Add two vectors element-wise
   * @param {Array|TypedArray} a - First vector
   * @param {Array|TypedArray} b - Second vector
   * @param {Array|TypedArray} [result] - Optional result vector (for in-place operations)
   * @returns {Array|TypedArray} - Result of addition
   */
  add: function (a, b, result) {
    if (!this.isVector(a) || !this.isVector(b)) {
      throw new Prime.ValidationError('Vectors must be arrays or TypedArrays');
    }

    if (a.length !== b.length) {
      throw new Prime.ValidationError('Vectors must have the same dimensions');
    }

    // If result vector is provided, use it for in-place operation
    if (result && this.isVector(result) && result.length === a.length) {
      for (let i = 0; i < a.length; i++) {
        result[i] = a[i] + b[i];
      }
      return result;
    }

    // Otherwise, create a new result vector
    // Use TypedArray if inputs are TypedArrays
    if (ArrayBuffer.isView(a)) {
      const resultVector = new a.constructor(a.length);
      for (let i = 0; i < a.length; i++) {
        resultVector[i] = a[i] + b[i];
      }
      return resultVector;
    }

    // Regular array implementation
    return a.map((val, i) => val + b[i]);
  },

  /**
   * Subtract vector b from vector a element-wise
   * @param {Array|TypedArray} a - First vector
   * @param {Array|TypedArray} b - Second vector
   * @param {Array|TypedArray} [result] - Optional result vector (for in-place operations)
   * @returns {Array|TypedArray} - Result of subtraction
   */
  subtract: function (a, b, result) {
    if (!this.isVector(a) || !this.isVector(b)) {
      throw new Prime.ValidationError('Vectors must be arrays or TypedArrays');
    }

    if (a.length !== b.length) {
      throw new Prime.ValidationError('Vectors must have the same dimensions');
    }

    // If result vector is provided, use it for in-place operation
    if (result && this.isVector(result) && result.length === a.length) {
      for (let i = 0; i < a.length; i++) {
        result[i] = a[i] - b[i];
      }
      return result;
    }

    // Otherwise, create a new result vector
    // Use TypedArray if inputs are TypedArrays
    if (ArrayBuffer.isView(a)) {
      const resultVector = new a.constructor(a.length);
      for (let i = 0; i < a.length; i++) {
        resultVector[i] = a[i] - b[i];
      }
      return resultVector;
    }

    // Regular array implementation
    return a.map((val, i) => val - b[i]);
  },

  /**
   * Calculate the dot product of two vectors with enhanced numerical stability
   * @param {Array|TypedArray} a - First vector
   * @param {Array|TypedArray} b - Second vector
   * @returns {number} - Dot product
   */
  dot: function (a, b) {
    if (!this.isVector(a) || !this.isVector(b)) {
      throw new Prime.ValidationError('Vectors must be arrays or TypedArrays');
    }

    if (a.length !== b.length) {
      throw new Prime.ValidationError('Vectors must have the same dimensions');
    }

    // Use Kahan summation for numerical stability
    let sum = 0;
    let compensation = 0;

    for (let i = 0; i < a.length; i++) {
      // Compute the product
      const product = a[i] * b[i];

      // Kahan summation step
      const y = product - compensation;
      const t = sum + y;
      compensation = t - sum - y;
      sum = t;
    }

    return sum;
  },

  /**
   * Scale a vector by a scalar
   * @param {Array|TypedArray} vector - Vector to scale
   * @param {number} scalar - Scaling factor
   * @param {Array|TypedArray} [result] - Optional result vector (for in-place operations)
   * @returns {Array|TypedArray} - Scaled vector
   */
  scale: function (vector, scalar, result) {
    if (!this.isVector(vector)) {
      throw new Prime.ValidationError('Vector must be an array or TypedArray');
    }

    if (!Prime.Utils.isNumber(scalar)) {
      throw new Prime.ValidationError('Scalar must be a number');
    }

    // If result vector is provided, use it for in-place operation
    if (result && this.isVector(result) && result.length === vector.length) {
      for (let i = 0; i < vector.length; i++) {
        result[i] = vector[i] * scalar;
      }
      return result;
    }

    // Otherwise, create a new result vector
    // Use TypedArray if input is TypedArray
    if (ArrayBuffer.isView(vector)) {
      const resultVector = new vector.constructor(vector.length);
      for (let i = 0; i < vector.length; i++) {
        resultVector[i] = vector[i] * scalar;
      }
      return resultVector;
    }

    // Regular array implementation
    return vector.map((val) => val * scalar);
  },

  /**
   * Calculate the magnitude (Euclidean norm) of a vector with enhanced numerical stability
   * @param {Array|TypedArray} vector - Input vector
   * @returns {number} - Vector magnitude
   */
  magnitude: function (vector) {
    if (!this.isVector(vector)) {
      throw new Prime.ValidationError('Vector must be an array or TypedArray');
    }

    // Use Kahan summation for numerical stability
    let sum = 0;
    let compensation = 0;

    for (let i = 0; i < vector.length; i++) {
      const squared = vector[i] * vector[i];

      // Kahan summation step
      const y = squared - compensation;
      const t = sum + y;
      compensation = t - sum - y;
      sum = t;
    }

    // Prevent negative square roots due to floating point errors
    return Math.sqrt(Math.max(0, sum));
  },

  /**
   * Calculate the squared magnitude of a vector (avoiding square root operation)
   * @param {Array|TypedArray} vector - Input vector
   * @returns {number} - Squared magnitude
   */
  magnitudeSquared: function (vector) {
    if (!this.isVector(vector)) {
      throw new Prime.ValidationError('Vector must be an array or TypedArray');
    }

    // Use Kahan summation for numerical stability
    let sum = 0;
    let compensation = 0;

    for (let i = 0; i < vector.length; i++) {
      const squared = vector[i] * vector[i];

      // Kahan summation step
      const y = squared - compensation;
      const t = sum + y;
      compensation = t - sum - y;
      sum = t;
    }

    return sum;
  },

  /**
   * Normalize a vector to unit length
   * @param {Array|TypedArray} vector - Vector to normalize
   * @param {Array|TypedArray} [result] - Optional result vector (for in-place operations)
   * @param {Object} [options={}] - Additional options
   * @param {number} [options.epsilon=1e-10] - Tolerance for zero vectors
   * @returns {Array|TypedArray} - Normalized vector
   */
  normalize: function (vector, result, options = {}) {
    if (!this.isVector(vector)) {
      throw new Prime.ValidationError('Vector must be an array or TypedArray');
    }

    const epsilon = options.epsilon || 1e-10;
    const mag = this.magnitude(vector);

    if (mag < epsilon) {
      throw new Prime.MathematicalError('Cannot normalize a zero vector');
    }

    // If result vector is provided, use it for in-place operation
    if (result && this.isVector(result) && result.length === vector.length) {
      for (let i = 0; i < vector.length; i++) {
        result[i] = vector[i] / mag;
      }
      return result;
    }

    // Otherwise, create a new result vector
    // Use TypedArray if input is TypedArray
    if (ArrayBuffer.isView(vector)) {
      const resultVector = new vector.constructor(vector.length);
      for (let i = 0; i < vector.length; i++) {
        resultVector[i] = vector[i] / mag;
      }
      return resultVector;
    }

    // Regular array implementation
    return vector.map((val) => val / mag);
  },

  /**
   * Calculate the distance between two vectors
   * @param {Array|TypedArray} a - First vector
   * @param {Array|TypedArray} b - Second vector
   * @returns {number} - Distance between vectors
   */
  distance: function (a, b) {
    if (!this.isVector(a) || !this.isVector(b)) {
      throw new Prime.ValidationError('Vectors must be arrays or TypedArrays');
    }

    if (a.length !== b.length) {
      throw new Prime.ValidationError('Vectors must have the same dimensions');
    }

    // Use Kahan summation for numerical stability
    let sum = 0;
    let compensation = 0;

    for (let i = 0; i < a.length; i++) {
      const diff = a[i] - b[i];
      const squared = diff * diff;

      // Kahan summation step
      const y = squared - compensation;
      const t = sum + y;
      compensation = t - sum - y;
      sum = t;
    }

    // Prevent negative square roots due to floating point errors
    return Math.sqrt(Math.max(0, sum));
  },

  /**
   * Fill a vector with a specific value
   * @param {Array|TypedArray} vector - Vector to fill
   * @param {number} value - Value to fill the vector with
   * @returns {Array|TypedArray} - Filled vector (modified in-place)
   */
  fill: function (vector, value) {
    if (!this.isVector(vector)) {
      throw new Prime.ValidationError('Vector must be an array or TypedArray');
    }

    if (!Prime.Utils.isNumber(value)) {
      throw new Prime.ValidationError('Fill value must be a number');
    }

    // Use built-in fill method
    vector.fill(value);
    return vector;
  },

  /**
   * Check if input is a valid vector (Array or TypedArray)
   * @param {*} v - Value to check
   * @returns {boolean} - True if v is a valid vector
   */
  isVector: function (v) {
    return Array.isArray(v) || ArrayBuffer.isView(v);
  },

  /**
   * Copy values from source vector to destination vector
   * @param {Array|TypedArray} source - Source vector
   * @param {Array|TypedArray} destination - Destination vector
   * @returns {Array|TypedArray} - Destination vector (modified in-place)
   */
  copy: function (source, destination) {
    if (!this.isVector(source) || !this.isVector(destination)) {
      throw new Prime.ValidationError('Vectors must be arrays or TypedArrays');
    }

    if (destination.length < source.length) {
      throw new Prime.ValidationError('Destination vector is too small');
    }

    for (let i = 0; i < source.length; i++) {
      destination[i] = source[i];
    }

    return destination;
  },

  /**
   * Create a copy of a vector
   * @param {Array|TypedArray} vector - Vector to copy
   * @returns {Array|TypedArray} - New copy of the vector
   */
  clone: function (vector) {
    if (!this.isVector(vector)) {
      throw new Prime.ValidationError('Vector must be an array or TypedArray');
    }

    // For TypedArrays
    if (ArrayBuffer.isView(vector)) {
      return new vector.constructor(vector);
    }

    // For regular arrays
    return [...vector];
  },

  /**
   * Calculate element-wise product of two vectors
   * @param {Array|TypedArray} a - First vector
   * @param {Array|TypedArray} b - Second vector
   * @param {Array|TypedArray} [result] - Optional result vector (for in-place operations)
   * @returns {Array|TypedArray} - Element-wise product
   */
  elementWiseProduct: function (a, b, result) {
    if (!this.isVector(a) || !this.isVector(b)) {
      throw new Prime.ValidationError('Vectors must be arrays or TypedArrays');
    }

    if (a.length !== b.length) {
      throw new Prime.ValidationError('Vectors must have the same dimensions');
    }

    // If result vector is provided, use it for in-place operation
    if (result && this.isVector(result) && result.length === a.length) {
      for (let i = 0; i < a.length; i++) {
        result[i] = a[i] * b[i];
      }
      return result;
    }

    // Otherwise, create a new result vector
    // Use TypedArray if inputs are TypedArrays
    if (ArrayBuffer.isView(a)) {
      const resultVector = new a.constructor(a.length);
      for (let i = 0; i < a.length; i++) {
        resultVector[i] = a[i] * b[i];
      }
      return resultVector;
    }

    // Regular array implementation
    return a.map((val, i) => val * b[i]);
  },
};

// Add vector-core to the Prime.Math namespace
Prime.Math = Prime.Math || {};
Prime.Math.VectorCore = VectorCore;

// Export the enhanced Prime object
module.exports = Prime;
