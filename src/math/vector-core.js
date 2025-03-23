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
   * @param {Object} [options={}] - Additional options
   * @param {string} [options.summationMethod='kahan'] - Summation method ('kahan', 'pairwise', 'adaptive')
   * @param {boolean} [options.useScaling=true] - Whether to use scaling for extreme values
   * @returns {number} - Dot product
   */
  dot: function (a, b, options = {}) {
    if (!this.isVector(a) || !this.isVector(b)) {
      throw new Prime.ValidationError('Vectors must be arrays or TypedArrays');
    }

    if (a.length !== b.length) {
      throw new Prime.ValidationError('Vectors must have the same dimensions');
    }

    const summationMethod = options.summationMethod || 'adaptive';
    const useScaling = options.useScaling !== false;

    // Select the most appropriate summation method based on input
    if (summationMethod === 'adaptive') {
      // For short vectors, Kahan is efficient
      if (a.length < 100) {
        return this._dotKahan(a, b, useScaling);
      }
      // For alternating signs, use specialized method
      if (this._hasAlternatingSigns(a) || this._hasAlternatingSigns(b)) {
        return this._dotAlternating(a, b, useScaling);
      }
      // For long vectors, pairwise may be better
      return this._dotPairwise(a, b, useScaling);
    } else if (summationMethod === 'pairwise') {
      return this._dotPairwise(a, b, useScaling);
    } else {
      // Default to Kahan summation
      return this._dotKahan(a, b, useScaling);
    }
  },

  /**
   * Internal method to check if a vector has alternating signs
   * @private
   * @param {Array|TypedArray} v - Vector to check
   * @returns {boolean} - True if vector has alternating signs
   */
  _hasAlternatingSigns: function (v) {
    let signChanges = 0;
    let prevSign = 0;
    
    for (let i = 0; i < v.length; i++) {
      if (v[i] === 0) continue;
      
      const sign = Math.sign(v[i]);
      if (prevSign !== 0 && sign !== prevSign) {
        signChanges++;
      }
      prevSign = sign;
      
      // If we have multiple sign changes, it might be alternating
      if (signChanges >= 2) {
        return true;
      }
    }
    
    return false;
  },

  /**
   * Calculate dot product using Kahan summation (numerically stable)
   * @private
   * @param {Array|TypedArray} a - First vector
   * @param {Array|TypedArray} b - Second vector
   * @param {boolean} useScaling - Whether to use scaling for extreme values
   * @returns {number} - Dot product
   */
  _dotKahan: function (a, b, useScaling) {
    let sum = 0;
    let compensation = 0;
    
    // Handle extreme values with scaling
    if (useScaling) {
      // Find max absolute values for scaling
      let maxA = 0;
      let maxB = 0;
      
      for (let i = 0; i < a.length; i++) {
        maxA = Math.max(maxA, Math.abs(a[i]));
        maxB = Math.max(maxB, Math.abs(b[i]));
      }
      
      // Avoid division by zero
      const scaleA = maxA === 0 ? 1 : maxA;
      const scaleB = maxB === 0 ? 1 : maxB;
      
      // Extreme value scaling
      if (maxA > 1e100 || maxB > 1e100 || maxA < 1e-100 || maxB < 1e-100) {
        // Compute dot product with scaling
        for (let i = 0; i < a.length; i++) {
          const scaledA = a[i] / scaleA;
          const scaledB = b[i] / scaleB;
          const product = scaledA * scaledB;
          
          // Kahan summation step
          const y = product - compensation;
          const t = sum + y;
          compensation = t - sum - y;
          sum = t;
        }
        
        // Scale back the result
        return sum * scaleA * scaleB;
      }
    }
    
    // Standard Kahan summation for normal values
    for (let i = 0; i < a.length; i++) {
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
   * Calculate dot product using pairwise summation (good for long vectors)
   * @private
   * @param {Array|TypedArray} a - First vector
   * @param {Array|TypedArray} b - Second vector
   * @param {boolean} useScaling - Whether to use scaling for extreme values
   * @returns {number} - Dot product
   */
  _dotPairwise: function (a, b, useScaling) {
    // Precompute all products
    const products = new Array(a.length);
    
    // Handle extreme values with scaling
    if (useScaling) {
      // Find max absolute values for scaling
      let maxA = 0;
      let maxB = 0;
      
      for (let i = 0; i < a.length; i++) {
        maxA = Math.max(maxA, Math.abs(a[i]));
        maxB = Math.max(maxB, Math.abs(b[i]));
      }
      
      // Avoid division by zero
      const scaleA = maxA === 0 ? 1 : maxA;
      const scaleB = maxB === 0 ? 1 : maxB;
      
      // Extreme value scaling
      if (maxA > 1e100 || maxB > 1e100 || maxA < 1e-100 || maxB < 1e-100) {
        // Compute products with scaling
        for (let i = 0; i < a.length; i++) {
          const scaledA = a[i] / scaleA;
          const scaledB = b[i] / scaleB;
          products[i] = scaledA * scaledB;
        }
        
        // Use pairwise summation
        const result = this._pairwiseSum(products);
        
        // Scale back the result
        return result * scaleA * scaleB;
      }
    }
    
    // Compute products without scaling
    for (let i = 0; i < a.length; i++) {
      products[i] = a[i] * b[i];
    }
    
    // Use pairwise summation
    return this._pairwiseSum(products);
  },

  /**
   * Calculate dot product optimized for vectors with alternating signs
   * @private
   * @param {Array|TypedArray} a - First vector
   * @param {Array|TypedArray} b - Second vector
   * @param {boolean} useScaling - Whether to use scaling for extreme values
   * @returns {number} - Dot product
   */
  _dotAlternating: function (a, b, useScaling) {
    // For alternating signs, first compute positive and negative sums separately
    let posSum = 0;
    let negSum = 0;
    let posCompensation = 0;
    let negCompensation = 0;
    
    // Handle extreme values with scaling
    if (useScaling) {
      // Find max absolute values for scaling
      let maxA = 0;
      let maxB = 0;
      
      for (let i = 0; i < a.length; i++) {
        maxA = Math.max(maxA, Math.abs(a[i]));
        maxB = Math.max(maxB, Math.abs(b[i]));
      }
      
      // Avoid division by zero
      const scaleA = maxA === 0 ? 1 : maxA;
      const scaleB = maxB === 0 ? 1 : maxB;
      
      // Extreme value scaling
      if (maxA > 1e100 || maxB > 1e100 || maxA < 1e-100 || maxB < 1e-100) {
        // Separate positive and negative contributions
        for (let i = 0; i < a.length; i++) {
          const scaledA = a[i] / scaleA;
          const scaledB = b[i] / scaleB;
          const product = scaledA * scaledB;
          
          if (product >= 0) {
            // Kahan summation for positive terms
            const y = product - posCompensation;
            const t = posSum + y;
            posCompensation = t - posSum - y;
            posSum = t;
          } else {
            // Kahan summation for negative terms
            const y = product - negCompensation;
            const t = negSum + y;
            negCompensation = t - negSum - y;
            negSum = t;
          }
        }
        
        // Add positive and negative sums and scale back
        return (posSum + negSum) * scaleA * scaleB;
      }
    }
    
    // Standard approach for normal values - separate positive and negative
    for (let i = 0; i < a.length; i++) {
      const product = a[i] * b[i];
      
      if (product >= 0) {
        // Kahan summation for positive terms
        const y = product - posCompensation;
        const t = posSum + y;
        posCompensation = t - posSum - y;
        posSum = t;
      } else {
        // Kahan summation for negative terms
        const y = product - negCompensation;
        const t = negSum + y;
        negCompensation = t - negSum - y;
        negSum = t;
      }
    }
    
    // Add positive and negative sums
    return posSum + negSum;
  },

  /**
   * Perform pairwise summation for better numerical stability
   * @private
   * @param {Array|TypedArray} arr - Array of values to sum
   * @returns {number} - Sum of values
   */
  _pairwiseSum: function (arr) {
    const n = arr.length;
    
    if (n === 0) return 0;
    if (n === 1) return arr[0];
    if (n === 2) return arr[0] + arr[1];
    
    // Recursively sum pairs
    const mid = Math.floor(n / 2);
    const left = arr.slice(0, mid);
    const right = arr.slice(mid);
    
    return this._pairwiseSum(left) + this._pairwiseSum(right);
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
   * @param {Object} [options={}] - Additional options
   * @param {string} [options.method='adaptive'] - Method to use ('kahan', 'pairwise', 'adaptive', 'scaling')
   * @param {boolean} [options.useScaling=true] - Whether to use scaling to prevent overflow/underflow
   * @returns {number} - Vector magnitude
   */
  magnitude: function (vector, options = {}) {
    if (!this.isVector(vector)) {
      throw new Prime.ValidationError('Vector must be an array or TypedArray');
    }

    const method = options.method || 'adaptive';
    const useScaling = options.useScaling !== false;

    // Select the most appropriate method based on input
    if (method === 'adaptive') {
      // For short vectors, Kahan is efficient
      if (vector.length < 100) {
        return this._magnitudeKahan(vector, useScaling);
      }
      // For longer vectors, pairwise may be better
      return this._magnitudePairwise(vector, useScaling);
    } else if (method === 'pairwise') {
      return this._magnitudePairwise(vector, useScaling);
    } else if (method === 'scaling') {
      return this._magnitudeScaling(vector);
    } else {
      // Default to Kahan summation
      return this._magnitudeKahan(vector, useScaling);
    }
  },

  /**
   * Calculate magnitude using Kahan summation (numerically stable)
   * @private
   * @param {Array|TypedArray} vector - Input vector
   * @param {boolean} useScaling - Whether to use scaling for extreme values
   * @returns {number} - Vector magnitude
   */
  _magnitudeKahan: function (vector, useScaling) {
    let sum = 0;
    let compensation = 0;
    
    // Handle extreme values with scaling
    if (useScaling) {
      // Find max absolute value for scaling
      let maxVal = 0;
      
      for (let i = 0; i < vector.length; i++) {
        maxVal = Math.max(maxVal, Math.abs(vector[i]));
      }
      
      // Avoid division by zero
      const scale = maxVal === 0 ? 1 : maxVal;
      
      // Extreme value scaling
      if (maxVal > 1e100 || maxVal < 1e-100) {
        // Compute sum of squares with scaling
        for (let i = 0; i < vector.length; i++) {
          const scaled = vector[i] / scale;
          const squared = scaled * scaled;
          
          // Kahan summation step
          const y = squared - compensation;
          const t = sum + y;
          compensation = t - sum - y;
          sum = t;
        }
        
        // Scale back the result
        return Math.sqrt(Math.max(0, sum)) * scale;
      }
    }
    
    // Standard Kahan summation for normal values
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
   * Calculate magnitude using pairwise summation (good for long vectors)
   * @private
   * @param {Array|TypedArray} vector - Input vector
   * @param {boolean} useScaling - Whether to use scaling for extreme values
   * @returns {number} - Vector magnitude
   */
  _magnitudePairwise: function (vector, useScaling) {
    // Precompute all squared values
    const squares = new Array(vector.length);
    
    // Handle extreme values with scaling
    if (useScaling) {
      // Find max absolute value for scaling
      let maxVal = 0;
      
      for (let i = 0; i < vector.length; i++) {
        maxVal = Math.max(maxVal, Math.abs(vector[i]));
      }
      
      // Avoid division by zero
      const scale = maxVal === 0 ? 1 : maxVal;
      
      // Extreme value scaling
      if (maxVal > 1e100 || maxVal < 1e-100) {
        // Compute squares with scaling
        for (let i = 0; i < vector.length; i++) {
          const scaled = vector[i] / scale;
          squares[i] = scaled * scaled;
        }
        
        // Use pairwise summation
        const sum = this._pairwiseSum(squares);
        
        // Scale back the result
        return Math.sqrt(Math.max(0, sum)) * scale;
      }
    }
    
    // Compute squares without scaling
    for (let i = 0; i < vector.length; i++) {
      squares[i] = vector[i] * vector[i];
    }
    
    // Use pairwise summation
    const sum = this._pairwiseSum(squares);
    
    // Prevent negative square roots due to floating point errors
    return Math.sqrt(Math.max(0, sum));
  },

  /**
   * Calculate magnitude using two-pass scaling method (most stable for extreme values)
   * @private
   * @param {Array|TypedArray} vector - Input vector
   * @returns {number} - Vector magnitude
   */
  _magnitudeScaling: function (vector) {
    // Find the maximum absolute value
    let maxVal = 0;
    
    for (let i = 0; i < vector.length; i++) {
      maxVal = Math.max(maxVal, Math.abs(vector[i]));
    }
    
    // Special case for zero vector
    if (maxVal === 0) {
      return 0;
    }
    
    // Compute scaled sum of squares
    let sum = 0;
    let compensation = 0;
    
    for (let i = 0; i < vector.length; i++) {
      const scaled = vector[i] / maxVal;
      const squared = scaled * scaled;
      
      // Kahan summation step
      const y = squared - compensation;
      const t = sum + y;
      compensation = t - sum - y;
      sum = t;
    }
    
    // Scale back the result
    return Math.sqrt(Math.max(0, sum)) * maxVal;
  },

  /**
   * Calculate the squared magnitude of a vector (avoiding square root operation)
   * @param {Array|TypedArray} vector - Input vector
   * @param {Object} [options={}] - Additional options
   * @param {string} [options.method='adaptive'] - Method to use ('kahan', 'pairwise', 'adaptive', 'scaling')
   * @param {boolean} [options.useScaling=true] - Whether to use scaling to prevent overflow/underflow
   * @returns {number} - Squared magnitude
   */
  magnitudeSquared: function (vector, options = {}) {
    if (!this.isVector(vector)) {
      throw new Prime.ValidationError('Vector must be an array or TypedArray');
    }

    const method = options.method || 'adaptive';
    const useScaling = options.useScaling !== false;

    // Select the most appropriate method based on input
    if (method === 'adaptive') {
      // For short vectors, Kahan is efficient
      if (vector.length < 100) {
        return this._magnitudeSquaredKahan(vector, useScaling);
      }
      // For longer vectors, pairwise may be better
      return this._magnitudeSquaredPairwise(vector, useScaling);
    } else if (method === 'pairwise') {
      return this._magnitudeSquaredPairwise(vector, useScaling);
    } else if (method === 'scaling') {
      return this._magnitudeSquaredScaling(vector);
    } else {
      // Default to Kahan summation
      return this._magnitudeSquaredKahan(vector, useScaling);
    }
  },

  /**
   * Calculate squared magnitude using Kahan summation (numerically stable)
   * @private
   * @param {Array|TypedArray} vector - Input vector
   * @param {boolean} useScaling - Whether to use scaling for extreme values
   * @returns {number} - Squared magnitude
   */
  _magnitudeSquaredKahan: function (vector, useScaling) {
    let sum = 0;
    let compensation = 0;
    
    // Handle extreme values with scaling
    if (useScaling) {
      // Find max absolute value for scaling
      let maxVal = 0;
      
      for (let i = 0; i < vector.length; i++) {
        maxVal = Math.max(maxVal, Math.abs(vector[i]));
      }
      
      // Avoid division by zero
      const scale = maxVal === 0 ? 1 : maxVal;
      
      // Extreme value scaling
      if (maxVal > 1e100 || maxVal < 1e-100) {
        // Compute sum of squares with scaling
        for (let i = 0; i < vector.length; i++) {
          const scaled = vector[i] / scale;
          const squared = scaled * scaled;
          
          // Kahan summation step
          const y = squared - compensation;
          const t = sum + y;
          compensation = t - sum - y;
          sum = t;
        }
        
        // Scale back the result
        return sum * scale * scale;
      }
    }
    
    // Standard Kahan summation for normal values
    for (let i = 0; i < vector.length; i++) {
      const squared = vector[i] * vector[i];
      
      // Kahan summation step
      const y = squared - compensation;
      const t = sum + y;
      compensation = t - sum - y;
      sum = t;
    }
    
    // Return sum of squares
    return sum;
  },

  /**
   * Calculate squared magnitude using pairwise summation (good for long vectors)
   * @private
   * @param {Array|TypedArray} vector - Input vector
   * @param {boolean} useScaling - Whether to use scaling for extreme values
   * @returns {number} - Squared magnitude
   */
  _magnitudeSquaredPairwise: function (vector, useScaling) {
    // Precompute all squared values
    const squares = new Array(vector.length);
    
    // Handle extreme values with scaling
    if (useScaling) {
      // Find max absolute value for scaling
      let maxVal = 0;
      
      for (let i = 0; i < vector.length; i++) {
        maxVal = Math.max(maxVal, Math.abs(vector[i]));
      }
      
      // Avoid division by zero
      const scale = maxVal === 0 ? 1 : maxVal;
      
      // Extreme value scaling
      if (maxVal > 1e100 || maxVal < 1e-100) {
        // Compute squares with scaling
        for (let i = 0; i < vector.length; i++) {
          const scaled = vector[i] / scale;
          squares[i] = scaled * scaled;
        }
        
        // Use pairwise summation
        const sum = this._pairwiseSum(squares);
        
        // Scale back the result
        return sum * scale * scale;
      }
    }
    
    // Compute squares without scaling
    for (let i = 0; i < vector.length; i++) {
      squares[i] = vector[i] * vector[i];
    }
    
    // Use pairwise summation
    return this._pairwiseSum(squares);
  },

  /**
   * Calculate squared magnitude using two-pass scaling method (most stable for extreme values)
   * @private
   * @param {Array|TypedArray} vector - Input vector
   * @returns {number} - Squared magnitude
   */
  _magnitudeSquaredScaling: function (vector) {
    // Find the maximum absolute value
    let maxVal = 0;
    
    for (let i = 0; i < vector.length; i++) {
      maxVal = Math.max(maxVal, Math.abs(vector[i]));
    }
    
    // Special case for zero vector
    if (maxVal === 0) {
      return 0;
    }
    
    // Compute scaled sum of squares
    let sum = 0;
    let compensation = 0;
    
    for (let i = 0; i < vector.length; i++) {
      const scaled = vector[i] / maxVal;
      const squared = scaled * scaled;
      
      // Kahan summation step
      const y = squared - compensation;
      const t = sum + y;
      compensation = t - sum - y;
      sum = t;
    }
    
    // Scale back the result
    return sum * maxVal * maxVal;
  },

  /**
   * Normalize a vector to unit length
   * @param {Array|TypedArray} vector - Vector to normalize
   * @param {Array|TypedArray} [result] - Optional result vector (for in-place operations)
   * @param {Object} [options={}] - Additional options
   * @param {number} [options.epsilon=1e-10] - Tolerance for zero vectors
   * @param {boolean} [options.useScaling=true] - Whether to use scaling for extreme values
   * @param {string} [options.method='adaptive'] - Method to use for magnitude calculation
   * @returns {Array|TypedArray} - Normalized vector
   */
  normalize: function (vector, result, options = {}) {
    if (!this.isVector(vector)) {
      throw new Prime.ValidationError('Vector must be an array or TypedArray');
    }

    const epsilon = options.epsilon || 1e-10;
    const useScaling = options.useScaling !== false;
    const method = options.method || 'adaptive';
    
    // Calculate magnitude using enhanced methods
    const mag = this.magnitude(vector, { 
      useScaling: useScaling, 
      method: method 
    });

    if (mag < epsilon) {
      throw new Prime.MathematicalError('Cannot normalize a zero vector');
    }

    // Find max absolute value for potential scaling
    let maxVal = 0;
    if (useScaling) {
      for (let i = 0; i < vector.length; i++) {
        maxVal = Math.max(maxVal, Math.abs(vector[i]));
      }
    }
    
    // Special handling for extreme values to prevent underflow/overflow
    const needsScaling = useScaling && (maxVal > 1e150 || (maxVal < 1e-150 && maxVal > 0));
    
    // If result vector is provided, use it for in-place operation
    if (result && this.isVector(result) && result.length === vector.length) {
      if (needsScaling) {
        // Use scaled normalization for extreme values
        const scale = maxVal;
        for (let i = 0; i < vector.length; i++) {
          const scaled = vector[i] / scale;
          result[i] = scaled / (mag / scale);
        }
      } else {
        // Standard normalization
        for (let i = 0; i < vector.length; i++) {
          result[i] = vector[i] / mag;
        }
      }
      return result;
    }

    // Otherwise, create a new result vector
    // Use TypedArray if input is TypedArray
    if (ArrayBuffer.isView(vector)) {
      const resultVector = new vector.constructor(vector.length);
      
      if (needsScaling) {
        // Use scaled normalization for extreme values
        const scale = maxVal;
        for (let i = 0; i < vector.length; i++) {
          const scaled = vector[i] / scale;
          resultVector[i] = scaled / (mag / scale);
        }
      } else {
        // Standard normalization
        for (let i = 0; i < vector.length; i++) {
          resultVector[i] = vector[i] / mag;
        }
      }
      
      return resultVector;
    }

    // Regular array implementation
    if (needsScaling) {
      // Use scaled normalization for extreme values 
      const scale = maxVal;
      return vector.map(val => (val / scale) / (mag / scale));
    } else {
      // Standard normalization
      return vector.map(val => val / mag);
    }
  },

  /**
   * Calculate the distance between two vectors
   * @param {Array|TypedArray} a - First vector
   * @param {Array|TypedArray} b - Second vector
   * @param {Object} [options={}] - Additional options
   * @param {string} [options.method='adaptive'] - Method to use ('kahan', 'pairwise', 'adaptive', 'scaling')
   * @param {boolean} [options.useScaling=true] - Whether to use scaling for extreme values
   * @returns {number} - Distance between vectors
   */
  distance: function (a, b, options = {}) {
    if (!this.isVector(a) || !this.isVector(b)) {
      throw new Prime.ValidationError('Vectors must be arrays or TypedArrays');
    }

    if (a.length !== b.length) {
      throw new Prime.ValidationError('Vectors must have the same dimensions');
    }

    const method = options.method || 'adaptive';
    const useScaling = options.useScaling !== false;

    // Select the most appropriate method based on input
    if (method === 'adaptive') {
      // For short vectors, Kahan is efficient
      if (a.length < 100) {
        return this._distanceKahan(a, b, useScaling);
      }
      // For longer vectors, pairwise may be better
      return this._distancePairwise(a, b, useScaling);
    } else if (method === 'pairwise') {
      return this._distancePairwise(a, b, useScaling);
    } else if (method === 'scaling') {
      return this._distanceScaling(a, b);
    } else {
      // Default to Kahan summation
      return this._distanceKahan(a, b, useScaling);
    }
  },

  /**
   * Calculate distance using Kahan summation (numerically stable)
   * @private
   * @param {Array|TypedArray} a - First vector
   * @param {Array|TypedArray} b - Second vector
   * @param {boolean} useScaling - Whether to use scaling for extreme values
   * @returns {number} - Distance between vectors
   */
  _distanceKahan: function (a, b, useScaling) {
    let sum = 0;
    let compensation = 0;
    
    // Handle extreme values with scaling
    if (useScaling) {
      // Find max absolute difference for scaling
      let maxDiff = 0;
      
      for (let i = 0; i < a.length; i++) {
        maxDiff = Math.max(maxDiff, Math.abs(a[i] - b[i]));
      }
      
      // Avoid division by zero
      const scale = maxDiff === 0 ? 1 : maxDiff;
      
      // Extreme value scaling
      if (maxDiff > 1e100 || maxDiff < 1e-100) {
        // Compute sum of squares with scaling
        for (let i = 0; i < a.length; i++) {
          const diff = a[i] - b[i];
          const scaledDiff = diff / scale;
          const squared = scaledDiff * scaledDiff;
          
          // Kahan summation step
          const y = squared - compensation;
          const t = sum + y;
          compensation = t - sum - y;
          sum = t;
        }
        
        // Scale back the result
        return Math.sqrt(Math.max(0, sum)) * scale;
      }
    }
    
    // Standard Kahan summation for normal values
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
   * Calculate distance using pairwise summation (good for long vectors)
   * @private
   * @param {Array|TypedArray} a - First vector
   * @param {Array|TypedArray} b - Second vector
   * @param {boolean} useScaling - Whether to use scaling for extreme values
   * @returns {number} - Distance between vectors
   */
  _distancePairwise: function (a, b, useScaling) {
    // Precompute all squared differences
    const squaredDiffs = new Array(a.length);
    
    // Handle extreme values with scaling
    if (useScaling) {
      // Find max absolute difference for scaling
      let maxDiff = 0;
      
      for (let i = 0; i < a.length; i++) {
        maxDiff = Math.max(maxDiff, Math.abs(a[i] - b[i]));
      }
      
      // Avoid division by zero
      const scale = maxDiff === 0 ? 1 : maxDiff;
      
      // Extreme value scaling
      if (maxDiff > 1e100 || maxDiff < 1e-100) {
        // Compute squares with scaling
        for (let i = 0; i < a.length; i++) {
          const diff = a[i] - b[i];
          const scaledDiff = diff / scale;
          squaredDiffs[i] = scaledDiff * scaledDiff;
        }
        
        // Use pairwise summation
        const sum = this._pairwiseSum(squaredDiffs);
        
        // Scale back the result
        return Math.sqrt(Math.max(0, sum)) * scale;
      }
    }
    
    // Compute squares without scaling
    for (let i = 0; i < a.length; i++) {
      const diff = a[i] - b[i];
      squaredDiffs[i] = diff * diff;
    }
    
    // Use pairwise summation
    const sum = this._pairwiseSum(squaredDiffs);
    
    // Prevent negative square roots due to floating point errors
    return Math.sqrt(Math.max(0, sum));
  },

  /**
   * Calculate distance using two-pass scaling method (most stable for extreme values)
   * @private
   * @param {Array|TypedArray} a - First vector
   * @param {Array|TypedArray} b - Second vector
   * @returns {number} - Distance between vectors
   */
  _distanceScaling: function (a, b) {
    // Find the maximum absolute difference
    let maxDiff = 0;
    
    for (let i = 0; i < a.length; i++) {
      maxDiff = Math.max(maxDiff, Math.abs(a[i] - b[i]));
    }
    
    // Special case for identical vectors
    if (maxDiff === 0) {
      return 0;
    }
    
    // Compute scaled sum of squares
    let sum = 0;
    let compensation = 0;
    
    for (let i = 0; i < a.length; i++) {
      const diff = a[i] - b[i];
      const scaledDiff = diff / maxDiff;
      const squared = scaledDiff * scaledDiff;
      
      // Kahan summation step
      const y = squared - compensation;
      const t = sum + y;
      compensation = t - sum - y;
      sum = t;
    }
    
    // Scale back the result
    return Math.sqrt(Math.max(0, sum)) * maxDiff;
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
