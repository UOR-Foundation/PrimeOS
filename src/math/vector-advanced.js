/**
 * PrimeOS JavaScript Library - Math
 * Vector Advanced Operations
 * Advanced vector operations building on the core functionality
 */

// Import the Prime object with VectorCore
const Prime = require("./vector-core");

// Ensure VectorCore exists
if (!Prime.Math.VectorCore) {
  throw new Error("VectorCore must be loaded before VectorAdvanced");
}

// Get reference to VectorCore
const VectorCore = Prime.Math.VectorCore;

/**
 * Advanced vector operations
 */
const VectorAdvanced = {
  /**
   * Calculate the cross product of two 3D vectors
   * @param {Array|TypedArray} a - First 3D vector
   * @param {Array|TypedArray} b - Second 3D vector
   * @param {Array|TypedArray} [result] - Optional result vector (for in-place operations)
   * @returns {Array|TypedArray} - Cross product
   */
  cross: function (a, b, result) {
    if (!VectorCore.isVector(a) || !VectorCore.isVector(b)) {
      throw new Prime.ValidationError("Vectors must be arrays or TypedArrays");
    }

    if (a.length !== 3 || b.length !== 3) {
      throw new Prime.ValidationError(
        "Cross product is only defined for 3D vectors",
      );
    }

    // Calculate cross product components
    const cx = a[1] * b[2] - a[2] * b[1];
    const cy = a[2] * b[0] - a[0] * b[2];
    const cz = a[0] * b[1] - a[1] * b[0];

    // If result vector is provided, use it for in-place operation
    if (result && VectorCore.isVector(result) && result.length >= 3) {
      result[0] = cx;
      result[1] = cy;
      result[2] = cz;
      return result;
    }

    // Otherwise, create a new result vector
    // Use TypedArray if inputs are TypedArrays
    if (ArrayBuffer.isView(a)) {
      const resultVector = new a.constructor(3);
      resultVector[0] = cx;
      resultVector[1] = cy;
      resultVector[2] = cz;
      return resultVector;
    }

    // Regular array implementation
    return [cx, cy, cz];
  },

  /**
   * Calculate the angle between two vectors in radians
   * @param {Array|TypedArray} a - First vector
   * @param {Array|TypedArray} b - Second vector
   * @returns {number} - Angle in radians
   */
  angle: function (a, b) {
    if (!VectorCore.isVector(a) || !VectorCore.isVector(b)) {
      throw new Prime.ValidationError("Vectors must be arrays or TypedArrays");
    }

    if (a.length !== b.length) {
      throw new Prime.ValidationError("Vectors must have the same dimensions");
    }

    const magA = VectorCore.magnitude(a);
    const magB = VectorCore.magnitude(b);

    if (magA === 0 || magB === 0) {
      throw new Prime.MathematicalError(
        "Cannot calculate angle with zero vector",
      );
    }

    const dotProduct = VectorCore.dot(a, b);
    const cosTheta = dotProduct / (magA * magB);

    // Handle floating point precision issues
    if (cosTheta > 1) return 0;
    if (cosTheta < -1) return Math.PI;

    return Math.acos(cosTheta);
  },

  /**
   * Project vector a onto vector b
   * @param {Array|TypedArray} a - Vector to project
   * @param {Array|TypedArray} b - Vector to project onto
   * @param {Array|TypedArray} [result] - Optional result vector (for in-place operations)
   * @returns {Array|TypedArray} - Projection result
   */
  project: function (a, b, result) {
    if (!VectorCore.isVector(a) || !VectorCore.isVector(b)) {
      throw new Prime.ValidationError("Vectors must be arrays or TypedArrays");
    }

    if (a.length !== b.length) {
      throw new Prime.ValidationError("Vectors must have the same dimensions");
    }

    const magBSquared = VectorCore.magnitudeSquared(b);

    if (magBSquared === 0) {
      throw new Prime.MathematicalError("Cannot project onto a zero vector");
    }

    const scalar = VectorCore.dot(a, b) / magBSquared;

    // Use in-place scale operation if result is provided
    if (result) {
      // First copy b to result
      VectorCore.copy(b, result);
      // Then scale result in-place
      return VectorCore.scale(result, scalar, result);
    }

    // Otherwise create a new vector
    return VectorCore.scale(b, scalar);
  },

  /**
   * Linear interpolation between two vectors
   * @param {Array|TypedArray} a - Start vector
   * @param {Array|TypedArray} b - End vector
   * @param {number} t - Interpolation parameter (0-1)
   * @param {Array|TypedArray} [result] - Optional result vector (for in-place operations)
   * @returns {Array|TypedArray} - Interpolated vector
   */
  lerp: function (a, b, t, result) {
    if (!VectorCore.isVector(a) || !VectorCore.isVector(b)) {
      throw new Prime.ValidationError("Vectors must be arrays or TypedArrays");
    }

    if (a.length !== b.length) {
      throw new Prime.ValidationError("Vectors must have the same dimensions");
    }

    if (!Prime.Utils.isNumber(t)) {
      throw new Prime.ValidationError(
        "Interpolation parameter must be a number",
      );
    }

    // Clamp t to [0,1] for safety
    const tClamped = Math.max(0, Math.min(1, t));
    const oneMinusT = 1 - tClamped;

    // If result vector is provided, use it for in-place operation
    if (result && VectorCore.isVector(result) && result.length === a.length) {
      for (let i = 0; i < a.length; i++) {
        result[i] = oneMinusT * a[i] + tClamped * b[i];
      }
      return result;
    }

    // Otherwise, create a new result vector
    // Use TypedArray if inputs are TypedArrays
    if (ArrayBuffer.isView(a)) {
      const resultVector = new a.constructor(a.length);
      for (let i = 0; i < a.length; i++) {
        resultVector[i] = oneMinusT * a[i] + tClamped * b[i];
      }
      return resultVector;
    }

    // Regular array implementation
    return a.map((val, i) => oneMinusT * val + tClamped * b[i]);
  },

  /**
   * Calculate average of multiple vectors
   * @param {Array<Array|TypedArray>} vectors - Array of vectors
   * @param {Array|TypedArray} [result] - Optional result vector (for in-place operations)
   * @returns {Array|TypedArray} - Average vector
   */
  average: function (vectors, result) {
    if (!Array.isArray(vectors) || vectors.length === 0) {
      throw new Prime.ValidationError("Must provide at least one vector");
    }

    const firstVec = vectors[0];
    if (!VectorCore.isVector(firstVec)) {
      throw new Prime.ValidationError("Vectors must be arrays or TypedArrays");
    }

    const dimensions = firstVec.length;

    // Ensure all vectors have the same dimensions
    for (let i = 1; i < vectors.length; i++) {
      if (
        !VectorCore.isVector(vectors[i]) ||
        vectors[i].length !== dimensions
      ) {
        throw new Prime.ValidationError(
          "All vectors must have the same dimensions",
        );
      }
    }

    // If result vector is provided, use it for in-place operation
    if (result && VectorCore.isVector(result) && result.length === dimensions) {
      // First fill with zeros
      VectorCore.fill(result, 0);

      // Accumulate each vector
      for (let i = 0; i < vectors.length; i++) {
        for (let j = 0; j < dimensions; j++) {
          result[j] += vectors[i][j];
        }
      }

      // Divide by count
      for (let j = 0; j < dimensions; j++) {
        result[j] /= vectors.length;
      }

      return result;
    }

    // Otherwise, create a new result vector
    // Use TypedArray if the first input is TypedArray
    if (ArrayBuffer.isView(firstVec)) {
      const resultVector = new firstVec.constructor(dimensions);
      resultVector.fill(0);

      // Accumulate each vector
      for (let i = 0; i < vectors.length; i++) {
        for (let j = 0; j < dimensions; j++) {
          resultVector[j] += vectors[i][j];
        }
      }

      // Divide by count
      for (let j = 0; j < dimensions; j++) {
        resultVector[j] /= vectors.length;
      }

      return resultVector;
    }

    // Regular array implementation
    const result_arr = Array(dimensions).fill(0);

    for (let i = 0; i < vectors.length; i++) {
      for (let j = 0; j < dimensions; j++) {
        result_arr[j] += vectors[i][j];
      }
    }

    for (let j = 0; j < dimensions; j++) {
      result_arr[j] /= vectors.length;
    }

    return result_arr;
  },

  /**
   * Calculate weighted average of multiple vectors
   * @param {Array<Array|TypedArray>} vectors - Array of vectors
   * @param {Array<number>} weights - Array of weights
   * @param {Array|TypedArray} [result] - Optional result vector (for in-place operations)
   * @returns {Array|TypedArray} - Weighted average vector
   */
  weightedAverage: function (vectors, weights, result) {
    if (!Array.isArray(vectors) || vectors.length === 0) {
      throw new Prime.ValidationError("Must provide at least one vector");
    }

    if (!Array.isArray(weights) || weights.length !== vectors.length) {
      throw new Prime.ValidationError(
        "Weights array must match vectors array length",
      );
    }

    const firstVec = vectors[0];
    if (!VectorCore.isVector(firstVec)) {
      throw new Prime.ValidationError("Vectors must be arrays or TypedArrays");
    }

    const dimensions = firstVec.length;

    // Ensure all vectors have the same dimensions
    for (let i = 1; i < vectors.length; i++) {
      if (
        !VectorCore.isVector(vectors[i]) ||
        vectors[i].length !== dimensions
      ) {
        throw new Prime.ValidationError(
          "All vectors must have the same dimensions",
        );
      }
    }

    // Calculate sum of weights
    let weightSum = 0;
    for (let i = 0; i < weights.length; i++) {
      if (!Prime.Utils.isNumber(weights[i])) {
        throw new Prime.ValidationError("Weights must be numbers");
      }
      weightSum += weights[i];
    }

    if (weightSum === 0) {
      throw new Prime.ValidationError("Sum of weights cannot be zero");
    }

    // If result vector is provided, use it for in-place operation
    if (result && VectorCore.isVector(result) && result.length === dimensions) {
      // First fill with zeros
      VectorCore.fill(result, 0);

      // Accumulate each vector * weight
      for (let i = 0; i < vectors.length; i++) {
        for (let j = 0; j < dimensions; j++) {
          result[j] += vectors[i][j] * weights[i];
        }
      }

      // Divide by weight sum
      for (let j = 0; j < dimensions; j++) {
        result[j] /= weightSum;
      }

      return result;
    }

    // Otherwise, create a new result vector
    // Use TypedArray if the first input is TypedArray
    if (ArrayBuffer.isView(firstVec)) {
      const resultVector = new firstVec.constructor(dimensions);
      resultVector.fill(0);

      // Accumulate each vector * weight
      for (let i = 0; i < vectors.length; i++) {
        for (let j = 0; j < dimensions; j++) {
          resultVector[j] += vectors[i][j] * weights[i];
        }
      }

      // Divide by weight sum
      for (let j = 0; j < dimensions; j++) {
        resultVector[j] /= weightSum;
      }

      return resultVector;
    }

    // Regular array implementation
    const result_arr = Array(dimensions).fill(0);

    for (let i = 0; i < vectors.length; i++) {
      for (let j = 0; j < dimensions; j++) {
        result_arr[j] += vectors[i][j] * weights[i];
      }
    }

    for (let j = 0; j < dimensions; j++) {
      result_arr[j] /= weightSum;
    }

    return result_arr;
  },

  /**
   * Spherically interpolate between two vectors
   * @param {Array|TypedArray} a - Start vector
   * @param {Array|TypedArray} b - End vector
   * @param {number} t - Interpolation parameter (0-1)
   * @param {Array|TypedArray} [result] - Optional result vector (for in-place operations)
   * @returns {Array|TypedArray} - Interpolated vector
   */
  slerp: function (a, b, t, result) {
    if (!VectorCore.isVector(a) || !VectorCore.isVector(b)) {
      throw new Prime.ValidationError("Vectors must be arrays or TypedArrays");
    }

    if (a.length !== b.length) {
      throw new Prime.ValidationError("Vectors must have the same dimensions");
    }

    if (!Prime.Utils.isNumber(t)) {
      throw new Prime.ValidationError(
        "Interpolation parameter must be a number",
      );
    }

    // Clamp t to [0,1]
    const tClamped = Math.max(0, Math.min(1, t));

    // Normalize inputs
    const normA = VectorCore.normalize(a);
    const normB = VectorCore.normalize(b);

    // Calculate dot product and determine the angle
    const dot = VectorCore.dot(normA, normB);

    // If vectors are parallel, use simple linear interpolation
    if (Math.abs(dot) >= 0.9999) {
      return this.lerp(a, b, tClamped, result);
    }

    // Clamp dot to [-1, 1] range to handle numerical errors
    const clampedDot = Math.max(-1, Math.min(1, dot));
    const theta = Math.acos(clampedDot);
    const sinTheta = Math.sin(theta);

    // Early return for division by zero
    if (sinTheta < 1e-10) {
      return this.lerp(a, b, tClamped, result);
    }

    // Calculate spherical interpolation coefficients
    const w1 = Math.sin((1 - tClamped) * theta) / sinTheta;
    const w2 = Math.sin(tClamped * theta) / sinTheta;

    // If result vector is provided, use it for in-place operation
    if (result && VectorCore.isVector(result) && result.length === a.length) {
      for (let i = 0; i < a.length; i++) {
        result[i] = w1 * a[i] + w2 * b[i];
      }
      return result;
    }

    // Otherwise, create a new result vector
    // Use TypedArray if inputs are TypedArrays
    if (ArrayBuffer.isView(a)) {
      const resultVector = new a.constructor(a.length);
      for (let i = 0; i < a.length; i++) {
        resultVector[i] = w1 * a[i] + w2 * b[i];
      }
      return resultVector;
    }

    // Regular array implementation
    return a.map((val, i) => w1 * val + w2 * b[i]);
  },

  /**
   * Orthogonalize a vector against another vector
   * (Gram-Schmidt process for a single vector)
   * @param {Array|TypedArray} v - Vector to orthogonalize
   * @param {Array|TypedArray} reference - Reference vector
   * @param {Array|TypedArray} [result] - Optional result vector (for in-place operations)
   * @returns {Array|TypedArray} - Orthogonalized vector
   */
  orthogonalize: function (v, reference, result) {
    if (!VectorCore.isVector(v) || !VectorCore.isVector(reference)) {
      throw new Prime.ValidationError("Vectors must be arrays or TypedArrays");
    }

    if (v.length !== reference.length) {
      throw new Prime.ValidationError("Vectors must have the same dimensions");
    }

    // Project v onto reference
    const projection = this.project(v, reference);

    // If result vector is provided, use it for in-place operation
    if (result && VectorCore.isVector(result) && result.length === v.length) {
      // First copy v to result
      VectorCore.copy(v, result);
      // Then subtract projection
      return VectorCore.subtract(result, projection, result);
    }

    // Otherwise, create a new result vector
    return VectorCore.subtract(v, projection);
  },

  /**
   * Check if two vectors are orthogonal (perpendicular)
   * @param {Array|TypedArray} a - First vector
   * @param {Array|TypedArray} b - Second vector
   * @param {Object} [options={}] - Options
   * @param {number} [options.tolerance=1e-10] - Tolerance for near-zero values
   * @returns {boolean} - True if vectors are orthogonal
   */
  isOrthogonal: function (a, b, options = {}) {
    if (!VectorCore.isVector(a) || !VectorCore.isVector(b)) {
      throw new Prime.ValidationError("Vectors must be arrays or TypedArrays");
    }

    if (a.length !== b.length) {
      throw new Prime.ValidationError("Vectors must have the same dimensions");
    }

    // Use an algorithm that handles extreme numerical values better
    // Similar to the one used in extreme-conditions-tests.js

    // Get the tolerance
    const tolerance = options.tolerance || 1e-10;

    // Calculate dot product
    const dot = VectorCore.dot(a, b);

    // Calculate norms
    const normA = VectorCore.magnitude(a);
    const normB = VectorCore.magnitude(b);

    // For vectors with extreme ranges, scale tolerance by the product of norms
    // Plus Number.MIN_VALUE to avoid division by zero when norms are extremely small
    const scaledTolerance = tolerance * (normA * normB + Number.MIN_VALUE);

    // Check if dot product is close to zero relative to vector magnitudes
    return Math.abs(dot) <= scaledTolerance;
  },

  /**
   * Check if two vectors are parallel
   * @param {Array|TypedArray} a - First vector
   * @param {Array|TypedArray} b - Second vector
   * @param {Object} [options={}] - Options
   * @param {number} [options.tolerance=1e-10] - Tolerance for near-1 cosine values
   * @returns {boolean} - True if vectors are parallel (or antiparallel)
   */
  isParallel: function (a, b, options = {}) {
    if (!VectorCore.isVector(a) || !VectorCore.isVector(b)) {
      throw new Prime.ValidationError("Vectors must be arrays or TypedArrays");
    }

    if (a.length !== b.length) {
      throw new Prime.ValidationError("Vectors must have the same dimensions");
    }

    const tolerance = options.tolerance || 1e-10;

    // Check for zero vectors
    const magA = VectorCore.magnitude(a);
    const magB = VectorCore.magnitude(b);

    if (magA < tolerance || magB < tolerance) {
      // Zero vectors are considered parallel by convention
      return true;
    }

    // Calculate cosine of angle
    const dot = VectorCore.dot(a, b);
    const cosAngle = Math.abs(dot / (magA * magB));

    // Vectors are parallel if cosine is close to 1
    return Math.abs(cosAngle - 1) < tolerance;
  },

  /**
   * Reflect a vector across a normal vector
   * @param {Array|TypedArray} v - Vector to reflect
   * @param {Array|TypedArray} normal - Normal vector (should be normalized)
   * @param {Array|TypedArray} [result] - Optional result vector (for in-place operations)
   * @returns {Array|TypedArray} - Reflected vector
   */
  reflect: function (v, normal, result) {
    if (!VectorCore.isVector(v) || !VectorCore.isVector(normal)) {
      throw new Prime.ValidationError("Vectors must be arrays or TypedArrays");
    }

    if (v.length !== normal.length) {
      throw new Prime.ValidationError("Vectors must have the same dimensions");
    }

    // Ensure normal is normalized
    const normalMag = VectorCore.magnitude(normal);
    if (Math.abs(normalMag - 1) > 1e-10) {
      throw new Prime.ValidationError("Normal vector should be normalized");
    }

    // Calculate reflection: v - 2 * dot(v, normal) * normal
    const dotProduct = VectorCore.dot(v, normal);
    const scaledNormal = VectorCore.scale(normal, 2 * dotProduct);

    // If result vector is provided, use it for in-place operation
    if (result && VectorCore.isVector(result) && result.length === v.length) {
      return VectorCore.subtract(v, scaledNormal, result);
    }

    // Otherwise, create a new result vector
    return VectorCore.subtract(v, scaledNormal);
  },
};

// Add vector-advanced to the Prime.Math namespace
Prime.Math = Prime.Math || {};

// Check if VectorAdvanced already has a getter defined, if so, use it
if (
  Object.getOwnPropertyDescriptor(Prime.Math, "VectorAdvanced") &&
  Object.getOwnPropertyDescriptor(Prime.Math, "VectorAdvanced").get
) {
  // Use a more careful approach to update the property
  const descriptor = Object.getOwnPropertyDescriptor(
    Prime.Math,
    "VectorAdvanced",
  );
  const originalGetter = descriptor.get;

  Object.defineProperty(Prime.Math, "VectorAdvanced", {
    get: function () {
      const result = originalGetter.call(this);
      // If result is an empty object (placeholder), return our implementation
      if (Object.keys(result).length === 0) {
        return VectorAdvanced;
      }
      // Otherwise, preserve what's already there
      return result;
    },
    configurable: true,
  });
} else {
  // Direct assignment if no getter exists
  Prime.Math.VectorAdvanced = VectorAdvanced;
}

// Export the enhanced Prime object
module.exports = Prime;
