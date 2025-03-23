/**
 * PrimeOS JavaScript Library - Framework
 * Math: Tensor Operations with Numerical Stability
 * Implementation for tensor operations with extreme value handling
 */

// Import core
const Prime = require("../../core/prime.js");
// Import the StandardMath interface
const StandardMath = require("./index.js").Standard;

/**
 * TensorOperations - Operations for working with tensors with extreme value stability
 *
 * This module provides tensor operations that are numerically stable
 * for both extremely small values (<1e-100) and extremely large values (>1e100).
 * It implements various techniques to prevent overflow, underflow, and
 * catastrophic cancellation during tensor calculations.
 */
const TensorOperations = {
  /**
   * Create a new tensor with the given shape and initial value
   *
   * @param {Array<number>} shape - Shape of the tensor to create
   * @param {number|Function} initialValue - Initial value or function to generate values
   * @returns {Array} New tensor with the given shape
   */
  create: function (shape, initialValue = 0) {
    if (
      !Array.isArray(shape) ||
      shape.some((dim) => !Number.isInteger(dim) || dim < 0)
    ) {
      throw new Error("Shape must be an array of non-negative integers");
    }

    // Base case: 0-dimensional tensor (scalar)
    if (shape.length === 0) {
      return typeof initialValue === "function" ? initialValue() : initialValue;
    }

    // Recursive case
    const [firstDim, ...restDims] = shape;
    const result = new Array(firstDim);

    // Calculate total elements for indexing when using function initializer
    let elementsPerItem = 1;
    for (const dim of restDims) {
      elementsPerItem *= dim;
    }

    for (let i = 0; i < firstDim; i++) {
      if (restDims.length === 0) {
        // For leaf elements
        result[i] =
          typeof initialValue === "function" ? initialValue(i) : initialValue;
      } else {
        // For nested arrays, pass the function with adjusted index if it's a function
        result[i] =
          typeof initialValue === "function"
            ? this.create(restDims, (j) =>
                initialValue(i * elementsPerItem + j),
              )
            : this.create(restDims, initialValue);
      }
    }

    return result;
  },

  /**
   * Get the shape of a tensor
   *
   * @param {Array} tensor - Input tensor
   * @returns {Array<number>} Shape of the tensor
   */
  shape: function (tensor) {
    if (!Array.isArray(tensor)) {
      return [];
    }

    const shape = [tensor.length];

    if (tensor.length > 0 && Array.isArray(tensor[0])) {
      const subShape = this.shape(tensor[0]);
      shape.push(...subShape);
    }

    return shape;
  },

  /**
   * Determine whether a value is extreme (very large or very small)
   *
   * @param {number} value - Value to check
   * @returns {boolean} True if value is extreme
   */
  isExtremeValue: function (value) {
    try {
      // Use StandardMath for extreme value detection with proper handling
      return StandardMath.isExtremeValue(value);
    } catch (error) {
      // Fallback to direct implementation if StandardMath is not available
      Prime.Logger &&
        Prime.Logger.warn(
          "StandardMath.isExtremeValue failed: " +
            error.message +
            ". Using direct implementation.",
        );

      if (!isFinite(value)) return true;
      const absValue = Math.abs(value);
      return absValue > 1e100 || (absValue > 0 && absValue < 1e-100);
    }
  },

  /**
   * Check if a tensor contains extreme values
   *
   * @param {Array} tensor - Input tensor
   * @returns {boolean} True if tensor contains extreme values
   */
  hasExtremeValues: function (tensor) {
    // For scalar values
    if (!Array.isArray(tensor)) {
      return this.isExtremeValue(tensor);
    }

    // For arrays, check recursively
    for (let i = 0; i < tensor.length; i++) {
      if (Array.isArray(tensor[i])) {
        if (this.hasExtremeValues(tensor[i])) {
          return true;
        }
      } else if (this.isExtremeValue(tensor[i])) {
        return true;
      }
    }

    return false;
  },

  /**
   * Apply a function to each element of a tensor
   *
   * @param {Array} tensor - Input tensor
   * @param {Function} fn - Function to apply to each element
   * @returns {Array} New tensor with function applied
   */
  map: function (tensor, fn) {
    if (!Array.isArray(tensor)) {
      return fn(tensor);
    }

    return tensor.map((element) => {
      if (Array.isArray(element)) {
        return this.map(element, fn);
      }
      return fn(element);
    });
  },

  /**
   * Find the scaling factor for a tensor to prevent overflow/underflow
   *
   * @param {Array} tensor - Input tensor
   * @returns {Object} Scaling information
   */
  findScalingFactor: function (tensor) {
    const flatValues = this.flatten(tensor);
    let maxAbsValue = 0;
    let minAbsNonZeroValue = Infinity;

    for (let i = 0; i < flatValues.length; i++) {
      const absValue = Math.abs(flatValues[i]);
      if (absValue > 0) {
        maxAbsValue = Math.max(maxAbsValue, absValue);
        minAbsNonZeroValue = Math.min(minAbsNonZeroValue, absValue);
      }
    }

    let scaleFactor = 1;
    let needsScaling = false;

    // Handle large values
    if (maxAbsValue > 1e100) {
      scaleFactor = 1e-100;
      needsScaling = true;
    }
    // Handle small values
    else if (maxAbsValue > 0 && maxAbsValue < 1e-100) {
      scaleFactor = 1e100;
      needsScaling = true;
    }
    // Handle mixed scales with large dynamic range
    else if (minAbsNonZeroValue < 1e-100 && maxAbsValue > 1) {
      const dynamicRange = maxAbsValue / minAbsNonZeroValue;
      if (dynamicRange > 1e200) {
        // Use logarithmic mean scaling for large dynamic range
        const logMean = Math.exp(
          (Math.log(maxAbsValue) + Math.log(minAbsNonZeroValue)) / 2,
        );
        scaleFactor = 1 / logMean;
        needsScaling = true;
      }
    }

    return {
      scaleFactor,
      needsScaling,
      maxAbsValue,
      minAbsNonZeroValue,
    };
  },

  /**
   * Scale a tensor by a factor to prevent overflow/underflow
   *
   * @param {Array} tensor - Input tensor
   * @param {number} factor - Scaling factor
   * @returns {Array} Scaled tensor
   */
  scale: function (tensor, factor) {
    return this.map(tensor, (value) => value * factor);
  },

  /**
   * Flatten a tensor to a 1D array
   *
   * @param {Array} tensor - Input tensor
   * @returns {Array} Flattened 1D array
   */
  flatten: function (tensor) {
    if (!Array.isArray(tensor)) {
      return [tensor];
    }

    let result = [];

    for (let i = 0; i < tensor.length; i++) {
      if (Array.isArray(tensor[i])) {
        result = result.concat(this.flatten(tensor[i]));
      } else {
        result.push(tensor[i]);
      }
    }

    return result;
  },

  /**
   * Reshape a flat array into a tensor with the given shape
   *
   * @param {Array} flat - Flat array of values
   * @param {Array<number>} shape - Desired shape
   * @returns {Array} Reshaped tensor
   */
  reshape: function (flat, shape) {
    if (shape.length === 0) {
      return flat[0];
    }

    if (shape.length === 1) {
      return flat.slice(0, shape[0]);
    }

    const [firstDim, ...restDims] = shape;
    const result = new Array(firstDim);
    const subSize = restDims.reduce((acc, dim) => acc * dim, 1);

    for (let i = 0; i < firstDim; i++) {
      const start = i * subSize;
      const end = start + subSize;
      result[i] = this.reshape(flat.slice(start, end), restDims);
    }

    return result;
  },

  /**
   * Add two tensors with numerical stability
   *
   * @param {Array} a - First tensor
   * @param {Array} b - Second tensor
   * @param {Object} [options={}] - Addition options
   * @param {boolean} [options.useKahan=true] - Whether to use Kahan summation
   * @param {boolean} [options.useScaling=true] - Whether to use scaling for extreme values
   * @returns {Array} Result of addition
   */
  add: function (a, b, options = {}) {
    const useKahan = options.useKahan !== false;
    const useScaling = options.useScaling !== false;

    // Check if tensors have extreme values
    const hasExtremeA = useScaling && this.hasExtremeValues(a);
    const hasExtremeB = useScaling && this.hasExtremeValues(b);

    // Apply scaling if needed
    let scaledA = a;
    let scaledB = b;
    let scaleFactorA = 1;
    let scaleFactorB = 1;

    if (hasExtremeA || hasExtremeB) {
      const scaleInfoA = this.findScalingFactor(a);
      const scaleInfoB = this.findScalingFactor(b);

      if (scaleInfoA.needsScaling) {
        scaledA = this.scale(a, scaleInfoA.scaleFactor);
        scaleFactorA = scaleInfoA.scaleFactor;
      }

      if (scaleInfoB.needsScaling) {
        scaledB = this.scale(b, scaleInfoB.scaleFactor);
        scaleFactorB = scaleInfoB.scaleFactor;
      }
    }

    // Helper function for adding elements with potential compensation
    const addElements = (x, y, compensation = 0) => {
      try {
        if (useKahan) {
          // Use StandardMath for Kahan summation for improved numerical stability
          const { sum, compensation: newCompensation } =
            StandardMath.addWithCompensation(x, y, compensation);
          return { result: sum, compensation: newCompensation };
        } else {
          return { result: StandardMath.add(x, y), compensation: 0 };
        }
      } catch (error) {
        // Fallback to direct implementation if StandardMath is not available
        if (useKahan) {
          // Kahan summation to reduce floating point errors
          const sum = x + y - compensation;
          const velation = sum - x;
          return { result: sum, compensation: velation - y };
        }
        return { result: x + y, compensation: 0 };
      }
    };

    // Helper function for adding arrays recursively
    const addArrays = (arrA, arrB, compensation = null) => {
      if (!Array.isArray(arrA) || !Array.isArray(arrB)) {
        // One or both inputs are scalars
        const scalarA = Array.isArray(arrA) ? 0 : arrA;
        const scalarB = Array.isArray(arrB) ? 0 : arrB;
        const comp = Array.isArray(compensation) ? 0 : compensation || 0;
        const { result, compensation: newComp } = addElements(
          scalarA,
          scalarB,
          comp,
        );
        return { result, compensation: newComp };
      }

      // Both inputs are arrays
      const result = new Array(Math.max(arrA.length, arrB.length));
      const newCompensation = compensation ? new Array(result.length) : null;

      for (let i = 0; i < result.length; i++) {
        const elemA = i < arrA.length ? arrA[i] : 0;
        const elemB = i < arrB.length ? arrB[i] : 0;
        const elemComp =
          compensation && i < compensation.length ? compensation[i] : 0;

        if (Array.isArray(elemA) || Array.isArray(elemB)) {
          // Recursive case for nested arrays
          // Ensure both operands have the right shape
          const arrAIsArray = Array.isArray(elemA);
          const arrBIsArray = Array.isArray(elemB);

          // Create zero-filled arrays if one side is not an array
          const opA = arrAIsArray ? elemA : [0];
          const opB = arrBIsArray ? elemB : [0];

          const { result: subResult, compensation: subComp } = addArrays(
            opA,
            opB,
            Array.isArray(elemComp) ? elemComp : null,
          );
          result[i] = subResult;
          if (newCompensation) newCompensation[i] = subComp;
        } else {
          // Base case for scalar values
          const { result: subResult, compensation: subComp } = addElements(
            elemA,
            elemB,
            elemComp,
          );
          result[i] = subResult;
          if (newCompensation) newCompensation[i] = subComp;
        }
      }

      return { result, compensation: newCompensation };
    };

    // Perform the addition
    const { result } = addArrays(scaledA, scaledB);

    // Scale the result back if needed
    if (scaleFactorA !== 1 || scaleFactorB !== 1) {
      // Choose the appropriate scaling based on which was more extreme
      const resultScale =
        scaleFactorA !== 1 && scaleFactorB !== 1
          ? 1 / Math.max(scaleFactorA, scaleFactorB)
          : scaleFactorA !== 1
            ? 1 / scaleFactorA
            : 1 / scaleFactorB;

      return this.scale(result, resultScale);
    }

    return result;
  },

  /**
   * Subtract one tensor from another with numerical stability
   *
   * @param {Array} a - First tensor
   * @param {Array} b - Second tensor
   * @param {Object} [options={}] - Subtraction options
   * @returns {Array} Result of subtraction
   */
  subtract: function (a, b, options = {}) {
    // Subtraction is implemented as addition with negated second operand
    const negatedB = this.map(b, (x) => -x);
    return this.add(a, negatedB, options);
  },

  /**
   * Element-wise multiply two tensors with numerical stability
   *
   * @param {Array} a - First tensor
   * @param {Array} b - Second tensor
   * @param {Object} [options={}] - Multiplication options
   * @returns {Array} Result of element-wise multiplication
   */
  multiply: function (a, b, options = {}) {
    const useScaling = options.useScaling !== false;

    // Check if tensors have extreme values
    const hasExtremeA = useScaling && this.hasExtremeValues(a);
    const hasExtremeB = useScaling && this.hasExtremeValues(b);

    // Apply scaling if needed
    let scaledA = a;
    let scaledB = b;
    let scaleFactorA = 1;
    let scaleFactorB = 1;

    if (hasExtremeA || hasExtremeB) {
      const scaleInfoA = this.findScalingFactor(a);
      const scaleInfoB = this.findScalingFactor(b);

      if (scaleInfoA.needsScaling) {
        scaledA = this.scale(a, scaleInfoA.scaleFactor);
        scaleFactorA = scaleInfoA.scaleFactor;
      }

      if (scaleInfoB.needsScaling) {
        scaledB = this.scale(b, scaleInfoB.scaleFactor);
        scaleFactorB = scaleInfoB.scaleFactor;
      }
    }

    // Helper function for multiplying elements
    const multiplyElements = (x, y) => {
      try {
        // Use StandardMath for multiplication with improved numerical stability
        return StandardMath.multiply(x, y);
      } catch (error) {
        // Fallback to direct implementation if StandardMath is not available
        return x * y;
      }
    };

    // Helper function for multiplying arrays recursively
    const multiplyArrays = (arrA, arrB) => {
      if (!Array.isArray(arrA) || !Array.isArray(arrB)) {
        // One or both inputs are scalars
        const scalarA = Array.isArray(arrA) ? 0 : arrA;
        const scalarB = Array.isArray(arrB) ? 0 : arrB;
        return multiplyElements(scalarA, scalarB);
      }

      // Both inputs are arrays
      const result = new Array(Math.max(arrA.length, arrB.length));

      for (let i = 0; i < result.length; i++) {
        const elemA = i < arrA.length ? arrA[i] : 0;
        const elemB = i < arrB.length ? arrB[i] : 0;

        if (Array.isArray(elemA) || Array.isArray(elemB)) {
          // Recursive case for nested arrays
          result[i] = multiplyArrays(
            Array.isArray(elemA) ? elemA : [elemA],
            Array.isArray(elemB) ? elemB : [elemB],
          );
        } else {
          // Base case for scalar values
          result[i] = multiplyElements(elemA, elemB);
        }
      }

      return result;
    };

    // Perform the multiplication
    const result = multiplyArrays(scaledA, scaledB);

    // Scale the result back if needed
    if (scaleFactorA !== 1 || scaleFactorB !== 1) {
      // For multiplication, we need to account for both scale factors
      const resultScale = 1 / (scaleFactorA * scaleFactorB);
      return this.scale(result, resultScale);
    }

    return result;
  },

  /**
   * Tensor-matrix multiplication with numerical stability
   *
   * @param {Array} tensor - Input tensor
   * @param {Array} matrix - Input matrix for the last two dimensions
   * @param {Object} [options={}] - Multiplication options
   * @returns {Array} Result of tensor-matrix multiplication
   */
  matmul: function (tensor, matrix, options = {}) {
    const useScaling = options.useScaling !== false;
    const useKahan = options.useKahan !== false;
    const separateSummation = options.separateSummation !== false;

    // Get shapes
    const tensorShape = this.shape(tensor);
    const matrixShape = this.shape(matrix);

    if (tensorShape.length < 2 || matrixShape.length < 2) {
      throw new Error(
        "Input tensors must have at least 2 dimensions for matmul",
      );
    }

    // Check compatibility
    const lastTensorDim = tensorShape[tensorShape.length - 1];
    const firstMatrixDim = matrixShape[matrixShape.length - 2];

    if (lastTensorDim !== firstMatrixDim) {
      throw new Error("Incompatible dimensions for matrix multiplication");
    }

    // Calculate result shape
    const resultShape = [
      ...tensorShape.slice(0, -1),
      matrixShape[matrixShape.length - 1],
    ];

    // Check if scaling is needed
    let needsScaling = false;
    let scaleFactor = 1;
    let maxAbsValue = 0;

    if (useScaling) {
      const tensorFlat = this.flatten(tensor);
      const matrixFlat = this.flatten(matrix);

      for (let i = 0; i < tensorFlat.length; i++) {
        maxAbsValue = Math.max(maxAbsValue, Math.abs(tensorFlat[i]));
      }

      for (let i = 0; i < matrixFlat.length; i++) {
        maxAbsValue = Math.max(maxAbsValue, Math.abs(matrixFlat[i]));
      }

      // Determine scaling
      if (maxAbsValue > 1e50) {
        needsScaling = true;
        scaleFactor = 1e-50;
      } else if (maxAbsValue < 1e-50 && maxAbsValue > 0) {
        needsScaling = true;
        scaleFactor = 1e50;
      }
    }

    // Apply scaling if needed
    let scaledTensor = tensor;
    let scaledMatrix = matrix;

    if (needsScaling) {
      scaledTensor = this.scale(tensor, scaleFactor);
      scaledMatrix = this.scale(matrix, scaleFactor);
    }

    // Helper function for calculating a single matrix multiplication
    const multiplyMatrices = (mat1, mat2) => {
      try {
        // Try using StandardMath.Matrix.multiply for optimal numerical stability
        if (
          StandardMath &&
          StandardMath.Matrix &&
          typeof StandardMath.Matrix.multiply === "function"
        ) {
          // Use StandardMath matrix multiplication which already handles numerical stability
          return StandardMath.Matrix.multiply(mat1, mat2);
        }
      } catch (error) {
        // If StandardMath is not available or fails, fall back to original implementation
        Prime.Logger &&
          Prime.Logger.warn(
            "StandardMath.Matrix.multiply failed: " +
              error.message +
              ". Using fallback implementation.",
          );
      }

      // Fallback implementation
      const rows1 = mat1.length;
      const cols1 = mat1[0].length;
      const cols2 = mat2[0].length;

      const result = new Array(rows1);

      for (let i = 0; i < rows1; i++) {
        result[i] = new Array(cols2);

        for (let j = 0; j < cols2; j++) {
          if (separateSummation) {
            // Use separate positive and negative summation to reduce cancellation
            let posSum = 0;
            let negSum = 0;
            let posComp = 0;
            let negComp = 0;

            for (let k = 0; k < cols1; k++) {
              const term = mat1[i][k] * mat2[k][j];

              if (term >= 0) {
                if (useKahan) {
                  const y = term - posComp;
                  const t = posSum + y;
                  posComp = t - posSum - y;
                  posSum = t;
                } else {
                  posSum += term;
                }
              } else {
                if (useKahan) {
                  const y = term - negComp;
                  const t = negSum + y;
                  negComp = t - negSum - y;
                  negSum = t;
                } else {
                  negSum += term;
                }
              }
            }

            result[i][j] = posSum + negSum;
          } else {
            // Use standard Kahan summation
            let sum = 0;
            let compensation = 0;

            for (let k = 0; k < cols1; k++) {
              const term = mat1[i][k] * mat2[k][j];

              if (useKahan) {
                const y = term - compensation;
                const t = sum + y;
                compensation = t - sum - y;
                sum = t;
              } else {
                sum += term;
              }
            }

            result[i][j] = sum;
          }
        }
      }

      return result;
    };

    // Helper function to recursively apply matrix multiplication
    const applyMatMul = (t, m) => {
      // Check if t is a 2D matrix (has rows that are arrays but not 3D)
      const is2D =
        Array.isArray(t) &&
        t.length > 0 &&
        Array.isArray(t[0]) &&
        (t[0].length === 0 || !Array.isArray(t[0][0]));

      if (is2D) {
        // Base case: 2D tensor (matrix)
        return multiplyMatrices(t, m);
      }

      // Recursive case: higher-dimensional tensor
      const result = new Array(t.length);

      for (let i = 0; i < t.length; i++) {
        result[i] = applyMatMul(t[i], m);
      }

      return result;
    };

    // Perform the multiplication
    const result = applyMatMul(scaledTensor, scaledMatrix);

    // Scale the result back if needed
    if (needsScaling) {
      // For matrix multiplication, we need to scale by the square of the scale factor
      return this.scale(result, 1 / scaleFactor);
    }

    return result;
  },

  /**
   * Tensor dot product with numerical stability
   *
   * @param {Array} a - First tensor
   * @param {Array} b - Second tensor
   * @param {Array<number>} [dims] - Dimensions to contract
   * @param {Object} [options={}] - Dot product options
   * @returns {Array} Result of dot product
   */
  dot: function (a, b, dims, options = {}) {
    const aShape = this.shape(a);
    const bShape = this.shape(b);

    // Default to dot product along last dimension of a and first dimension of b
    if (!dims) {
      dims = [aShape.length - 1, 0];
    }

    // Validate dimensions
    if (aShape[dims[0]] !== bShape[dims[1]]) {
      throw new Error("Incompatible dimensions for dot product");
    }

    // For 1D vectors, use simple dot product
    if (aShape.length === 1 && bShape.length === 1) {
      return this._dotVectors(a, b, options);
    }

    // For now, we'll only implement the most common case:
    // matrix-vector, matrix-matrix, tensor-matrix
    // A general tensor dot product would be more complex

    // Matrix-vector product
    if (aShape.length === 2 && bShape.length === 1) {
      return this._matrixVectorDot(a, b, options);
    }

    // Matrix-matrix product
    if (aShape.length === 2 && bShape.length === 2) {
      return this.matmul(a, b, options);
    }

    // Tensor-matrix product along specified dimensions
    // This is a simplified implementation for demonstration
    // A full implementation would handle arbitrary tensor contractions

    throw new Error("General tensor dot products not yet implemented");
  },

  /**
   * Vector dot product with numerical stability
   *
   * @private
   * @param {Array} a - First vector
   * @param {Array} b - Second vector
   * @param {Object} [options={}] - Dot product options
   * @returns {number} Dot product result
   */
  _dotVectors: function (a, b, options = {}) {
    const useKahan = options.useKahan !== false;
    const useScaling = options.useScaling !== false;
    const separateSummation = options.separateSummation !== false;

    // Validate inputs
    if (!Array.isArray(a) || !Array.isArray(b)) {
      throw new Error("Inputs must be arrays");
    }

    if (a.length !== b.length) {
      throw new Error("Vectors must have the same length");
    }

    try {
      // Try using StandardMath.Vector.dot for optimal numerical stability
      if (
        StandardMath &&
        StandardMath.Vector &&
        typeof StandardMath.Vector.dot === "function"
      ) {
        // StandardMath.Vector.dot already handles extreme values and uses Kahan summation
        return StandardMath.Vector.dot(a, b);
      }
    } catch (error) {
      // If StandardMath is not available or fails, fall back to original implementation
      Prime.Logger &&
        Prime.Logger.warn(
          "StandardMath.Vector.dot failed: " +
            error.message +
            ". Using fallback implementation.",
        );
    }

    // Fallback implementation with original scaling approach
    // Check if scaling is needed
    let needsScaling = false;
    let scaleFactor = 1;
    let maxAbsValue = 0;

    if (useScaling) {
      for (let i = 0; i < a.length; i++) {
        maxAbsValue = Math.max(maxAbsValue, Math.abs(a[i]), Math.abs(b[i]));
      }

      if (maxAbsValue > 1e100) {
        needsScaling = true;
        scaleFactor = 1e-100;
      } else if (maxAbsValue < 1e-100 && maxAbsValue > 0) {
        needsScaling = true;
        scaleFactor = 1e100;
      }
    }

    // Apply scaling if needed
    const scaleA =
      needsScaling && maxAbsValue > 1e100
        ? 1e-100
        : needsScaling && maxAbsValue < 1e-100
          ? 1e100
          : 1;
    const vecA = scaleA !== 1 ? a.map((x) => x * scaleA) : a;
    const vecB = scaleA !== 1 ? b.map((x) => x * scaleA) : b;

    if (separateSummation) {
      // Use separate summation for positive and negative products
      let posSum = 0;
      let negSum = 0;
      let posComp = 0;
      let negComp = 0;

      for (let i = 0; i < vecA.length; i++) {
        const product = vecA[i] * vecB[i];

        if (product >= 0) {
          if (useKahan) {
            const y = product - posComp;
            const t = posSum + y;
            posComp = t - posSum - y;
            posSum = t;
          } else {
            posSum += product;
          }
        } else {
          if (useKahan) {
            const y = product - negComp;
            const t = negSum + y;
            negComp = t - negSum - y;
            negSum = t;
          } else {
            negSum += product;
          }
        }
      }

      // Scale the result back if needed
      const result = posSum + negSum;
      return needsScaling ? result / scaleFactor : result;
    } else {
      // Use standard Kahan summation
      let dot = 0;
      let compensation = 0;

      for (let i = 0; i < vecA.length; i++) {
        const product = vecA[i] * vecB[i];

        if (useKahan) {
          const y = product - compensation;
          const t = dot + y;
          compensation = t - dot - y;
          dot = t;
        } else {
          dot += product;
        }
      }

      // Scale the result back if needed
      return needsScaling ? dot / scaleFactor : dot;
    }
  },

  /**
   * Matrix-vector dot product with numerical stability
   *
   * @private
   * @param {Array} matrix - Input matrix
   * @param {Array} vector - Input vector
   * @param {Object} [options={}] - Dot product options
   * @returns {Array} Resulting vector
   */
  _matrixVectorDot: function (matrix, vector, options = {}) {
    const useKahan = options.useKahan !== false;
    const useScaling = options.useScaling !== false;
    const separateSummation = options.separateSummation !== false;

    // Validate inputs
    if (
      !Array.isArray(matrix) ||
      !Array.isArray(matrix[0]) ||
      !Array.isArray(vector)
    ) {
      throw new Error("Invalid inputs for matrix-vector multiplication");
    }

    if (matrix[0].length !== vector.length) {
      throw new Error("Matrix columns must match vector length");
    }

    // Check if scaling is needed
    let needsScaling = false;
    let scaleFactor = 1;

    if (useScaling) {
      let maxAbsValue = 0;

      // Find maximum absolute value in matrix
      for (let i = 0; i < matrix.length; i++) {
        for (let j = 0; j < matrix[i].length; j++) {
          maxAbsValue = Math.max(maxAbsValue, Math.abs(matrix[i][j]));
        }
      }

      // Find maximum absolute value in vector
      for (let i = 0; i < vector.length; i++) {
        maxAbsValue = Math.max(maxAbsValue, Math.abs(vector[i]));
      }

      if (maxAbsValue > 1e100) {
        needsScaling = true;
        scaleFactor = 1e-100;
      } else if (maxAbsValue < 1e-100 && maxAbsValue > 0) {
        needsScaling = true;
        scaleFactor = 1e100;
      }
    }

    // Apply scaling if needed
    const scaledMatrix = needsScaling
      ? matrix.map((row) => row.map((x) => x * scaleFactor))
      : matrix;
    const scaledVector = needsScaling
      ? vector.map((x) => x * scaleFactor)
      : vector;

    // Compute result
    const result = new Array(matrix.length);

    for (let i = 0; i < matrix.length; i++) {
      if (separateSummation) {
        // Use separate summation for positive and negative products
        let posSum = 0;
        let negSum = 0;
        let posComp = 0;
        let negComp = 0;

        for (let j = 0; j < scaledVector.length; j++) {
          const product = scaledMatrix[i][j] * scaledVector[j];

          if (product >= 0) {
            if (useKahan) {
              const y = product - posComp;
              const t = posSum + y;
              posComp = t - posSum - y;
              posSum = t;
            } else {
              posSum += product;
            }
          } else {
            if (useKahan) {
              const y = product - negComp;
              const t = negSum + y;
              negComp = t - negSum - y;
              negSum = t;
            } else {
              negSum += product;
            }
          }
        }

        result[i] = posSum + negSum;
      } else {
        // Use standard Kahan summation
        let sum = 0;
        let compensation = 0;

        for (let j = 0; j < scaledVector.length; j++) {
          const product = scaledMatrix[i][j] * scaledVector[j];

          if (useKahan) {
            const y = product - compensation;
            const t = sum + y;
            compensation = t - sum - y;
            sum = t;
          } else {
            sum += product;
          }
        }

        result[i] = sum;
      }
    }

    // Scale the result back if needed
    return needsScaling ? result.map((x) => x / scaleFactor) : result;
  },

  /**
   * Calculate the norm of a tensor with numerical stability
   *
   * @param {Array} tensor - Input tensor
   * @param {string|number} [p='fro'] - Norm type: 'fro' (Frobenius), 1, 2, Infinity
   * @param {Object} [options={}] - Norm calculation options
   * @returns {number} Norm value
   */
  norm: function (tensor, p = "fro", options = {}) {
    const useKahan = options.useKahan !== false;
    const useScaling = options.useScaling !== false;

    try {
      // Try using StandardMath.Vector.norm for optimal numerical stability
      if (
        StandardMath &&
        StandardMath.Vector &&
        typeof StandardMath.Vector.norm === "function"
      ) {
        // Flatten tensor
        const flat = this.flatten(tensor);

        // Use StandardMath norm which already handles extreme values and uses Kahan summation
        if (p === "fro" || p === 2) {
          return StandardMath.Vector.norm(flat);
        } else if (p === 1) {
          return StandardMath.Vector.norm(flat, 1);
        } else if (p === Infinity || p === "inf") {
          return StandardMath.Vector.norm(flat, "inf");
        } else {
          return StandardMath.Vector.norm(flat, p);
        }
      }
    } catch (error) {
      // If StandardMath is not available or fails, fall back to original implementation
      Prime.Logger &&
        Prime.Logger.warn(
          "StandardMath.Vector.norm failed: " +
            error.message +
            ". Using fallback implementation.",
        );
    }

    // Fallback implementation
    // Flatten tensor
    const flat = this.flatten(tensor);

    // Check if scaling is needed
    let needsScaling = false;
    let scaleFactor = 1;

    if (useScaling) {
      let maxAbsValue = 0;
      for (let i = 0; i < flat.length; i++) {
        maxAbsValue = Math.max(maxAbsValue, Math.abs(flat[i]));
      }

      if (maxAbsValue > 1e100) {
        needsScaling = true;
        scaleFactor = 1e-100;
      } else if (maxAbsValue < 1e-100 && maxAbsValue > 0) {
        needsScaling = true;
        scaleFactor = 1e100;
      }
    }

    // Apply scaling if needed
    const scaledFlat = needsScaling ? flat.map((x) => x * scaleFactor) : flat;

    let normValue;

    // Calculate norm based on type
    if (p === "fro" || p === 2) {
      // Frobenius or L2 norm
      let sumSquares = 0;
      let compensation = 0;

      for (let i = 0; i < scaledFlat.length; i++) {
        const squared = scaledFlat[i] * scaledFlat[i];

        if (useKahan) {
          const y = squared - compensation;
          const t = sumSquares + y;
          compensation = t - sumSquares - y;
          sumSquares = t;
        } else {
          sumSquares += squared;
        }
      }

      normValue = Math.sqrt(sumSquares);
    } else if (p === 1) {
      // L1 norm
      let sum = 0;
      let compensation = 0;

      for (let i = 0; i < scaledFlat.length; i++) {
        const absValue = Math.abs(scaledFlat[i]);

        if (useKahan) {
          const y = absValue - compensation;
          const t = sum + y;
          compensation = t - sum - y;
          sum = t;
        } else {
          sum += absValue;
        }
      }

      normValue = sum;
    } else if (p === Infinity || p === "inf") {
      // L-infinity norm
      let maxVal = 0;

      for (let i = 0; i < scaledFlat.length; i++) {
        maxVal = Math.max(maxVal, Math.abs(scaledFlat[i]));
      }

      normValue = maxVal;
    } else {
      // General Lp norm
      let sum = 0;
      let compensation = 0;

      for (let i = 0; i < scaledFlat.length; i++) {
        const term = Math.pow(Math.abs(scaledFlat[i]), p);

        if (useKahan) {
          const y = term - compensation;
          const t = sum + y;
          compensation = t - sum - y;
          sum = t;
        } else {
          sum += term;
        }
      }

      normValue = Math.pow(sum, 1 / p);
    }

    // Scale the result back if needed
    if (needsScaling) {
      if (p === "fro" || p === 2) {
        // For L2/Frobenius norm, scale by the scale factor
        return normValue / scaleFactor;
      } else if (p === 1) {
        // For L1 norm, scale by the scale factor
        return normValue / scaleFactor;
      } else if (p === Infinity || p === "inf") {
        // For L-infinity norm, scale by the scale factor
        return normValue / scaleFactor;
      } else {
        // For Lp norm, scale by the scale factor
        return normValue / scaleFactor;
      }
    }

    return normValue;
  },

  /**
   * Tensor inner product with numerical stability
   *
   * @param {Array} a - First tensor
   * @param {Array} b - Second tensor
   * @param {Object} [options={}] - Inner product options
   * @returns {number} Inner product value
   */
  innerProduct: function (a, b, options = {}) {
    // Inner product is equivalent to dot product for flattened tensors
    const flatA = this.flatten(a);
    const flatB = this.flatten(b);

    if (flatA.length !== flatB.length) {
      throw new Error(
        "Tensors must have the same number of elements for inner product",
      );
    }

    return this._dotVectors(flatA, flatB, options);
  },

  /**
   * Normalize a tensor with numerical stability
   *
   * @param {Array} tensor - Input tensor
   * @param {string|number} [p='fro'] - Norm type for normalization
   * @param {Object} [options={}] - Normalization options
   * @returns {Array} Normalized tensor
   */
  normalize: function (tensor, p = "fro", options = {}) {
    try {
      // For simple vector (1D array), use StandardMath.Vector.normalize
      if (
        Array.isArray(tensor) &&
        !Array.isArray(tensor[0]) &&
        StandardMath &&
        StandardMath.Vector &&
        typeof StandardMath.Vector.normalize === "function"
      ) {
        return StandardMath.Vector.normalize(tensor, p);
      }
    } catch (error) {
      // If StandardMath is not available or fails, fall back to original implementation
      Prime.Logger &&
        Prime.Logger.warn(
          "StandardMath.Vector.normalize failed: " +
            error.message +
            ". Using fallback implementation.",
        );
    }

    // For tensors (nested arrays) or if StandardMath is unavailable, use the calculation approach
    // Calculate the norm
    const normValue = this.norm(tensor, p, options);

    // Avoid division by zero
    if (normValue === 0 || !isFinite(normValue)) {
      return this.map(tensor, () => 0);
    }

    // Normalize by dividing by the norm
    return this.map(tensor, (x) => x / normValue);
  },

  /**
   * Tensor outer product with numerical stability
   *
   * @param {Array} a - First tensor
   * @param {Array} b - Second tensor
   * @param {Object} [options={}] - Outer product options
   * @returns {Array} Outer product result
   */
  outerProduct: function (a, b, options = {}) {
    const flatA = this.flatten(a);
    const flatB = this.flatten(b);
    const useScaling = options.useScaling !== false;

    // Check if scaling is needed
    let needsScaling = false;
    let scaleFactor = 1;

    if (useScaling) {
      let maxAbsA = 0;
      let maxAbsB = 0;

      for (let i = 0; i < flatA.length; i++) {
        maxAbsA = Math.max(maxAbsA, Math.abs(flatA[i]));
      }

      for (let i = 0; i < flatB.length; i++) {
        maxAbsB = Math.max(maxAbsB, Math.abs(flatB[i]));
      }

      if (maxAbsA * maxAbsB > 1e100) {
        needsScaling = true;
        scaleFactor = 1e-50; // Split scaling between both tensors
      } else if (maxAbsA * maxAbsB < 1e-100 && maxAbsA * maxAbsB > 0) {
        needsScaling = true;
        scaleFactor = 1e50; // Split scaling between both tensors
      }
    }

    // Apply scaling if needed
    const scaledA = needsScaling ? flatA.map((x) => x * scaleFactor) : flatA;
    const scaledB = needsScaling ? flatB.map((x) => x * scaleFactor) : flatB;

    // Compute outer product
    const result = new Array(flatA.length);

    for (let i = 0; i < flatA.length; i++) {
      result[i] = new Array(flatB.length);

      for (let j = 0; j < flatB.length; j++) {
        result[i][j] = scaledA[i] * scaledB[j];
      }
    }

    // Scale the result back if needed
    if (needsScaling) {
      // For outer product, we need to account for both scale factors
      // But we only applied to one tensor, not both, so we use 1/scaleFactor
      return this.scale(result, 1 / scaleFactor);
    }

    return result;
  },

  /**
   * Apply softmax function to tensor with numerical stability
   *
   * @param {Array} tensor - Input tensor
   * @param {number} [axis=-1] - Axis along which to apply softmax
   * @param {Object} [options={}] - Softmax options
   * @returns {Array} Softmax result
   */
  softmax: function (tensor, axis = -1, options = {}) {
    const useScaling = options.useScaling !== false;

    // Handle negative axis
    const tensorShape = this.shape(tensor);
    if (axis < 0) {
      axis = tensorShape.length + axis;
    }

    // For 1D tensors
    if (tensorShape.length === 1) {
      // Find max value for numerical stability
      let maxVal = -Infinity;
      for (let i = 0; i < tensor.length; i++) {
        maxVal = Math.max(maxVal, tensor[i]);
      }

      // Compute exponentials with shifting
      const expValues = new Array(tensor.length);
      let sumExp = 0;

      for (let i = 0; i < tensor.length; i++) {
        const expVal = Math.exp(tensor[i] - maxVal);
        expValues[i] = expVal;
        sumExp += expVal;
      }

      // Normalize by sum
      return expValues.map((exp) => exp / sumExp);
    }

    // For higher dimensional tensors, we need a more general approach
    // We'll implement a simplified version for 2D tensors as an example

    if (tensorShape.length === 2) {
      if (axis === 0) {
        // Softmax along columns
        const result = new Array(tensorShape[0]);
        for (let i = 0; i < tensorShape[0]; i++) {
          result[i] = new Array(tensorShape[1]).fill(0);
        }

        for (let j = 0; j < tensorShape[1]; j++) {
          // Find max value in this column
          let maxVal = -Infinity;
          for (let i = 0; i < tensorShape[0]; i++) {
            maxVal = Math.max(maxVal, tensor[i][j]);
          }

          // Compute exponentials and sum
          let sumExp = 0;
          const expValues = new Array(tensorShape[0]);

          for (let i = 0; i < tensorShape[0]; i++) {
            const expVal = Math.exp(tensor[i][j] - maxVal);
            expValues[i] = expVal;
            sumExp += expVal;
          }

          // Normalize
          for (let i = 0; i < tensorShape[0]; i++) {
            result[i][j] = expValues[i] / sumExp;
          }
        }

        return result;
      } else {
        // Softmax along rows
        const result = new Array(tensorShape[0]);

        for (let i = 0; i < tensorShape[0]; i++) {
          // Find max value in this row
          let maxVal = -Infinity;
          for (let j = 0; j < tensorShape[1]; j++) {
            maxVal = Math.max(maxVal, tensor[i][j]);
          }

          // Compute exponentials and sum
          let sumExp = 0;
          const expValues = new Array(tensorShape[1]);

          for (let j = 0; j < tensorShape[1]; j++) {
            const expVal = Math.exp(tensor[i][j] - maxVal);
            expValues[j] = expVal;
            sumExp += expVal;
          }

          // Normalize
          result[i] = expValues.map((exp) => exp / sumExp);
        }

        return result;
      }
    }

    // For higher dimensions, we would need a more general implementation
    // that transforms the tensor, applies softmax, and transforms back
    throw new Error(
      "Softmax for tensors with more than 2 dimensions not implemented",
    );
  },

  /**
   * Apply ReLU function to tensor
   *
   * @param {Array} tensor - Input tensor
   * @returns {Array} ReLU result
   */
  relu: function (tensor) {
    return this.map(tensor, (x) => Math.max(0, x));
  },

  /**
   * Apply sigmoid function to tensor with numerical stability
   *
   * @param {Array} tensor - Input tensor
   * @returns {Array} Sigmoid result
   */
  sigmoid: function (tensor) {
    return this.map(tensor, (x) => {
      // Handle extreme values
      if (x > 100) return 1;
      if (x < -100) return 0;
      return 1 / (1 + Math.exp(-x));
    });
  },

  /**
   * Apply tanh function to tensor
   *
   * @param {Array} tensor - Input tensor
   * @returns {Array} Tanh result
   */
  tanh: function (tensor) {
    return this.map(tensor, (x) => {
      // Handle extreme values
      if (x > 20) return 1;
      if (x < -20) return -1;
      return Math.tanh(x);
    });
  },
};

// Export the module
module.exports = TensorOperations;
