/**
 * PrimeOS JavaScript Library - Framework
 * Standardized Tensor Operations
 * Provides a unified interface for tensor operations with numerical stability
 */

// Import direct dependencies to avoid circular dependencies
const Prime = require("../../core/prime.js");
const MathUtils = require("./index.js");
const TensorOperations = require("./tensor-operations.js");
const TypeValidation = require("./type-validation.js");

/**
 * StandardizedTensor - Unified interface for tensor operations
 *
 * This module provides a standardized interface for tensor operations,
 * integrating the numerical stability features from tensor-operations.js
 * with the consistent interface style of the Prime.Math namespace.
 */
class StandardizedTensor {
  /**
   * Create a new tensor with the given shape and initial value
   *
   * @param {Array<number>} shape - Shape of the tensor to create
   * @param {number|Function} initialValue - Initial value or function to generate values
   */
  constructor(shape, initialValue = 0) {
    // Validate shape
    TypeValidation.assertArray(shape, "shape", {
      operation: "StandardizedTensor.constructor",
    });

    // Check that shape contains only non-negative integers
    for (let i = 0; i < shape.length; i++) {
      TypeValidation.assertInteger(shape[i], `shape[${i}]`, {
        operation: "StandardizedTensor.constructor",
      });

      TypeValidation.assertNonNegativeInteger(shape[i], `shape[${i}]`, {
        operation: "StandardizedTensor.constructor",
      });
    }

    // Validate initialValue
    if (
      typeof initialValue !== "number" &&
      typeof initialValue !== "function"
    ) {
      throw new Prime.ValidationError(
        "Initial value must be a number or a function",
        {
          operation: "StandardizedTensor.constructor",
          expectedTypes: ["number", "function"],
          actualType: typeof initialValue,
        },
      );
    }

    // Check for extreme values that might cause numerical instability
    if (typeof initialValue === "number") {
      try {
        TypeValidation.validateMagnitude(
          initialValue,
          "initialValue",
          {
            allowZero: true,
          },
          { operation: "StandardizedTensor.constructor" },
        );
      } catch (error) {
        // If validation fails due to extreme values, log a warning but continue
        console.warn(
          `Warning in StandardizedTensor.constructor: ${error.message}`,
        );
      }
    }

    this.shape = shape.slice();
    this.values = TensorOperations.create(shape, initialValue);
  }

  /**
   * Create a new tensor from an existing array or nested arrays
   *
   * @param {Array} values - Array or nested arrays of values
   * @returns {StandardizedTensor} New tensor
   */
  static fromArray(values) {
    // Validate input
    TypeValidation.assertArray(values, "values", {
      operation: "StandardizedTensor.fromArray",
    });

    // Determine shape from values
    const shape = TensorOperations.shape(values);

    // Create a new tensor with the determined shape
    const tensor = new StandardizedTensor(shape, 0);

    // Validate values for extreme magnitudes that might cause numerical instability
    try {
      // Recursively check all numerical values in the nested arrays
      const validateNestedArray = (arr, path = "") => {
        for (let i = 0; i < arr.length; i++) {
          const value = arr[i];
          const currentPath = path ? `${path}[${i}]` : `values[${i}]`;

          if (Array.isArray(value)) {
            validateNestedArray(value, currentPath);
          } else if (typeof value === "number") {
            TypeValidation.validateMagnitude(
              value,
              currentPath,
              {
                allowZero: true,
              },
              { operation: "StandardizedTensor.fromArray" },
            );
          } else {
            throw new Prime.ValidationError(
              `All tensor values must be numbers, found ${typeof value}`,
              {
                operation: "StandardizedTensor.fromArray",
                path: currentPath,
                value: value,
              },
            );
          }
        }
      };

      validateNestedArray(values);
    } catch (error) {
      // If validation fails due to extreme values, log a warning but continue
      console.warn(`Warning in StandardizedTensor.fromArray: ${error.message}`);
    }

    // Deep copy values
    tensor.values = JSON.parse(JSON.stringify(values));

    return tensor;
  }

  /**
   * Create a new tensor filled with zeros
   *
   * @param {Array<number>} shape - Shape of the tensor
   * @returns {StandardizedTensor} Zero tensor
   */
  static zeros(shape) {
    return new StandardizedTensor(shape, 0);
  }

  /**
   * Create a new tensor filled with ones
   *
   * @param {Array<number>} shape - Shape of the tensor
   * @returns {StandardizedTensor} Tensor of ones
   */
  static ones(shape) {
    return new StandardizedTensor(shape, 1);
  }

  /**
   * Create a tensor with random values
   *
   * @param {Array<number>} shape - Shape of the tensor
   * @param {Function} [distribution=Math.random] - Distribution function to generate values
   * @returns {StandardizedTensor} Random tensor
   */
  static random(shape, distribution = Math.random) {
    return new StandardizedTensor(shape, distribution);
  }

  /**
   * Get the shape of the tensor
   *
   * @returns {Array<number>} Shape of the tensor
   */
  getShape() {
    return this.shape.slice();
  }

  /**
   * Get the rank (number of dimensions) of the tensor
   *
   * @returns {number} Rank
   */
  getRank() {
    return this.shape.length;
  }

  /**
   * Get the total number of elements in the tensor
   *
   * @returns {number} Number of elements
   */
  getSize() {
    return this.shape.reduce((a, b) => a * b, 1);
  }

  /**
   * Get an element at the specified indices
   *
   * @param {Array<number>} indices - Indices for each dimension
   * @returns {number} Element value
   */
  get(indices) {
    if (!Array.isArray(indices)) {
      throw new Prime.ValidationError("Indices must be an array", {
        context: {
          module: "StandardizedTensor",
          method: "get",
          actualType: typeof indices,
        },
      });
    }

    if (indices.length !== this.shape.length) {
      throw new Prime.ValidationError("Indices must match tensor rank", {
        context: {
          module: "StandardizedTensor",
          method: "get",
          expectedRank: this.shape.length,
          actualRank: indices.length,
        },
      });
    }

    // Access element recursively
    let current = this.values;
    for (const idx of indices) {
      if (idx < 0 || idx >= current.length) {
        throw new Prime.ValidationError("Index out of bounds", {
          context: {
            module: "StandardizedTensor",
            method: "get",
            index: idx,
            dimension: current.length,
          },
        });
      }
      current = current[idx];
    }

    return current;
  }

  /**
   * Set an element at the specified indices
   *
   * @param {Array<number>} indices - Indices for each dimension
   * @param {number} value - Value to set
   * @returns {StandardizedTensor} This tensor for method chaining
   */
  set(indices, value) {
    if (!Array.isArray(indices)) {
      throw new Prime.ValidationError("Indices must be an array", {
        context: {
          module: "StandardizedTensor",
          method: "set",
          actualType: typeof indices,
        },
      });
    }

    if (indices.length !== this.shape.length) {
      throw new Prime.ValidationError("Indices must match tensor rank", {
        context: {
          module: "StandardizedTensor",
          method: "set",
          expectedRank: this.shape.length,
          actualRank: indices.length,
        },
      });
    }

    if (typeof value !== "number") {
      throw new Prime.ValidationError("Value must be a number", {
        context: {
          module: "StandardizedTensor",
          method: "set",
          actualType: typeof value,
        },
      });
    }

    // Access element recursively
    let current = this.values;
    for (let i = 0; i < indices.length - 1; i++) {
      const idx = indices[i];
      if (idx < 0 || idx >= current.length) {
        throw new Prime.ValidationError("Index out of bounds", {
          context: {
            module: "StandardizedTensor",
            method: "set",
            index: idx,
            dimension: current.length,
          },
        });
      }
      current = current[idx];
    }

    const lastIdx = indices[indices.length - 1];
    if (lastIdx < 0 || lastIdx >= current.length) {
      throw new Prime.ValidationError("Index out of bounds", {
        context: {
          module: "StandardizedTensor",
          method: "set",
          index: lastIdx,
          dimension: current.length,
        },
      });
    }

    current[lastIdx] = value;
    return this;
  }

  /**
   * Apply a function to each element of the tensor
   *
   * @param {Function} fn - Function to apply to each element
   * @returns {StandardizedTensor} New tensor with function applied
   */
  map(fn) {
    if (typeof fn !== "function") {
      throw new Prime.ValidationError("Argument must be a function", {
        context: {
          module: "StandardizedTensor",
          method: "map",
          actualType: typeof fn,
        },
      });
    }

    const result = new StandardizedTensor(this.shape);
    result.values = TensorOperations.map(this.values, fn);
    return result;
  }

  /**
   * Add another tensor to this one
   *
   * @param {StandardizedTensor|Array} tensor - Tensor to add
   * @param {Object} [options={}] - Addition options
   * @returns {StandardizedTensor} Result of addition
   */
  add(tensor, options = {}) {
    // Validate input
    if (!(tensor instanceof StandardizedTensor) && !Array.isArray(tensor)) {
      throw new Prime.ValidationError(
        "Tensor to add must be a StandardizedTensor or an array",
        {
          operation: "StandardizedTensor.add",
          expectedTypes: ["StandardizedTensor", "Array"],
          actualType: typeof tensor,
        },
      );
    }

    // Validate options if provided
    if (options !== undefined && typeof options !== "object") {
      throw new Prime.ValidationError("Options must be an object", {
        operation: "StandardizedTensor.add",
        expectedType: "object",
        actualType: typeof options,
      });
    }

    const other = tensor instanceof StandardizedTensor ? tensor.values : tensor;

    // Handle shape validation
    if (tensor instanceof StandardizedTensor) {
      if (!this._areShapesEqual(this.shape, tensor.shape)) {
        throw new Prime.DimensionMismatchError(
          "Tensor shapes must match for addition",
          {
            operation: "StandardizedTensor.add",
            firstShape: this.shape,
            secondShape: tensor.shape,
          },
        );
      }
    } else if (Array.isArray(tensor)) {
      const otherShape = TensorOperations.shape(tensor);
      if (!this._areShapesEqual(this.shape, otherShape)) {
        throw new Prime.DimensionMismatchError(
          "Tensor shapes must match for addition",
          {
            operation: "StandardizedTensor.add",
            firstShape: this.shape,
            secondShape: otherShape,
          },
        );
      }
    }

    // Check for extreme values that might cause numerical instability
    try {
      // Validate this tensor's values
      const validateNestedArray = (arr, path = "") => {
        for (let i = 0; i < arr.length; i++) {
          const value = arr[i];
          const currentPath = path ? `${path}[${i}]` : `values[${i}]`;

          if (Array.isArray(value)) {
            validateNestedArray(value, currentPath);
          } else if (typeof value === "number") {
            TypeValidation.validateMagnitude(
              value,
              currentPath,
              {
                allowZero: true,
              },
              { operation: "StandardizedTensor.add" },
            );
          }
        }
      };

      validateNestedArray(this.values);
      validateNestedArray(other);
    } catch (error) {
      // If validation fails due to extreme values, log a warning but continue
      console.warn(`Warning in StandardizedTensor.add: ${error.message}`);
    }

    const result = new StandardizedTensor(this.shape);
    result.values = TensorOperations.add(this.values, other, options);
    return result;
  }

  /**
   * Subtract another tensor from this one
   *
   * @param {StandardizedTensor|Array} tensor - Tensor to subtract
   * @param {Object} [options={}] - Subtraction options
   * @returns {StandardizedTensor} Result of subtraction
   */
  subtract(tensor, options = {}) {
    // Validate input
    if (!(tensor instanceof StandardizedTensor) && !Array.isArray(tensor)) {
      throw new Prime.ValidationError(
        "Tensor to subtract must be a StandardizedTensor or an array",
        {
          operation: "StandardizedTensor.subtract",
          expectedTypes: ["StandardizedTensor", "Array"],
          actualType: typeof tensor,
        },
      );
    }

    // Validate options if provided
    if (options !== undefined && typeof options !== "object") {
      throw new Prime.ValidationError("Options must be an object", {
        operation: "StandardizedTensor.subtract",
        expectedType: "object",
        actualType: typeof options,
      });
    }

    const other = tensor instanceof StandardizedTensor ? tensor.values : tensor;

    // Handle shape validation
    if (tensor instanceof StandardizedTensor) {
      if (!this._areShapesEqual(this.shape, tensor.shape)) {
        throw new Prime.DimensionMismatchError(
          "Tensor shapes must match for subtraction",
          {
            operation: "StandardizedTensor.subtract",
            firstShape: this.shape,
            secondShape: tensor.shape,
          },
        );
      }
    } else if (Array.isArray(tensor)) {
      const otherShape = TensorOperations.shape(tensor);
      if (!this._areShapesEqual(this.shape, otherShape)) {
        throw new Prime.DimensionMismatchError(
          "Tensor shapes must match for subtraction",
          {
            operation: "StandardizedTensor.subtract",
            firstShape: this.shape,
            secondShape: otherShape,
          },
        );
      }
    }

    // Check for extreme values that might cause numerical instability
    try {
      // Validate this tensor's values
      const validateNestedArray = (arr, path = "") => {
        for (let i = 0; i < arr.length; i++) {
          const value = arr[i];
          const currentPath = path ? `${path}[${i}]` : `values[${i}]`;

          if (Array.isArray(value)) {
            validateNestedArray(value, currentPath);
          } else if (typeof value === "number") {
            TypeValidation.validateMagnitude(
              value,
              currentPath,
              {
                allowZero: true,
              },
              { operation: "StandardizedTensor.subtract" },
            );
          }
        }
      };

      validateNestedArray(this.values);
      validateNestedArray(other);
    } catch (error) {
      // If validation fails due to extreme values, log a warning but continue
      console.warn(`Warning in StandardizedTensor.subtract: ${error.message}`);
    }

    // Check for potential catastrophic cancellation when tensors are nearly identical
    const checkNearlySame = (arr1, arr2, path = "") => {
      if (!Array.isArray(arr1) || !Array.isArray(arr2)) {
        // We're at leaf nodes (numbers)
        if (typeof arr1 === "number" && typeof arr2 === "number") {
          const relDiff =
            Math.abs(arr1 - arr2) /
            Math.max(Math.abs(arr1), Math.abs(arr2), 1e-10);
          if (relDiff < 1e-10) {
            return true;
          }
          return false;
        }
        return false;
      }

      if (arr1.length !== arr2.length) return false;

      for (let i = 0; i < arr1.length; i++) {
        if (!checkNearlySame(arr1[i], arr2[i], `${path}[${i}]`)) {
          return false;
        }
      }

      return true;
    };

    const areNearlySame = checkNearlySame(this.values, other);
    if (areNearlySame) {
      console.warn(
        "Warning in StandardizedTensor.subtract: Potential catastrophic cancellation detected when subtracting nearly identical tensors",
      );
    }

    const result = new StandardizedTensor(this.shape);
    result.values = TensorOperations.subtract(this.values, other, options);
    return result;
  }

  /**
   * Multiply this tensor element-wise with another tensor
   *
   * @param {StandardizedTensor|Array} tensor - Tensor to multiply with
   * @param {Object} [options={}] - Multiplication options
   * @returns {StandardizedTensor} Result of multiplication
   */
  multiply(tensor, options = {}) {
    // Validate input
    if (!(tensor instanceof StandardizedTensor) && !Array.isArray(tensor)) {
      throw new Prime.ValidationError(
        "Tensor to multiply with must be a StandardizedTensor or an array",
        {
          operation: "StandardizedTensor.multiply",
          expectedTypes: ["StandardizedTensor", "Array"],
          actualType: typeof tensor,
        },
      );
    }

    // Validate options if provided
    if (options !== undefined && typeof options !== "object") {
      throw new Prime.ValidationError("Options must be an object", {
        operation: "StandardizedTensor.multiply",
        expectedType: "object",
        actualType: typeof options,
      });
    }

    const other = tensor instanceof StandardizedTensor ? tensor.values : tensor;

    // Handle shape validation
    if (tensor instanceof StandardizedTensor) {
      if (!this._areShapesEqual(this.shape, tensor.shape)) {
        throw new Prime.DimensionMismatchError(
          "Tensor shapes must match for element-wise multiplication",
          {
            operation: "StandardizedTensor.multiply",
            firstShape: this.shape,
            secondShape: tensor.shape,
          },
        );
      }
    } else if (Array.isArray(tensor)) {
      const otherShape = TensorOperations.shape(tensor);
      if (!this._areShapesEqual(this.shape, otherShape)) {
        throw new Prime.DimensionMismatchError(
          "Tensor shapes must match for element-wise multiplication",
          {
            operation: "StandardizedTensor.multiply",
            firstShape: this.shape,
            secondShape: otherShape,
          },
        );
      }
    }

    // Check for extreme values that might cause numerical instability
    try {
      // Validate this tensor's values
      const validateNestedArray = (arr, path = "") => {
        for (let i = 0; i < arr.length; i++) {
          const value = arr[i];
          const currentPath = path ? `${path}[${i}]` : `values[${i}]`;

          if (Array.isArray(value)) {
            validateNestedArray(value, currentPath);
          } else if (typeof value === "number") {
            TypeValidation.validateMagnitude(
              value,
              currentPath,
              {
                allowZero: true,
              },
              { operation: "StandardizedTensor.multiply" },
            );
          }
        }
      };

      validateNestedArray(this.values);
      validateNestedArray(other);
    } catch (error) {
      // If validation fails due to extreme values, log a warning but continue
      console.warn(`Warning in StandardizedTensor.multiply: ${error.message}`);
    }

    // Check for very small values that might be lost in multiplication
    let hasSmallValues = false;
    const checkSmallValues = (arr) => {
      if (!Array.isArray(arr)) {
        return typeof arr === "number" && arr !== 0 && Math.abs(arr) < 1e-8;
      }

      for (let i = 0; i < arr.length; i++) {
        if (checkSmallValues(arr[i])) {
          return true;
        }
      }

      return false;
    };

    if (checkSmallValues(this.values) || checkSmallValues(other)) {
      console.warn(
        "Warning in StandardizedTensor.multiply: Very small values detected which may be lost in multiplication",
      );
    }

    const result = new StandardizedTensor(this.shape);
    result.values = TensorOperations.multiply(this.values, other, options);
    return result;
  }

  /**
   * Scale this tensor by a scalar value
   *
   * @param {number} scalar - Scalar value
   * @returns {StandardizedTensor} Scaled tensor
   */
  scale(scalar) {
    // Validate input
    TypeValidation.assertNumber(scalar, "scalar", {
      operation: "StandardizedTensor.scale",
    });
    TypeValidation.assertFinite(scalar, "scalar", {
      operation: "StandardizedTensor.scale",
    });

    // Check for extreme values that might cause numerical instability
    try {
      TypeValidation.validateMagnitude(
        scalar,
        "scalar",
        {
          allowZero: true,
        },
        { operation: "StandardizedTensor.scale" },
      );
    } catch (error) {
      // If validation fails due to extreme values, log a warning but continue
      console.warn(`Warning in StandardizedTensor.scale: ${error.message}`);
    }

    // Check for very small scalar that might effectively zero out the tensor
    if (scalar !== 0 && Math.abs(scalar) < 1e-8) {
      console.warn(
        "Warning in StandardizedTensor.scale: Very small scalar may effectively zero out the tensor",
      );
    }

    // Validate tensor values for extreme magnitudes
    try {
      // Validate this tensor's values
      const validateNestedArray = (arr, path = "") => {
        for (let i = 0; i < arr.length; i++) {
          const value = arr[i];
          const currentPath = path ? `${path}[${i}]` : `values[${i}]`;

          if (Array.isArray(value)) {
            validateNestedArray(value, currentPath);
          } else if (typeof value === "number") {
            TypeValidation.validateMagnitude(
              value,
              currentPath,
              {
                allowZero: true,
              },
              { operation: "StandardizedTensor.scale" },
            );
          }
        }
      };

      validateNestedArray(this.values);
    } catch (error) {
      // If validation fails due to extreme values, log a warning but continue
      console.warn(`Warning in StandardizedTensor.scale: ${error.message}`);
    }

    const result = new StandardizedTensor(this.shape);
    result.values = TensorOperations.scale(this.values, scalar);
    return result;
  }

  /**
   * Perform matrix multiplication with another tensor
   *
   * @param {StandardizedTensor|Array} tensor - Tensor to multiply with
   * @param {Object} [options={}] - Matrix multiplication options
   * @returns {StandardizedTensor} Result of matrix multiplication
   */
  matmul(tensor, options = {}) {
    // Validate input
    if (!(tensor instanceof StandardizedTensor) && !Array.isArray(tensor)) {
      throw new Prime.ValidationError(
        "Tensor to multiply with must be a StandardizedTensor or an array",
        {
          operation: "StandardizedTensor.matmul",
          expectedTypes: ["StandardizedTensor", "Array"],
          actualType: typeof tensor,
        },
      );
    }

    // Validate options if provided
    if (options !== undefined && typeof options !== "object") {
      throw new Prime.ValidationError("Options must be an object", {
        operation: "StandardizedTensor.matmul",
        expectedType: "object",
        actualType: typeof options,
      });
    }

    const other = tensor instanceof StandardizedTensor ? tensor.values : tensor;

    // Validate shapes for matrix multiplication
    if (this.shape.length < 2) {
      throw new Prime.DimensionMismatchError(
        "First tensor must have at least 2 dimensions for matmul",
        {
          operation: "StandardizedTensor.matmul",
          shape: this.shape,
          details:
            "Matrix multiplication requires tensors with at least 2 dimensions",
        },
      );
    }

    const otherShape =
      tensor instanceof StandardizedTensor
        ? tensor.shape
        : TensorOperations.shape(other);

    if (otherShape.length < 2) {
      throw new Prime.DimensionMismatchError(
        "Second tensor must have at least 2 dimensions for matmul",
        {
          operation: "StandardizedTensor.matmul",
          shape: otherShape,
          details:
            "Matrix multiplication requires tensors with at least 2 dimensions",
        },
      );
    }

    // Check compatibility
    if (
      this.shape[this.shape.length - 1] !== otherShape[otherShape.length - 2]
    ) {
      throw new Prime.DimensionMismatchError(
        "Incompatible dimensions for matrix multiplication",
        {
          operation: "StandardizedTensor.matmul",
          firstDim: this.shape[this.shape.length - 1],
          secondDim: otherShape[otherShape.length - 2],
          details:
            "For matrix multiplication, the last dimension of the first tensor must match the second-to-last dimension of the second tensor",
        },
      );
    }

    // Check for extreme values that might cause numerical instability
    try {
      // Recursively validate tensor values
      const validateNestedArray = (arr, path = "") => {
        for (let i = 0; i < arr.length; i++) {
          const value = arr[i];
          const currentPath = path ? `${path}[${i}]` : `values[${i}]`;

          if (Array.isArray(value)) {
            validateNestedArray(value, currentPath);
          } else if (typeof value === "number") {
            TypeValidation.validateMagnitude(
              value,
              currentPath,
              {
                allowZero: true,
              },
              { operation: "StandardizedTensor.matmul" },
            );
          }
        }
      };

      validateNestedArray(this.values);
      validateNestedArray(other);
    } catch (error) {
      // If validation fails due to extreme values, log a warning but continue
      console.warn(`Warning in StandardizedTensor.matmul: ${error.message}`);
    }

    // Check for potential numerical stability issues
    const innerDimension = this.shape[this.shape.length - 1];
    if (innerDimension > 50) {
      // Large inner dimension can lead to numerical issues due to accumulation errors
      console.warn(
        `Warning in StandardizedTensor.matmul: Large inner dimension (${innerDimension}) may lead to numerical instability`,
      );
    }

    // Check for very small values that might be lost in multiplication
    const checkSmallValues = (arr) => {
      if (!Array.isArray(arr)) {
        return typeof arr === "number" && arr !== 0 && Math.abs(arr) < 1e-8;
      }

      for (let i = 0; i < arr.length; i++) {
        if (checkSmallValues(arr[i])) {
          return true;
        }
      }

      return false;
    };

    if (checkSmallValues(this.values) || checkSmallValues(other)) {
      console.warn(
        "Warning in StandardizedTensor.matmul: Very small values detected which may be lost in multiplication",
      );
    }

    // Calculate result shape
    const resultShape = [
      ...this.shape.slice(0, -1),
      otherShape[otherShape.length - 1],
    ];

    const resultValues = TensorOperations.matmul(this.values, other, options);

    const result = new StandardizedTensor(resultShape);
    result.values = resultValues;
    return result;
  }

  /**
   * Calculate the dot product with another tensor
   *
   * @param {StandardizedTensor|Array} tensor - Tensor to calculate dot product with
   * @param {Array<number>} [dims] - Dimensions to contract
   * @param {Object} [options={}] - Dot product options
   * @returns {StandardizedTensor|number} Dot product result
   */
  dot(tensor, dims, options = {}) {
    const other = tensor instanceof StandardizedTensor ? tensor.values : tensor;

    try {
      const result = TensorOperations.dot(this.values, other, dims, options);

      // Check if result is a scalar
      if (!Array.isArray(result)) {
        return result;
      }

      // Create a new tensor with the appropriate shape
      const resultShape = TensorOperations.shape(result);
      const resultTensor = new StandardizedTensor(resultShape);
      resultTensor.values = result;
      return resultTensor;
    } catch (error) {
      throw new Prime.MathematicalError("Error computing dot product", {
        context: {
          module: "StandardizedTensor",
          method: "dot",
          originalError: error.message,
        },
      });
    }
  }

  /**
   * Calculate the norm of the tensor
   *
   * @param {string|number} [p='fro'] - Norm type: 'fro' (Frobenius), 1, 2, Infinity
   * @param {Object} [options={}] - Norm calculation options
   * @returns {number} Norm value
   */
  norm(p = "fro", options = {}) {
    return TensorOperations.norm(this.values, p, options);
  }

  /**
   * Normalize the tensor
   *
   * @param {string|number} [p='fro'] - Norm type for normalization
   * @param {Object} [options={}] - Normalization options
   * @returns {StandardizedTensor} Normalized tensor
   */
  normalize(p = "fro", options = {}) {
    const normalizedValues = TensorOperations.normalize(
      this.values,
      p,
      options,
    );

    const result = new StandardizedTensor(this.shape);
    result.values = normalizedValues;
    return result;
  }

  /**
   * Reshape the tensor to a new shape
   *
   * @param {Array<number>} newShape - New shape
   * @returns {StandardizedTensor} Reshaped tensor
   */
  reshape(newShape) {
    if (!Array.isArray(newShape)) {
      throw new Prime.ValidationError("New shape must be an array", {
        context: {
          module: "StandardizedTensor",
          method: "reshape",
          actualType: typeof newShape,
        },
      });
    }

    // Check if the total number of elements remains the same
    const currentSize = this.getSize();
    const newSize = newShape.reduce((a, b) => a * b, 1);

    if (currentSize !== newSize) {
      throw new Prime.MathematicalError(
        "Cannot reshape tensor: new shape must have the same number of elements",
        {
          context: {
            module: "StandardizedTensor",
            method: "reshape",
            currentSize,
            newSize,
          },
        },
      );
    }

    // Flatten and reshape
    const flat = TensorOperations.flatten(this.values);
    const reshaped = TensorOperations.reshape(flat, newShape);

    const result = new StandardizedTensor(newShape);
    result.values = reshaped;
    return result;
  }

  /**
   * Flatten the tensor to a 1D tensor
   *
   * @returns {StandardizedTensor} Flattened tensor
   */
  flatten() {
    const flat = TensorOperations.flatten(this.values);

    const result = new StandardizedTensor([flat.length]);
    result.values = flat;
    return result;
  }

  /**
   * Transpose the tensor by swapping the last two dimensions
   *
   * @returns {StandardizedTensor} Transposed tensor
   */
  transpose() {
    if (this.shape.length < 2) {
      throw new Prime.MathematicalError(
        "Tensor must have at least 2 dimensions for transpose",
        {
          context: {
            module: "StandardizedTensor",
            method: "transpose",
            shape: this.shape,
          },
        },
      );
    }

    // Create new shape with last two dimensions swapped
    const newShape = this.shape.slice();
    const lastIdx = newShape.length - 1;
    const temp = newShape[lastIdx];
    newShape[lastIdx] = newShape[lastIdx - 1];
    newShape[lastIdx - 1] = temp;

    // Implement transpose recursively
    const transpose2D = (matrix) => {
      const rows = matrix.length;
      const cols = matrix[0].length;
      const result = Array(cols)
        .fill()
        .map(() => Array(rows).fill(0));

      for (let i = 0; i < rows; i++) {
        for (let j = 0; j < cols; j++) {
          result[j][i] = matrix[i][j];
        }
      }

      return result;
    };

    const transposeRecursive = (tensor, depth = 0) => {
      if (depth === this.shape.length - 2) {
        return transpose2D(tensor);
      }

      return tensor.map((t) => transposeRecursive(t, depth + 1));
    };

    const result = new StandardizedTensor(newShape);
    result.values = transposeRecursive(this.values);
    return result;
  }

  /**
   * Apply softmax function to tensor with numerical stability
   *
   * @param {number} [axis=-1] - Axis along which to apply softmax
   * @param {Object} [options={}] - Softmax options
   * @returns {StandardizedTensor} Softmax result
   */
  softmax(axis = -1, options = {}) {
    // Normalize negative axis
    if (axis < 0) {
      axis = this.shape.length + axis;
    }

    if (axis < 0 || axis >= this.shape.length) {
      throw new Prime.ValidationError("Axis out of bounds", {
        context: {
          module: "StandardizedTensor",
          method: "softmax",
          axis,
          rank: this.shape.length,
        },
      });
    }

    const result = new StandardizedTensor(this.shape);
    result.values = TensorOperations.softmax(this.values, axis, options);
    return result;
  }

  /**
   * Apply ReLU function to tensor
   *
   * @returns {StandardizedTensor} ReLU result
   */
  relu() {
    const result = new StandardizedTensor(this.shape);
    result.values = TensorOperations.relu(this.values);
    return result;
  }

  /**
   * Apply sigmoid function to tensor with numerical stability
   *
   * @returns {StandardizedTensor} Sigmoid result
   */
  sigmoid() {
    const result = new StandardizedTensor(this.shape);
    result.values = TensorOperations.sigmoid(this.values);
    return result;
  }

  /**
   * Apply tanh function to tensor
   *
   * @returns {StandardizedTensor} Tanh result
   */
  tanh() {
    const result = new StandardizedTensor(this.shape);
    result.values = TensorOperations.tanh(this.values);
    return result;
  }

  /**
   * Check if two shapes are equal
   *
   * @private
   * @param {Array<number>} shape1 - First shape
   * @param {Array<number>} shape2 - Second shape
   * @returns {boolean} True if shapes are equal
   */
  _areShapesEqual(shape1, shape2) {
    if (shape1.length !== shape2.length) {
      return false;
    }

    for (let i = 0; i < shape1.length; i++) {
      if (shape1[i] !== shape2[i]) {
        return false;
      }
    }

    return true;
  }

  /**
   * Convert the tensor to a regular JavaScript array
   *
   * @returns {Array} JavaScript array representation
   */
  toArray() {
    return JSON.parse(JSON.stringify(this.values));
  }

  /**
   * Create a copy of this tensor
   *
   * @returns {StandardizedTensor} Copied tensor
   */
  clone() {
    const result = new StandardizedTensor(this.shape);
    result.values = JSON.parse(JSON.stringify(this.values));
    return result;
  }

  /**
   * Create a string representation of the tensor
   *
   * @returns {string} String representation
   */
  toString() {
    return `Tensor(${this.shape.join("×")})`;
  }
}

// Export the StandardizedTensor class
module.exports = StandardizedTensor;
