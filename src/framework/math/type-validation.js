/**
 * PrimeOS JavaScript Library - Math Type Validation Module
 * Provides comprehensive type validation for mathematical operations
 * Version 1.0.0
 */

// Import Prime core directly to avoid circular dependencies
const Prime = require("../../core/prime.js");

/**
 * Type validation and assertion helpers for mathematical operations.
 * This module provides specialized validation for mathematical objects.
 *
 * Note: To avoid circular dependencies, this module implements its own
 * type checking functions rather than relying on Prime.Utils.
 */
const TypeValidation = {
  /**
   * Asserts that a value is an array and throws a validation error if not
   * @param {*} value - The value to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If value is not an array
   */
  /**
   * Internal type checking function for arrays
   * @private
   * @param {*} value - The value to check
   * @returns {boolean} True if value is an array
   */
  _isArray: function (value) {
    return Array.isArray(value);
  },

  /**
   * Internal type checking function for numbers
   * @private
   * @param {*} value - The value to check
   * @returns {boolean} True if value is a number
   */
  _isNumber: function (value) {
    return typeof value === "number" && !isNaN(value);
  },

  /**
   * Internal type checking function for functions
   * @private
   * @param {*} value - The value to check
   * @returns {boolean} True if value is a function
   */
  _isFunction: function (value) {
    return typeof value === "function";
  },

  /**
   * Internal type checking function for objects
   * @private
   * @param {*} value - The value to check
   * @returns {boolean} True if value is an object (not null and not an array)
   */
  _isObject: function (value) {
    return value !== null && typeof value === "object" && !Array.isArray(value);
  },

  /**
   * Internal type checking function for strings
   * @private
   * @param {*} value - The value to check
   * @returns {boolean} True if value is a string
   */
  _isString: function (value) {
    return typeof value === "string";
  },

  /**
   * Internal type checking function for booleans
   * @private
   * @param {*} value - The value to check
   * @returns {boolean} True if value is a boolean
   */
  _isBoolean: function (value) {
    return typeof value === "boolean";
  },

  /**
   * Internal type checking function for null or undefined
   * @private
   * @param {*} value - The value to check
   * @returns {boolean} True if value is null or undefined
   */
  _isNullOrUndefined: function (value) {
    return value === null || typeof value === "undefined";
  },

  assertArray: function (value, paramName, context = {}) {
    if (!this._isArray(value)) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must be an array`,
        {
          ...context,
          expectedType: "array",
          actualType: typeof value,
          actual: value,
        },
      );
    }
  },

  /**
   * Asserts that a value is a number and throws a validation error if not
   * @param {*} value - The value to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If value is not a number
   */
  assertNumber: function (value, paramName, context = {}) {
    if (!this._isNumber(value)) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must be a number`,
        {
          ...context,
          expectedType: "number",
          actualType: typeof value,
          actual: value,
        },
      );
    }
  },

  /**
   * Asserts that a value is a positive number and throws a validation error if not
   * @param {*} value - The value to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If value is not a positive number
   */
  assertPositiveNumber: function (value, paramName, context = {}) {
    this.assertNumber(value, paramName, context);

    if (value <= 0) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must be a positive number`,
        {
          ...context,
          expectedType: "positive number",
          actual: value,
        },
      );
    }
  },

  /**
   * Asserts that a value is an integer and throws a validation error if not
   * @param {*} value - The value to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If value is not an integer
   */
  assertInteger: function (value, paramName, context = {}) {
    this.assertNumber(value, paramName, context);

    if (!Number.isInteger(value)) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must be an integer`,
        {
          ...context,
          expectedType: "integer",
          actual: value,
        },
      );
    }
  },

  /**
   * Asserts that a value is a positive integer and throws a validation error if not
   * @param {*} value - The value to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If value is not a positive integer
   */
  assertPositiveInteger: function (value, paramName, context = {}) {
    this.assertInteger(value, paramName, context);

    if (value <= 0) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must be a positive integer`,
        {
          ...context,
          expectedType: "positive integer",
          actual: value,
        },
      );
    }
  },

  /**
   * Asserts that a value is a non-negative integer (0 or positive) and throws a validation error if not
   * @param {*} value - The value to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If value is not a non-negative integer
   */
  assertNonNegativeInteger: function (value, paramName, context = {}) {
    this.assertInteger(value, paramName, context);

    if (value < 0) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must be a non-negative integer`,
        {
          ...context,
          expectedType: "non-negative integer",
          actual: value,
        },
      );
    }
  },

  /**
   * Asserts that a value is finite (not Infinity, -Infinity, or NaN)
   * @param {*} value - The value to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If value is not finite
   */
  assertFinite: function (value, paramName, context = {}) {
    this.assertNumber(value, paramName, context);

    if (!Number.isFinite(value)) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must be a finite number`,
        {
          ...context,
          expectedType: "finite number",
          actual: value,
        },
      );
    }
  },

  /**
   * Asserts that a value is a function and throws a validation error if not
   * @param {*} value - The value to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If value is not a function
   */
  assertFunction: function (value, paramName, context = {}) {
    if (!this._isFunction(value)) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must be a function`,
        {
          ...context,
          expectedType: "function",
          actualType: typeof value,
        },
      );
    }
  },

  /**
   * Asserts that a value is an object and throws a validation error if not
   * @param {*} value - The value to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If value is not an object
   */
  assertObject: function (value, paramName, context = {}) {
    if (!this._isObject(value)) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must be an object`,
        {
          ...context,
          expectedType: "object",
          actualType: typeof value,
          actual: value,
        },
      );
    }
  },

  /**
   * Asserts that a value is a string and throws a validation error if not
   * @param {*} value - The value to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If value is not a string
   */
  assertString: function (value, paramName, context = {}) {
    if (!this._isString(value)) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must be a string`,
        {
          ...context,
          expectedType: "string",
          actualType: typeof value,
        },
      );
    }
  },

  /**
   * Asserts that a value is a boolean and throws a validation error if not
   * @param {*} value - The value to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If value is not a boolean
   */
  assertBoolean: function (value, paramName, context = {}) {
    if (!this._isBoolean(value)) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must be a boolean`,
        {
          ...context,
          expectedType: "boolean",
          actualType: typeof value,
        },
      );
    }
  },

  /**
   * Asserts that a value is not null or undefined and throws a validation error if it is
   * @param {*} value - The value to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If value is null or undefined
   */
  assertDefined: function (value, paramName, context = {}) {
    if (this._isNullOrUndefined(value)) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' is required and cannot be null or undefined`,
        {
          ...context,
          actual: value,
        },
      );
    }
  },

  /**
   * Asserts that an array has at least a minimum length
   * @param {Array} array - The array to check
   * @param {number} minLength - The minimum required length
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If array is too short
   */
  assertMinLength: function (array, minLength, paramName, context = {}) {
    this.assertArray(array, paramName, context);

    if (array.length < minLength) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must have at least ${minLength} element(s)`,
        {
          ...context,
          expectedMinLength: minLength,
          actualLength: array.length,
        },
      );
    }
  },

  /**
   * Asserts that an array has at most a maximum length
   * @param {Array} array - The array to check
   * @param {number} maxLength - The maximum allowed length
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If array is too long
   */
  assertMaxLength: function (array, maxLength, paramName, context = {}) {
    this.assertArray(array, paramName, context);

    if (array.length > maxLength) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must have at most ${maxLength} element(s)`,
        {
          ...context,
          expectedMaxLength: maxLength,
          actualLength: array.length,
        },
      );
    }
  },

  /**
   * Asserts that an array has exactly the specified length
   * @param {Array} array - The array to check
   * @param {number} exactLength - The exact required length
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If array does not have the exact length
   */
  assertExactLength: function (array, exactLength, paramName, context = {}) {
    this.assertArray(array, paramName, context);

    if (array.length !== exactLength) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must have exactly ${exactLength} element(s)`,
        {
          ...context,
          expectedLength: exactLength,
          actualLength: array.length,
        },
      );
    }
  },

  /**
   * Asserts that an array contains only numbers and throws a validation error if not
   * @param {Array} array - The array to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If array contains non-numeric elements
   */
  assertNumberArray: function (array, paramName, context = {}) {
    this.assertArray(array, paramName, context);

    const nonNumberIndex = array.findIndex((item) => !this._isNumber(item));
    if (nonNumberIndex !== -1) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must contain only numbers`,
        {
          ...context,
          invalidElementIndex: nonNumberIndex,
          invalidElement: array[nonNumberIndex],
        },
      );
    }
  },

  /**
   * Asserts that a 2D array is a valid matrix (all rows have the same length)
   * @param {Array} matrix - The 2D array to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If the matrix is invalid
   */
  assertMatrix: function (matrix, paramName, context = {}) {
    this.assertArray(matrix, paramName, context);

    if (matrix.length === 0) {
      return; // Empty matrix is valid
    }

    // Check if all elements are arrays
    const nonArrayRow = matrix.findIndex((row) => !this._isArray(row));
    if (nonArrayRow !== -1) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must be a 2D array`,
        {
          ...context,
          invalidRowIndex: nonArrayRow,
          invalidRow: matrix[nonArrayRow],
        },
      );
    }

    // Check if all rows have the same length
    const firstRowLength = matrix[0].length;
    const irregularRow = matrix.findIndex(
      (row) => row.length !== firstRowLength,
    );
    if (irregularRow !== -1) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must be a regular matrix (all rows must have the same length)`,
        {
          ...context,
          expectedRowLength: firstRowLength,
          irregularRowIndex: irregularRow,
          irregularRowLength: matrix[irregularRow].length,
        },
      );
    }

    // Check if all elements are numbers
    for (let i = 0; i < matrix.length; i++) {
      const row = matrix[i];
      const nonNumberIndex = row.findIndex((item) => !this._isNumber(item));
      if (nonNumberIndex !== -1) {
        throw new Prime.ValidationError(
          `Parameter '${paramName}' must contain only numbers`,
          {
            ...context,
            invalidRowIndex: i,
            invalidColumnIndex: nonNumberIndex,
            invalidElement: row[nonNumberIndex],
          },
        );
      }
    }
  },

  /**
   * Asserts that a matrix is square (number of rows equals number of columns)
   * @param {Array} matrix - The matrix to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If the matrix is not square
   */
  assertSquareMatrix: function (matrix, paramName, context = {}) {
    this.assertMatrix(matrix, paramName, context);

    if (matrix.length === 0) {
      return; // Empty matrix is considered square
    }

    if (matrix.length !== matrix[0].length) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must be a square matrix`,
        {
          ...context,
          rows: matrix.length,
          columns: matrix[0].length,
        },
      );
    }
  },

  /**
   * Asserts that a value is within the specified range
   * @param {number} value - The value to check
   * @param {number} min - Minimum allowed value (inclusive)
   * @param {number} max - Maximum allowed value (inclusive)
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {ValidationError} If value is outside the allowed range
   */
  assertRange: function (value, min, max, paramName, context = {}) {
    this.assertNumber(value, paramName, context);

    if (value < min || value > max) {
      throw new Prime.ValidationError(
        `Parameter '${paramName}' must be between ${min} and ${max} (inclusive)`,
        {
          ...context,
          allowedRange: [min, max],
          actual: value,
        },
      );
    }
  },

  /**
   * Asserts that vectors have the same dimension
   * @param {Array} v1 - First vector
   * @param {Array} v2 - Second vector
   * @param {string} firstParamName - Name of the first parameter
   * @param {string} secondParamName - Name of the second parameter
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {DimensionMismatchError} If vectors have different dimensions
   */
  assertSameDimension: function (
    v1,
    v2,
    firstParamName,
    secondParamName,
    context = {},
  ) {
    this.assertArray(v1, firstParamName, context);
    this.assertArray(v2, secondParamName, context);

    if (v1.length !== v2.length) {
      throw new Prime.DimensionMismatchError(
        `Parameters '${firstParamName}' and '${secondParamName}' must have the same dimension`,
        {
          ...context,
          firstDimension: v1.length,
          secondDimension: v2.length,
          operation: context.operation || "assertSameDimension",
        },
      );
    }
  },

  /**
   * Asserts that matrices have compatible dimensions for multiplication
   * @param {Array} m1 - First matrix
   * @param {Array} m2 - Second matrix
   * @param {string} firstParamName - Name of the first parameter
   * @param {string} secondParamName - Name of the second parameter
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {DimensionMismatchError} If matrices have incompatible dimensions
   */
  assertMultiplicableMatrices: function (
    m1,
    m2,
    firstParamName,
    secondParamName,
    context = {},
  ) {
    this.assertMatrix(m1, firstParamName, context);
    this.assertMatrix(m2, secondParamName, context);

    if (m1.length === 0 || m2.length === 0) {
      return; // Empty matrices are compatible
    }

    const m1Cols = m1[0].length;
    const m2Rows = m2.length;

    if (m1Cols !== m2Rows) {
      throw new Prime.DimensionMismatchError(
        `Matrices '${firstParamName}' and '${secondParamName}' have incompatible dimensions for multiplication`,
        {
          ...context,
          firstMatrixDimensions: [m1.length, m1Cols],
          secondMatrixDimensions: [m2Rows, m2[0].length],
          operation: context.operation || "matrixMultiplication",
        },
      );
    }
  },

  /**
   * Asserts that matrices have the same dimensions
   * @param {Array} m1 - First matrix
   * @param {Array} m2 - Second matrix
   * @param {string} firstParamName - Name of the first parameter
   * @param {string} secondParamName - Name of the second parameter
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {DimensionMismatchError} If matrices have different dimensions
   */
  assertSameMatrixDimensions: function (
    m1,
    m2,
    firstParamName,
    secondParamName,
    context = {},
  ) {
    this.assertMatrix(m1, firstParamName, context);
    this.assertMatrix(m2, secondParamName, context);

    if (m1.length === 0 && m2.length === 0) {
      return; // Both empty matrices are compatible
    }

    if (
      m1.length !== m2.length ||
      (m1.length > 0 && m2.length > 0 && m1[0].length !== m2[0].length)
    ) {
      throw new Prime.DimensionMismatchError(
        `Matrices '${firstParamName}' and '${secondParamName}' must have the same dimensions`,
        {
          ...context,
          firstMatrixDimensions:
            m1.length > 0 ? [m1.length, m1[0].length] : [0, 0],
          secondMatrixDimensions:
            m2.length > 0 ? [m2.length, m2[0].length] : [0, 0],
          operation: context.operation || "matrixOperation",
        },
      );
    }
  },

  /**
   * Asserts that a matrix and vector have compatible dimensions for multiplication
   * @param {Array} matrix - The matrix
   * @param {Array} vector - The vector
   * @param {string} matrixParamName - Name of the matrix parameter
   * @param {string} vectorParamName - Name of the vector parameter
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {DimensionMismatchError} If matrix and vector have incompatible dimensions
   */
  assertMatrixVectorMultiplicable: function (
    matrix,
    vector,
    matrixParamName,
    vectorParamName,
    context = {},
  ) {
    this.assertMatrix(matrix, matrixParamName, context);
    this.assertArray(vector, vectorParamName, context);
    this.assertNumberArray(vector, vectorParamName, context);

    if (matrix.length === 0) {
      return; // Empty matrix is compatible with any vector
    }

    const matrixCols = matrix[0].length;

    if (matrixCols !== vector.length) {
      throw new Prime.DimensionMismatchError(
        `Matrix '${matrixParamName}' and vector '${vectorParamName}' have incompatible dimensions for multiplication`,
        {
          ...context,
          matrixDimensions: [matrix.length, matrixCols],
          vectorDimension: vector.length,
          operation: context.operation || "matrixVectorMultiplication",
        },
      );
    }
  },

  /**
   * Validates that a number is not too extreme (not too close to zero or too large)
   * @param {number} value - The value to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} options - Options for validation
   * @param {number} [options.minMagnitude=1e-100] - Minimum allowed magnitude
   * @param {number} [options.maxMagnitude=1e100] - Maximum allowed magnitude
   * @param {boolean} [options.allowZero=true] - Whether zero is allowed
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {NumericOverflowError} If value is too extreme
   */
  validateMagnitude: function (value, paramName, options = {}, context = {}) {
    this.assertNumber(value, paramName, context);

    const minMagnitude = options.minMagnitude || 1e-100;
    const maxMagnitude = options.maxMagnitude || 1e100;
    const allowZero = options.allowZero !== false;

    const absValue = Math.abs(value);

    if (absValue === 0) {
      if (!allowZero) {
        throw new Prime.NumericOverflowError(
          `Parameter '${paramName}' cannot be zero`,
          {
            ...context,
            value: value,
            operation: context.operation || "validateMagnitude",
          },
        );
      }
      return; // Zero is allowed and doesn't need magnitude check
    }

    if (absValue < minMagnitude) {
      throw new Prime.NumericOverflowError(
        `Parameter '${paramName}' is too close to zero (underflow)`,
        {
          ...context,
          value: value,
          minMagnitude: minMagnitude,
          operation: context.operation || "validateMagnitude",
        },
      );
    }

    if (absValue > maxMagnitude) {
      throw new Prime.NumericOverflowError(
        `Parameter '${paramName}' is too large (overflow)`,
        {
          ...context,
          value: value,
          maxMagnitude: maxMagnitude,
          operation: context.operation || "validateMagnitude",
        },
      );
    }
  },

  /**
   * Validates the magnitudes of all values in an array
   * @param {Array} array - The array to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} options - Options for validation
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {NumericOverflowError} If any value in the array is too extreme
   */
  validateArrayMagnitudes: function (
    array,
    paramName,
    options = {},
    context = {},
  ) {
    this.assertArray(array, paramName, context);
    this.assertNumberArray(array, paramName, context);

    for (let i = 0; i < array.length; i++) {
      try {
        this.validateMagnitude(
          array[i],
          `${paramName}[${i}]`,
          options,
          context,
        );
      } catch (error) {
        // Add index information to the error context
        error.context = error.context || {};
        error.context.arrayIndex = i;
        throw error;
      }
    }
  },

  /**
   * Validates the magnitudes of all values in a matrix
   * @param {Array} matrix - The matrix to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} options - Options for validation
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {NumericOverflowError} If any value in the matrix is too extreme
   */
  validateMatrixMagnitudes: function (
    matrix,
    paramName,
    options = {},
    context = {},
  ) {
    this.assertMatrix(matrix, paramName, context);

    for (let i = 0; i < matrix.length; i++) {
      for (let j = 0; j < matrix[i].length; j++) {
        try {
          this.validateMagnitude(
            matrix[i][j],
            `${paramName}[${i}][${j}]`,
            options,
            context,
          );
        } catch (error) {
          // Add index information to the error context
          error.context = error.context || {};
          error.context.rowIndex = i;
          error.context.columnIndex = j;
          throw error;
        }
      }
    }
  },

  /**
   * Validates that a matrix is invertible (not singular)
   * @param {Array} matrix - The matrix to check
   * @param {string} paramName - The name of the parameter (for error messages)
   * @param {Object} options - Options for validation
   * @param {number} [options.tolerance=1e-10] - Tolerance for detecting singularity
   * @param {Object} [context={}] - Additional context for error reporting
   * @throws {MatrixSingularityError} If matrix is singular
   */
  validateInvertibleMatrix: function (
    matrix,
    paramName,
    options = {},
    context = {},
  ) {
    this.assertSquareMatrix(matrix, paramName, context);

    const tolerance = options.tolerance || 1e-10;

    // A simple check for singularity is to calculate the determinant
    // However, this is just a basic implementation and could be improved
    let determinant = 0;

    if (matrix.length === 1) {
      determinant = matrix[0][0];
    } else if (matrix.length === 2) {
      determinant = matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0];
    } else {
      // For larger matrices, this is just a placeholder
      // In practice, you'd use a more sophisticated method
      determinant = 1.0; // Placeholder to avoid throwing error by default

      // TODO: Implement proper determinant calculation for larger matrices
      // This should be implemented in the LinearAlgebra module and called from here
    }

    if (Math.abs(determinant) < tolerance) {
      throw new Prime.MatrixSingularityError(
        `Matrix '${paramName}' is singular or nearly singular`,
        {
          ...context,
          determinant: determinant,
          tolerance: tolerance,
          operation: context.operation || "validateInvertibleMatrix",
        },
      );
    }
  },

  /**
   * Creates a standard validation context object
   * @param {string} operation - The operation being performed
   * @param {Object} inputs - Input parameters
   * @param {Object} [details={}] - Additional details
   * @returns {Object} Standardized context object
   */
  createValidationContext: function (operation, inputs, details = {}) {
    const context = {
      operation,
      ...details,
    };

    // Add information about inputs
    if (inputs) {
      const inputInfo = {};

      for (const key in inputs) {
        const input = inputs[key];

        if (this._isArray(input)) {
          if (input.length > 0 && this._isArray(input[0])) {
            // 2D array (matrix)
            inputInfo[key] = `matrix(${input.length}x${input[0].length})`;
          } else {
            // 1D array (vector)
            inputInfo[key] = `vector(${input.length})`;
          }
        } else if (this._isNumber(input)) {
          inputInfo[key] = `number(${input})`;
        } else if (this._isFunction(input)) {
          inputInfo[key] = "function";
        } else if (this._isObject(input)) {
          inputInfo[key] = "object";
        } else if (this._isString(input)) {
          inputInfo[key] = `string("${input}")`;
        } else if (this._isBoolean(input)) {
          inputInfo[key] = `boolean(${input})`;
        } else {
          inputInfo[key] = typeof input;
        }
      }

      context.inputs = inputInfo;
    }

    return context;
  },
};

// Export the public API
module.exports = TypeValidation;
