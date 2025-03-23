/**
 * PrimeOS JavaScript Library - Framework
 * Base 0: Coherence Constraints
 * Constraint definitions for mathematical coherence validation
 */

// Import Prime directly from core/prime
const Prime = require("../../core/prime.js");

/**
 * Predefined constraints for various mathematical domains
 * Used by the coherence validation system to verify mathematical operations
 */
const CoherenceConstraints = {
  /**
   * Numeric domain constraints
   * Used to verify properties of numeric values
   */
  numeric: {
    /**
     * Check if a value is finite
     * @param {number} value - Value to check
     * @returns {boolean} True if value is finite
     */
    finiteness: {
      name: "finiteness",
      validator: (value) => Number.isFinite(value),
      priority: 10,
      description:
        "Checks if a numeric value is finite (not Infinity or -Infinity)",
    },

    /**
     * Check if a value is not NaN
     * @param {number} value - Value to check
     * @returns {boolean} True if value is not NaN
     */
    nonNaN: {
      name: "non_nan",
      validator: (value) => !Number.isNaN(value),
      priority: 10,
      description: "Checks if a numeric value is not NaN (Not a Number)",
    },

    /**
     * Check if a value is within reasonable bounds
     * @param {number} value - Value to check
     * @param {Object} context - Context with bounds information
     * @returns {boolean} True if value is within bounds
     */
    reasonableBounds: {
      name: "reasonable_bounds",
      validator: (value, context = {}) => {
        const { min = -1e12, max = 1e12 } = context;
        return value >= min && value <= max;
      },
      priority: 5,
      description: "Checks if a numeric value is within reasonable bounds",
    },
  },

  /**
   * Vector space constraints
   * Used to verify properties of vectors and arrays
   */
  vectorSpace: {
    /**
     * Check if all elements of an array are numbers
     * @param {Array} value - Array to check
     * @returns {boolean} True if all elements are numbers
     */
    arrayElements: {
      name: "array_elements",
      validator: (value) =>
        Array.isArray(value) && value.every((item) => typeof item === "number"),
      priority: 8,
      description: "Checks if all elements in an array are numbers",
    },

    /**
     * Check if all elements of an array are finite
     * @param {Array} value - Array to check
     * @returns {boolean} True if all elements are finite
     */
    finiteElements: {
      name: "finite_elements",
      validator: (value) =>
        Array.isArray(value) && value.every((item) => Number.isFinite(item)),
      priority: 7,
      description: "Checks if all elements in an array are finite numbers",
    },

    /**
     * Check if vector has non-zero magnitude
     * @param {Array} value - Vector to check
     * @returns {boolean} True if vector has non-zero magnitude
     */
    nonZeroMagnitude: {
      name: "non_zero_magnitude",
      validator: (value) => {
        if (!Array.isArray(value)) return false;
        return value.some((v) => v !== 0);
      },
      priority: 4,
      description: "Checks if a vector has at least one non-zero element",
    },
  },

  /**
   * Matrix algebra constraints
   * Used to verify properties of matrices
   */
  matrixAlgebra: {
    /**
     * Check if a matrix has proper structure (all rows same length)
     * @param {Array} value - Matrix to check
     * @returns {boolean} True if matrix has proper structure
     */
    matrixStructure: {
      name: "matrix_structure",
      validator: (value) => {
        if (!Array.isArray(value) || value.length === 0) return false;
        if (!value.every((row) => Array.isArray(row))) return false;

        // Check that all rows have the same length
        const rowLength = value[0].length;
        return value.every((row) => row.length === rowLength);
      },
      priority: 9,
      description:
        "Checks if a matrix has proper structure with consistent row lengths",
    },

    /**
     * Check if all matrix elements are finite numbers
     * @param {Array} value - Matrix to check
     * @returns {boolean} True if all elements are finite numbers
     */
    matrixElements: {
      name: "matrix_elements",
      validator: (value) => {
        if (!Array.isArray(value)) return false;
        return value.every(
          (row) =>
            Array.isArray(row) &&
            row.every(
              (item) => typeof item === "number" && Number.isFinite(item),
            ),
        );
      },
      priority: 8,
      description: "Checks if all elements in a matrix are finite numbers",
    },

    /**
     * Check if matrix is square (rows = columns)
     * @param {Array} value - Matrix to check
     * @returns {boolean} True if matrix is square
     */
    squareMatrix: {
      name: "square_matrix",
      validator: (value) => {
        if (!Array.isArray(value) || value.length === 0) return false;
        if (!value.every((row) => Array.isArray(row))) return false;

        return value.length === value[0].length;
      },
      priority: 6,
      description:
        "Checks if a matrix is square (same number of rows and columns)",
    },
  },

  /**
   * Functional domain constraints
   * Used to verify properties of functions
   */
  functional: {
    /**
     * Check if value is a function
     * @param {*} value - Value to check
     * @returns {boolean} True if value is a function
     */
    isFunction: {
      name: "is_function",
      validator: (value) => typeof value === "function",
      priority: 10,
      description: "Checks if a value is a function",
    },

    /**
     * Check if function has expected arity (number of arguments)
     * @param {Function} value - Function to check
     * @param {Object} context - Context with expected arity
     * @returns {boolean} True if function has expected arity
     */
    functionArity: {
      name: "function_arity",
      validator: (value, context = {}) => {
        if (typeof value !== "function") return false;
        return (
          context.expectedArity === undefined ||
          value.length === context.expectedArity
        );
      },
      priority: 7,
      description: "Checks if a function has the expected number of parameters",
    },
  },

  /**
   * Tensor algebra constraints
   * Used to verify properties of tensors
   */
  tensorAlgebra: {
    /**
     * Check if tensor has valid structure
     * @param {Array} value - Tensor to check
     * @returns {boolean} True if tensor has valid structure
     */
    tensorStructure: {
      name: "tensor_structure",
      validator: (value) => {
        // Recursive check for multi-dimensional arrays with consistent structure
        const checkTensorStructure = (arr, dims = null, depth = 0) => {
          if (!Array.isArray(arr)) {
            return depth > 0; // Allow scalar values at the deepest level
          }

          if (arr.length === 0) return true;

          if (depth === 0) {
            // First level must be an array
            dims = Array(arr[0].length).fill(0);
            if (!Array.isArray(arr[0])) return false;
          } else if (Array.isArray(arr[0])) {
            // If we expect an array at this level
            if (arr[0].length !== dims[depth]) {
              // Non-consistent dimensions
              return false;
            }
          } else {
            // We expected a scalar here
            return depth === dims.length;
          }

          // Check all elements at this level
          return arr.every((subArr) =>
            checkTensorStructure(subArr, dims, depth + 1),
          );
        };

        return checkTensorStructure(value);
      },
      priority: 9,
      description: "Checks if a tensor has valid and consistent structure",
    },

    /**
     * Check if all tensor elements are finite numbers
     * @param {Array} value - Tensor to check
     * @returns {boolean} True if all elements are finite numbers
     */
    tensorElements: {
      name: "tensor_elements",
      validator: (value) => {
        // Recursive check for all values in a tensor
        const checkAllValues = (arr) => {
          if (!Array.isArray(arr)) {
            return typeof arr === "number" && Number.isFinite(arr);
          }
          return arr.every((subArr) => checkAllValues(subArr));
        };

        return checkAllValues(value);
      },
      priority: 8,
      description: "Checks if all elements in a tensor are finite numbers",
    },
  },
};

/**
 * Coherence norms for different domains
 * Used to compute coherence scores for validation results
 */
const CoherenceNorms = {
  /**
   * Compute coherence norm for numeric values
   * @param {Array} results - Constraint validation results
   * @returns {number} Coherence score (0-1)
   */
  numeric: (results) => {
    // For numeric values, coherence is binary - either fully coherent or not
    return results.every((r) => r.satisfied) ? 1.0 : 0.0;
  },

  /**
   * Compute coherence norm for vector spaces
   * @param {Array} results - Constraint validation results
   * @param {Array} value - Vector value
   * @returns {number} Coherence score (0-1)
   */
  vectorSpace: (results, value) => {
    // For vectors, consider partial coherence based on the proportion of valid elements
    if (!Array.isArray(value)) return 0.0;

    // If fundamental constraints are violated, coherence is 0
    if (!results.find((r) => r.name === "array_elements")?.satisfied) {
      return 0.0;
    }

    // Count finite elements
    const finiteCount = value.filter((v) => Number.isFinite(v)).length;
    return value.length > 0 ? finiteCount / value.length : 0.0;
  },

  /**
   * Compute coherence norm for matrix algebra
   * @param {Array} results - Constraint validation results
   * @param {Array} value - Matrix value
   * @returns {number} Coherence score (0-1)
   */
  matrixAlgebra: (results, value) => {
    // For matrices, consider structure and element validity
    if (!results.find((r) => r.name === "matrix_structure")?.satisfied) {
      return 0.0;
    }

    // Count valid elements
    let validCount = 0;
    let totalCount = 0;

    for (const row of value) {
      for (const element of row) {
        totalCount++;
        if (typeof element === "number" && Number.isFinite(element)) {
          validCount++;
        }
      }
    }

    return totalCount > 0 ? validCount / totalCount : 0.0;
  },

  /**
   * Compute coherence norm for functional domain
   * @param {Array} results - Constraint validation results
   * @returns {number} Coherence score (0-1)
   */
  functional: (results) => {
    // For functions, coherence is primarily based on type correctness
    if (!results.find((r) => r.name === "is_function")?.satisfied) {
      return 0.0;
    }

    // Consider other constraints with weighted importance
    let totalWeight = 0;
    let satisfiedWeight = 0;

    for (const result of results) {
      totalWeight += result.priority;
      if (result.satisfied) {
        satisfiedWeight += result.priority;
      }
    }

    return totalWeight > 0 ? satisfiedWeight / totalWeight : 1.0;
  },

  /**
   * Compute coherence norm for tensor algebra
   * @param {Array} results - Constraint validation results
   * @param {Array} value - Tensor value
   * @returns {number} Coherence score (0-1)
   */
  tensorAlgebra: (results, value) => {
    // For tensors, check structure first
    if (!results.find((r) => r.name === "tensor_structure")?.satisfied) {
      return 0.0;
    }

    // Count tensor elements (recursively)
    const countElements = (arr) => {
      if (!Array.isArray(arr)) return 1;
      return arr.reduce((sum, subArr) => sum + countElements(subArr), 0);
    };

    // Count valid elements (recursively)
    const countValidElements = (arr) => {
      if (!Array.isArray(arr)) {
        return typeof arr === "number" && Number.isFinite(arr) ? 1 : 0;
      }
      return arr.reduce((sum, subArr) => sum + countValidElements(subArr), 0);
    };

    const totalElements = countElements(value);
    const validElements = countValidElements(value);

    return totalElements > 0 ? validElements / totalElements : 0.0;
  },
};

module.exports = {
  CoherenceConstraints,
  CoherenceNorms,
};
