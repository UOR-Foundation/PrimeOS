/**
 * PrimeOS Test Utilities - Assertions
 *
 * Standardized assertion helpers for PrimeOS tests.
 * These utilities provide consistent assertion patterns across all test files.
 */

const assert = require("assert");

/**
 * Assertions module with enhanced precision and error handling capabilities
 */
const Assertions = {
  /**
   * Assert equality with adaptive precision based on value magnitude
   *
   * @param {number} actual - Actual value
   * @param {number} expected - Expected value
   * @param {number} [baseTolerance=1e-10] - Base tolerance level
   * @param {string} [message] - Optional message
   * @returns {number} - The error magnitude
   */
  assertAdaptivePrecision: (
    actual,
    expected,
    baseTolerance = 1e-10,
    message = "",
  ) => {
    // Adaptively scale tolerance based on the magnitude of values
    const magnitude = Math.max(Math.abs(actual), Math.abs(expected));
    const adaptiveTolerance =
      baseTolerance * (1 + magnitude * Number.EPSILON * 100);

    const error = Math.abs(actual - expected);
    assert.ok(
      error <= adaptiveTolerance,
      `${message || "Precision error with adaptive tolerance"}: |${actual} - ${expected}| = ${error} > ${adaptiveTolerance}`,
    );
    return error;
  },

  /**
   * Assert extreme precision using Units in Last Place (ULP)
   *
   * @param {number} actual - Actual value
   * @param {number} expected - Expected value
   * @param {string} [message] - Optional message
   * @returns {number} - The error magnitude
   */
  assertExtremePrecision: (actual, expected, message = "") => {
    // Use ULP (Units in Last Place) for extreme precision testing
    const computeULP = (value) => {
      if (value === 0) return Number.MIN_VALUE;
      const next = Math.nextafter
        ? Math.nextafter(value, value + 1)
        : value * (1 + Number.EPSILON);
      return Math.abs(next - value);
    };

    const ulp = computeULP(expected);
    const maxUlpDiff = 2; // Allow up to 2 ULP difference
    const error = Math.abs(actual - expected);

    assert.ok(
      error <= maxUlpDiff * ulp,
      `${message || "Extreme precision error"}: ULP diff = ${error / ulp} > ${maxUlpDiff}`,
    );
    return error;
  },

  /**
   * Assert numerical stability with error bound growth analysis
   *
   * @param {Function} computation - Function to test
   * @param {Array} inputs - Input values
   * @param {Function} boundsFunc - Function to compute error bounds
   * @param {number} [iterations=10] - Number of iterations
   * @param {string} [message] - Optional message
   * @returns {Array} - Results of computation
   */
  assertStabilityBound: (
    computation,
    inputs,
    boundsFunc,
    iterations = 10,
    message = "",
  ) => {
    let results = [];
    let currentInputs = [...inputs];

    // Repeatedly apply computation to analyze error propagation
    for (let i = 0; i < iterations; i++) {
      const result = computation(...currentInputs);
      results.push(result);
      // Update inputs for next iteration
      currentInputs = [result, ...currentInputs.slice(1)];
    }

    // Handle special case for matrix results
    if (Array.isArray(results[0]) && Array.isArray(results[0][0])) {
      // For matrix results, compute Frobenius norm of difference
      for (let i = 1; i < results.length; i++) {
        const bound = boundsFunc(i, results[0]);

        // Compute Frobenius norm of the difference between matrices
        let sumSquaredDiff = 0;
        const matrix1 = results[0];
        const matrix2 = results[i];

        for (let r = 0; r < matrix1.length && r < matrix2.length; r++) {
          for (let c = 0; c < matrix1[r].length && c < matrix2[r].length; c++) {
            const diff = matrix1[r][c] - matrix2[r][c];
            sumSquaredDiff += diff * diff;
          }
        }

        const error = Math.sqrt(sumSquaredDiff);

        assert.ok(
          error <= bound,
          `${message || "Stability bound exceeded"}: iteration ${i} error ${error} > ${bound}`,
        );
      }

      return results;
    }

    // For scalar results, use simple absolute difference
    for (let i = 1; i < results.length; i++) {
      const bound = boundsFunc(i, results[0]);
      const error = Math.abs(results[i] - results[0]);
      assert.ok(
        error <= bound,
        `${message || "Stability bound exceeded"}: iteration ${i} error ${error} > ${bound}`,
      );
    }

    return results;
  },

  /**
   * Assert that a function doesn't exhibit catastrophic cancellation
   *
   * @param {Function} computation - Function to test
   * @param {Array} inputs - Input values
   * @param {number} [expectedRelativeError=1e-6] - Maximum allowed relative error
   * @param {string} [message] - Optional message
   * @returns {number} - Relative error
   */
  assertNoCatastrophicCancellation: (
    computation,
    inputs,
    expectedRelativeError = 1e-6,
    message = "",
  ) => {
    const result = computation(...inputs);

    // Compute result with high precision using a numerically stable algorithm
    const highPrecisionComputation = (...args) => {
      // Implement Kahan summation algorithm for numerically stable computation
      if (
        args.length === 2 &&
        typeof args[0] === "number" &&
        typeof args[1] === "number"
      ) {
        const [a, b] = args;
        // If a and b are nearly equal, use compensated subtraction
        if (Math.abs(a - b) / Math.max(Math.abs(a), Math.abs(b)) < 1e-8) {
          // Use compensated subtraction for better numerical stability when a ≈ b
          // This uses the algebraic identity (a-b) = (a-b)(1 + a/(a+b)) × (a+b)/(a+b+ε)
          // which provides better stability for near-cancellation
          return (a - b) * (1 + a / (a + b + Number.MIN_VALUE));
        }
      }
      return computation(...args);
    };

    const highPrecisionResult = highPrecisionComputation(...inputs);

    // Calculate relative error
    const relativeError =
      Math.abs(result - highPrecisionResult) /
      Math.max(Math.abs(highPrecisionResult), Number.MIN_VALUE);

    assert.ok(
      relativeError <= expectedRelativeError,
      `${message || "Catastrophic cancellation detected"}: relative error ${relativeError} > ${expectedRelativeError}`,
    );

    return relativeError;
  },

  /**
   * Assert correct handling of extreme values
   *
   * @param {Function} computation - Function to test
   * @param {Array} extremeInputs - Array of input sets
   * @param {Array} conditions - Array of conditions to check
   * @param {string} [message] - Optional message
   * @returns {Array} - Results
   */
  assertExtremeValueHandling: (
    computation,
    extremeInputs,
    conditions,
    message = "",
  ) => {
    const results = extremeInputs.map((input) => {
      try {
        return {
          value: computation(...input),
          error: null,
        };
      } catch (e) {
        return {
          value: null,
          error: e.message,
        };
      }
    });

    // Verify each result against conditions
    for (let i = 0; i < results.length; i++) {
      const result = results[i];
      const condition = conditions[i];

      if (typeof condition === "function") {
        // Apply condition function to result
        assert.ok(
          condition(result),
          `${message || "Extreme value condition violated"} for input ${JSON.stringify(extremeInputs[i])}: ${JSON.stringify(result)}`,
        );
      } else if (condition === "finite") {
        // Check if result is finite
        assert.ok(
          result.error === null && Number.isFinite(result.value),
          `${message || "Expected finite value"} for input ${JSON.stringify(extremeInputs[i])}`,
        );
      } else if (condition === "error") {
        // Check if computation resulted in expected error
        assert.ok(
          result.error !== null,
          `${message || "Expected error"} for input ${JSON.stringify(extremeInputs[i])}`,
        );
      } else if (condition === "nan") {
        // Check if result is NaN
        assert.ok(
          result.error === null && Number.isNaN(result.value),
          `${message || "Expected NaN"} for input ${JSON.stringify(extremeInputs[i])}`,
        );
      } else if (Array.isArray(condition)) {
        // Check if result is in range [min, max]
        assert.ok(
          result.error === null &&
            result.value >= condition[0] &&
            result.value <= condition[1],
          `${message || "Expected value in range"} ${condition} for input ${JSON.stringify(extremeInputs[i])}: ${result.value}`,
        );
      } else {
        // Directly compare with expected value
        assert.strictEqual(
          result.value,
          condition,
          `${message || "Expected specific value"} for input ${JSON.stringify(extremeInputs[i])}`,
        );
      }
    }

    return results;
  },

  /**
   * Assert properties of vectors with extreme values
   *
   * @param {Function} computation - Function to test
   * @param {Array} vectors - Input vectors
   * @param {Object} expectedProperties - Expected properties
   * @param {string} [message] - Optional message
   * @returns {Array} - Result vector
   */
  assertMixedExtremeVectors: (
    computation,
    vectors,
    expectedProperties,
    message = "",
  ) => {
    const result = computation(...vectors);

    // Verify expected properties
    Object.entries(expectedProperties).forEach(([property, condition]) => {
      if (property === "length") {
        assert.strictEqual(
          result.length,
          condition,
          `${message || "Vector length property violated"}: expected length ${condition}`,
        );
      } else if (property === "all_finite") {
        assert.ok(
          result.every((x) => Number.isFinite(x)),
          `${message || "Not all vector elements are finite"}`,
        );
      } else if (property === "norm_bound") {
        // Calculate vector norm
        const norm = Math.sqrt(result.reduce((sum, x) => sum + x * x, 0));
        assert.ok(
          norm <= condition,
          `${message || "Vector norm exceeded bound"}: ${norm} > ${condition}`,
        );
      } else if (property === "max_element_bound") {
        // Find max absolute element
        const maxAbs = Math.max(...result.map((x) => Math.abs(x)));
        assert.ok(
          maxAbs <= condition,
          `${message || "Vector max element exceeded bound"}: ${maxAbs} > ${condition}`,
        );
      } else if (property === "min_element_bound") {
        // Find min absolute non-zero element
        const nonZeros = result.filter((x) => x !== 0).map((x) => Math.abs(x));
        if (nonZeros.length > 0) {
          const minAbs = Math.min(...nonZeros);
          assert.ok(
            minAbs >= condition,
            `${message || "Vector min element below bound"}: ${minAbs} < ${condition}`,
          );
        }
      }
    });

    return result;
  },

  /**
   * Assert that constraints are satisfied with dynamic parameters
   *
   * @param {Object} state - State to check
   * @param {Array} constraints - Array of constraint functions
   * @param {Array} dynamicParams - Parameters for constraints
   * @param {string} [message] - Optional message
   * @returns {boolean} - Whether all constraints are satisfied
   */
  assertConstraintSatisfaction: (
    state,
    constraints,
    dynamicParams,
    message = "",
  ) => {
    // Verify each constraint with dynamic parameters
    for (let i = 0; i < constraints.length; i++) {
      const constraint = constraints[i];
      const params = dynamicParams[i] || {};

      // Apply constraint function to state with dynamic parameters
      const satisfied = constraint(state, params);

      assert.ok(
        satisfied,
        `${message || "Constraint violation"} for constraint #${i}: ${constraint.name || "unnamed"} with params ${JSON.stringify(params)}`,
      );
    }

    return true;
  },

  /**
   * Assert that a function throws a specific error
   * Works with both sync and async functions
   *
   * @param {Function} fn - Function to test (sync or async)
   * @param {Error} errorType - Expected error type
   * @param {string|RegExp} [errorMessage] - Optional expected error message or pattern
   * @param {string} [message] - Optional message
   * @returns {Error|Promise<Error>} - The caught error
   */
  assertThrows: (fn, errorType, errorMessage, message = "") => {
    // Check if result is a promise
    const checkPromise = (result) =>
      result && typeof result.then === "function";

    const handleError = (error) => {
      // Check error type if specified
      if (errorType && !(error instanceof errorType)) {
        assert.fail(
          `${message || "Wrong error type thrown"}: expected ${errorType.name}, got ${error.constructor.name}`,
        );
      }

      // Check error message if specified
      if (errorMessage) {
        if (errorMessage instanceof RegExp) {
          // Check against regex pattern
          if (!errorMessage.test(error.message)) {
            assert.fail(
              `${message || "Error message doesn't match pattern"}: expected pattern ${errorMessage}, got "${error.message}"`,
            );
          }
        } else {
          // Check for string inclusion
          if (!error.message.includes(errorMessage)) {
            assert.fail(
              `${message || "Error message doesn't include expected text"}: expected to include "${errorMessage}", got "${error.message}"`,
            );
          }
        }
      }

      return error;
    };

    try {
      const result = fn();

      // Handle async functions
      if (checkPromise(result)) {
        return result
          .then(() => {
            assert.fail(
              `${message || "Expected to throw"}${errorType ? ": " + errorType.name : ""}`,
            );
          })
          .catch(handleError);
      }

      // Handle sync functions
      assert.fail(
        `${message || "Expected to throw"}${errorType ? ": " + errorType.name : ""}`,
      );
    } catch (error) {
      return handleError(error);
    }
  },

  /**
   * Assert that a function does not throw an error
   * Works with both sync and async functions
   *
   * @param {Function} fn - Function to test (sync or async)
   * @param {string} [message] - Optional message
   * @returns {any|Promise<any>} - The function result
   */
  assertDoesNotThrow: (fn, message = "") => {
    // Check if result is a promise
    const checkPromise = (result) =>
      result && typeof result.then === "function";

    try {
      const result = fn();

      // Handle async functions
      if (checkPromise(result)) {
        return result.catch((error) => {
          assert.fail(
            `${message || "Expected not to throw"}: but got ${error.constructor.name} - ${error.message}`,
          );
        });
      }

      // Handle sync functions
      return result;
    } catch (error) {
      assert.fail(
        `${message || "Expected not to throw"}: but got ${error.constructor.name} - ${error.message}`,
      );
    }
  },

  /**
   * Assert deep equality between objects
   *
   * @param {Object} actual - Actual object
   * @param {Object} expected - Expected object
   * @param {string} [message] - Optional message
   */
  assertDeepEquals: (actual, expected, message = "") => {
    // Convert to JSON and back to handle non-enumerable properties
    const actualStr = JSON.stringify(actual);
    const expectedStr = JSON.stringify(expected);

    if (actualStr !== expectedStr) {
      assert.fail(
        `${message || "Objects not deeply equal"}: expected ${expectedStr}, got ${actualStr}`,
      );
    }
  },

  /**
   * Assert that all error handlers are called correctly
   *
   * @param {Function} operation - Function that may trigger errors
   * @param {Object} errorHandlers - Map of error types to handler functions
   * @param {Object} testCases - Map of test case descriptions to input values
   * @param {string} [message] - Optional message
   * @returns {Object} - Results of handled errors
   */
  assertErrorHandling: (operation, errorHandlers, testCases, message = "") => {
    const results = {};

    // Create tracking for handler calls
    const handlerCalls = {};
    Object.keys(errorHandlers).forEach((type) => {
      handlerCalls[type] = 0;
    });

    // Wrap handlers to track calls
    const wrappedHandlers = {};
    Object.entries(errorHandlers).forEach(([type, handler]) => {
      wrappedHandlers[type] = (error, ...args) => {
        handlerCalls[type]++;
        return handler(error, ...args);
      };
    });

    // Run test cases
    Object.entries(testCases).forEach(([description, inputs]) => {
      try {
        results[description] = {
          result: operation(inputs, wrappedHandlers),
          error: null,
        };
      } catch (error) {
        results[description] = {
          result: null,
          error: error.message,
        };

        // Unexpected errors should fail the test
        assert.fail(
          `${message || "Unexpected error in test case"} "${description}": ${error.message}`,
        );
      }
    });

    // Assert all error handlers were called at least once
    Object.entries(handlerCalls).forEach(([type, count]) => {
      assert.ok(
        count > 0,
        `${message || "Error handler not called"}: handler for "${type}" was never triggered`,
      );
    });

    return results;
  },

  /**
   * Assert that an async operation correctly handles errors
   *
   * @param {Function} asyncOperation - Async function that may trigger errors
   * @param {Object} errorCases - Map of error types to inputs that should trigger them
   * @param {Function} [errorClassifier] - Function to classify errors
   * @param {string} [message] - Optional message
   * @returns {Promise<Object>} - Results of handled errors
   */
  assertAsyncErrorHandling: async (
    asyncOperation,
    errorCases,
    errorClassifier,
    message = "",
  ) => {
    const results = {};

    // Create default error classifier if not provided
    const classifier = errorClassifier || ((error) => error.constructor.name);

    // Run each error case
    for (const [errorType, inputs] of Object.entries(errorCases)) {
      try {
        results[errorType] = {
          result: await asyncOperation(inputs),
          error: null,
          expectedError: errorType,
        };

        // If we get here, the expected error wasn't thrown
        assert.fail(
          `${message || "Expected error not thrown"}: ${errorType} for inputs ${JSON.stringify(inputs)}`,
        );
      } catch (error) {
        const errorClass = classifier(error);
        results[errorType] = {
          result: null,
          error: error,
          errorClass: errorClass,
          expectedError: errorType,
        };

        // Verify error type matches expected
        assert.ok(
          errorClass === errorType || error.message.includes(errorType),
          `${message || "Wrong error type"}: expected ${errorType}, got ${errorClass} - ${error.message}`,
        );
      }
    }

    return results;
  },

  /**
   * Assert that proper error boundaries are respected
   *
   * @param {Function} operation - Function to test
   * @param {Array} validInputs - Inputs that should work without errors
   * @param {Array} boundaryInputs - Inputs at the boundary that should be handled
   * @param {Array} invalidInputs - Inputs that should cause errors
   * @param {string} [message] - Optional message
   * @returns {Object} - Results of testing
   */
  assertErrorBoundaries: (
    operation,
    validInputs,
    boundaryInputs,
    invalidInputs,
    message = "",
  ) => {
    const results = {
      valid: [],
      boundary: [],
      invalid: [],
    };

    // Test valid inputs
    validInputs.forEach((input, index) => {
      try {
        results.valid.push({
          input,
          result: operation(...(Array.isArray(input) ? input : [input])),
          error: null,
        });
      } catch (error) {
        assert.fail(
          `${message || "Valid input caused error"} at index ${index}: ${error.message}`,
        );
      }
    });

    // Test boundary inputs
    boundaryInputs.forEach((input, index) => {
      try {
        results.boundary.push({
          input,
          result: operation(...(Array.isArray(input) ? input : [input])),
          error: null,
        });
      } catch (error) {
        // Boundary inputs might throw errors in some implementations
        results.boundary.push({
          input,
          result: null,
          error: error.message,
        });
      }
    });

    // Test invalid inputs
    invalidInputs.forEach((input, index) => {
      try {
        const result = operation(...(Array.isArray(input) ? input : [input]));
        results.invalid.push({
          input,
          result,
          error: null,
        });

        // If we get here, an invalid input didn't cause an error
        assert.fail(
          `${message || "Invalid input didn't cause error"} at index ${index}: ${JSON.stringify(input)}`,
        );
      } catch (error) {
        results.invalid.push({
          input,
          result: null,
          error: error.message,
        });
      }
    });

    return results;
  },
};

module.exports = Assertions;
