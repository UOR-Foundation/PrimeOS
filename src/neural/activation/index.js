/**
 * PrimeOS JavaScript Library - Neural Activation Functions Module
 * Specialized and optimized activation functions with coherence awareness
 */

// Import the Prime object from core
const Prime = require("../../core");

// Create the Activation module using IIFE
(function () {
  /**
   * Activation functions collection
   * Provides optimized implementations of various activation functions with
   * gradient computation, in-place operations, and coherence monitoring
   */
  class ActivationFunctions {
    /**
     * Factory method to get an activation function by name
     * @param {string} name - Activation function name
     * @returns {Object} Activation functions (forward and backward)
     */
    static get(name) {
      // Validate input
      if (!name || typeof name !== "string") {
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Activation function name must be a non-empty string",
          { providedType: typeof name, providedValue: name },
          "INVALID_ACTIVATION_NAME"
        );
      }

      const lowerName = name.toLowerCase();

      switch (lowerName) {
        case "sigmoid":
          return {
            forward: ActivationFunctions.sigmoid,
            backward: ActivationFunctions.sigmoidGradient,
            inPlace: ActivationFunctions.sigmoidInPlace,
            gradientInPlace: ActivationFunctions.sigmoidGradientInPlace,
            isStable: true,
            rangeMin: 0,
            rangeMax: 1,
            name: "sigmoid"
          };
        case "tanh":
          return {
            forward: ActivationFunctions.tanh,
            backward: ActivationFunctions.tanhGradient,
            inPlace: ActivationFunctions.tanhInPlace,
            gradientInPlace: ActivationFunctions.tanhGradientInPlace,
            isStable: true,
            rangeMin: -1,
            rangeMax: 1,
            name: "tanh"
          };
        case "relu":
          return {
            forward: ActivationFunctions.relu,
            backward: ActivationFunctions.reluGradient,
            inPlace: ActivationFunctions.reluInPlace,
            gradientInPlace: ActivationFunctions.reluGradientInPlace,
            isStable: false, // May suffer from dying ReLU problem
            rangeMin: 0,
            rangeMax: Infinity,
            name: "relu"
          };
        case "leaky_relu":
          return {
            forward: ActivationFunctions.leakyRelu,
            backward: ActivationFunctions.leakyReluGradient,
            inPlace: ActivationFunctions.leakyReluInPlace,
            gradientInPlace: ActivationFunctions.leakyReluGradientInPlace,
            isStable: true,
            rangeMin: -Infinity,
            rangeMax: Infinity,
            name: "leaky_relu"
          };
        case "elu":
          return {
            forward: ActivationFunctions.elu,
            backward: ActivationFunctions.eluGradient,
            inPlace: ActivationFunctions.eluInPlace,
            gradientInPlace: ActivationFunctions.eluGradientInPlace,
            isStable: true,
            rangeMin: -1,
            rangeMax: Infinity,
            name: "elu"
          };
        case "selu":
          return {
            forward: ActivationFunctions.selu,
            backward: ActivationFunctions.seluGradient,
            inPlace: ActivationFunctions.seluInPlace,
            gradientInPlace: ActivationFunctions.seluGradientInPlace,
            isStable: true,
            rangeMin: -1.7581,
            rangeMax: Infinity,
            name: "selu"
          };
        case "softmax":
          return {
            forward: ActivationFunctions.softmax,
            backward: ActivationFunctions.softmaxGradient,
            inPlace: null, // Softmax can't be computed in-place
            gradientInPlace: null,
            isStable: true,
            rangeMin: 0,
            rangeMax: 1,
            name: "softmax"
          };
        case "linear":
        case "identity":
          return {
            forward: ActivationFunctions.linear,
            backward: ActivationFunctions.linearGradient,
            inPlace: ActivationFunctions.linearInPlace,
            gradientInPlace: ActivationFunctions.linearGradientInPlace,
            isStable: true,
            rangeMin: -Infinity,
            rangeMax: Infinity,
            name: lowerName
          };
        case "swish":
          return {
            forward: ActivationFunctions.swish,
            backward: ActivationFunctions.swishGradient,
            inPlace: ActivationFunctions.swishInPlace,
            gradientInPlace: ActivationFunctions.swishGradientInPlace,
            isStable: true,
            rangeMin: -0.278,
            rangeMax: Infinity,
            name: "swish"
          };
        default:
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            `Unknown activation function: ${name}`,
            { 
              providedName: name,
              availableActivations: [
                "sigmoid", "tanh", "relu", "leaky_relu", "elu", 
                "selu", "softmax", "linear", "identity", "swish"
              ]
            },
            "UNKNOWN_ACTIVATION_FUNCTION"
          );
      }
    }

    /**
     * Helper to create a new array or typed array matching input type
     * @private
     * @param {Array|TypedArray} input - Input array
     * @returns {Array|TypedArray} - New array of same type
     */
    static _createMatchingArray(input) {
      // Validate input
      if (!input) {
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Cannot create matching array for null or undefined input",
          { providedValue: input },
          "NULL_INPUT_ARRAY"
        );
      }

      if (!Array.isArray(input) && 
          !(input instanceof Float32Array) && 
          !(input instanceof Float64Array)) {
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Input must be an array or typed array",
          { 
            providedType: typeof input,
            isArray: Array.isArray(input)
          },
          "INVALID_INPUT_TYPE"
        );
      }

      if (!Number.isFinite(input.length) || input.length < 0) {
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Input array must have a valid length",
          { providedLength: input.length },
          "INVALID_ARRAY_LENGTH"
        );
      }
      
      // Create appropriate array type
      try {
        if (input instanceof Float32Array) {
          return new Float32Array(input.length);
        } else if (input instanceof Float64Array) {
          return new Float64Array(input.length);
        } else {
          return new Array(input.length);
        }
      } catch (error) {
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Failed to create matching array",
          { 
            originalError: error.message,
            inputLength: input.length,
            inputType: Array.isArray(input) ? "Array" : input.constructor.name
          },
          "ARRAY_CREATION_FAILED",
          error
        );
      }
    }

    /**
     * Vectorized sigmoid function: 1 / (1 + exp(-x))
     * @param {Array|TypedArray} x - Input values
     * @returns {Array|TypedArray} - Activated values
     */
    static sigmoid(x) {
      try {
        // Validate input
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to sigmoid cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        // Create result array with matching type
        const result = ActivationFunctions._createMatchingArray(x);

        // Process each element
        let hasNaN = false;
        let hasInf = false;
        
        for (let i = 0; i < x.length; i++) {
          // Validate input value
          if (!Number.isFinite(x[i])) {
            if (Number.isNaN(x[i])) {
              hasNaN = true;
              result[i] = 0.5; // Midpoint value as a reasonable fallback
            } else if (x[i] === Number.POSITIVE_INFINITY) {
              hasInf = true;
              result[i] = 1.0; // Limit of sigmoid as x→∞
            } else if (x[i] === Number.NEGATIVE_INFINITY) {
              hasInf = true;
              result[i] = 0.0; // Limit of sigmoid as x→-∞
            }
            continue;
          }

          // Numerical stability: Avoid overflow for large negative values
          if (x[i] < -709) {
            result[i] = 0;
          } else if (x[i] > 709) {
            result[i] = 1;
          } else {
            result[i] = 1 / (1 + Math.exp(-x[i]));
          }
        }

        // Warn about non-finite inputs if found
        if (hasNaN || hasInf) {
          console.warn(
            `Sigmoid activation received ${hasNaN ? 'NaN' : ''}${hasNaN && hasInf ? ' and ' : ''}${hasInf ? 'infinite' : ''} input values. Results may be unreliable.`
          );
        }

        return result;
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error applying sigmoid activation",
          { originalError: error.message },
          "SIGMOID_ACTIVATION_ERROR",
          error
        );
      }
    }

    /**
     * In-place sigmoid computation (modifies input array)
     * @param {Array|TypedArray} x - Input/output values
     */
    static sigmoidInPlace(x) {
      for (let i = 0; i < x.length; i++) {
        // Numerical stability
        if (x[i] < -709) {
          x[i] = 0;
        } else if (x[i] > 709) {
          x[i] = 1;
        } else {
          x[i] = 1 / (1 + Math.exp(-x[i]));
        }
      }
    }

    /**
     * Sigmoid gradient computation: sigmoid(x) * (1 - sigmoid(x))
     * @param {Array|TypedArray} x - Input values
     * @param {Array|TypedArray} y - Output of sigmoid(x)
     * @returns {Array|TypedArray} - Gradient values
     */
    static sigmoidGradient(x, y) {
      const result = ActivationFunctions._createMatchingArray(x);

      for (let i = 0; i < x.length; i++) {
        // Using pre-computed sigmoid values for efficiency
        result[i] = y[i] * (1 - y[i]);
      }

      return result;
    }

    /**
     * In-place sigmoid gradient computation (modifies input array)
     * @param {Array|TypedArray} grad - Gradient values (modified in-place)
     * @param {Array|TypedArray} y - Output of sigmoid(x)
     */
    static sigmoidGradientInPlace(grad, y) {
      for (let i = 0; i < grad.length; i++) {
        grad[i] *= y[i] * (1 - y[i]);
      }
    }

    /**
     * Vectorized hyperbolic tangent function
     * @param {Array|TypedArray} x - Input values
     * @returns {Array|TypedArray} - Activated values
     * @throws {ActivationError} - If input is invalid or operation fails
     */
    static tanh(x) {
      try {
        // Validate input
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to tanh cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        // Create result array with matching type
        const result = ActivationFunctions._createMatchingArray(x);

        // Process each element
        let hasNaN = false;
        let hasInf = false;
        
        for (let i = 0; i < x.length; i++) {
          // Validate input value
          if (!Number.isFinite(x[i])) {
            if (Number.isNaN(x[i])) {
              hasNaN = true;
              result[i] = 0; // tanh(NaN) = 0 as a reasonable fallback
            } else if (x[i] === Number.POSITIVE_INFINITY) {
              hasInf = true;
              result[i] = 1.0; // Limit of tanh as x→∞
            } else if (x[i] === Number.NEGATIVE_INFINITY) {
              hasInf = true;
              result[i] = -1.0; // Limit of tanh as x→-∞
            }
            continue;
          }

          // Apply tanh with numerical stability
          // Math.tanh is stable for a wide range of inputs, so we can use it directly
          result[i] = Math.tanh(x[i]);
        }

        // Warn about non-finite inputs if found
        if (hasNaN || hasInf) {
          console.warn(
            `Tanh activation received ${hasNaN ? 'NaN' : ''}${hasNaN && hasInf ? ' and ' : ''}${hasInf ? 'infinite' : ''} input values. Results may be unreliable.`
          );
        }

        return result;
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error applying tanh activation",
          { originalError: error.message },
          "TANH_ACTIVATION_ERROR",
          error
        );
      }
    }

    /**
     * In-place tanh computation (modifies input array)
     * @param {Array|TypedArray} x - Input/output values
     * @throws {ActivationError} - If input is invalid or operation fails
     */
    static tanhInPlace(x) {
      try {
        // Validate input
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to tanhInPlace cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        if (!Array.isArray(x) && 
            !(x instanceof Float32Array) && 
            !(x instanceof Float64Array)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input must be an array or typed array",
            { 
              providedType: typeof x,
              isArray: Array.isArray(x)
            },
            "INVALID_INPUT_TYPE"
          );
        }

        let hasNaN = false;
        let hasInf = false;

        for (let i = 0; i < x.length; i++) {
          // Handle non-finite inputs
          if (!Number.isFinite(x[i])) {
            if (Number.isNaN(x[i])) {
              hasNaN = true;
              x[i] = 0; // tanh(NaN) = 0 as a reasonable fallback
            } else if (x[i] === Number.POSITIVE_INFINITY) {
              hasInf = true;
              x[i] = 1.0; // Limit of tanh as x→∞
            } else if (x[i] === Number.NEGATIVE_INFINITY) {
              hasInf = true;
              x[i] = -1.0; // Limit of tanh as x→-∞
            }
            continue;
          }
          
          // Apply tanh
          x[i] = Math.tanh(x[i]);
        }

        // Warn about non-finite inputs if found
        if (hasNaN || hasInf) {
          console.warn(
            `TanhInPlace received ${hasNaN ? 'NaN' : ''}${hasNaN && hasInf ? ' and ' : ''}${hasInf ? 'infinite' : ''} input values. Results may be unreliable.`
          );
        }
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error applying in-place tanh activation",
          { originalError: error.message },
          "TANH_INPLACE_ERROR",
          error
        );
      }
    }

    /**
     * Tanh gradient computation: 1 - tanh(x)²
     * @param {Array|TypedArray} x - Input values
     * @param {Array|TypedArray} y - Output of tanh(x)
     * @returns {Array|TypedArray} - Gradient values
     * @throws {ActivationError} - If inputs are invalid or operation fails
     */
    static tanhGradient(x, y) {
      try {
        // Validate inputs
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to tanhGradient cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        if (!y) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Output (y) for tanhGradient cannot be null or undefined",
            { providedValue: y },
            "NULL_OUTPUT"
          );
        }

        if (x.length !== y.length) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input and output arrays must have the same length",
            { inputLength: x.length, outputLength: y.length },
            "LENGTH_MISMATCH"
          );
        }

        const result = ActivationFunctions._createMatchingArray(x);
        let hasNaN = false;

        for (let i = 0; i < x.length; i++) {
          // Handle non-finite values in y
          if (!Number.isFinite(y[i])) {
            hasNaN = true;
            result[i] = 0; // Avoid propagating NaN/Infinity
            continue;
          }

          // Using pre-computed tanh values for efficiency
          // Gradient of tanh(x) is 1 - tanh(x)²
          result[i] = 1 - y[i] * y[i];
        }

        // Warn about non-finite values if found
        if (hasNaN) {
          console.warn("TanhGradient received non-finite output values. Results may be unreliable.");
        }

        return result;
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error computing tanh gradient",
          { originalError: error.message },
          "TANH_GRADIENT_ERROR",
          error
        );
      }
    }

    /**
     * In-place tanh gradient computation (modifies input array)
     * @param {Array|TypedArray} grad - Gradient values (modified in-place)
     * @param {Array|TypedArray} y - Output of tanh(x)
     * @throws {ActivationError} - If inputs are invalid or operation fails
     */
    static tanhGradientInPlace(grad, y) {
      try {
        // Validate inputs
        if (!grad) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Gradient array for tanhGradientInPlace cannot be null or undefined",
            { providedValue: grad },
            "NULL_GRADIENT"
          );
        }

        if (!y) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Output (y) for tanhGradientInPlace cannot be null or undefined",
            { providedValue: y },
            "NULL_OUTPUT"
          );
        }

        if (grad.length !== y.length) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Gradient and output arrays must have the same length",
            { gradientLength: grad.length, outputLength: y.length },
            "LENGTH_MISMATCH"
          );
        }

        let hasNaN = false;

        for (let i = 0; i < grad.length; i++) {
          // Handle non-finite values
          if (!Number.isFinite(y[i]) || !Number.isFinite(grad[i])) {
            hasNaN = true;
            grad[i] = 0; // Avoid propagating NaN/Infinity
            continue;
          }

          // Gradient of tanh(x) is 1 - tanh(x)²
          grad[i] *= 1 - y[i] * y[i];
        }

        // Warn about non-finite values if found
        if (hasNaN) {
          console.warn("TanhGradientInPlace received non-finite values. Results may be unreliable.");
        }
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error computing in-place tanh gradient",
          { originalError: error.message },
          "TANH_GRADIENT_INPLACE_ERROR",
          error
        );
      }
    }

    /**
     * Rectified Linear Unit (ReLU) function: max(0, x)
     * @param {Array|TypedArray} x - Input values
     * @returns {Array|TypedArray} - Activated values
     * @throws {ActivationError} - If input is invalid or operation fails
     */
    static relu(x) {
      try {
        // Validate input
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to relu cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        // Create result array with matching type
        const result = ActivationFunctions._createMatchingArray(x);

        // Process each element
        let hasNaN = false;
        let hasInf = false;
        
        for (let i = 0; i < x.length; i++) {
          // Validate input value
          if (!Number.isFinite(x[i])) {
            if (Number.isNaN(x[i])) {
              hasNaN = true;
              result[i] = 0; // relu(NaN) = 0 as a reasonable fallback
            } else if (x[i] === Number.POSITIVE_INFINITY) {
              hasInf = true;
              result[i] = Number.POSITIVE_INFINITY; // relu(+∞) = +∞
            } else if (x[i] === Number.NEGATIVE_INFINITY) {
              hasInf = true;
              result[i] = 0; // relu(-∞) = 0
            }
            continue;
          }

          // Apply ReLU: max(0, x)
          result[i] = Math.max(0, x[i]);
        }

        // Warn about non-finite inputs if found
        if (hasNaN || hasInf) {
          console.warn(
            `ReLU activation received ${hasNaN ? 'NaN' : ''}${hasNaN && hasInf ? ' and ' : ''}${hasInf ? 'infinite' : ''} input values. Results may be unreliable.`
          );
        }

        return result;
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error applying relu activation",
          { originalError: error.message },
          "RELU_ACTIVATION_ERROR",
          error
        );
      }
    }

    /**
     * In-place ReLU computation (modifies input array)
     * @param {Array|TypedArray} x - Input/output values
     * @throws {ActivationError} - If input is invalid or operation fails
     */
    static reluInPlace(x) {
      try {
        // Validate input
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to reluInPlace cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        if (!Array.isArray(x) && 
            !(x instanceof Float32Array) && 
            !(x instanceof Float64Array)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input must be an array or typed array",
            { 
              providedType: typeof x,
              isArray: Array.isArray(x)
            },
            "INVALID_INPUT_TYPE"
          );
        }

        let hasNaN = false;
        let hasInf = false;

        for (let i = 0; i < x.length; i++) {
          // Handle non-finite inputs
          if (!Number.isFinite(x[i])) {
            if (Number.isNaN(x[i])) {
              hasNaN = true;
              x[i] = 0; // relu(NaN) = 0
            } else if (x[i] === Number.POSITIVE_INFINITY) {
              hasInf = true;
              // Leave positive infinity as is
            } else if (x[i] === Number.NEGATIVE_INFINITY) {
              hasInf = true;
              x[i] = 0; // relu(-∞) = 0
            }
            continue;
          }
          
          // Apply ReLU: max(0, x)
          if (x[i] < 0) {
            x[i] = 0;
          }
        }

        // Warn about non-finite inputs if found
        if (hasNaN || hasInf) {
          console.warn(
            `ReluInPlace received ${hasNaN ? 'NaN' : ''}${hasNaN && hasInf ? ' and ' : ''}${hasInf ? 'infinite' : ''} input values. Results may be unreliable.`
          );
        }
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error applying in-place relu activation",
          { originalError: error.message },
          "RELU_INPLACE_ERROR",
          error
        );
      }
    }

    /**
     * ReLU gradient computation: 1 if x > 0 else 0
     * @param {Array|TypedArray} x - Input values
     * @param {Array|TypedArray} y - Output of relu(x)
     * @returns {Array|TypedArray} - Gradient values
     * @throws {ActivationError} - If inputs are invalid or operation fails
     */
    static reluGradient(x, y) {
      try {
        // Validate inputs
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to reluGradient cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        if (!y) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Output (y) for reluGradient cannot be null or undefined",
            { providedValue: y },
            "NULL_OUTPUT"
          );
        }

        if (x.length !== y.length) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input and output arrays must have the same length",
            { inputLength: x.length, outputLength: y.length },
            "LENGTH_MISMATCH"
          );
        }

        const result = ActivationFunctions._createMatchingArray(x);
        let hasNaN = false;

        for (let i = 0; i < x.length; i++) {
          // Handle non-finite inputs
          if (!Number.isFinite(x[i])) {
            hasNaN = true;
            result[i] = 0; // Avoid propagating NaN/Infinity
            continue;
          }

          // ReLU gradient: 1 if x > 0 else 0
          result[i] = x[i] > 0 ? 1 : 0;
        }

        // Warn about non-finite values if found
        if (hasNaN) {
          console.warn("ReluGradient received non-finite input values. Results may be unreliable.");
        }

        return result;
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error computing relu gradient",
          { originalError: error.message },
          "RELU_GRADIENT_ERROR",
          error
        );
      }
    }

    /**
     * In-place ReLU gradient computation (modifies input array)
     * @param {Array|TypedArray} grad - Gradient values (modified in-place)
     * @param {Array|TypedArray} x - Original input values
     * @throws {ActivationError} - If inputs are invalid or operation fails
     */
    static reluGradientInPlace(grad, x) {
      try {
        // Validate inputs
        if (!grad) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Gradient array for reluGradientInPlace cannot be null or undefined",
            { providedValue: grad },
            "NULL_GRADIENT"
          );
        }

        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input (x) for reluGradientInPlace cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        if (grad.length !== x.length) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Gradient and input arrays must have the same length",
            { gradientLength: grad.length, inputLength: x.length },
            "LENGTH_MISMATCH"
          );
        }

        let hasNaN = false;

        for (let i = 0; i < grad.length; i++) {
          // Handle non-finite values
          if (!Number.isFinite(x[i]) || !Number.isFinite(grad[i])) {
            hasNaN = true;
            grad[i] = 0; // Avoid propagating NaN/Infinity
            continue;
          }

          // ReLU gradient: if x <= 0 then gradient is 0
          if (x[i] <= 0) {
            grad[i] = 0;
          }
        }

        // Warn about non-finite values if found
        if (hasNaN) {
          console.warn("ReluGradientInPlace received non-finite values. Results may be unreliable.");
        }
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error computing in-place relu gradient",
          { originalError: error.message },
          "RELU_GRADIENT_INPLACE_ERROR",
          error
        );
      }
    }

    /**
     * Leaky ReLU function: max(alpha * x, x)
     * @param {Array|TypedArray} x - Input values
     * @param {number} [alpha=0.01] - Leak parameter
     * @returns {Array|TypedArray} - Activated values
     * @throws {ActivationError} - If input is invalid or operation fails
     */
    static leakyRelu(x, alpha = 0.01) {
      try {
        // Validate input
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to leakyRelu cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }
        
        // Validate alpha
        if (!Number.isFinite(alpha)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Alpha parameter for leakyRelu must be a finite number",
            { providedAlpha: alpha },
            "INVALID_ALPHA"
          );
        }

        // Create result array with matching type
        const result = ActivationFunctions._createMatchingArray(x);

        // Process each element
        let hasNaN = false;
        let hasInf = false;
        
        for (let i = 0; i < x.length; i++) {
          // Validate input value
          if (!Number.isFinite(x[i])) {
            if (Number.isNaN(x[i])) {
              hasNaN = true;
              result[i] = 0; // leakyRelu(NaN) = 0 as fallback
            } else if (x[i] === Number.POSITIVE_INFINITY) {
              hasInf = true;
              result[i] = Number.POSITIVE_INFINITY; // leakyRelu(+∞) = +∞
            } else if (x[i] === Number.NEGATIVE_INFINITY) {
              hasInf = true;
              result[i] = Number.NEGATIVE_INFINITY * alpha; // leakyRelu(-∞) = -∞ * alpha
            }
            continue;
          }

          // Apply Leaky ReLU: x > 0 ? x : alpha * x
          result[i] = x[i] > 0 ? x[i] : alpha * x[i];
        }

        // Warn about non-finite inputs if found
        if (hasNaN || hasInf) {
          console.warn(
            `Leaky ReLU activation received ${hasNaN ? 'NaN' : ''}${hasNaN && hasInf ? ' and ' : ''}${hasInf ? 'infinite' : ''} input values. Results may be unreliable.`
          );
        }

        return result;
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error applying leaky relu activation",
          { 
            originalError: error.message,
            alpha 
          },
          "LEAKY_RELU_ACTIVATION_ERROR",
          error
        );
      }
    }

    /**
     * In-place Leaky ReLU computation (modifies input array)
     * @param {Array|TypedArray} x - Input/output values
     * @param {number} [alpha=0.01] - Leak parameter
     * @throws {ActivationError} - If input is invalid or operation fails
     */
    static leakyReluInPlace(x, alpha = 0.01) {
      try {
        // Validate input
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to leakyReluInPlace cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        // Validate alpha
        if (!Number.isFinite(alpha)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Alpha parameter for leakyReluInPlace must be a finite number",
            { providedAlpha: alpha },
            "INVALID_ALPHA"
          );
        }

        if (!Array.isArray(x) && 
            !(x instanceof Float32Array) && 
            !(x instanceof Float64Array)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input must be an array or typed array",
            { 
              providedType: typeof x,
              isArray: Array.isArray(x)
            },
            "INVALID_INPUT_TYPE"
          );
        }

        let hasNaN = false;
        let hasInf = false;

        for (let i = 0; i < x.length; i++) {
          // Handle non-finite inputs
          if (!Number.isFinite(x[i])) {
            if (Number.isNaN(x[i])) {
              hasNaN = true;
              x[i] = 0; // leakyRelu(NaN) = 0
            } else if (x[i] === Number.POSITIVE_INFINITY) {
              hasInf = true;
              // Leave positive infinity as is
            } else if (x[i] === Number.NEGATIVE_INFINITY) {
              hasInf = true;
              x[i] = Number.NEGATIVE_INFINITY * alpha; // leakyRelu(-∞) = -∞ * alpha
            }
            continue;
          }
          
          // Apply Leaky ReLU: if x < 0 then alpha * x
          if (x[i] < 0) {
            x[i] *= alpha;
          }
        }

        // Warn about non-finite inputs if found
        if (hasNaN || hasInf) {
          console.warn(
            `LeakyReluInPlace received ${hasNaN ? 'NaN' : ''}${hasNaN && hasInf ? ' and ' : ''}${hasInf ? 'infinite' : ''} input values. Results may be unreliable.`
          );
        }
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error applying in-place leaky relu activation",
          { 
            originalError: error.message,
            alpha 
          },
          "LEAKY_RELU_INPLACE_ERROR",
          error
        );
      }
    }

    /**
     * Leaky ReLU gradient computation
     * @param {Array|TypedArray} x - Input values
     * @param {Array|TypedArray} y - Output of leakyRelu(x)
     * @param {number} [alpha=0.01] - Leak parameter
     * @returns {Array|TypedArray} - Gradient values
     * @throws {ActivationError} - If inputs are invalid or operation fails
     */
    static leakyReluGradient(x, y, alpha = 0.01) {
      try {
        // Validate inputs
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to leakyReluGradient cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        if (!y) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Output (y) for leakyReluGradient cannot be null or undefined",
            { providedValue: y },
            "NULL_OUTPUT"
          );
        }

        // Validate alpha
        if (!Number.isFinite(alpha)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Alpha parameter for leakyReluGradient must be a finite number",
            { providedAlpha: alpha },
            "INVALID_ALPHA"
          );
        }

        if (x.length !== y.length) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input and output arrays must have the same length",
            { inputLength: x.length, outputLength: y.length },
            "LENGTH_MISMATCH"
          );
        }

        const result = ActivationFunctions._createMatchingArray(x);
        let hasNaN = false;

        for (let i = 0; i < x.length; i++) {
          // Handle non-finite inputs
          if (!Number.isFinite(x[i])) {
            hasNaN = true;
            result[i] = 0; // Avoid propagating NaN/Infinity
            continue;
          }

          // Leaky ReLU gradient: 1 if x > 0 else alpha
          result[i] = x[i] > 0 ? 1 : alpha;
        }

        // Warn about non-finite values if found
        if (hasNaN) {
          console.warn("LeakyReluGradient received non-finite input values. Results may be unreliable.");
        }

        return result;
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error computing leaky relu gradient",
          { 
            originalError: error.message,
            alpha
          },
          "LEAKY_RELU_GRADIENT_ERROR",
          error
        );
      }
    }

    /**
     * In-place Leaky ReLU gradient computation (modifies input array)
     * @param {Array|TypedArray} grad - Gradient values (modified in-place)
     * @param {Array|TypedArray} x - Original input values
     * @param {number} [alpha=0.01] - Leak parameter
     * @throws {ActivationError} - If inputs are invalid or operation fails
     */
    static leakyReluGradientInPlace(grad, x, alpha = 0.01) {
      try {
        // Validate inputs
        if (!grad) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Gradient array for leakyReluGradientInPlace cannot be null or undefined",
            { providedValue: grad },
            "NULL_GRADIENT"
          );
        }

        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input (x) for leakyReluGradientInPlace cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        // Validate alpha
        if (!Number.isFinite(alpha)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Alpha parameter for leakyReluGradientInPlace must be a finite number",
            { providedAlpha: alpha },
            "INVALID_ALPHA"
          );
        }

        if (grad.length !== x.length) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Gradient and input arrays must have the same length",
            { gradientLength: grad.length, inputLength: x.length },
            "LENGTH_MISMATCH"
          );
        }

        let hasNaN = false;

        for (let i = 0; i < grad.length; i++) {
          // Handle non-finite values
          if (!Number.isFinite(x[i]) || !Number.isFinite(grad[i])) {
            hasNaN = true;
            grad[i] = 0; // Avoid propagating NaN/Infinity
            continue;
          }

          // Leaky ReLU gradient: if x <= 0 then multiply by alpha
          if (x[i] <= 0) {
            grad[i] *= alpha;
          }
        }

        // Warn about non-finite values if found
        if (hasNaN) {
          console.warn("LeakyReluGradientInPlace received non-finite values. Results may be unreliable.");
        }
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error computing in-place leaky relu gradient",
          { 
            originalError: error.message,
            alpha
          },
          "LEAKY_RELU_GRADIENT_INPLACE_ERROR",
          error
        );
      }
    }

    /**
     * Exponential Linear Unit (ELU) function: x if x > 0 else alpha * (exp(x) - 1)
     * @param {Array|TypedArray} x - Input values
     * @param {number} [alpha=1.0] - Alpha parameter
     * @returns {Array|TypedArray} - Activated values
     * @throws {ActivationError} - If input is invalid or operation fails
     */
    static elu(x, alpha = 1.0) {
      try {
        // Validate input
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to elu cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }
        
        // Validate alpha
        if (!Number.isFinite(alpha)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Alpha parameter for elu must be a finite number",
            { providedAlpha: alpha },
            "INVALID_ALPHA"
          );
        }

        // Create result array with matching type
        const result = ActivationFunctions._createMatchingArray(x);

        // Process each element
        let hasNaN = false;
        let hasInf = false;
        
        for (let i = 0; i < x.length; i++) {
          // Validate input value
          if (!Number.isFinite(x[i])) {
            if (Number.isNaN(x[i])) {
              hasNaN = true;
              result[i] = 0; // elu(NaN) = 0 as fallback
            } else if (x[i] === Number.POSITIVE_INFINITY) {
              hasInf = true;
              result[i] = Number.POSITIVE_INFINITY; // elu(+∞) = +∞
            } else if (x[i] === Number.NEGATIVE_INFINITY) {
              hasInf = true;
              result[i] = -alpha; // elu(-∞) = -alpha (limit of alpha * (exp(-∞) - 1))
            }
            continue;
          }

          // Apply ELU with numerical stability
          if (x[i] > 0) {
            result[i] = x[i];
          } else {
            // Avoid overflow for very negative values: exp(x) becomes 0 when x < -745
            if (x[i] < -745) {
              result[i] = -alpha; // effectively alpha * (0 - 1)
            } else {
              result[i] = alpha * (Math.exp(x[i]) - 1);
            }
          }
        }

        // Warn about non-finite inputs if found
        if (hasNaN || hasInf) {
          console.warn(
            `ELU activation received ${hasNaN ? 'NaN' : ''}${hasNaN && hasInf ? ' and ' : ''}${hasInf ? 'infinite' : ''} input values. Results may be unreliable.`
          );
        }

        return result;
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error applying elu activation",
          { 
            originalError: error.message,
            alpha 
          },
          "ELU_ACTIVATION_ERROR",
          error
        );
      }
    }

    /**
     * In-place ELU computation (modifies input array)
     * @param {Array|TypedArray} x - Input/output values
     * @param {number} [alpha=1.0] - Alpha parameter
     * @throws {ActivationError} - If input is invalid or operation fails
     */
    static eluInPlace(x, alpha = 1.0) {
      try {
        // Validate input
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to eluInPlace cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        // Validate alpha
        if (!Number.isFinite(alpha)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Alpha parameter for eluInPlace must be a finite number",
            { providedAlpha: alpha },
            "INVALID_ALPHA"
          );
        }

        if (!Array.isArray(x) && 
            !(x instanceof Float32Array) && 
            !(x instanceof Float64Array)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input must be an array or typed array",
            { 
              providedType: typeof x,
              isArray: Array.isArray(x)
            },
            "INVALID_INPUT_TYPE"
          );
        }

        let hasNaN = false;
        let hasInf = false;

        for (let i = 0; i < x.length; i++) {
          // Handle non-finite inputs
          if (!Number.isFinite(x[i])) {
            if (Number.isNaN(x[i])) {
              hasNaN = true;
              x[i] = 0; // elu(NaN) = 0
            } else if (x[i] === Number.POSITIVE_INFINITY) {
              hasInf = true;
              // Leave positive infinity as is
            } else if (x[i] === Number.NEGATIVE_INFINITY) {
              hasInf = true;
              x[i] = -alpha; // elu(-∞) = -alpha
            }
            continue;
          }
          
          // Apply ELU: if x <= 0 then alpha * (exp(x) - 1)
          if (x[i] <= 0) {
            // Avoid overflow for very negative values
            if (x[i] < -745) {
              x[i] = -alpha;
            } else {
              x[i] = alpha * (Math.exp(x[i]) - 1);
            }
          }
        }

        // Warn about non-finite inputs if found
        if (hasNaN || hasInf) {
          console.warn(
            `EluInPlace received ${hasNaN ? 'NaN' : ''}${hasNaN && hasInf ? ' and ' : ''}${hasInf ? 'infinite' : ''} input values. Results may be unreliable.`
          );
        }
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error applying in-place elu activation",
          { 
            originalError: error.message,
            alpha 
          },
          "ELU_INPLACE_ERROR",
          error
        );
      }
    }

    /**
     * ELU gradient computation
     * @param {Array|TypedArray} x - Input values
     * @param {Array|TypedArray} y - Output of elu(x)
     * @param {number} [alpha=1.0] - Alpha parameter
     * @returns {Array|TypedArray} - Gradient values
     * @throws {ActivationError} - If inputs are invalid or operation fails
     */
    static eluGradient(x, y, alpha = 1.0) {
      try {
        // Validate inputs
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to eluGradient cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        if (!y) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Output (y) for eluGradient cannot be null or undefined",
            { providedValue: y },
            "NULL_OUTPUT"
          );
        }

        // Validate alpha
        if (!Number.isFinite(alpha)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Alpha parameter for eluGradient must be a finite number",
            { providedAlpha: alpha },
            "INVALID_ALPHA"
          );
        }

        if (x.length !== y.length) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input and output arrays must have the same length",
            { inputLength: x.length, outputLength: y.length },
            "LENGTH_MISMATCH"
          );
        }

        const result = ActivationFunctions._createMatchingArray(x);
        let hasNaN = false;

        for (let i = 0; i < x.length; i++) {
          // Handle non-finite inputs
          if (!Number.isFinite(x[i]) || !Number.isFinite(y[i])) {
            hasNaN = true;
            result[i] = 0; // Avoid propagating NaN/Infinity
            continue;
          }

          // ELU gradient: 1 if x > 0 else y + alpha
          result[i] = x[i] > 0 ? 1 : y[i] + alpha;
        }

        // Warn about non-finite values if found
        if (hasNaN) {
          console.warn("EluGradient received non-finite values. Results may be unreliable.");
        }

        return result;
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error computing elu gradient",
          { 
            originalError: error.message,
            alpha
          },
          "ELU_GRADIENT_ERROR",
          error
        );
      }
    }

    /**
     * In-place ELU gradient computation (modifies input array)
     * @param {Array|TypedArray} grad - Gradient values (modified in-place)
     * @param {Array|TypedArray} x - Original input values
     * @param {Array|TypedArray} y - Output of elu(x)
     * @param {number} [alpha=1.0] - Alpha parameter
     * @throws {ActivationError} - If inputs are invalid or operation fails
     */
    static eluGradientInPlace(grad, x, y, alpha = 1.0) {
      try {
        // Validate inputs
        if (!grad) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Gradient array for eluGradientInPlace cannot be null or undefined",
            { providedValue: grad },
            "NULL_GRADIENT"
          );
        }

        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input (x) for eluGradientInPlace cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        if (!y) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Output (y) for eluGradientInPlace cannot be null or undefined",
            { providedValue: y },
            "NULL_OUTPUT"
          );
        }

        // Validate alpha
        if (!Number.isFinite(alpha)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Alpha parameter for eluGradientInPlace must be a finite number",
            { providedAlpha: alpha },
            "INVALID_ALPHA"
          );
        }

        if (grad.length !== x.length || grad.length !== y.length) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Gradient, input, and output arrays must have the same length",
            { 
              gradientLength: grad.length, 
              inputLength: x.length,
              outputLength: y.length
            },
            "LENGTH_MISMATCH"
          );
        }

        let hasNaN = false;

        for (let i = 0; i < grad.length; i++) {
          // Handle non-finite values
          if (!Number.isFinite(x[i]) || !Number.isFinite(y[i]) || !Number.isFinite(grad[i])) {
            hasNaN = true;
            grad[i] = 0; // Avoid propagating NaN/Infinity
            continue;
          }

          // ELU gradient: if x <= 0 then multiply by (y + alpha)
          if (x[i] <= 0) {
            grad[i] *= (y[i] + alpha);
          }
        }

        // Warn about non-finite values if found
        if (hasNaN) {
          console.warn("EluGradientInPlace received non-finite values. Results may be unreliable.");
        }
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error computing in-place elu gradient",
          { 
            originalError: error.message,
            alpha
          },
          "ELU_GRADIENT_INPLACE_ERROR",
          error
        );
      }
    }

    /**
     * Scaled Exponential Linear Unit (SELU) function
     * Self-normalizing variant of ELU
     * @param {Array|TypedArray} x - Input values
     * @returns {Array|TypedArray} - Activated values
     * @throws {ActivationError} - If input is invalid or operation fails
     */
    static selu(x) {
      try {
        // SELU parameters (fixed values from the paper)
        const alpha = 1.6732632423543772848170429916717;
        const scale = 1.0507009873554804934193349852946;

        // Validate input
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to selu cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        // Create result array with matching type
        const result = ActivationFunctions._createMatchingArray(x);

        // Process each element
        let hasNaN = false;
        let hasInf = false;
        
        for (let i = 0; i < x.length; i++) {
          // Validate input value
          if (!Number.isFinite(x[i])) {
            if (Number.isNaN(x[i])) {
              hasNaN = true;
              result[i] = 0; // selu(NaN) = 0 as fallback
            } else if (x[i] === Number.POSITIVE_INFINITY) {
              hasInf = true;
              result[i] = Number.POSITIVE_INFINITY; // selu(+∞) = +∞ * scale
            } else if (x[i] === Number.NEGATIVE_INFINITY) {
              hasInf = true;
              result[i] = -scale * alpha; // selu(-∞) = -scale * alpha
            }
            continue;
          }

          // Apply SELU with numerical stability
          if (x[i] > 0) {
            result[i] = scale * x[i];
          } else {
            // Avoid overflow for very negative values: exp(x) becomes 0 when x < -745
            if (x[i] < -745) {
              result[i] = -scale * alpha; // scale * alpha * (0 - 1)
            } else {
              result[i] = scale * alpha * (Math.exp(x[i]) - 1);
            }
          }
        }

        // Warn about non-finite inputs if found
        if (hasNaN || hasInf) {
          console.warn(
            `SELU activation received ${hasNaN ? 'NaN' : ''}${hasNaN && hasInf ? ' and ' : ''}${hasInf ? 'infinite' : ''} input values. Results may be unreliable.`
          );
        }

        return result;
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error applying selu activation",
          { originalError: error.message },
          "SELU_ACTIVATION_ERROR",
          error
        );
      }
    }

    /**
     * In-place SELU computation (modifies input array)
     * @param {Array|TypedArray} x - Input/output values
     * @throws {ActivationError} - If input is invalid or operation fails
     */
    static seluInPlace(x) {
      try {
        // SELU parameters (fixed values)
        const alpha = 1.6732632423543772848170429916717;
        const scale = 1.0507009873554804934193349852946;

        // Validate input
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to seluInPlace cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        if (!Array.isArray(x) && 
            !(x instanceof Float32Array) && 
            !(x instanceof Float64Array)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input must be an array or typed array",
            { 
              providedType: typeof x,
              isArray: Array.isArray(x)
            },
            "INVALID_INPUT_TYPE"
          );
        }

        let hasNaN = false;
        let hasInf = false;

        for (let i = 0; i < x.length; i++) {
          // Handle non-finite inputs
          if (!Number.isFinite(x[i])) {
            if (Number.isNaN(x[i])) {
              hasNaN = true;
              x[i] = 0; // selu(NaN) = 0
            } else if (x[i] === Number.POSITIVE_INFINITY) {
              hasInf = true;
              // Leave positive infinity as is, but scale it
              x[i] = Number.POSITIVE_INFINITY; // scale * infinity is still infinity
            } else if (x[i] === Number.NEGATIVE_INFINITY) {
              hasInf = true;
              x[i] = -scale * alpha; // selu(-∞) = -scale * alpha
            }
            continue;
          }
          
          // Apply SELU: scale * (x if x > 0 else alpha * (exp(x) - 1))
          if (x[i] <= 0) {
            // Avoid overflow for very negative values
            if (x[i] < -745) {
              x[i] = -scale * alpha;
            } else {
              x[i] = scale * alpha * (Math.exp(x[i]) - 1);
            }
          } else {
            x[i] *= scale;
          }
        }

        // Warn about non-finite inputs if found
        if (hasNaN || hasInf) {
          console.warn(
            `SeluInPlace received ${hasNaN ? 'NaN' : ''}${hasNaN && hasInf ? ' and ' : ''}${hasInf ? 'infinite' : ''} input values. Results may be unreliable.`
          );
        }
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error applying in-place selu activation",
          { originalError: error.message },
          "SELU_INPLACE_ERROR",
          error
        );
      }
    }

    /**
     * SELU gradient computation
     * @param {Array|TypedArray} x - Input values
     * @param {Array|TypedArray} y - Output of selu(x)
     * @returns {Array|TypedArray} - Gradient values
     * @throws {ActivationError} - If inputs are invalid or operation fails
     */
    static seluGradient(x, y) {
      try {
        // SELU parameters (fixed values)
        const alpha = 1.6732632423543772848170429916717;
        const scale = 1.0507009873554804934193349852946;

        // Validate inputs
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to seluGradient cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        if (!y) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Output (y) for seluGradient cannot be null or undefined",
            { providedValue: y },
            "NULL_OUTPUT"
          );
        }

        if (x.length !== y.length) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input and output arrays must have the same length",
            { inputLength: x.length, outputLength: y.length },
            "LENGTH_MISMATCH"
          );
        }

        const result = ActivationFunctions._createMatchingArray(x);
        let hasNaN = false;

        for (let i = 0; i < x.length; i++) {
          // Handle non-finite inputs
          if (!Number.isFinite(x[i]) || !Number.isFinite(y[i])) {
            hasNaN = true;
            result[i] = 0; // Avoid propagating NaN/Infinity
            continue;
          }

          // SELU gradient calculation
          if (x[i] > 0) {
            result[i] = scale;
          } else {
            // For x <= 0, gradient is: scale * alpha * exp(x)
            // Note: y = scale * alpha * (exp(x) - 1) for x <= 0
            // So we need to add back scale * alpha to get scale * alpha * exp(x)
            result[i] = y[i] + scale * alpha;
          }
        }

        // Warn about non-finite values if found
        if (hasNaN) {
          console.warn("SeluGradient received non-finite values. Results may be unreliable.");
        }

        return result;
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error computing selu gradient",
          { originalError: error.message },
          "SELU_GRADIENT_ERROR",
          error
        );
      }
    }

    /**
     * In-place SELU gradient computation (modifies input array)
     * @param {Array|TypedArray} grad - Gradient values (modified in-place)
     * @param {Array|TypedArray} x - Original input values
     * @param {Array|TypedArray} y - Output of selu(x)
     * @throws {ActivationError} - If inputs are invalid or operation fails
     */
    static seluGradientInPlace(grad, x, y) {
      try {
        // SELU parameters (fixed values)
        const alpha = 1.6732632423543772848170429916717;
        const scale = 1.0507009873554804934193349852946;

        // Validate inputs
        if (!grad) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Gradient array for seluGradientInPlace cannot be null or undefined",
            { providedValue: grad },
            "NULL_GRADIENT"
          );
        }

        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input (x) for seluGradientInPlace cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        if (!y) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Output (y) for seluGradientInPlace cannot be null or undefined",
            { providedValue: y },
            "NULL_OUTPUT"
          );
        }

        if (grad.length !== x.length || grad.length !== y.length) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Gradient, input, and output arrays must have the same length",
            { 
              gradientLength: grad.length, 
              inputLength: x.length,
              outputLength: y.length
            },
            "LENGTH_MISMATCH"
          );
        }

        let hasNaN = false;

        for (let i = 0; i < grad.length; i++) {
          // Handle non-finite values
          if (!Number.isFinite(x[i]) || !Number.isFinite(y[i]) || !Number.isFinite(grad[i])) {
            hasNaN = true;
            grad[i] = 0; // Avoid propagating NaN/Infinity
            continue;
          }

          // SELU gradient calculation
          if (x[i] > 0) {
            grad[i] *= scale;
          } else {
            grad[i] *= (y[i] + scale * alpha);
          }
        }

        // Warn about non-finite values if found
        if (hasNaN) {
          console.warn("SeluGradientInPlace received non-finite values. Results may be unreliable.");
        }
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error computing in-place selu gradient",
          { originalError: error.message },
          "SELU_GRADIENT_INPLACE_ERROR",
          error
        );
      }
    }

    /**
     * Softmax function: exp(x_i) / sum(exp(x_j))
     * Transforms input into a probability distribution
     * Note: This function can't be applied element-wise
     * @param {Array|TypedArray} x - Input values
     * @returns {Array|TypedArray} - Softmax values
     * @throws {ActivationError} - If input is invalid or operation fails
     */
    static softmax(x) {
      try {
        // Validate input
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to softmax cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        if (x.length === 0) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to softmax must not be empty",
            { providedLength: 0 },
            "EMPTY_INPUT"
          );
        }

        // Create result array with matching type
        const result = ActivationFunctions._createMatchingArray(x);

        // Check for non-finite values
        let hasNaN = false;
        let hasInf = false;

        // Find max for numerical stability
        let maxVal = Number.NEGATIVE_INFINITY;
        for (let i = 0; i < x.length; i++) {
          if (!Number.isFinite(x[i])) {
            if (Number.isNaN(x[i])) {
              hasNaN = true;
            } else {
              hasInf = true;
            }
          } else if (x[i] > maxVal) {
            maxVal = x[i];
          }
        }

        // Handle case where all values are non-finite
        if (maxVal === Number.NEGATIVE_INFINITY) {
          // Return uniform distribution as fallback
          const uniformValue = 1.0 / x.length;
          for (let i = 0; i < x.length; i++) {
            result[i] = uniformValue;
          }
          
          if (hasNaN || hasInf) {
            console.warn(
              `Softmax received all ${hasNaN ? 'NaN' : ''}${hasNaN && hasInf ? ' and ' : ''}${hasInf ? 'infinite' : ''} values. Returning uniform distribution.`
            );
          }
          
          return result;
        }

        // Calculate exp(x - max) and sum
        let sum = 0;
        for (let i = 0; i < x.length; i++) {
          if (!Number.isFinite(x[i])) {
            if (Number.isNaN(x[i])) {
              // NaN inputs get 0 probability
              result[i] = 0;
            } else if (x[i] === Number.POSITIVE_INFINITY) {
              // If we have positive infinity input(s), they should get all probability mass
              // We'll handle this after the loop to ensure we catch all such cases
              result[i] = 1; // Temporary value
            } else {
              // Negative infinity gets 0 probability
              result[i] = 0;
            }
          } else {
            // Numerical stability: avoid overflow by subtracting max
            const expVal = Math.exp(x[i] - maxVal);
            result[i] = expVal;
            sum += expVal;
          }
        }

        // Handle special case with positive infinity values
        if (hasInf) {
          // Count positive infinities
          let posInfCount = 0;
          for (let i = 0; i < x.length; i++) {
            if (x[i] === Number.POSITIVE_INFINITY) {
              posInfCount++;
            }
          }

          if (posInfCount > 0) {
            // Positive infinities share probability equally
            const infProb = 1.0 / posInfCount;
            for (let i = 0; i < x.length; i++) {
              result[i] = x[i] === Number.POSITIVE_INFINITY ? infProb : 0;
            }
            
            console.warn(
              `Softmax received positive infinite values. Assigning equal probability (${infProb.toFixed(6)}) to each.`
            );
            
            return result;
          }
        }

        // Normalize by sum for valid inputs
        if (sum > 0) {
          for (let i = 0; i < x.length; i++) {
            result[i] /= sum;
          }
        } else {
          // If sum is 0 or negative (extremely rare but possible due to numerical issues),
          // return uniform distribution as fallback
          const uniformValue = 1.0 / x.length;
          for (let i = 0; i < x.length; i++) {
            result[i] = uniformValue;
          }
          
          console.warn(
            "Softmax calculation resulted in zero sum. Returning uniform distribution."
          );
        }

        // Warn about non-finite inputs if found
        if (hasNaN || hasInf) {
          console.warn(
            `Softmax activation received ${hasNaN ? 'NaN' : ''}${hasNaN && hasInf ? ' and ' : ''}${hasInf ? 'infinite' : ''} input values. Results may be unreliable.`
          );
        }

        return result;
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error applying softmax activation",
          { originalError: error.message },
          "SOFTMAX_ACTIVATION_ERROR",
          error
        );
      }
    }

    /**
     * Softmax gradient computation
     * Note: This implementation assumes a specific loss function (cross-entropy)
     * It's a simplification for common use cases
     * @param {Array|TypedArray} x - Input values
     * @param {Array|TypedArray} y - Output of softmax(x)
     * @param {Array|TypedArray} dy - Upstream gradient
     * @returns {Array|TypedArray} - Gradient values
     * @throws {ActivationError} - If inputs are invalid or operation fails
     */
    static softmaxGradient(x, y, dy) {
      try {
        // Validate inputs
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to softmaxGradient cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        if (!y) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Output (y) for softmaxGradient cannot be null or undefined",
            { providedValue: y },
            "NULL_OUTPUT"
          );
        }

        if (x.length !== y.length) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input and output arrays must have the same length",
            { inputLength: x.length, outputLength: y.length },
            "LENGTH_MISMATCH"
          );
        }

        // Create result array
        const result = ActivationFunctions._createMatchingArray(x);
        let hasNaN = false;

        // For cross-entropy loss with softmax, gradient is typically (y - targets)
        // which is usually passed directly in dy, so we just copy dy if provided
        if (dy) {
          if (dy.length !== x.length) {
            throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
              "Upstream gradient (dy) length must match input length",
              { dyLength: dy.length, inputLength: x.length },
              "GRADIENT_LENGTH_MISMATCH"
            );
          }

          for (let i = 0; i < result.length; i++) {
            // Handle non-finite values
            if (!Number.isFinite(dy[i])) {
              hasNaN = true;
              result[i] = 0; // Avoid propagating NaN/Infinity
            } else {
              result[i] = dy[i];
            }
          }
        } else {
          // If no gradient is provided, just return ones (identity gradient)
          // This is a simplification but works for most common use cases
          for (let i = 0; i < result.length; i++) {
            result[i] = 1;
          }
        }

        // Warn about non-finite values if found
        if (hasNaN) {
          console.warn("SoftmaxGradient received non-finite values. Results may be unreliable.");
        }

        return result;
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error computing softmax gradient",
          { originalError: error.message },
          "SOFTMAX_GRADIENT_ERROR",
          error
        );
      }
    }

    /**
     * Linear/Identity activation function
     * @param {Array|TypedArray} x - Input values
     * @returns {Array|TypedArray} - Same values (copy)
     * @throws {ActivationError} - If input is invalid or operation fails
     */
    static linear(x) {
      try {
        // Validate input
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to linear activation cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        // Create result array with matching type
        const result = ActivationFunctions._createMatchingArray(x);
        
        // Process each element
        let hasNaN = false;
        let hasInf = false;
        
        for (let i = 0; i < x.length; i++) {
          // Check for non-finite values
          if (!Number.isFinite(x[i])) {
            if (Number.isNaN(x[i])) {
              hasNaN = true;
            } else {
              hasInf = true;
            }
          }
          
          // Copy value (identity function)
          result[i] = x[i];
        }
        
        // Warn about non-finite inputs if found
        if (hasNaN || hasInf) {
          console.warn(
            `Linear activation received ${hasNaN ? 'NaN' : ''}${hasNaN && hasInf ? ' and ' : ''}${hasInf ? 'infinite' : ''} input values. These will be passed through unchanged.`
          );
        }

        return result;
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error applying linear activation",
          { originalError: error.message },
          "LINEAR_ACTIVATION_ERROR",
          error
        );
      }
    }

    /**
     * In-place linear activation (no-op, but included for API consistency)
     * @param {Array|TypedArray} x - Input/output values
     * @throws {ActivationError} - If input is invalid
     */
    static linearInPlace(x) {
      try {
        // Validate input
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to linearInPlace cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        if (!Array.isArray(x) && 
            !(x instanceof Float32Array) && 
            !(x instanceof Float64Array)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input must be an array or typed array",
            { 
              providedType: typeof x,
              isArray: Array.isArray(x)
            },
            "INVALID_INPUT_TYPE"
          );
        }
        
        // No operation needed - values remain unchanged
        // Just check for non-finite values to issue warning
        let hasNaN = false;
        let hasInf = false;
        
        for (let i = 0; i < x.length; i++) {
          if (!Number.isFinite(x[i])) {
            if (Number.isNaN(x[i])) {
              hasNaN = true;
            } else {
              hasInf = true;
            }
            
            if (hasNaN && hasInf) {
              break; // Found both types, no need to keep checking
            }
          }
        }
        
        // Warn about non-finite inputs if found
        if (hasNaN || hasInf) {
          console.warn(
            `LinearInPlace received ${hasNaN ? 'NaN' : ''}${hasNaN && hasInf ? ' and ' : ''}${hasInf ? 'infinite' : ''} input values. These will remain unchanged.`
          );
        }
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error applying in-place linear activation",
          { originalError: error.message },
          "LINEAR_INPLACE_ERROR",
          error
        );
      }
    }

    /**
     * Linear/Identity gradient (always 1)
     * @param {Array|TypedArray} x - Input values
     * @returns {Array|TypedArray} - Gradient values (all 1)
     * @throws {ActivationError} - If input is invalid or operation fails
     */
    static linearGradient(x) {
      try {
        // Validate input
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to linearGradient cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        // Create result array with matching type
        const result = ActivationFunctions._createMatchingArray(x);

        // Fill with 1s (identity function derivative)
        for (let i = 0; i < x.length; i++) {
          result[i] = 1;
        }

        return result;
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error computing linear gradient",
          { originalError: error.message },
          "LINEAR_GRADIENT_ERROR",
          error
        );
      }
    }

    /**
     * In-place linear gradient computation (no change to gradient values)
     * @param {Array|TypedArray} grad - Gradient values (unmodified)
     * @throws {ActivationError} - If input is invalid
     */
    static linearGradientInPlace(grad) {
      try {
        // Validate input
        if (!grad) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Gradient array for linearGradientInPlace cannot be null or undefined",
            { providedValue: grad },
            "NULL_GRADIENT"
          );
        }

        if (!Array.isArray(grad) && 
            !(grad instanceof Float32Array) && 
            !(grad instanceof Float64Array)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Gradient must be an array or typed array",
            { 
              providedType: typeof grad,
              isArray: Array.isArray(grad)
            },
            "INVALID_GRADIENT_TYPE"
          );
        }
        
        // No operation needed - gradient is unchanged
        // Linear function's derivative is 1, so we keep gradient as is
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error computing in-place linear gradient",
          { originalError: error.message },
          "LINEAR_GRADIENT_INPLACE_ERROR",
          error
        );
      }
    }

    /**
     * Swish activation function: x * sigmoid(x)
     * @param {Array|TypedArray} x - Input values
     * @returns {Array|TypedArray} - Activated values
     * @throws {ActivationError} - If input is invalid or operation fails
     */
    static swish(x) {
      try {
        // Validate input
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to swish cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        // Create result array with matching type
        const result = ActivationFunctions._createMatchingArray(x);

        // Process each element
        let hasNaN = false;
        let hasInf = false;
        
        for (let i = 0; i < x.length; i++) {
          // Check for non-finite values
          if (!Number.isFinite(x[i])) {
            if (Number.isNaN(x[i])) {
              hasNaN = true;
              result[i] = 0; // swish(NaN) = 0 as a fallback
              continue;
            } else if (x[i] === Number.POSITIVE_INFINITY) {
              hasInf = true;
              result[i] = Number.POSITIVE_INFINITY; // swish(+∞) = +∞
              continue;
            } else if (x[i] === Number.NEGATIVE_INFINITY) {
              hasInf = true;
              result[i] = 0; // swish(-∞) = -∞ * 0 = 0
              continue;
            }
          }

          // Calculate sigmoid with numerical stability
          let sigX;
          if (x[i] < -709) {
            sigX = 0;
          } else if (x[i] > 709) {
            sigX = 1;
          } else {
            sigX = 1 / (1 + Math.exp(-x[i]));
          }

          // Apply swish: x * sigmoid(x)
          result[i] = x[i] * sigX;
        }

        // Warn about non-finite inputs if found
        if (hasNaN || hasInf) {
          console.warn(
            `Swish activation received ${hasNaN ? 'NaN' : ''}${hasNaN && hasInf ? ' and ' : ''}${hasInf ? 'infinite' : ''} input values. Results may be unreliable.`
          );
        }

        return result;
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error applying swish activation",
          { originalError: error.message },
          "SWISH_ACTIVATION_ERROR",
          error
        );
      }
    }

    /**
     * In-place Swish computation (modifies input array)
     * @param {Array|TypedArray} x - Input/output values
     * @throws {ActivationError} - If input is invalid or operation fails
     */
    static swishInPlace(x) {
      try {
        // Validate input
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to swishInPlace cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        if (!Array.isArray(x) && 
            !(x instanceof Float32Array) && 
            !(x instanceof Float64Array)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input must be an array or typed array",
            { 
              providedType: typeof x,
              isArray: Array.isArray(x)
            },
            "INVALID_INPUT_TYPE"
          );
        }

        let hasNaN = false;
        let hasInf = false;

        for (let i = 0; i < x.length; i++) {
          // Handle non-finite inputs
          if (!Number.isFinite(x[i])) {
            if (Number.isNaN(x[i])) {
              hasNaN = true;
              x[i] = 0; // swish(NaN) = 0
              continue;
            } else if (x[i] === Number.POSITIVE_INFINITY) {
              hasInf = true;
              // Leave positive infinity as is - swish(+∞) = +∞
              continue;
            } else if (x[i] === Number.NEGATIVE_INFINITY) {
              hasInf = true;
              x[i] = 0; // swish(-∞) = -∞ * 0 = 0
              continue;
            }
          }
          
          // Calculate sigmoid with numerical stability
          let sigX;
          if (x[i] < -709) {
            sigX = 0;
          } else if (x[i] > 709) {
            sigX = 1;
          } else {
            sigX = 1 / (1 + Math.exp(-x[i]));
          }

          // Apply swish in-place: x = x * sigmoid(x)
          x[i] = x[i] * sigX;
        }

        // Warn about non-finite inputs if found
        if (hasNaN || hasInf) {
          console.warn(
            `SwishInPlace received ${hasNaN ? 'NaN' : ''}${hasNaN && hasInf ? ' and ' : ''}${hasInf ? 'infinite' : ''} input values. Results may be unreliable.`
          );
        }
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error applying in-place swish activation",
          { originalError: error.message },
          "SWISH_INPLACE_ERROR",
          error
        );
      }
    }

    /**
     * Swish gradient computation
     * @param {Array|TypedArray} x - Input values
     * @param {Array|TypedArray} y - Output of swish(x)
     * @returns {Array|TypedArray} - Gradient values
     * @throws {ActivationError} - If inputs are invalid or operation fails
     */
    static swishGradient(x, y) {
      try {
        // Validate inputs
        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input to swishGradient cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        if (!y) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Output (y) for swishGradient cannot be null or undefined",
            { providedValue: y },
            "NULL_OUTPUT"
          );
        }

        if (x.length !== y.length) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input and output arrays must have the same length",
            { inputLength: x.length, outputLength: y.length },
            "LENGTH_MISMATCH"
          );
        }

        const result = ActivationFunctions._createMatchingArray(x);
        let hasNaN = false;

        for (let i = 0; i < x.length; i++) {
          // Handle non-finite inputs
          if (!Number.isFinite(x[i]) || !Number.isFinite(y[i])) {
            hasNaN = true;
            result[i] = 0; // Avoid propagating NaN/Infinity
            continue;
          }

          // Calculate sigmoid with numerical stability
          let sigX;
          if (x[i] < -709) {
            sigX = 0;
          } else if (x[i] > 709) {
            sigX = 1;
          } else {
            sigX = 1 / (1 + Math.exp(-x[i]));
          }

          // Gradient of swish: sigmoid(x) + x * sigmoid(x) * (1 - sigmoid(x))
          result[i] = sigX + x[i] * sigX * (1 - sigX);
        }

        // Warn about non-finite values if found
        if (hasNaN) {
          console.warn("SwishGradient received non-finite values. Results may be unreliable.");
        }

        return result;
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error computing swish gradient",
          { originalError: error.message },
          "SWISH_GRADIENT_ERROR",
          error
        );
      }
    }

    /**
     * In-place Swish gradient computation (modifies input array)
     * @param {Array|TypedArray} grad - Gradient values (modified in-place)
     * @param {Array|TypedArray} x - Original input values
     * @param {Array|TypedArray} y - Output of swish(x)
     * @throws {ActivationError} - If inputs are invalid or operation fails
     */
    static swishGradientInPlace(grad, x, y) {
      try {
        // Validate inputs
        if (!grad) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Gradient array for swishGradientInPlace cannot be null or undefined",
            { providedValue: grad },
            "NULL_GRADIENT"
          );
        }

        if (!x) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Input (x) for swishGradientInPlace cannot be null or undefined",
            { providedValue: x },
            "NULL_INPUT"
          );
        }

        if (!y) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Output (y) for swishGradientInPlace cannot be null or undefined",
            { providedValue: y },
            "NULL_OUTPUT"
          );
        }

        if (grad.length !== x.length || grad.length !== y.length) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Gradient, input, and output arrays must have the same length",
            { 
              gradientLength: grad.length, 
              inputLength: x.length,
              outputLength: y.length
            },
            "LENGTH_MISMATCH"
          );
        }

        let hasNaN = false;

        for (let i = 0; i < grad.length; i++) {
          // Handle non-finite values
          if (!Number.isFinite(x[i]) || !Number.isFinite(y[i]) || !Number.isFinite(grad[i])) {
            hasNaN = true;
            grad[i] = 0; // Avoid propagating NaN/Infinity
            continue;
          }

          // Calculate sigmoid with numerical stability
          let sigX;
          if (x[i] < -709) {
            sigX = 0;
          } else if (x[i] > 709) {
            sigX = 1;
          } else {
            sigX = 1 / (1 + Math.exp(-x[i]));
          }

          // Gradient of swish: sigmoid(x) + x * sigmoid(x) * (1 - sigmoid(x))
          grad[i] *= sigX + x[i] * sigX * (1 - sigX);
        }

        // Warn about non-finite values if found
        if (hasNaN) {
          console.warn("SwishGradientInPlace received non-finite values. Results may be unreliable.");
        }
      } catch (error) {
        // Re-throw ActivationError instances
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error computing in-place swish gradient",
          { originalError: error.message },
          "SWISH_GRADIENT_INPLACE_ERROR",
          error
        );
      }
    }

    /**
     * Calculate coherence score for activation values
     * Detects unhealthy activation patterns like:
     * - Dead neurons (activations always near 0)
     * - Saturated neurons (activations always near max/min)
     * - Unstable activations (high variance)
     *
     * @param {Array|TypedArray} values - Activation values
     * @param {string} activationType - Type of activation function
     * @returns {Object} Coherence statistics
     */
    /**
     * Calculate coherence score for activation values
     * Detects unhealthy activation patterns like:
     * - Dead neurons (activations always near 0)
     * - Saturated neurons (activations always near max/min)
     * - Unstable activations (high variance)
     *
     * @param {Array|TypedArray} values - Activation values
     * @param {string} activationType - Type of activation function
     * @param {Object} [options={}] - Options for coherence calculation
     * @param {boolean} [options.throwOnViolation=false] - Whether to throw error on coherence violations
     * @returns {Object} Coherence statistics
     * @throws {NeuralCoherenceError} If throwOnViolation is true and coherence violations are detected
     */
    static calculateCoherence(values, activationType, options = {}) {
      try {
        // Quick return for empty arrays
        if (!values || values.length === 0) {
          return { score: 1.0, deadRatio: 0, saturatedRatio: 0 };
        }
        
        // Validate inputs
        if (!Array.isArray(values) && 
            !(values instanceof Float32Array) && 
            !(values instanceof Float64Array)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Values must be an array or typed array",
            { 
              providedType: typeof values,
              isArray: Array.isArray(values)
            },
            "INVALID_VALUES_TYPE"
          );
        }
        
        // Validate options
        const throwOnViolation = !!options.throwOnViolation;
        
        // Get activation function details
        const activation = ActivationFunctions.get(activationType);
        const { rangeMin, rangeMax, name: activationName } = activation;
        
        // Initialize statistics
        let sum = 0;
        let sumSq = 0;
        let dead = 0;
        let saturated = 0;
        let hasNaN = false;
        let hasInf = false;
        const n = values.length;
        const violations = [];

        // Define thresholds for dead/saturated
        const deadThreshold =
          typeof rangeMin === "number" && isFinite(rangeMin)
            ? rangeMin + 0.01 * ((rangeMax || 1) - rangeMin)
            : 0.01;

        const saturatedThreshold =
          typeof rangeMax === "number" && isFinite(rangeMax)
            ? rangeMax - 0.01 * ((rangeMax || 1) - (rangeMin || 0))
            : 0.99;

        // Count dead and saturated neurons, calculate mean
        for (let i = 0; i < n; i++) {
          const value = values[i];
          
          // Check for non-finite values
          if (!Number.isFinite(value)) {
            if (Number.isNaN(value)) {
              hasNaN = true;
            } else {
              hasInf = true;
            }
            continue;
          }
          
          sum += value;
          sumSq += value * value;

          if (Math.abs(value - rangeMin) < deadThreshold) {
            dead++;
          }

          if (
            typeof rangeMax === "number" &&
            isFinite(rangeMax) &&
            Math.abs(value - rangeMax) < rangeMax - saturatedThreshold
          ) {
            saturated++;
          }
        }
        
        // Report non-finite values as coherence violations
        if (hasNaN || hasInf) {
          violations.push({
            type: hasNaN ? "NAN_ACTIVATIONS" : "INFINITE_ACTIVATIONS",
            severity: "high",
            message: `${hasNaN ? 'NaN' : 'Infinite'} activation values detected for ${activationName} activation function`,
            details: {
              activationType: activationName
            }
          });
        }

        // Calculate statistics
        const mean = sum / n;
        const variance = sumSq / n - mean * mean;
        const deadRatio = dead / n;
        const saturatedRatio = saturated / n;

        // Calculate coherence score (higher is better)
        // Penalize dead and saturated neurons, and high variance
        let score = 1.0;

        // Penalty for dead neurons
        const deadNeuronThreshold = 0.05;
        if (deadRatio > deadNeuronThreshold) {
          score -= 0.5 * Math.min(1, deadRatio / 0.5);
          violations.push({
            type: "DEAD_NEURONS",
            severity: deadRatio > 0.2 ? "high" : "medium",
            message: `High ratio of dead neurons (${(deadRatio * 100).toFixed(1)}%) detected with ${activationName} activation`,
            threshold: deadNeuronThreshold,
            actual: deadRatio,
            details: {
              activationType: activationName,
              rangeMin,
              deadThreshold
            }
          });
        }

        // Penalty for saturated neurons
        const saturatedNeuronThreshold = 0.05;
        if (saturatedRatio > saturatedNeuronThreshold) {
          score -= 0.3 * Math.min(1, saturatedRatio / 0.5);
          violations.push({
            type: "SATURATED_NEURONS",
            severity: saturatedRatio > 0.2 ? "high" : "medium",
            message: `High ratio of saturated neurons (${(saturatedRatio * 100).toFixed(1)}%) detected with ${activationName} activation`,
            threshold: saturatedNeuronThreshold,
            actual: saturatedRatio,
            details: {
              activationType: activationName,
              rangeMax,
              saturatedThreshold
            }
          });
        }

        // Penalty for high variance (specific to activation type)
        const idealVariance = activation.isStable ? 0.1 : 0.3;
        const variancePenalty = Math.abs(variance - idealVariance) / idealVariance;
        const varianceThreshold = 2.0; // We allow variance to be up to 2x ideal before penalizing
        
        if (variancePenalty > varianceThreshold) {
          score -= 0.2 * Math.min(1, (variancePenalty - varianceThreshold) / 3.0);
          violations.push({
            type: variance > idealVariance ? "HIGH_ACTIVATION_VARIANCE" : "LOW_ACTIVATION_VARIANCE",
            severity: variancePenalty > 5.0 ? "high" : "medium",
            message: `${variance > idealVariance ? 'High' : 'Low'} activation variance detected with ${activationName} activation`,
            threshold: idealVariance,
            actual: variance,
            details: {
              activationType: activationName,
              idealVariance,
              variancePenalty
            }
          });
        }

        // Ensure score is between 0 and 1
        score = Math.max(0, Math.min(1, score));
        
        // Create result object
        const result = {
          score,
          mean,
          variance,
          deadRatio,
          saturatedRatio,
          violations: violations.length > 0 ? violations : undefined
        };
        
        // Throw error if violations detected and throwOnViolation is true
        if (throwOnViolation && violations.length > 0) {
          // Find the most severe violation
          const sortedViolations = [...violations].sort((a, b) => {
            const severityRank = { high: 3, medium: 2, low: 1 };
            return severityRank[b.severity] - severityRank[a.severity];
          });
          
          const worstViolation = sortedViolations[0];
          
          throw new (Prime.Neural.Errors.NeuralCoherenceError || Prime.ValidationError)(
            worstViolation.message,
            worstViolation.threshold,
            worstViolation.actual,
            { 
              violations,
              score,
              activationType: activationName,
              statistics: {
                mean,
                variance,
                deadRatio,
                saturatedRatio
              }
            },
            worstViolation.type
          );
        }

        return result;
      } catch (error) {
        // Re-throw NeuralCoherenceError or ActivationError
        if (error instanceof Prime.Neural.Errors.NeuralCoherenceError ||
            error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error calculating activation coherence",
          { 
            activationType,
            originalError: error.message
          },
          "COHERENCE_CALCULATION_ERROR",
          error
        );
      }
    }

    /**
     * Applies activation function to a batch of inputs (2D array)
     * @param {Array<Array>|TypedArray} inputs - 2D array of input values
     * @param {string} activationType - Type of activation function
     * @param {boolean} [inPlace=false] - Whether to modify inputs in-place
     * @returns {Array<Array>|TypedArray} - Activated values
     */
    /**
     * Applies activation function to a batch of inputs (2D array)
     * @param {Array<Array>|TypedArray} inputs - 2D array of input values
     * @param {string} activationType - Type of activation function
     * @param {boolean} [inPlace=false] - Whether to modify inputs in-place
     * @returns {Array<Array>|TypedArray} - Activated values
     * @throws {ActivationError} If inputs are invalid or activation fails
     */
    static batchActivate(inputs, activationType, inPlace = false) {
      try {
        // Validate inputs
        if (!inputs) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Inputs to batchActivate cannot be null or undefined",
            { providedValue: inputs },
            "NULL_BATCH_INPUT"
          );
        }
        
        if (!Array.isArray(inputs)) {
          throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
            "Inputs to batchActivate must be an array",
            { 
              providedType: typeof inputs, 
              isArray: Array.isArray(inputs)
            },
            "INVALID_BATCH_TYPE"
          );
        }
        
        if (inputs.length === 0) {
          return [];
        }
        
        // Get activation function
        const activation = ActivationFunctions.get(activationType);
        
        // Infer shape of the input and validate
        let nestedArrays = false;
        let vectorArrays = false;
        let inputShape = [inputs.length];
        
        // Check first element to determine shape
        if (Array.isArray(inputs[0]) || 
            inputs[0] instanceof Float32Array || 
            inputs[0] instanceof Float64Array) {
          vectorArrays = true;
          if (inputs[0].length > 0) {
            inputShape.push(inputs[0].length);
          }
        }
        
        // Special case for softmax (operates on whole vector)
        if (activationType.toLowerCase() === "softmax") {
          // Validate inputs for softmax
          if (!vectorArrays) {
            throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
              "Softmax activation requires vector inputs",
              { shapeFound: inputShape },
              "INVALID_SOFTMAX_INPUT"
            );
          }
          
          const result = [];
          for (let i = 0; i < inputs.length; i++) {
            if (!inputs[i] || inputs[i].length === 0) {
              throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
                `Empty or null vector at index ${i} for softmax activation`,
                { index: i },
                "EMPTY_VECTOR_INPUT"
              );
            }
            result.push(activation.forward(inputs[i]));
          }
          return result;
        }

        // For element-wise activations
        if (inPlace && activation.inPlace) {
          // Check if in-place operation is supported
          if (!activation.inPlace) {
            throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
              `In-place activation not supported for ${activationType}`,
              { activationType },
              "INPLACE_NOT_SUPPORTED"
            );
          }
          
          for (let i = 0; i < inputs.length; i++) {
            if (!inputs[i] || !inputs[i].length) {
              throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
                `Empty or null vector at index ${i}`,
                { index: i },
                "EMPTY_VECTOR_INPUT"
              );
            }
            activation.inPlace(inputs[i]);
          }
          return inputs;
        } else {
          const result = [];
          for (let i = 0; i < inputs.length; i++) {
            if (!inputs[i] || !inputs[i].length) {
              throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
                `Empty or null vector at index ${i}`,
                { index: i },
                "EMPTY_VECTOR_INPUT"
              );
            }
            result.push(activation.forward(inputs[i]));
          }
          return result;
        }
      } catch (error) {
        // Re-throw ActivationError
        if (error instanceof Prime.Neural.Errors.ActivationError) {
          throw error;
        }
        
        // Wrap other errors
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          "Error in batch activation",
          { 
            activationType,
            batchSize: inputs?.length,
            originalError: error.message
          },
          "BATCH_ACTIVATION_ERROR",
          error
        );
      }
    }
  }

  // Add class to Prime.Neural namespace
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Activation = ActivationFunctions;
})();

// Export the enhanced Prime object
module.exports = Prime;
