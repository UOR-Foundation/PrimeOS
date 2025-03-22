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
      const lowerName = name.toLowerCase();
      
      switch (lowerName) {
        case 'sigmoid':
          return {
            forward: ActivationFunctions.sigmoid,
            backward: ActivationFunctions.sigmoidGradient,
            inPlace: ActivationFunctions.sigmoidInPlace,
            gradientInPlace: ActivationFunctions.sigmoidGradientInPlace,
            isStable: true,
            rangeMin: 0,
            rangeMax: 1
          };
        case 'tanh':
          return {
            forward: ActivationFunctions.tanh,
            backward: ActivationFunctions.tanhGradient,
            inPlace: ActivationFunctions.tanhInPlace,
            gradientInPlace: ActivationFunctions.tanhGradientInPlace,
            isStable: true,
            rangeMin: -1,
            rangeMax: 1
          };
        case 'relu':
          return {
            forward: ActivationFunctions.relu,
            backward: ActivationFunctions.reluGradient,
            inPlace: ActivationFunctions.reluInPlace,
            gradientInPlace: ActivationFunctions.reluGradientInPlace,
            isStable: false, // May suffer from dying ReLU problem
            rangeMin: 0,
            rangeMax: Infinity
          };
        case 'leaky_relu':
          return {
            forward: ActivationFunctions.leakyRelu,
            backward: ActivationFunctions.leakyReluGradient,
            inPlace: ActivationFunctions.leakyReluInPlace,
            gradientInPlace: ActivationFunctions.leakyReluGradientInPlace,
            isStable: true,
            rangeMin: -Infinity,
            rangeMax: Infinity
          };
        case 'elu':
          return {
            forward: ActivationFunctions.elu,
            backward: ActivationFunctions.eluGradient,
            inPlace: ActivationFunctions.eluInPlace,
            gradientInPlace: ActivationFunctions.eluGradientInPlace,
            isStable: true,
            rangeMin: -1,
            rangeMax: Infinity
          };
        case 'selu':
          return {
            forward: ActivationFunctions.selu,
            backward: ActivationFunctions.seluGradient,
            inPlace: ActivationFunctions.seluInPlace,
            gradientInPlace: ActivationFunctions.seluGradientInPlace,
            isStable: true,
            rangeMin: -1.7581,
            rangeMax: Infinity
          };
        case 'softmax':
          return {
            forward: ActivationFunctions.softmax,
            backward: ActivationFunctions.softmaxGradient,
            inPlace: null, // Softmax can't be computed in-place
            gradientInPlace: null,
            isStable: true,
            rangeMin: 0,
            rangeMax: 1
          };
        case 'linear':
        case 'identity':
          return {
            forward: ActivationFunctions.linear,
            backward: ActivationFunctions.linearGradient,
            inPlace: ActivationFunctions.linearInPlace,
            gradientInPlace: ActivationFunctions.linearGradientInPlace,
            isStable: true,
            rangeMin: -Infinity,
            rangeMax: Infinity
          };
        case 'swish':
          return {
            forward: ActivationFunctions.swish,
            backward: ActivationFunctions.swishGradient,
            inPlace: ActivationFunctions.swishInPlace,
            gradientInPlace: ActivationFunctions.swishGradientInPlace,
            isStable: true,
            rangeMin: -0.278,
            rangeMax: Infinity
          };
        default:
          throw new Error(`Unknown activation function: ${name}`);
      }
    }

    /**
     * Helper to create a new array or typed array matching input type
     * @private
     * @param {Array|TypedArray} input - Input array
     * @returns {Array|TypedArray} - New array of same type
     */
    static _createMatchingArray(input) {
      if (input instanceof Float32Array) {
        return new Float32Array(input.length);
      } else if (input instanceof Float64Array) {
        return new Float64Array(input.length);
      } else {
        return new Array(input.length);
      }
    }

    /**
     * Vectorized sigmoid function: 1 / (1 + exp(-x))
     * @param {Array|TypedArray} x - Input values
     * @returns {Array|TypedArray} - Activated values
     */
    static sigmoid(x) {
      const result = ActivationFunctions._createMatchingArray(x);

      for (let i = 0; i < x.length; i++) {
        // Numerical stability: Avoid overflow for large negative values
        if (x[i] < -709) {
          result[i] = 0;
        } else if (x[i] > 709) {
          result[i] = 1;
        } else {
          result[i] = 1 / (1 + Math.exp(-x[i]));
        }
      }

      return result;
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
     */
    static tanh(x) {
      const result = ActivationFunctions._createMatchingArray(x);

      for (let i = 0; i < x.length; i++) {
        result[i] = Math.tanh(x[i]);
      }

      return result;
    }

    /**
     * In-place tanh computation (modifies input array)
     * @param {Array|TypedArray} x - Input/output values
     */
    static tanhInPlace(x) {
      for (let i = 0; i < x.length; i++) {
        x[i] = Math.tanh(x[i]);
      }
    }

    /**
     * Tanh gradient computation: 1 - tanh(x)²
     * @param {Array|TypedArray} x - Input values
     * @param {Array|TypedArray} y - Output of tanh(x)
     * @returns {Array|TypedArray} - Gradient values
     */
    static tanhGradient(x, y) {
      const result = ActivationFunctions._createMatchingArray(x);

      for (let i = 0; i < x.length; i++) {
        // Using pre-computed tanh values for efficiency
        result[i] = 1 - y[i] * y[i];
      }

      return result;
    }

    /**
     * In-place tanh gradient computation (modifies input array)
     * @param {Array|TypedArray} grad - Gradient values (modified in-place)
     * @param {Array|TypedArray} y - Output of tanh(x)
     */
    static tanhGradientInPlace(grad, y) {
      for (let i = 0; i < grad.length; i++) {
        grad[i] *= (1 - y[i] * y[i]);
      }
    }

    /**
     * Rectified Linear Unit (ReLU) function: max(0, x)
     * @param {Array|TypedArray} x - Input values
     * @returns {Array|TypedArray} - Activated values
     */
    static relu(x) {
      const result = ActivationFunctions._createMatchingArray(x);

      for (let i = 0; i < x.length; i++) {
        result[i] = Math.max(0, x[i]);
      }

      return result;
    }

    /**
     * In-place ReLU computation (modifies input array)
     * @param {Array|TypedArray} x - Input/output values
     */
    static reluInPlace(x) {
      for (let i = 0; i < x.length; i++) {
        if (x[i] < 0) {
          x[i] = 0;
        }
      }
    }

    /**
     * ReLU gradient computation: 1 if x > 0 else 0
     * @param {Array|TypedArray} x - Input values
     * @param {Array|TypedArray} y - Output of relu(x)
     * @returns {Array|TypedArray} - Gradient values
     */
    static reluGradient(x, y) {
      const result = ActivationFunctions._createMatchingArray(x);

      for (let i = 0; i < x.length; i++) {
        result[i] = x[i] > 0 ? 1 : 0;
      }

      return result;
    }

    /**
     * In-place ReLU gradient computation (modifies input array)
     * @param {Array|TypedArray} grad - Gradient values (modified in-place)
     * @param {Array|TypedArray} x - Original input values
     */
    static reluGradientInPlace(grad, x) {
      for (let i = 0; i < grad.length; i++) {
        if (x[i] <= 0) {
          grad[i] = 0;
        }
      }
    }

    /**
     * Leaky ReLU function: max(alpha * x, x)
     * @param {Array|TypedArray} x - Input values
     * @param {number} [alpha=0.01] - Leak parameter
     * @returns {Array|TypedArray} - Activated values
     */
    static leakyRelu(x, alpha = 0.01) {
      const result = ActivationFunctions._createMatchingArray(x);

      for (let i = 0; i < x.length; i++) {
        result[i] = x[i] > 0 ? x[i] : alpha * x[i];
      }

      return result;
    }

    /**
     * In-place Leaky ReLU computation (modifies input array)
     * @param {Array|TypedArray} x - Input/output values
     * @param {number} [alpha=0.01] - Leak parameter
     */
    static leakyReluInPlace(x, alpha = 0.01) {
      for (let i = 0; i < x.length; i++) {
        if (x[i] < 0) {
          x[i] *= alpha;
        }
      }
    }

    /**
     * Leaky ReLU gradient computation
     * @param {Array|TypedArray} x - Input values
     * @param {Array|TypedArray} y - Output of leakyRelu(x)
     * @param {number} [alpha=0.01] - Leak parameter
     * @returns {Array|TypedArray} - Gradient values
     */
    static leakyReluGradient(x, y, alpha = 0.01) {
      const result = ActivationFunctions._createMatchingArray(x);

      for (let i = 0; i < x.length; i++) {
        result[i] = x[i] > 0 ? 1 : alpha;
      }

      return result;
    }

    /**
     * In-place Leaky ReLU gradient computation (modifies input array)
     * @param {Array|TypedArray} grad - Gradient values (modified in-place)
     * @param {Array|TypedArray} x - Original input values
     * @param {number} [alpha=0.01] - Leak parameter
     */
    static leakyReluGradientInPlace(grad, x, alpha = 0.01) {
      for (let i = 0; i < grad.length; i++) {
        if (x[i] <= 0) {
          grad[i] *= alpha;
        }
      }
    }

    /**
     * Exponential Linear Unit (ELU) function: x if x > 0 else alpha * (exp(x) - 1)
     * @param {Array|TypedArray} x - Input values
     * @param {number} [alpha=1.0] - Alpha parameter
     * @returns {Array|TypedArray} - Activated values
     */
    static elu(x, alpha = 1.0) {
      const result = ActivationFunctions._createMatchingArray(x);

      for (let i = 0; i < x.length; i++) {
        result[i] = x[i] > 0 ? x[i] : alpha * (Math.exp(x[i]) - 1);
      }

      return result;
    }

    /**
     * In-place ELU computation (modifies input array)
     * @param {Array|TypedArray} x - Input/output values
     * @param {number} [alpha=1.0] - Alpha parameter
     */
    static eluInPlace(x, alpha = 1.0) {
      for (let i = 0; i < x.length; i++) {
        if (x[i] <= 0) {
          x[i] = alpha * (Math.exp(x[i]) - 1);
        }
      }
    }

    /**
     * ELU gradient computation
     * @param {Array|TypedArray} x - Input values
     * @param {Array|TypedArray} y - Output of elu(x)
     * @param {number} [alpha=1.0] - Alpha parameter
     * @returns {Array|TypedArray} - Gradient values
     */
    static eluGradient(x, y, alpha = 1.0) {
      const result = ActivationFunctions._createMatchingArray(x);

      for (let i = 0; i < x.length; i++) {
        result[i] = x[i] > 0 ? 1 : y[i] + alpha;
      }

      return result;
    }

    /**
     * In-place ELU gradient computation (modifies input array)
     * @param {Array|TypedArray} grad - Gradient values (modified in-place)
     * @param {Array|TypedArray} x - Original input values
     * @param {Array|TypedArray} y - Output of elu(x)
     * @param {number} [alpha=1.0] - Alpha parameter
     */
    static eluGradientInPlace(grad, x, y, alpha = 1.0) {
      for (let i = 0; i < grad.length; i++) {
        if (x[i] <= 0) {
          grad[i] *= (y[i] + alpha);
        }
      }
    }

    /**
     * Scaled Exponential Linear Unit (SELU) function
     * Self-normalizing variant of ELU
     * @param {Array|TypedArray} x - Input values
     * @returns {Array|TypedArray} - Activated values
     */
    static selu(x) {
      // SELU parameters (fixed values from the paper)
      const alpha = 1.6732632423543772848170429916717;
      const scale = 1.0507009873554804934193349852946;
      
      const result = ActivationFunctions._createMatchingArray(x);

      for (let i = 0; i < x.length; i++) {
        result[i] = scale * (x[i] > 0 ? x[i] : alpha * (Math.exp(x[i]) - 1));
      }

      return result;
    }

    /**
     * In-place SELU computation (modifies input array)
     * @param {Array|TypedArray} x - Input/output values
     */
    static seluInPlace(x) {
      // SELU parameters (fixed values)
      const alpha = 1.6732632423543772848170429916717;
      const scale = 1.0507009873554804934193349852946;

      for (let i = 0; i < x.length; i++) {
        if (x[i] <= 0) {
          x[i] = scale * alpha * (Math.exp(x[i]) - 1);
        } else {
          x[i] *= scale;
        }
      }
    }

    /**
     * SELU gradient computation
     * @param {Array|TypedArray} x - Input values
     * @param {Array|TypedArray} y - Output of selu(x)
     * @returns {Array|TypedArray} - Gradient values
     */
    static seluGradient(x, y) {
      // SELU parameters (fixed values)
      const alpha = 1.6732632423543772848170429916717;
      const scale = 1.0507009873554804934193349852946;
      
      const result = ActivationFunctions._createMatchingArray(x);

      for (let i = 0; i < x.length; i++) {
        if (x[i] > 0) {
          result[i] = scale;
        } else {
          // For x <= 0, gradient is: scale * alpha * exp(x)
          // Note: y = scale * alpha * (exp(x) - 1) for x <= 0
          // So exp(x) = (y / (scale * alpha)) + 1
          result[i] = y[i] + scale * alpha;
        }
      }

      return result;
    }

    /**
     * In-place SELU gradient computation (modifies input array)
     * @param {Array|TypedArray} grad - Gradient values (modified in-place)
     * @param {Array|TypedArray} x - Original input values
     * @param {Array|TypedArray} y - Output of selu(x)
     */
    static seluGradientInPlace(grad, x, y) {
      // SELU parameters (fixed values)
      const alpha = 1.6732632423543772848170429916717;
      const scale = 1.0507009873554804934193349852946;

      for (let i = 0; i < grad.length; i++) {
        if (x[i] > 0) {
          grad[i] *= scale;
        } else {
          grad[i] *= y[i] + scale * alpha;
        }
      }
    }

    /**
     * Softmax function: exp(x_i) / sum(exp(x_j))
     * Transforms input into a probability distribution
     * Note: This function can't be applied element-wise
     * @param {Array|TypedArray} x - Input values
     * @returns {Array|TypedArray} - Softmax values
     */
    static softmax(x) {
      const result = ActivationFunctions._createMatchingArray(x);
      
      // Find max for numerical stability
      let maxVal = x[0];
      for (let i = 1; i < x.length; i++) {
        if (x[i] > maxVal) {
          maxVal = x[i];
        }
      }
      
      // Calculate exp(x - max) and sum
      let sum = 0;
      for (let i = 0; i < x.length; i++) {
        result[i] = Math.exp(x[i] - maxVal);
        sum += result[i];
      }
      
      // Normalize
      if (sum !== 0) {
        for (let i = 0; i < x.length; i++) {
          result[i] /= sum;
        }
      }
      
      return result;
    }

    /**
     * Softmax gradient computation
     * Note: This implementation assumes a specific loss function (cross-entropy)
     * It's a simplification for common use cases
     * @param {Array|TypedArray} x - Input values
     * @param {Array|TypedArray} y - Output of softmax(x)
     * @param {Array|TypedArray} dy - Upstream gradient
     * @returns {Array|TypedArray} - Gradient values
     */
    static softmaxGradient(x, y, dy) {
      const result = ActivationFunctions._createMatchingArray(x);
      
      // For cross-entropy loss with softmax, gradient is (y - targets)
      // which is usually passed directly in dy, so we just return dy
      
      // In the more general case, the Jacobian for softmax is complex
      // This is a simplified implementation for common use cases
      if (dy) {
        for (let i = 0; i < result.length; i++) {
          result[i] = dy[i];
        }
      } else {
        // If no gradient is provided, just return ones (identity gradient)
        for (let i = 0; i < result.length; i++) {
          result[i] = 1;
        }
      }
      
      return result;
    }

    /**
     * Linear/Identity activation function
     * @param {Array|TypedArray} x - Input values
     * @returns {Array|TypedArray} - Same values (copy)
     */
    static linear(x) {
      return ActivationFunctions._createMatchingArray(x).map((_, i) => x[i]);
    }

    /**
     * In-place linear activation (no-op, but included for API consistency)
     * @param {Array|TypedArray} x - Input/output values
     */
    static linearInPlace(x) {
      // No operation needed - identity function
    }

    /**
     * Linear/Identity gradient (always 1)
     * @param {Array|TypedArray} x - Input values
     * @returns {Array|TypedArray} - Gradient values (all 1)
     */
    static linearGradient(x) {
      const result = ActivationFunctions._createMatchingArray(x);
      
      for (let i = 0; i < x.length; i++) {
        result[i] = 1;
      }
      
      return result;
    }

    /**
     * In-place linear gradient computation (no change to gradient values)
     * @param {Array|TypedArray} grad - Gradient values (unmodified)
     */
    static linearGradientInPlace(grad) {
      // No operation needed - gradient is unchanged
    }

    /**
     * Swish activation function: x * sigmoid(x)
     * @param {Array|TypedArray} x - Input values
     * @returns {Array|TypedArray} - Activated values
     */
    static swish(x) {
      const result = ActivationFunctions._createMatchingArray(x);

      for (let i = 0; i < x.length; i++) {
        // Calculate sigmoid with numerical stability
        let sigX;
        if (x[i] < -709) {
          sigX = 0;
        } else if (x[i] > 709) {
          sigX = 1;
        } else {
          sigX = 1 / (1 + Math.exp(-x[i]));
        }
        
        result[i] = x[i] * sigX;
      }

      return result;
    }

    /**
     * In-place Swish computation (modifies input array)
     * @param {Array|TypedArray} x - Input/output values
     */
    static swishInPlace(x) {
      for (let i = 0; i < x.length; i++) {
        // Calculate sigmoid with numerical stability
        let sigX;
        if (x[i] < -709) {
          sigX = 0;
        } else if (x[i] > 709) {
          sigX = 1;
        } else {
          sigX = 1 / (1 + Math.exp(-x[i]));
        }
        
        x[i] = x[i] * sigX;
      }
    }

    /**
     * Swish gradient computation
     * @param {Array|TypedArray} x - Input values
     * @param {Array|TypedArray} y - Output of swish(x)
     * @returns {Array|TypedArray} - Gradient values
     */
    static swishGradient(x, y) {
      const result = ActivationFunctions._createMatchingArray(x);

      for (let i = 0; i < x.length; i++) {
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

      return result;
    }

    /**
     * In-place Swish gradient computation (modifies input array)
     * @param {Array|TypedArray} grad - Gradient values (modified in-place)
     * @param {Array|TypedArray} x - Original input values
     * @param {Array|TypedArray} y - Output of swish(x)
     */
    static swishGradientInPlace(grad, x, y) {
      for (let i = 0; i < grad.length; i++) {
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
        grad[i] *= (sigX + x[i] * sigX * (1 - sigX));
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
    static calculateCoherence(values, activationType) {
      if (!values || values.length === 0) {
        return { score: 1.0, deadRatio: 0, saturatedRatio: 0 };
      }

      const activation = ActivationFunctions.get(activationType);
      const { rangeMin, rangeMax } = activation;
      
      // Calculate statistics
      let sum = 0;
      let sumSq = 0;
      let dead = 0;
      let saturated = 0;
      const n = values.length;
      
      // Define thresholds for dead/saturated
      const deadThreshold = typeof rangeMin === 'number' && isFinite(rangeMin) 
        ? rangeMin + 0.01 * (rangeMax - rangeMin) 
        : 0.01;
        
      const saturatedThreshold = typeof rangeMax === 'number' && isFinite(rangeMax) 
        ? rangeMax - 0.01 * (rangeMax - rangeMin) 
        : 0.99;
      
      // Count dead and saturated neurons, calculate mean
      for (let i = 0; i < n; i++) {
        const value = values[i];
        sum += value;
        sumSq += value * value;
        
        if (Math.abs(value - rangeMin) < deadThreshold) {
          dead++;
        }
        
        if (typeof rangeMax === 'number' && isFinite(rangeMax) && 
            Math.abs(value - rangeMax) < (rangeMax - saturatedThreshold)) {
          saturated++;
        }
      }
      
      const mean = sum / n;
      const variance = (sumSq / n) - (mean * mean);
      const deadRatio = dead / n;
      const saturatedRatio = saturated / n;
      
      // Calculate coherence score (higher is better)
      // Penalize dead and saturated neurons, and high variance
      let score = 1.0;
      
      // Penalty for dead neurons
      if (deadRatio > 0.05) {
        score -= 0.5 * Math.min(1, deadRatio / 0.5);
      }
      
      // Penalty for saturated neurons
      if (saturatedRatio > 0.05) {
        score -= 0.3 * Math.min(1, saturatedRatio / 0.5);
      }
      
      // Penalty for high variance (specific to activation type)
      const idealVariance = activation.isStable ? 0.1 : 0.3;
      const variancePenalty = Math.abs(variance - idealVariance) / idealVariance;
      score -= 0.2 * Math.min(1, variancePenalty);
      
      // Ensure score is between 0 and 1
      score = Math.max(0, Math.min(1, score));
      
      return {
        score,
        mean,
        variance,
        deadRatio,
        saturatedRatio
      };
    }
    
    /**
     * Applies activation function to a batch of inputs (2D array)
     * @param {Array<Array>|TypedArray} inputs - 2D array of input values
     * @param {string} activationType - Type of activation function
     * @param {boolean} [inPlace=false] - Whether to modify inputs in-place
     * @returns {Array<Array>|TypedArray} - Activated values
     */
    static batchActivate(inputs, activationType, inPlace = false) {
      const activation = ActivationFunctions.get(activationType);
      
      // Special case for softmax (operates on whole vector)
      if (activationType.toLowerCase() === 'softmax') {
        const result = [];
        for (let i = 0; i < inputs.length; i++) {
          result.push(activation.forward(inputs[i]));
        }
        return result;
      }
      
      // For element-wise activations
      if (inPlace && activation.inPlace) {
        for (let i = 0; i < inputs.length; i++) {
          activation.inPlace(inputs[i]);
        }
        return inputs;
      } else {
        const result = [];
        for (let i = 0; i < inputs.length; i++) {
          result.push(activation.forward(inputs[i]));
        }
        return result;
      }
    }
  }

  // Add class to Prime.Neural namespace
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Activation = ActivationFunctions;
})();

// Export the enhanced Prime object
module.exports = Prime;