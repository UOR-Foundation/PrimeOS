/**
 * PrimeOS JavaScript Library - Neural Layer Module
 * Unified Dense (Fully-Connected) Layer Implementation
 */

// Import the Prime object from core
const Prime = require("../../core");

// Ensure Prime and Neural namespace exist
Prime.Neural = Prime.Neural || {};
Prime.Neural.Layer = Prime.Neural.Layer || {};

// Create the Dense Layer module using IIFE
(function () {
  /**
   * Dense Layer - Fully connected neural network layer
   * Standard implementation with memory efficiency and coherence awareness
   */
  class DenseLayer {
    /**
     * Create a new dense (fully connected) layer
     * @param {Object} config - Layer configuration
     * @param {number} config.inputSize - Number of input neurons
     * @param {number} config.outputSize - Number of output neurons
     * @param {string} [config.activation='sigmoid'] - Activation function
     * @param {Object} [config.initParams={}] - Weight initialization parameters
     * @param {boolean} [config.useTypedArrays=false] - Use typed arrays for memory efficiency
     */
    constructor(config) {
      if (!Prime.Utils.isObject(config)) {
        throw new Prime.ValidationError(
          "Layer configuration must be an object",
        );
      }

      this.inputSize = config.inputSize;
      this.outputSize = config.outputSize;
      this.activation = config.activation || "sigmoid";
      this.useTypedArrays = config.useTypedArrays || false;

      // Validate dimensions
      if (!Number.isInteger(this.inputSize) || this.inputSize <= 0) {
        throw new Prime.ValidationError(
          "Input size must be a positive integer",
        );
      }

      if (!Number.isInteger(this.outputSize) || this.outputSize <= 0) {
        throw new Prime.ValidationError(
          "Output size must be a positive integer",
        );
      }

      // Initialize weights and biases
      this.weights = this._initializeWeights(config.initParams || {});
      this.biases = this._initializeBiases(config.initParams || {});

      // Performance tracking
      this.metrics = {
        forwardCount: 0,
        backwardCount: 0,
        averageForwardTime: 0,
        averageBackwardTime: 0,
        coherence: 1.0,
      };

      // Optimization state
      this.momentumWeights = null;
      this.momentumBiases = null;
      this.iteration = 0;

      // Cache for forward pass
      this.cache = {
        lastInput: null,
        lastZ: null,
        lastActivation: null,
      };

      // Selected activation functions
      this._setupActivationFunctions();
    }

    /**
     * Initialize weights with appropriate distribution
     * @private
     * @param {Object} params - Initialization parameters
     * @returns {Array|TypedArray} Initialized weights matrix
     */
    _initializeWeights(params) {
      // Determine initialization scale based on activation function
      let scale = params.scale;
      if (!scale) {
        if (this.activation === "relu") {
          // He initialization
          scale = Math.sqrt(2 / this.inputSize);
        } else {
          // Xavier/Glorot initialization
          scale = Math.sqrt(2 / (this.inputSize + this.outputSize));
        }
      }

      const distribution = params.distribution || "xavier";

      // Create weights matrix
      if (this.useTypedArrays && typeof Float32Array !== "undefined") {
        // Use TypedArrays for memory efficiency
        const flatWeights = new Float32Array(this.outputSize * this.inputSize);

        // Initialize with proper distribution
        for (let i = 0; i < this.outputSize; i++) {
          for (let j = 0; j < this.inputSize; j++) {
            const index = i * this.inputSize + j;
            let value;

            if (distribution === "xavier") {
              // Xavier/Glorot initialization
              value = (Math.random() * 2 - 1) * scale;
            } else if (distribution === "he") {
              // He initialization
              value = Math.random() * Math.sqrt(2 / this.inputSize);
            } else if (distribution === "zeros") {
              value = 0;
            } else {
              // Default to small random values
              value = Math.random() * 0.2 - 0.1;
            }

            flatWeights[index] = value;
          }
        }

        // Create a 2D view of the weights for easier access
        const weights = new Array(this.outputSize);
        for (let i = 0; i < this.outputSize; i++) {
          weights[i] = new Float32Array(
            flatWeights.buffer,
            i * this.inputSize * Float32Array.BYTES_PER_ELEMENT,
            this.inputSize,
          );
        }

        // Add metadata
        Object.defineProperties(weights, {
          _isTypedArray: { value: true },
          _flatArray: { value: flatWeights },
        });

        return weights;
      } else {
        // Use standard arrays
        const weights = new Array(this.outputSize);

        for (let i = 0; i < this.outputSize; i++) {
          weights[i] = new Array(this.inputSize);

          for (let j = 0; j < this.inputSize; j++) {
            let value;

            if (distribution === "xavier") {
              // Xavier/Glorot initialization
              value = (Math.random() * 2 - 1) * scale;
            } else if (distribution === "he") {
              // He initialization
              value = Math.random() * Math.sqrt(2 / this.inputSize);
            } else if (distribution === "zeros") {
              value = 0;
            } else {
              // Default to small random values
              value = Math.random() * 0.2 - 0.1;
            }

            weights[i][j] = value;
          }
        }

        return weights;
      }
    }

    /**
     * Initialize biases
     * @private
     * @param {Object} params - Initialization parameters
     * @returns {Array|TypedArray} Initialized biases vector
     */
    _initializeBiases(params) {
      const biasValue = params.bias !== undefined ? params.bias : 0;

      if (this.useTypedArrays && typeof Float32Array !== "undefined") {
        // Use TypedArrays for memory efficiency
        const biases = new Float32Array(this.outputSize);

        if (biasValue !== 0) {
          biases.fill(biasValue);
        }

        return biases;
      } else {
        // Use regular array
        return new Array(this.outputSize).fill(biasValue);
      }
    }

    /**
     * Set up activation functions based on selected activation type
     * @private
     */
    _setupActivationFunctions() {
      switch (this.activation) {
        case "sigmoid":
          this._activate = this._sigmoid;
          this._activateDerivative = this._sigmoidDerivative;
          break;
        case "relu":
          this._activate = this._relu;
          this._activateDerivative = this._reluDerivative;
          break;
        case "leaky_relu":
          this._activate = this._leakyRelu;
          this._activateDerivative = this._leakyReluDerivative;
          break;
        case "tanh":
          this._activate = this._tanh;
          this._activateDerivative = this._tanhDerivative;
          break;
        case "linear":
          this._activate = this._linear;
          this._activateDerivative = this._linearDerivative;
          break;
        case "softmax":
          this._activate = this._softmax;
          this._activateDerivative = this._softmaxDerivative;
          break;
        default:
          // Default to sigmoid
          this._activate = this._sigmoid;
          this._activateDerivative = this._sigmoidDerivative;
      }
    }

    /**
     * Sigmoid activation function
     * @private
     * @param {Array|TypedArray} z - Pre-activation values
     * @returns {Array|TypedArray} Activated values
     */
    _sigmoid(z) {
      const result = this.useTypedArrays
        ? new Float32Array(z.length)
        : new Array(z.length);

      for (let i = 0; i < z.length; i++) {
        result[i] = 1 / (1 + Math.exp(-z[i]));
      }

      return result;
    }

    /**
     * Sigmoid derivative
     * @private
     * @param {Array|TypedArray} a - Activated values
     * @returns {Array|TypedArray} Derivative values
     */
    _sigmoidDerivative(a) {
      const result = this.useTypedArrays
        ? new Float32Array(a.length)
        : new Array(a.length);

      for (let i = 0; i < a.length; i++) {
        result[i] = a[i] * (1 - a[i]);
      }

      return result;
    }

    /**
     * ReLU activation function
     * @private
     * @param {Array|TypedArray} z - Pre-activation values
     * @returns {Array|TypedArray} Activated values
     */
    _relu(z) {
      const result = this.useTypedArrays
        ? new Float32Array(z.length)
        : new Array(z.length);

      for (let i = 0; i < z.length; i++) {
        result[i] = Math.max(0, z[i]);
      }

      return result;
    }

    /**
     * ReLU derivative
     * @private
     * @param {Array|TypedArray} z - Pre-activation values
     * @returns {Array|TypedArray} Derivative values
     */
    _reluDerivative(z) {
      const result = this.useTypedArrays
        ? new Float32Array(z.length)
        : new Array(z.length);

      for (let i = 0; i < z.length; i++) {
        result[i] = z[i] > 0 ? 1 : 0;
      }

      return result;
    }

    /**
     * Leaky ReLU activation function
     * @private
     * @param {Array|TypedArray} z - Pre-activation values
     * @returns {Array|TypedArray} Activated values
     */
    _leakyRelu(z) {
      const result = this.useTypedArrays
        ? new Float32Array(z.length)
        : new Array(z.length);
      const alpha = 0.01; // Leak parameter

      for (let i = 0; i < z.length; i++) {
        result[i] = z[i] > 0 ? z[i] : alpha * z[i];
      }

      return result;
    }

    /**
     * Leaky ReLU derivative
     * @private
     * @param {Array|TypedArray} z - Pre-activation values
     * @returns {Array|TypedArray} Derivative values
     */
    _leakyReluDerivative(z) {
      const result = this.useTypedArrays
        ? new Float32Array(z.length)
        : new Array(z.length);
      const alpha = 0.01; // Leak parameter

      for (let i = 0; i < z.length; i++) {
        result[i] = z[i] > 0 ? 1 : alpha;
      }

      return result;
    }

    /**
     * Tanh activation function
     * @private
     * @param {Array|TypedArray} z - Pre-activation values
     * @returns {Array|TypedArray} Activated values
     */
    _tanh(z) {
      const result = this.useTypedArrays
        ? new Float32Array(z.length)
        : new Array(z.length);

      for (let i = 0; i < z.length; i++) {
        result[i] = Math.tanh(z[i]);
      }

      return result;
    }

    /**
     * Tanh derivative
     * @private
     * @param {Array|TypedArray} a - Activated values
     * @returns {Array|TypedArray} Derivative values
     */
    _tanhDerivative(a) {
      const result = this.useTypedArrays
        ? new Float32Array(a.length)
        : new Array(a.length);

      for (let i = 0; i < a.length; i++) {
        result[i] = 1 - a[i] * a[i];
      }

      return result;
    }

    /**
     * Linear activation function
     * @private
     * @param {Array|TypedArray} z - Pre-activation values
     * @returns {Array|TypedArray} Activated values
     */
    _linear(z) {
      // For linear activation, we can just return a copy of z
      if (this.useTypedArrays) {
        return new Float32Array(z);
      } else {
        return [...z];
      }
    }

    /**
     * Linear derivative (always 1)
     * @private
     * @param {Array|TypedArray} z - Pre-activation values
     * @returns {Array|TypedArray} Derivative values
     */
    _linearDerivative(z) {
      const result = this.useTypedArrays
        ? new Float32Array(z.length)
        : new Array(z.length);
      result.fill(1);
      return result;
    }

    /**
     * Softmax activation function
     * @private
     * @param {Array|TypedArray} z - Pre-activation values
     * @returns {Array|TypedArray} Activated values
     */
    _softmax(z) {
      const result = this.useTypedArrays
        ? new Float32Array(z.length)
        : new Array(z.length);

      // For numerical stability, subtract max value
      const maxVal = Math.max(...z);
      let sum = 0;

      // Calculate exponentials and sum
      for (let i = 0; i < z.length; i++) {
        result[i] = Math.exp(z[i] - maxVal);
        sum += result[i];
      }

      // Normalize
      for (let i = 0; i < z.length; i++) {
        result[i] /= sum;
      }

      return result;
    }

    /**
     * Softmax derivative (must be handled specially during backprop)
     * Note: This is a simplification since softmax derivative is a Jacobian matrix
     * @private
     * @param {Array|TypedArray} a - Activated values (softmax outputs)
     * @returns {Array|TypedArray} Derivative values
     */
    _softmaxDerivative(a) {
      // For crossentropy loss, softmax derivative simplifies in backprop
      // This method is included for completeness, but is not typically used
      return a; // The actual Jacobian is handled in backward pass
    }

    /**
     * Forward pass through the layer
     * @param {Array|TypedArray} input - Input activation vector
     * @param {Object} [options={}] - Forward pass options
     * @param {boolean} [options.training=true] - Whether in training mode
     * @param {boolean} [options.cacheInput=true] - Whether to cache input for backprop
     * @returns {Object} Output activation and cache for backprop
     */
    forward(input, options = {}) {
      const isTraining = options.training !== false;
      const shouldCache = options.cacheInput !== false;

      if (
        !Array.isArray(input) &&
        !(input instanceof Float32Array) &&
        !(input instanceof Float64Array)
      ) {
        throw new Prime.ValidationError("Input must be an array or TypedArray");
      }

      if (input.length !== this.inputSize) {
        throw new Prime.ValidationError(
          `Input must have length ${this.inputSize}, got ${input.length}`,
        );
      }

      const startTime = performance.now();

      // Compute linear combination (z = Wx + b)
      const z = this.useTypedArrays
        ? new Float32Array(this.outputSize)
        : new Array(this.outputSize).fill(0);

      for (let i = 0; i < this.outputSize; i++) {
        z[i] = this.biases[i];
        for (let j = 0; j < this.inputSize; j++) {
          z[i] += this.weights[i][j] * input[j];
        }
      }

      // Apply activation function
      const activation = this._activate(z);

      // Cache for backward pass
      if (isTraining && shouldCache) {
        this.cache.lastInput = input;
        this.cache.lastZ = z;
        this.cache.lastActivation = activation;
      }

      // Update performance metrics
      const endTime = performance.now();
      this._updateForwardMetrics(endTime - startTime);

      return {
        activation,
        cache: { input, z, activation },
      };
    }

    /**
     * Backward pass to compute gradients
     * @param {Array|TypedArray} dY - Gradient of loss with respect to output
     * @param {Object} [cache] - Cache from forward pass (optional if was cached in forward)
     * @returns {Object} Gradients for weights, biases, and inputs
     */
    backward(dY, cache) {
      if (
        !Array.isArray(dY) &&
        !(dY instanceof Float32Array) &&
        !(dY instanceof Float64Array)
      ) {
        throw new Prime.ValidationError("dY must be an array or TypedArray");
      }

      if (dY.length !== this.outputSize) {
        throw new Prime.ValidationError(
          `Output gradient must have length ${this.outputSize}, got ${dY.length}`,
        );
      }

      const startTime = performance.now();

      // Use provided cache or cached values from forward pass
      const { input, z, activation } = cache || {
        input: this.cache.lastInput,
        z: this.cache.lastZ,
        activation: this.cache.lastActivation,
      };

      if (!input || !z) {
        throw new Prime.ValidationError(
          "Cache not provided and no cached values available from forward pass",
        );
      }

      // Handle special case for softmax + crossentropy
      // For softmax, the derivative calculation is special when paired with crossentropy loss
      let dZ;
      if (this.activation === "softmax") {
        // For softmax with crossentropy, dZ is often just (activation - target)
        // But we'll use the provided dY which should already account for this
        dZ = dY;
      } else {
        // For other activation functions
        const activationDerivative = this._activateDerivative(activation, z);

        // Calculate gradient of z with respect to loss
        dZ = this.useTypedArrays
          ? new Float32Array(this.outputSize)
          : new Array(this.outputSize);

        for (let i = 0; i < this.outputSize; i++) {
          dZ[i] = dY[i] * activationDerivative[i];
        }
      }

      // Compute gradients for weights (dW = dZ * input^T)
      // Create dW with same type as weights
      const dW = this.useTypedArrays
        ? new Array(this.outputSize)
        : new Array(this.outputSize);

      for (let i = 0; i < this.outputSize; i++) {
        dW[i] = this.useTypedArrays
          ? new Float32Array(this.inputSize)
          : new Array(this.inputSize);

        for (let j = 0; j < this.inputSize; j++) {
          dW[i][j] = dZ[i] * input[j];
        }
      }

      // Compute gradients for biases (dB = dZ)
      const dB = this.useTypedArrays ? new Float32Array(dZ) : [...dZ];

      // Compute gradients for inputs (dX = W^T * dZ)
      const dX = this.useTypedArrays
        ? new Float32Array(this.inputSize).fill(0)
        : new Array(this.inputSize).fill(0);

      for (let j = 0; j < this.inputSize; j++) {
        for (let i = 0; i < this.outputSize; i++) {
          dX[j] += this.weights[i][j] * dZ[i];
        }
      }

      // Update performance metrics
      const endTime = performance.now();
      this._updateBackwardMetrics(endTime - startTime);

      return { dW, dB, dX };
    }

    /**
     * Update forward performance metrics
     * @private
     * @param {number} time - Time in ms for this forward pass
     */
    _updateForwardMetrics(time) {
      this.metrics.forwardCount++;
      // Exponential moving average of forward time
      this.metrics.averageForwardTime =
        0.9 * this.metrics.averageForwardTime + 0.1 * time;
    }

    /**
     * Update backward performance metrics
     * @private
     * @param {number} time - Time in ms for this backward pass
     */
    _updateBackwardMetrics(time) {
      this.metrics.backwardCount++;
      // Exponential moving average of backward time
      this.metrics.averageBackwardTime =
        0.9 * this.metrics.averageBackwardTime + 0.1 * time;
    }

    /**
     * Calculate current layer coherence
     * @returns {number} Coherence score (0-1)
     */
    calculateCoherence() {
      // Calculate weight statistics
      let totalWeight = 0;
      let maxWeight = 0;

      for (let i = 0; i < this.outputSize; i++) {
        for (let j = 0; j < this.inputSize; j++) {
          const absWeight = Math.abs(this.weights[i][j]);
          totalWeight += absWeight;
          maxWeight = Math.max(maxWeight, absWeight);
        }
      }

      const avgWeight = totalWeight / (this.inputSize * this.outputSize);

      // Check for extreme weights (indicates potential instability)
      const weightRatio = maxWeight > 0 ? avgWeight / maxWeight : 1;

      // Check for dying ReLUs (if using ReLU activation)
      let activationHealth = 1.0;
      if (this.activation === "relu" && this.cache.lastActivation) {
        const numActive = this.cache.lastActivation.filter((a) => a > 0).length;
        activationHealth = numActive / this.outputSize;
      }

      // Calculate coherence as a combination of factors
      const weightCoherence = 0.5 + 0.5 * weightRatio;
      this.metrics.coherence = 0.7 * weightCoherence + 0.3 * activationHealth;

      return this.metrics.coherence;
    }

    /**
     * Get layer performance metrics
     * @returns {Object} Current performance metrics
     */
    getMetrics() {
      // Update coherence if we have data
      if (this.metrics.forwardCount > 0) {
        this.calculateCoherence();
      }

      return { ...this.metrics };
    }

    /**
     * Update layer parameters with given gradients
     * @param {Object} gradients - Weight and bias gradients
     * @param {number} learningRate - Learning rate for update
     * @param {Object} [options={}] - Update options
     * @param {number} [options.momentum=0] - Momentum coefficient
     * @param {number} [options.l2Regularization=0] - L2 regularization coefficient
     * @param {boolean} [options.inPlace=true] - Whether to update weights in-place
     */
    update(gradients, learningRate, options = {}) {
      const { dW, dB } = gradients;
      const momentum = options.momentum || 0;
      const l2Reg = options.l2Regularization || 0;
      const inPlace = options.inPlace !== false;

      // Initialize momentum arrays if needed
      if (momentum > 0 && !this.momentumWeights) {
        // Create momentum storage with same structure as weights and biases
        this.momentumWeights = new Array(this.outputSize);
        for (let i = 0; i < this.outputSize; i++) {
          this.momentumWeights[i] = this.useTypedArrays
            ? new Float32Array(this.inputSize).fill(0)
            : new Array(this.inputSize).fill(0);
        }

        this.momentumBiases = this.useTypedArrays
          ? new Float32Array(this.outputSize).fill(0)
          : new Array(this.outputSize).fill(0);
      }

      // Update weights with momentum and L2 regularization
      for (let i = 0; i < this.outputSize; i++) {
        for (let j = 0; j < this.inputSize; j++) {
          // Calculate update with regularization
          let update = dW[i][j];

          // Add L2 regularization gradient
          if (l2Reg > 0) {
            update += l2Reg * this.weights[i][j];
          }

          // Apply momentum if needed
          if (momentum > 0) {
            this.momentumWeights[i][j] =
              momentum * this.momentumWeights[i][j] - learningRate * update;

            if (inPlace) {
              this.weights[i][j] += this.momentumWeights[i][j];
            } else {
              this.weights[i][j] =
                this.weights[i][j] + this.momentumWeights[i][j];
            }
          } else {
            // Standard SGD update
            if (inPlace) {
              this.weights[i][j] -= learningRate * update;
            } else {
              this.weights[i][j] = this.weights[i][j] - learningRate * update;
            }
          }
        }
      }

      // Update biases
      for (let i = 0; i < this.outputSize; i++) {
        if (momentum > 0) {
          this.momentumBiases[i] =
            momentum * this.momentumBiases[i] - learningRate * dB[i];

          if (inPlace) {
            this.biases[i] += this.momentumBiases[i];
          } else {
            this.biases[i] = this.biases[i] + this.momentumBiases[i];
          }
        } else {
          if (inPlace) {
            this.biases[i] -= learningRate * dB[i];
          } else {
            this.biases[i] = this.biases[i] - learningRate * dB[i];
          }
        }
      }

      this.iteration++;
    }

    /**
     * Get a summary of the layer
     * @returns {Object} Layer summary
     */
    getSummary() {
      return {
        type: "Dense",
        inputSize: this.inputSize,
        outputSize: this.outputSize,
        activation: this.activation,
        parameters: this.inputSize * this.outputSize + this.outputSize,
        useTypedArrays: this.useTypedArrays,
        metrics: this.getMetrics(),
      };
    }
  }

  // Add class to Prime.Neural.Layer namespace
  Prime.Neural.Layer = Prime.Neural.Layer || {};
  Prime.Neural.Layer.Dense = DenseLayer;
  
  // For backward compatibility, register as DenseLayer as well
  Prime.Neural.Layer.DenseLayer = DenseLayer;
})();

// This module does not export anything directly