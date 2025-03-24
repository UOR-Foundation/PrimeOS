/**
 * PrimeOS JavaScript Library - Neural Layer Module
 * Core neural layer functionality
 * Version 1.1.0
 */

// Import the Prime object from core
const Prime = require("../../core");

// Import from math module
const Vector = Prime.Math.Vector;
const Matrix = Prime.Math.Matrix;

// Initialize Layer namespace if it doesn't exist
(function(Prime) {
  // Ensure namespaces exist to prevent "cannot read property of undefined" errors
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Layer = Prime.Neural.Layer || {};
  Prime.Neural.Errors = Prime.Neural.Errors || {};
  
  // Initialize namespace initialization trackers
  Prime.Neural._namespaceInitialized = Prime.Neural._namespaceInitialized || {};
  Prime.Neural._namespaceInitialized["Layer"] = true;
  
  if (Prime.Logger && Prime.Logger.debug) {
    Prime.Logger.debug("Neural Layer namespace initialized");
  }
})(Prime);

// Create the Layer module using IIFE
(function () {
  /**
   * Base Neural Layer class
   * Foundation for all neural layer types
   */
  class NeuralLayer {
    /**
     * Create a new neural layer
     * @param {Object} config - Layer configuration
     * @param {number} config.inputSize - Number of input neurons
     * @param {number} config.outputSize - Number of output neurons
     * @param {string} [config.activation='sigmoid'] - Activation function
     * @param {Object} [config.initParams={}] - Weight initialization parameters
     */
    constructor(config) {
      if (!Prime.Utils.isObject(config)) {
        throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
          "Layer configuration must be an object",
          { providedType: typeof config },
          "INVALID_LAYER_CONFIG"
        );
      }

      this.inputSize = config.inputSize;
      this.outputSize = config.outputSize;
      this.activation = config.activation || "sigmoid";

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
      this.momentum = null;
      this.velocity = null;
      this.iteration = 0;

      // Usage pattern tracking
      this.usagePatterns = {
        activationDistribution: new Array(this.outputSize).fill(0),
        inputDistribution: new Array(this.inputSize).fill(0),
        sampleCount: 0,
      };
    }

    /**
     * Initialize weights with appropriate distribution
     * @private
     * @param {Object} params - Initialization parameters
     * @returns {Array} Initialized weights matrix
     */
    _initializeWeights(params) {
      // Validate dimensions before creating the weight matrix
      if (!Number.isInteger(this.outputSize) || this.outputSize <= 0) {
        throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
          `Invalid output size ${this.outputSize} for weight initialization. Must be a positive integer.`,
          { outputSize: this.outputSize },
          "INVALID_OUTPUT_SIZE"
        );
      }

      if (!Number.isInteger(this.inputSize) || this.inputSize <= 0) {
        throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
          `Invalid input size ${this.inputSize} for weight initialization. Must be a positive integer.`,
          { inputSize: this.inputSize },
          "INVALID_INPUT_SIZE"
        );
      }

      const scale = params.scale || Math.sqrt(2 / this.inputSize);
      const distribution = params.distribution || "xavier";

      try {
        // Use Matrix.create which has dimension validation
        const weights = Matrix.create(this.outputSize, this.inputSize);

        for (let i = 0; i < this.outputSize; i++) {
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

        // Log dimensions for debugging if logger is available
        if (Prime.Logger && Prime.Logger.debug) {
          Prime.Logger.debug(
            `Initialized weight matrix: [${this.outputSize}x${this.inputSize}]`,
          );
        }

        return weights;
      } catch (error) {
        // Wrap all errors with proper context
        throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
          `Error initializing weights: ${error.message}`,
          { 
            inputSize: this.inputSize, 
            outputSize: this.outputSize,
            distribution,
            scale,
            originalError: error.message
          },
          "WEIGHT_INITIALIZATION_ERROR",
          error
        );
      }
    }

    /**
     * Initialize biases
     * @private
     * @param {Object} params - Initialization parameters
     * @returns {Array} Initialized biases vector
     */
    _initializeBiases(params) {
      // Validate dimensions before creating the bias vector
      if (!Number.isInteger(this.outputSize) || this.outputSize <= 0) {
        throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
          `Invalid output size ${this.outputSize} for bias initialization. Must be a positive integer.`,
          { outputSize: this.outputSize },
          "INVALID_OUTPUT_SIZE"
        );
      }

      const biasValue = params.bias || 0;

      try {
        // Use Vector.create if available, otherwise fallback to regular array
        if (Vector && Vector.create) {
          return Vector.create(this.outputSize, biasValue);
        } else {
          return new Array(this.outputSize).fill(biasValue);
        }
      } catch (error) {
        // Wrap all errors with proper context
        throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
          `Error initializing biases: ${error.message}`,
          { 
            outputSize: this.outputSize,
            biasValue,
            originalError: error.message
          },
          "BIAS_INITIALIZATION_ERROR",
          error
        );
      }
    }

    /**
     * Apply activation function to a value
     * @param {number} x - Input value
     * @returns {number} Activated value
     */
    _activate(x) {
      try {
        // If Neural.Activation is available, use it
        if (Prime.Neural.Activation && typeof Prime.Neural.Activation.get === 'function') {
          const activation = Prime.Neural.Activation.get(this.activation);
          if (activation && typeof activation.forward === 'function') {
            return activation.forward([x])[0];
          }
        }
        
        // Otherwise, use built-in implementations
        switch (this.activation) {
          case "sigmoid":
            return 1 / (1 + Math.exp(-x));
          case "relu":
            return Math.max(0, x);
          case "tanh":
            return Math.tanh(x);
          case "linear":
            return x;
          default:
            return 1 / (1 + Math.exp(-x)); // Default to sigmoid
        }
      } catch (error) {
        // Handle activation errors gracefully - use sigmoid as fallback
        if (Prime.Logger && Prime.Logger.warn) {
          Prime.Logger.warn(
            `Error applying activation function ${this.activation}: ${error.message}. Using sigmoid as fallback.`
          );
        }
        return 1 / (1 + Math.exp(-x)); // Sigmoid fallback
      }
    }

    /**
     * Apply activation function derivative to a value
     * @param {number} x - Input value
     * @returns {number} Derivative of activation
     */
    _activationDerivative(x) {
      try {
        // If Neural.Activation is available, use it for gradient calculation
        if (Prime.Neural.Activation && typeof Prime.Neural.Activation.get === 'function') {
          const activation = Prime.Neural.Activation.get(this.activation);
          if (activation && typeof activation.backward === 'function') {
            const y = this._activate(x);
            return activation.backward([x], [y])[0];
          }
        }
        
        // Otherwise, use built-in implementations
        switch (this.activation) {
          case "sigmoid": {
            const sigX = 1 / (1 + Math.exp(-x));
            return sigX * (1 - sigX);
          }
          case "relu":
            return x > 0 ? 1 : 0;
          case "tanh": {
            const tanhX = Math.tanh(x);
            return 1 - tanhX * tanhX;
          }
          case "linear":
            return 1;
          default: {
            const sigX = 1 / (1 + Math.exp(-x));
            return sigX * (1 - sigX);
          }
        }
      } catch (error) {
        // Handle activation errors gracefully - use sigmoid derivative as fallback
        if (Prime.Logger && Prime.Logger.warn) {
          Prime.Logger.warn(
            `Error calculating activation derivative for ${this.activation}: ${error.message}. Using sigmoid derivative as fallback.`
          );
        }
        const sigX = 1 / (1 + Math.exp(-x));
        return sigX * (1 - sigX); // Sigmoid derivative fallback
      }
    }

    /**
     * Forward pass through the layer
     * @param {Array} input - Input activation vector
     * @returns {Object} Output with activation and cache for backprop
     */
    forward(input) {
      try {
        if (!Array.isArray(input) || input.length !== this.inputSize) {
          throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
            `Input must be an array of length ${this.inputSize}`,
            { 
              inputLength: input ? input.length : null, 
              expectedLength: this.inputSize,
              isArray: Array.isArray(input)
            },
            "INVALID_INPUT_DIMENSIONS"
          );
        }

        const startTime = performance.now();

        // Update usage pattern tracking
        this._updateInputDistribution(input);

        // Compute linear combination (z = Wx + b)
        const z = new Array(this.outputSize).fill(0);

        for (let i = 0; i < this.outputSize; i++) {
          for (let j = 0; j < this.inputSize; j++) {
            z[i] += this.weights[i][j] * input[j];
          }
          z[i] += this.biases[i];
        }

        // Apply activation function
        const activation = z.map(this._activate.bind(this));

        // Update activation distribution
        this._updateActivationDistribution(activation);

        // Update performance metrics
        const endTime = performance.now();
        this._updateForwardMetrics(endTime - startTime);

        // Return both activation and cache for backprop
        return {
          activation,
          cache: { input, z },
        };
      } catch (error) {
        // Re-throw LayerError instances
        if (error instanceof Prime.Neural.Errors.LayerError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
          `Error during layer forward pass: ${error.message}`,
          { 
            inputSize: input ? input.length : null,
            layerType: this.constructor.name,
            originalError: error.message 
          },
          "FORWARD_PASS_ERROR",
          error
        );
      }
    }

    /**
     * Backward pass to compute gradients
     * @param {Array} dY - Gradient of loss with respect to output
     * @param {Object} cache - Cache from forward pass
     * @returns {Object} Gradients for weights, biases, and inputs
     */
    backward(dY, cache) {
      try {
        if (!Array.isArray(dY) || dY.length !== this.outputSize) {
          throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
            `Output gradient must be an array of length ${this.outputSize}`,
            { 
              gradientLength: dY ? dY.length : null, 
              expectedLength: this.outputSize,
              isArray: Array.isArray(dY)
            },
            "INVALID_GRADIENT_DIMENSIONS"
          );
        }

        const startTime = performance.now();
        const { input, z } = cache;

        // Compute gradient of activation function
        const dZ = dY.map((dy, i) => dy * this._activationDerivative(z[i]));

        // Compute gradients for weights
        const dW = Matrix.create(this.outputSize, this.inputSize);
        for (let i = 0; i < this.outputSize; i++) {
          for (let j = 0; j < this.inputSize; j++) {
            dW[i][j] = dZ[i] * input[j];
          }
        }

        // Compute gradients for biases
        const dB = [...dZ]; // Clone dZ array

        // Compute gradients for inputs (for backprop to previous layer)
        const dX = new Array(this.inputSize).fill(0);
        for (let j = 0; j < this.inputSize; j++) {
          for (let i = 0; i < this.outputSize; i++) {
            dX[j] += dZ[i] * this.weights[i][j];
          }
        }

        // Update performance metrics
        const endTime = performance.now();
        this._updateBackwardMetrics(endTime - startTime);

        return { dW, dB, dX };
      } catch (error) {
        // Re-throw LayerError instances
        if (error instanceof Prime.Neural.Errors.LayerError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
          `Error during layer backward pass: ${error.message}`,
          { 
            outputSize: this.outputSize,
            layerType: this.constructor.name,
            originalError: error.message 
          },
          "BACKWARD_PASS_ERROR",
          error
        );
      }
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
     * Update input distribution statistics
     * @private
     * @param {Array} input - Input vector
     */
    _updateInputDistribution(input) {
      this.usagePatterns.sampleCount++;

      // Update exponential moving average of input distribution
      for (let i = 0; i < this.inputSize; i++) {
        this.usagePatterns.inputDistribution[i] =
          0.999 * this.usagePatterns.inputDistribution[i] +
          0.001 * Math.abs(input[i]);
      }
    }

    /**
     * Update activation distribution statistics
     * @private
     * @param {Array} activation - Output activation vector
     */
    _updateActivationDistribution(activation) {
      // Update exponential moving average of activation distribution
      for (let i = 0; i < this.outputSize; i++) {
        this.usagePatterns.activationDistribution[i] =
          0.999 * this.usagePatterns.activationDistribution[i] +
          0.001 * activation[i];
      }
    }

    /**
     * Get layer performance metrics
     * @returns {Object} Current performance metrics
     */
    getMetrics() {
      return { ...this.metrics };
    }

    /**
     * Get layer usage patterns
     * @returns {Object} Current usage patterns
     */
    getUsagePatterns() {
      return {
        activationDistribution: [...this.usagePatterns.activationDistribution],
        inputDistribution: [...this.usagePatterns.inputDistribution],
        sampleCount: this.usagePatterns.sampleCount,
      };
    }

    /**
     * Update layer parameters with given gradients
     * @param {Object} gradients - Weight and bias gradients
     * @param {number} learningRate - Learning rate for update
     */
    update(gradients, learningRate) {
      try {
        const { dW, dB } = gradients;

        // Validate gradients
        if (!dW || !dB) {
          throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
            "Gradients object must contain dW and dB properties",
            { 
              hasWeightGradients: !!dW, 
              hasBiasGradients: !!dB 
            },
            "INVALID_GRADIENTS"
          );
        }

        // Update weights
        for (let i = 0; i < this.outputSize; i++) {
          for (let j = 0; j < this.inputSize; j++) {
            this.weights[i][j] -= learningRate * dW[i][j];
          }
        }

        // Update biases
        for (let i = 0; i < this.outputSize; i++) {
          this.biases[i] -= learningRate * dB[i];
        }

        this.iteration++;
      } catch (error) {
        // Re-throw LayerError instances
        if (error instanceof Prime.Neural.Errors.LayerError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
          `Error updating layer parameters: ${error.message}`,
          { 
            learningRate,
            iteration: this.iteration,
            layerType: this.constructor.name,
            originalError: error.message 
          },
          "PARAMETER_UPDATE_ERROR",
          error
        );
      }
    }
    
    /**
     * Calculate layer coherence score
     * Higher values indicate better numerical properties
     * @returns {number} Coherence score between 0 and 1
     */
    calculateCoherence() {
      try {
        // Component 1: Check for NaN/Infinity in weights and biases
        let nonFiniteCount = 0;
        const totalParams = this.outputSize * this.inputSize + this.outputSize;
        
        // Check weights
        for (let i = 0; i < this.outputSize; i++) {
          for (let j = 0; j < this.inputSize; j++) {
            if (!Number.isFinite(this.weights[i][j])) {
              nonFiniteCount++;
            }
          }
        }
        
        // Check biases
        for (let i = 0; i < this.outputSize; i++) {
          if (!Number.isFinite(this.biases[i])) {
            nonFiniteCount++;
          }
        }
        
        // Component 2: Weight magnitude distribution
        let weightMagnitude = 0;
        for (let i = 0; i < this.outputSize; i++) {
          for (let j = 0; j < this.inputSize; j++) {
            weightMagnitude += Math.pow(this.weights[i][j], 2);
          }
        }
        weightMagnitude = Math.sqrt(weightMagnitude);
        
        const idealMagnitude = Math.sqrt(this.inputSize * this.outputSize) * 0.5;
        const weightCoherence = Math.exp(
          -Math.abs(weightMagnitude - idealMagnitude) / idealMagnitude
        );
        
        // Component 3: Activation distribution
        const activationDist = this.usagePatterns.activationDistribution;
        const mean = activationDist.reduce((a, b) => a + b, 0) / this.outputSize;
        
        let deadNeurons = 0;
        let saturatedNeurons = 0;
        
        for (let i = 0; i < activationDist.length; i++) {
          if (activationDist[i] < 0.01) deadNeurons++;
          if (activationDist[i] > 0.9) saturatedNeurons++;
        }
        
        const deadRatio = deadNeurons / this.outputSize;
        const saturatedRatio = saturatedNeurons / this.outputSize;
        const activationBalance = 1 - Math.max(deadRatio, saturatedRatio);
        
        // Calculate final coherence score
        // Non-finite parameters instantly reduce coherence
        const finitePenalty = nonFiniteCount > 0 ? 
          Math.max(0, 1 - nonFiniteCount / totalParams) : 1;
        
        return finitePenalty * (
          0.4 * activationBalance + 
          0.3 * weightCoherence + 
          0.3 * (1 - Math.min(deadRatio + saturatedRatio, 1))
        );
      } catch (error) {
        // For coherence calculation, we return a low score on error rather than throwing
        if (Prime.Logger && Prime.Logger.warn) {
          Prime.Logger.warn(
            `Error calculating layer coherence: ${error.message}. Returning minimum score.`
          );
        }
        return 0;
      }
    }
  }

  /**
   * Self-Optimizing Neural Layer
   * Extends base layer with adaptation mechanisms
   */
  class SelfOptimizingLayer extends NeuralLayer {
    /**
     * Create a new self-optimizing neural layer
     * @param {Object} config - Layer configuration
     * @param {Object} [config.optimization={}] - Optimization parameters
     */
    constructor(config) {
      super(config);

      // Self-optimization parameters
      this.optimization = {
        enabled: config.optimization?.enabled ?? true,
        adaptThreshold: config.optimization?.adaptThreshold ?? 100,
        coherenceThreshold: config.optimization?.coherenceThreshold ?? 0.8,
        adaptationRate: config.optimization?.adaptationRate ?? 0.01,
        sparsityTarget: config.optimization?.sparsityTarget ?? 0.5,
        dropoutRate: config.optimization?.dropoutRate ?? 0.0,
        l1Regularization: config.optimization?.l1Regularization ?? 0.0,
        l2Regularization: config.optimization?.l2Regularization ?? 0.0,
      };

      // Adaptation state
      this.adaptationState = {
        lastOptimized: 0,
        dropoutMask: new Array(this.outputSize).fill(1),
        weightImportance: Matrix.create(this.outputSize, this.inputSize, 1),
        adaptationHistory: [],
      };
    }

    /**
     * Forward pass with self-optimization features
     * @param {Array} input - Input activation vector
     * @returns {Object} Output activation and cache
     */
    forward(input) {
      try {
        // Apply standard forward pass
        const result = super.forward(input);

        // Apply dropout during training if enabled
        if (this.optimization.dropoutRate > 0) {
          this._applyDropout(result.activation);
        }

        // Check if adaptation is needed
        if (
          this.optimization.enabled &&
          this.metrics.forwardCount % this.optimization.adaptThreshold === 0 &&
          this.metrics.forwardCount > 0
        ) {
          this._adaptLayer();
        }

        return result;
      } catch (error) {
        // Re-throw LayerError instances
        if (error instanceof Prime.Neural.Errors.LayerError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
          `Error during self-optimizing layer forward pass: ${error.message}`,
          { 
            dropoutRate: this.optimization.dropoutRate,
            adaptEnabled: this.optimization.enabled,
            forwardCount: this.metrics.forwardCount,
            layerType: "SelfOptimizingLayer",
            originalError: error.message 
          },
          "SELF_OPTIMIZING_FORWARD_ERROR",
          error
        );
      }
    }

    /**
     * Apply dropout to activation
     * @private
     * @param {Array} activation - Activation values to apply dropout to
     */
    _applyDropout(activation) {
      // Only generate new dropout mask occasionally to ensure consistency
      if (this.metrics.forwardCount % 20 === 0) {
        for (let i = 0; i < this.outputSize; i++) {
          this.adaptationState.dropoutMask[i] =
            Math.random() >= this.optimization.dropoutRate ? 1 : 0;
        }
      }

      // Apply dropout mask
      for (let i = 0; i < this.outputSize; i++) {
        if (this.adaptationState.dropoutMask[i] === 0) {
          activation[i] = 0;
        } else if (this.optimization.dropoutRate > 0) {
          // Scale by dropout probability to maintain expected value
          activation[i] /= 1 - this.optimization.dropoutRate;
        }
      }
    }

    /**
     * Adapt layer based on usage patterns
     * @private
     */
    _adaptLayer() {
      try {
        if (Prime.Logger && Prime.Logger.info) {
          Prime.Logger.info("Adapting self-optimizing neural layer", {
            inputSize: this.inputSize,
            outputSize: this.outputSize,
            iteration: this.iteration,
          });
        }

        // Calculate current coherence score
        const coherenceScore = this._calculateCoherenceScore();
        this.metrics.coherence = coherenceScore;

        // Record adaptation attempt
        this.adaptationState.lastOptimized = this.metrics.forwardCount;

        // Only adapt if coherence is below threshold
        if (coherenceScore < this.optimization.coherenceThreshold) {
          this._optimizeWeightDistribution();
          this._pruneInactiveConnections();
          this._adjustActivationFunction();
        }

        // Record adaptation in history (even if no changes were made)
        this.adaptationState.adaptationHistory.push({
          iteration: this.iteration,
          coherenceBefore: coherenceScore,
          coherenceAfter: this._calculateCoherenceScore(),
          timestamp: new Date().toISOString(),
          adapted: coherenceScore < this.optimization.coherenceThreshold,
        });
      } catch (error) {
        // For adaptation errors, log but don't throw (allow training to continue)
        if (Prime.Logger && Prime.Logger.warn) {
          Prime.Logger.warn(
            `Error during layer adaptation: ${error.message}. Skipping adaptation.`,
            {
              layerType: "SelfOptimizingLayer",
              iteration: this.iteration,
              forwardCount: this.metrics.forwardCount
            }
          );
        }
      }
    }

    /**
     * Calculate coherence score of the layer
     * @private
     * @returns {number} Coherence score between 0 and 1
     */
    _calculateCoherenceScore() {
      // Use standard coherence calculation from the base class if available
      if (typeof super.calculateCoherence === 'function') {
        return super.calculateCoherence();
      }
      
      // Component 1: Activation distribution uniformity (0-1)
      // Higher is better - we want balanced neuron activations
      const activationDistribution = this.usagePatterns.activationDistribution;
      const meanActivation =
        activationDistribution.reduce((a, b) => a + b, 0) / this.outputSize;

      const activationVariance =
        activationDistribution.reduce(
          (sum, act) => sum + Math.pow(act - meanActivation, 2),
          0,
        ) / this.outputSize;

      const maxVariance = Math.pow(meanActivation, 2); // Theoretical max variance
      const activationBalance = Math.max(
        0,
        1 - Math.sqrt(activationVariance / (maxVariance + 1e-10)),
      );

      // Component 2: Weight matrix coherence (0-1)
      // Lower magnitude, better distributed weights = higher score
      let weightMagnitude = 0;
      for (let i = 0; i < this.outputSize; i++) {
        for (let j = 0; j < this.inputSize; j++) {
          weightMagnitude += Math.pow(this.weights[i][j], 2);
        }
      }
      weightMagnitude = Math.sqrt(weightMagnitude);

      const idealMagnitude = Math.sqrt(this.inputSize * this.outputSize) * 0.5;
      const weightCoherence = Math.exp(
        -Math.abs(weightMagnitude - idealMagnitude) / idealMagnitude,
      );

      // Component 3: Input-output correlation appropriateness (0-1)
      // Higher score means weights align well with input distribution
      let correlationScore = 0;
      for (let j = 0; j < this.inputSize; j++) {
        const inputActivity = this.usagePatterns.inputDistribution[j];
        let weightMagnitudeForInput = 0;

        for (let i = 0; i < this.outputSize; i++) {
          weightMagnitudeForInput += Math.pow(this.weights[i][j], 2);
        }
        weightMagnitudeForInput = Math.sqrt(weightMagnitudeForInput);

        // Score is higher when active inputs have appropriate weight magnitudes
        correlationScore +=
          (1 - Math.exp(-inputActivity)) *
          (1 - Math.abs(weightMagnitudeForInput - inputActivity));
      }
      correlationScore /= this.inputSize;

      // Combine components with appropriate weights
      return (
        0.4 * activationBalance + 0.3 * weightCoherence + 0.3 * correlationScore
      );
    }

    /**
     * Optimize weight distribution based on usage patterns
     * @private
     */
    _optimizeWeightDistribution() {
      const inputImportance = [...this.usagePatterns.inputDistribution];
      const activationImportance = [
        ...this.usagePatterns.activationDistribution,
      ];

      // Normalize importance vectors
      const normalizeVector = (v) => {
        const sum = v.reduce((a, b) => a + b, 0) || 1;
        return v.map((x) => x / sum);
      };

      const normInputImp = normalizeVector(inputImportance);
      const normActImp = normalizeVector(activationImportance);

      // Adjust weights based on input and activation importance
      for (let i = 0; i < this.outputSize; i++) {
        for (let j = 0; j < this.inputSize; j++) {
          // Calculate target weight importance
          const targetImportance = Math.sqrt(normInputImp[j] * normActImp[i]);

          // Adjust weight distribution (slowly)
          const currentMagnitude = Math.abs(this.weights[i][j]);
          const adjustmentFactor = Math.pow(
            targetImportance /
              (this.adaptationState.weightImportance[i][j] || 0.01),
            this.optimization.adaptationRate,
          );

          // Update weight while preserving sign
          const sign = Math.sign(this.weights[i][j]) || 1;
          this.weights[i][j] = sign * currentMagnitude * adjustmentFactor;

          // Update importance record
          this.adaptationState.weightImportance[i][j] =
            0.9 * this.adaptationState.weightImportance[i][j] +
            0.1 * targetImportance;
        }
      }
    }

    /**
     * Prune inactive connections to promote sparsity
     * @private
     */
    _pruneInactiveConnections() {
      // Calculate importance threshold based on distribution
      const allImportances = [];
      for (let i = 0; i < this.outputSize; i++) {
        for (let j = 0; j < this.inputSize; j++) {
          allImportances.push(this.adaptationState.weightImportance[i][j]);
        }
      }

      // Sort importances and find threshold value
      allImportances.sort((a, b) => a - b);
      const thresholdIndex = Math.floor(
        allImportances.length * this.optimization.sparsityTarget,
      );
      const importanceThreshold = allImportances[thresholdIndex] || 0;

      // Apply pruning to low-importance connections
      for (let i = 0; i < this.outputSize; i++) {
        for (let j = 0; j < this.inputSize; j++) {
          if (
            this.adaptationState.weightImportance[i][j] < importanceThreshold &&
            Math.random() < 0.1
          ) {
            // Probabilistic pruning to avoid sudden changes
            this.weights[i][j] = 0;
          }
        }
      }
    }

    /**
     * Adjust activation function parameters based on distribution
     * @private
     */
    _adjustActivationFunction() {
      // Get current activation distribution
      const activationDist = this.usagePatterns.activationDistribution;
      const mean = activationDist.reduce((a, b) => a + b, 0) / this.outputSize;

      // Skip adjustment if not enough data
      if (this.metrics.forwardCount < 10) return;

      // Calculate statistics about activation distribution
      let deadNeurons = 0;
      let saturatedNeurons = 0;

      for (let i = 0; i < activationDist.length; i++) {
        if (activationDist[i] < 0.01) deadNeurons++;
        if (activationDist[i] > 0.9) saturatedNeurons++;
      }

      const deadRatio = deadNeurons / this.outputSize;
      const saturatedRatio = saturatedNeurons / this.outputSize;

      // Adjust activation parameters based on type
      switch (this.activation) {
        case "relu":
          // For ReLU, introduce leakiness if too many dead neurons
          if (deadRatio > 0.2) {
            this.activationParams = this.activationParams || {};
            this.activationParams.leakySlope = 0.01;

            // Replace activation function implementation
            this._activate = (x) =>
              x > 0 ? x : x * this.activationParams.leakySlope;
            this._activationDerivative = (x) =>
              x > 0 ? 1 : this.activationParams.leakySlope;
          }
          break;

        case "sigmoid":
          // For sigmoid, adjust scaling factor if too many saturated neurons
          if (saturatedRatio > 0.3) {
            this.activationParams = this.activationParams || {};
            this.activationParams.scale = Math.max(
              0.5,
              this.activationParams.scale || 1.0 - 0.1,
            );

            // Replace activation function implementation with scaled version
            this._activate = (x) =>
              1 / (1 + Math.exp(-x * this.activationParams.scale));
            this._activationDerivative = (x) => {
              const sigX = 1 / (1 + Math.exp(-x * this.activationParams.scale));
              return this.activationParams.scale * sigX * (1 - sigX);
            };
          }
          break;

        case "tanh":
          // For tanh, adjust scaling factor if too many saturated neurons
          if (saturatedRatio > 0.3) {
            this.activationParams = this.activationParams || {};
            this.activationParams.scale = Math.max(
              0.5,
              this.activationParams.scale || 1.0 - 0.1,
            );

            // Replace activation function implementation with scaled version
            this._activate = (x) => Math.tanh(x * this.activationParams.scale);
            this._activationDerivative = (x) => {
              const tanhX = Math.tanh(x * this.activationParams.scale);
              return this.activationParams.scale * (1 - tanhX * tanhX);
            };
          }
          break;

        default:
          // No adjustment for other activation functions
          break;
      }

      // Log adaptation
      if (this.activationParams) {
        this.adaptationState.adaptationHistory.push({
          iteration: this.iteration,
          type: "activation_adjustment",
          activation: this.activation,
          params: { ...this.activationParams },
          deadRatio,
          saturatedRatio,
          timestamp: new Date().toISOString(),
        });
      }
    }

    /**
     * Update with regularization
     * @param {Object} gradients - Weight and bias gradients
     * @param {number} learningRate - Learning rate for update
     */
    update(gradients, learningRate) {
      try {
        const { dW, dB } = gradients;

        // Apply regularization to gradients
        if (
          this.optimization.l1Regularization > 0 ||
          this.optimization.l2Regularization > 0
        ) {
          for (let i = 0; i < this.outputSize; i++) {
            for (let j = 0; j < this.inputSize; j++) {
              // L1 regularization (LASSO) - promotes sparsity
              if (this.optimization.l1Regularization > 0) {
                dW[i][j] +=
                  this.optimization.l1Regularization *
                  Math.sign(this.weights[i][j]);
              }

              // L2 regularization (Ridge) - prevents large weights
              if (this.optimization.l2Regularization > 0) {
                dW[i][j] +=
                  this.optimization.l2Regularization * this.weights[i][j];
              }
            }
          }
        }

        // Call parent update method with modified gradients
        super.update({ dW, dB }, learningRate);
      } catch (error) {
        // Re-throw LayerError instances
        if (error instanceof Prime.Neural.Errors.LayerError) {
          throw error;
        }
        
        // Wrap other errors with context
        throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
          `Error updating self-optimizing layer parameters: ${error.message}`,
          { 
            l1Regularization: this.optimization.l1Regularization,
            l2Regularization: this.optimization.l2Regularization,
            learningRate,
            layerType: "SelfOptimizingLayer",
            originalError: error.message 
          },
          "SELF_OPTIMIZING_UPDATE_ERROR",
          error
        );
      }
    }

    /**
     * Get adaptation history
     * @returns {Array} History of adaptation events
     */
    getAdaptationHistory() {
      return [...this.adaptationState.adaptationHistory];
    }

    /**
     * Analyze layer and return optimization recommendations
     * @returns {Object} Recommendations for layer optimization
     */
    analyzeLayer() {
      try {
        const metrics = this.getMetrics();
        const patterns = this.getUsagePatterns();

        // Calculate neuron activity
        const activeNeurons = patterns.activationDistribution.filter(
          (a) => a > 0.01,
        ).length;

        const unusedNeurons = patterns.activationDistribution.filter(
          (a) => a < 0.001,
        ).length;

        // Calculate sparsity
        let nonZeroWeights = 0;
        const totalWeights = this.inputSize * this.outputSize;

        for (let i = 0; i < this.outputSize; i++) {
          for (let j = 0; j < this.inputSize; j++) {
            if (Math.abs(this.weights[i][j]) > 1e-6) {
              nonZeroWeights++;
            }
          }
        }

        const weightSparsity = 1 - nonZeroWeights / totalWeights;

        // Generate recommendations
        return {
          coherence: metrics.coherence,
          activeNeurons,
          unusedNeurons,
          utilizationRate: activeNeurons / this.outputSize,
          weightSparsity,
          recommendations: [
            unusedNeurons > this.outputSize * 0.3
              ? "Consider reducing layer size"
              : null,
            weightSparsity < 0.2
              ? "Increase L1 regularization to promote sparsity"
              : null,
            metrics.coherence < 0.5
              ? "Layer may benefit from more frequent adaptation"
              : null,
          ].filter(Boolean),
        };
      } catch (error) {
        // For analysis errors, return simplified diagnostic info without throwing
        if (Prime.Logger && Prime.Logger.warn) {
          Prime.Logger.warn(
            `Error analyzing self-optimizing layer: ${error.message}. Returning basic diagnostics.`,
            {
              layerType: "SelfOptimizingLayer",
              inputSize: this.inputSize,
              outputSize: this.outputSize
            }
          );
        }
        
        return {
          coherence: this.metrics.coherence || 0,
          activeNeurons: "Error during analysis",
          recommendations: ["Analysis failed due to error: " + error.message]
        };
      }
    }
  }

  // Initialize the namespace if it doesn't exist
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Layer = Prime.Neural.Layer || {};

  // Add classes to Prime.Neural namespace
  Object.assign(Prime.Neural.Layer, {
    NeuralLayer,
    SelfOptimizingLayer,
  });
  
  // Eagerly load other layer types to ensure they're registered
  try {
    require('./dense.js');
    require('./dense-layer.js');
    require('./convolutional.js');
    require('./recurrent.js');
  } catch (e) {
    // Silently ignore errors if files can't be loaded
    // This happens in browser environments where require() might not work
    if (Prime.Logger && Prime.Logger.debug) {
      Prime.Logger.debug('Could not eagerly load all layer types', { error: e.message });
    }
  }
})();

// This module exports the Prime object with the Neural namespace
module.exports = Prime;