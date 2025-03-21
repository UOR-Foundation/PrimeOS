/**
 * PrimeOS JavaScript Library - Neural Layer Module
 * Core neural layer functionality
 */

// Import the Prime object from core
const Prime = require("../../core");
const Vector = Prime.Math.Vector;
const Matrix = Prime.Math.Matrix;

// Import from other modules if needed
// These will be implemented later

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
        throw new Prime.ValidationError(
          "Layer configuration must be an object",
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
      const scale = params.scale || Math.sqrt(2 / this.inputSize);
      const distribution = params.distribution || "xavier";

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

      return weights;
    }

    /**
     * Initialize biases
     * @private
     * @param {Object} params - Initialization parameters
     * @returns {Array} Initialized biases vector
     */
    _initializeBiases(params) {
      const biasValue = params.bias || 0;

      return new Array(this.outputSize).fill(biasValue);
    }

    /**
     * Apply activation function to a value
     * @param {number} x - Input value
     * @returns {number} Activated value
     */
    _activate(x) {
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
    }

    /**
     * Apply activation function derivative to a value
     * @param {number} x - Input value
     * @returns {number} Derivative of activation
     */
    _activationDerivative(x) {
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
    }

    /**
     * Forward pass through the layer
     * @param {Array} input - Input activation vector
     * @returns {Object} Output with activation and cache for backprop
     */
    forward(input) {
      if (!Array.isArray(input) || input.length !== this.inputSize) {
        throw new Prime.ValidationError(
          `Input must be an array of length ${this.inputSize}`,
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
    }

    /**
     * Backward pass to compute gradients
     * @param {Array} dY - Gradient of loss with respect to output
     * @param {Object} cache - Cache from forward pass
     * @returns {Object} Gradients for weights, biases, and inputs
     */
    backward(dY, cache) {
      if (!Array.isArray(dY) || dY.length !== this.outputSize) {
        throw new Prime.ValidationError(
          `Output gradient must be an array of length ${this.outputSize}`,
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
      const { dW, dB } = gradients;

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
      Prime.Logger.info("Adapting self-optimizing neural layer", {
        inputSize: this.inputSize,
        outputSize: this.outputSize,
        iteration: this.iteration,
      });

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
    }

    /**
     * Calculate coherence score of the layer
     * @private
     * @returns {number} Coherence score between 0 and 1
     */
    _calculateCoherenceScore() {
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
      // This is a placeholder for activation function adjustment
      // In a real implementation, this could modify activation function parameters
      // like the slope of sigmoid or threshold of ReLU
    }

    /**
     * Update with regularization
     * @param {Object} gradients - Weight and bias gradients
     * @param {number} learningRate - Learning rate for update
     */
    update(gradients, learningRate) {
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
      let totalWeights = this.inputSize * this.outputSize;

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
    }
  }

  // Add classes to Prime.Neural namespace
  Prime.Neural.Layer = {
    NeuralLayer,
    SelfOptimizingLayer,
  };
})();

// Export the enhanced Prime object
module.exports = Prime;
