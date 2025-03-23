/**
 * PrimeOS JavaScript Library - Neural Network Model
 * Core model implementation with memory optimization and coherence awareness
 */

// Import the Prime object from core
const Prime = require('../core');

// Create the Neural Model module using IIFE
(function () {
  /**
   * Neural Network Model
   * Main class for creating, training, and using neural network models
   */
  class NeuralModel {
    /**
     * Create a new neural network model
     * @param {Object} config - Model configuration
     * @param {Array} [config.layers=[]] - Array of layer configurations or instances
     * @param {Object} [config.optimizer=null] - Optimizer configuration or instance
     * @param {boolean} [config.useTypedArrays=true] - Whether to use TypedArrays for memory efficiency
     * @param {Object} [config.coherence={}] - Coherence monitoring configuration
     * @param {Object} [config.metadata={}] - Model metadata
     */
    constructor(config = {}) {
      // Initialize model properties
      this.layers = [];
      this.optimizer = null;
      this.compiled = false;
      this.lossFunction = null;
      this.metric = null;
      this.useTypedArrays = config.useTypedArrays !== false;

      // Set coherence configuration
      this.coherenceConfig = {
        enabled: true,
        minThreshold: 0.7,
        checkFrequency: 10,
        autoCorrect: true,
        ...(config.coherence || {}),
      };

      // Initialize metadata
      this.metadata = {
        createdAt: new Date().toISOString(),
        ...(config.metadata || {}),
      };

      // Track performance and training history
      this.history = [];
      this.performance = {
        forwardTime: 0,
        backwardTime: 0,
        iterationCount: 0,
        lastCoherence: 1.0,
      };

      // Add layers if provided
      if (Array.isArray(config.layers)) {
        config.layers.forEach((layerConfig) => {
          this.addLayer(layerConfig);
        });
      }

      // Set optimizer if provided
      if (config.optimizer) {
        this.setOptimizer(config.optimizer);
      }
    }

    /**
     * Add a layer to the model
     * @param {Object|Prime.Neural.Layer.NeuralLayer} layerConfig - Layer configuration or instance
     * @returns {Prime.Neural.Model.NeuralModel} This model instance (for chaining)
     */
    addLayer(layerConfig) {
      let layer;

      // If layerConfig is already a layer instance, use it directly
      if (
        Prime.Neural.Layer &&
        ((Prime.Neural.Layer.NeuralLayer &&
          layerConfig instanceof Prime.Neural.Layer.NeuralLayer) ||
          (Prime.Neural.Layer.SelfOptimizingLayer &&
            layerConfig instanceof Prime.Neural.Layer.SelfOptimizingLayer) ||
          (Prime.Neural.Layer.ConvolutionalLayer &&
            layerConfig instanceof Prime.Neural.Layer.ConvolutionalLayer) ||
          (Prime.Neural.Layer.RecurrentLayer &&
            layerConfig instanceof Prime.Neural.Layer.RecurrentLayer))
      ) {
        layer = layerConfig;
      } else {
        // Otherwise, create a layer from the configuration
        const type = (layerConfig.type || 'dense').toLowerCase();

        // Create layer based on type
        switch (type) {
          case 'dense':
            layer = Prime.Neural.Neural.createLayer('dense', {
              ...layerConfig,
              useTypedArrays: this.useTypedArrays,
            });
            break;
          case 'conv':
          case 'convolutional':
            layer = Prime.Neural.Neural.createLayer('conv', {
              ...layerConfig,
              useTypedArrays: this.useTypedArrays,
            });
            break;
          case 'rnn':
          case 'recurrent':
            layer = Prime.Neural.Neural.createLayer('recurrent', {
              ...layerConfig,
              useTypedArrays: this.useTypedArrays,
            });
            break;
          case 'self_optimizing':
          case 'selfoptimizing':
            layer = new Prime.Neural.Layer.SelfOptimizingLayer({
              ...layerConfig,
              useTypedArrays: this.useTypedArrays,
            });
            break;
          default:
            throw new Error(`Unknown layer type: ${type}`);
        }
      }

      // Validate layer compatibility with the previous layer
      if (this.layers.length > 0) {
        const prevLayer = this.layers[this.layers.length - 1];
        if (prevLayer.outputSize !== layer.inputSize) {
          throw new Error(
            `Layer input size mismatch: previous layer output size is ${prevLayer.outputSize}, ` +
              `but new layer input size is ${layer.inputSize}`,
          );
        }
      }

      // Add layer to the model
      this.layers.push(layer);

      // Reset compiled state as model structure has changed
      this.compiled = false;

      return this;
    }

    /**
     * Set the optimizer for the model
     * @param {Object|Prime.Neural.Optimization.Optimizer} optimizer - Optimizer configuration or instance
     * @returns {Prime.Neural.Model.NeuralModel} This model instance (for chaining)
     */
    setOptimizer(optimizer) {
      // If optimizer is a string, create from factory
      if (typeof optimizer === 'string') {
        this.optimizer = Prime.Neural.Neural.createOptimizer(optimizer);
      }
      // If optimizer is configuration object, create from factory
      else if (typeof optimizer === 'object' && optimizer.type) {
        this.optimizer = Prime.Neural.Neural.createOptimizer(
          optimizer.type,
          optimizer,
        );
      }
      // If optimizer is already an optimizer instance, use directly
      else if (
        typeof optimizer === 'object' &&
        typeof optimizer.update === 'function'
      ) {
        this.optimizer = optimizer;
      }
      // Otherwise, throw error
      else {
        throw new Error('Invalid optimizer configuration');
      }

      return this;
    }

    /**
     * Compile the model with loss function and metrics
     * @param {Object} config - Compilation configuration
     * @param {string|Function} config.loss - Loss function name or custom function
     * @param {string|Function} [config.metric] - Evaluation metric name or custom function
     * @returns {Prime.Neural.Model.NeuralModel} This model instance (for chaining)
     */
    compile(config) {
      // Validate model has layers
      if (this.layers.length === 0) {
        throw new Error('Model must have at least one layer');
      }

      // Validate optimizer is set
      if (!this.optimizer) {
        // Default to Adam optimizer if none is set
        this.setOptimizer('adam');
      }

      // Set loss function
      if (typeof config.loss === 'string') {
        this.lossFunction = this._getLossFunction(config.loss);
      } else if (typeof config.loss === 'function') {
        this.lossFunction = config.loss;
      } else {
        throw new Error('Loss function must be a string or function');
      }

      // Set metric (optional)
      if (config.metric) {
        if (typeof config.metric === 'string') {
          this.metric = this._getMetricFunction(config.metric);
        } else if (typeof config.metric === 'function') {
          this.metric = config.metric;
        }
      }

      this.compiled = true;

      // Update metadata
      this.metadata.compiledAt = new Date().toISOString();
      if (typeof config.loss === 'string') {
        this.metadata.loss = config.loss;
      }
      if (typeof config.metric === 'string') {
        this.metadata.metric = config.metric;
      }

      return this;
    }

    /**
     * Forward pass through the model
     * @param {Array|TypedArray} input - Input data
     * @param {Object} [options={}] - Forward pass options
     * @param {boolean} [options.training=false] - Whether this is a training pass
     * @param {boolean} [options.returnIntermediates=false] - Whether to return intermediate activations
     * @returns {Object} Model output with activations and cache
     */
    forward(input, options = {}) {
      if (!this.layers.length) {
        throw new Error('Model has no layers');
      }

      const startTime = performance.now();
      const training = options.training !== false;
      const returnIntermediates = options.returnIntermediates === true;

      // Convert input to appropriate type if necessary
      let currentInput =
        this.useTypedArrays &&
        !(input instanceof Float32Array || input instanceof Float64Array)
          ? Prime.Neural.Neural.toTypedArray(input)
          : input;

      // Intermediate activations and cache for backprop
      const intermediates = returnIntermediates ? [] : null;
      const layerCache = training ? [] : null;

      // Forward pass through each layer
      for (let i = 0; i < this.layers.length; i++) {
        const layer = this.layers[i];
        const { activation, cache } = layer.forward(currentInput);

        // Store intermediates if requested
        if (returnIntermediates) {
          intermediates.push(activation);
        }

        // Store cache if in training mode
        if (training) {
          layerCache.push(cache);
        }

        // Update input for next layer
        currentInput = activation;
      }

      // Update performance metrics
      const endTime = performance.now();
      this._updateForwardTime(endTime - startTime);

      // Return output and cache
      return {
        output: currentInput,
        cache: layerCache,
        intermediates: intermediates,
      };
    }

    /**
     * Perform backward pass to compute gradients
     * @param {Array|TypedArray} expected - Expected output values
     * @param {Array|TypedArray} predicted - Predicted output values from forward pass
     * @param {Array} cache - Layer cache from forward pass
     * @returns {Object} Loss value and gradients
     */
    backward(expected, predicted, cache) {
      if (!this.compiled) {
        throw new Error('Model must be compiled before training');
      }

      const startTime = performance.now();

      // Calculate initial gradient from loss function
      const { loss, gradient } = this.lossFunction(expected, predicted, true);

      // Backward pass through each layer, starting from the last
      let currentGradient = gradient;
      const gradients = [];

      for (let i = this.layers.length - 1; i >= 0; i--) {
        const layer = this.layers[i];
        const layerCache = cache[i];

        // Compute gradients for this layer
        const { dW, dB, dX } = layer.backward(currentGradient, layerCache);

        // Store gradients for parameter updates
        gradients.unshift({ dW, dB });

        // Update gradient for previous layer
        currentGradient = dX;
      }

      // Update performance metrics
      const endTime = performance.now();
      this._updateBackwardTime(endTime - startTime);

      return { loss, gradients };
    }

    /**
     * Update model parameters based on gradients
     * @param {Array} gradients - Gradients for each layer
     * @returns {Promise<Object>} Updated coherence information
     */
    async update(gradients) {
      if (!this.optimizer) {
        throw new Error('Model must have an optimizer');
      }

      // Calculate model coherence before update if needed
      let preUpdateCoherence = null;
      if (
        this.coherenceConfig.enabled &&
        this.performance.iterationCount %
          this.coherenceConfig.checkFrequency ===
          0
      ) {
        preUpdateCoherence = this.calculateCoherence();
      }

      // Update each layer's parameters
      for (let i = 0; i < this.layers.length; i++) {
        const layer = this.layers[i];
        const layerGradients = gradients[i];

        // Use coherence-aware optimizer if available
        if (
          this.coherenceConfig.enabled &&
          typeof this.optimizer.update === 'function' &&
          typeof this.optimizer.calculateCoherence === 'function'
        ) {
          // Get current parameters
          const params = {
            weights: layer.weights,
            biases: layer.biases,
          };

          // Update parameters with coherence constraints
          const updatedParams = this.optimizer.update(
            params,
            layerGradients,
            this.calculateCoherence.bind(this),
          );

          // Apply updated parameters
          layer.weights = updatedParams.weights;
          layer.biases = updatedParams.biases;
        } else {
          // Standard update without coherence awareness
          layer.update(layerGradients, this.optimizer.learningRate);
        }
      }

      // Calculate post-update coherence if needed
      let coherenceInfo = null;
      if (preUpdateCoherence !== null) {
        const postUpdateCoherence = this.calculateCoherence();
        this.performance.lastCoherence = postUpdateCoherence;

        coherenceInfo = {
          before: preUpdateCoherence,
          after: postUpdateCoherence,
          delta: postUpdateCoherence - preUpdateCoherence,
          stable: postUpdateCoherence >= this.coherenceConfig.minThreshold,
        };

        // If coherence dropped below threshold and auto-correct is enabled,
        // attempt to restore coherence
        if (
          this.coherenceConfig.autoCorrect &&
          coherenceInfo.after < this.coherenceConfig.minThreshold
        ) {
          await this._attemptCoherenceCorrection(coherenceInfo);
          coherenceInfo.corrected = true;
          coherenceInfo.afterCorrection = this.calculateCoherence();
        }
      }

      return coherenceInfo;
    }

    /**
     * Train the model on a batch of data
     * @param {Array|TypedArray} inputs - Input data
     * @param {Array|TypedArray} targets - Target outputs
     * @param {Object} [options={}] - Training options
     * @returns {Object} Training results with loss and metrics
     */
    trainOnBatch(inputs, targets, options = {}) {
      if (!this.compiled) {
        throw new Error('Model must be compiled before training');
      }

      // Forward pass
      const { output, cache } = this.forward(inputs, { training: true });

      // Backward pass
      const { loss, gradients } = this.backward(targets, output, cache);

      // Update parameters
      this.update(gradients);

      // Calculate metric if available
      let metricValue = null;
      if (this.metric) {
        metricValue = this.metric(targets, output);
      }

      // Return training results
      return {
        loss,
        metric: metricValue,
      };
    }

    /**
     * Make predictions with the model
     * @param {Array|TypedArray} inputs - Input data
     * @returns {Array|TypedArray} Predicted outputs
     */
    predict(inputs) {
      const { output } = this.forward(inputs, { training: false });
      return output;
    }

    /**
     * Calculate the coherence score of the model
     * @returns {number} Coherence score (0-1)
     */
    calculateCoherence() {
      if (this.layers.length === 0) {
        return 1.0; // Perfect coherence for empty model
      }

      // Calculate coherence for each layer
      const layerCoherences = this.layers.map((layer) => {
        // Use layer's calculateCoherence method if available
        if (typeof layer.calculateCoherence === 'function') {
          return layer.calculateCoherence();
        }

        // Otherwise use a heuristic based on weight distribution
        let sumWeightsMagnitude = 0;
        let maxWeight = 0;

        for (let i = 0; i < layer.weights.length; i++) {
          for (let j = 0; j < layer.weights[i].length; j++) {
            const magnitude = Math.abs(layer.weights[i][j]);
            sumWeightsMagnitude += magnitude;
            maxWeight = Math.max(maxWeight, magnitude);
          }
        }

        // Calculate coefficient of variation as a coherence indicator
        const avgMagnitude =
          sumWeightsMagnitude /
          (layer.weights.length * layer.weights[0].length);
        return Math.min(1.0, (3.0 * avgMagnitude) / (maxWeight + 1e-8));
      });

      // Overall coherence is a weighted average of layer coherences,
      // with more weight given to deeper layers
      let weightedSum = 0;
      let weightSum = 0;

      for (let i = 0; i < layerCoherences.length; i++) {
        const layerWeight = 1 + i / layerCoherences.length; // Deeper layers get more weight
        weightedSum += layerCoherences[i] * layerWeight;
        weightSum += layerWeight;
      }

      return weightedSum / weightSum;
    }

    /**
     * Save the model to a serializable object
     * @returns {Object} Serialized model
     */
    toJSON() {
      // Create base model object
      const modelData = {
        version: '1.0',
        timestamp: new Date().toISOString(),
        metadata: this.metadata,
        coherenceConfig: this.coherenceConfig,
        layers: [],
        history: this.history.slice(-100), // Keep only recent history
      };

      // Add optimizer configuration if available
      if (this.optimizer) {
        modelData.optimizer = {
          type: this.optimizer.constructor.name,
          config: {
            learningRate: this.optimizer.learningRate,
          },
        };

        // Add optimizer-specific parameters
        if (this.optimizer.momentum !== undefined) {
          modelData.optimizer.config.momentum = this.optimizer.momentum;
        }
        if (this.optimizer.beta1 !== undefined) {
          modelData.optimizer.config.beta1 = this.optimizer.beta1;
        }
        if (this.optimizer.beta2 !== undefined) {
          modelData.optimizer.config.beta2 = this.optimizer.beta2;
        }
        if (this.optimizer.epsilon !== undefined) {
          modelData.optimizer.config.epsilon = this.optimizer.epsilon;
        }
      }

      // Add layer data
      this.layers.forEach((layer, index) => {
        // Common layer properties
        const layerData = {
          index,
          type: layer.constructor.name,
          inputSize: layer.inputSize,
          outputSize: layer.outputSize,
          activation: layer.activation,
          weights: this._serializeMatrix(layer.weights),
          biases: this._serializeArray(layer.biases),
        };

        // Add layer-specific properties
        if (layer.filters !== undefined) {
          layerData.filters = layer.filters;
        }
        if (layer.kernelSize !== undefined) {
          layerData.kernelSize = layer.kernelSize;
        }
        if (layer.strides !== undefined) {
          layerData.strides = layer.strides;
        }
        if (layer.padding !== undefined) {
          layerData.padding = layer.padding;
        }
        if (layer.hiddenSize !== undefined) {
          layerData.hiddenSize = layer.hiddenSize;
        }
        if (layer.cellType !== undefined) {
          layerData.cellType = layer.cellType;
        }
        if (layer.returnSequences !== undefined) {
          layerData.returnSequences = layer.returnSequences;
        }

        // Add to model layers
        modelData.layers.push(layerData);
      });

      return modelData;
    }

    /**
     * Load a model from a serialized object
     * @param {Object} modelData - Serialized model data
     * @returns {Prime.Neural.Model.NeuralModel} New model instance
     */
    static fromJSON(modelData) {
      // Create empty model
      const model = new NeuralModel({
        coherence: modelData.coherenceConfig,
        metadata: modelData.metadata,
      });

      // Add layers
      modelData.layers.forEach((layerData) => {
        // Reconstruct weights and biases
        const weights = this._deserializeMatrix(layerData.weights);
        const biases = this._deserializeArray(layerData.biases);

        // Create layer configuration
        const layerConfig = {
          type: layerData.type,
          inputSize: layerData.inputSize,
          outputSize: layerData.outputSize,
          activation: layerData.activation,
        };

        // Add layer-specific properties
        if (layerData.filters !== undefined) {
          layerConfig.filters = layerData.filters;
        }
        if (layerData.kernelSize !== undefined) {
          layerConfig.kernelSize = layerData.kernelSize;
        }
        if (layerData.strides !== undefined) {
          layerConfig.strides = layerData.strides;
        }
        if (layerData.padding !== undefined) {
          layerConfig.padding = layerData.padding;
        }
        if (layerData.hiddenSize !== undefined) {
          layerConfig.hiddenSize = layerData.hiddenSize;
        }
        if (layerData.cellType !== undefined) {
          layerConfig.cellType = layerData.cellType;
        }
        if (layerData.returnSequences !== undefined) {
          layerConfig.returnSequences = layerData.returnSequences;
        }

        // Create and add layer
        const layer = Prime.Neural.Neural.createLayer(
          layerConfig.type,
          layerConfig,
        );

        // Set weights and biases
        layer.weights = weights;
        layer.biases = biases;

        // Add to model
        model.layers.push(layer);
      });

      // Set optimizer if available
      if (modelData.optimizer) {
        model.setOptimizer({
          type: modelData.optimizer.type,
          ...modelData.optimizer.config,
        });
      }

      // Set history if available
      if (Array.isArray(modelData.history)) {
        model.history = [...modelData.history];
      }

      // Mark as compiled if it has an optimizer
      if (model.optimizer) {
        model.compiled = true;
      }

      return model;
    }

    /**
     * Attempt to correct coherence issues
     * @private
     * @param {Object} coherenceInfo - Current coherence information
     * @returns {Promise<void>}
     */
    async _attemptCoherenceCorrection(coherenceInfo) {
      // Simple strategy: apply weight decay to reduce extreme values
      const decayFactor = 0.95;

      for (const layer of this.layers) {
        for (let i = 0; i < layer.weights.length; i++) {
          for (let j = 0; j < layer.weights[i].length; j++) {
            // Only decay large weights
            if (Math.abs(layer.weights[i][j]) > 1.0) {
              layer.weights[i][j] *= decayFactor;
            }
          }
        }
      }

      // Log correction attempt
      this.history.push({
        type: 'coherence_correction',
        timestamp: new Date().toISOString(),
        iteration: this.performance.iterationCount,
        coherenceBefore: coherenceInfo.after,
        coherenceAfter: this.calculateCoherence(),
      });
    }

    /**
     * Get loss function by name
     * @private
     * @param {string} name - Name of loss function
     * @returns {Function} Loss function
     */
    _getLossFunction(name) {
      const lowerName = name.toLowerCase();

      switch (lowerName) {
        case 'mse':
        case 'meansquarederror':
          return this._meanSquaredError.bind(this);
        case 'mae':
        case 'meanabsoluteerror':
          return this._meanAbsoluteError.bind(this);
        case 'bce':
        case 'binarycrossentropy':
          return this._binaryCrossEntropy.bind(this);
        case 'cce':
        case 'categoricalcrossentropy':
          return this._categoricalCrossEntropy.bind(this);
        default:
          throw new Error(`Unknown loss function: ${name}`);
      }
    }

    /**
     * Get metric function by name
     * @private
     * @param {string} name - Name of metric function
     * @returns {Function} Metric function
     */
    _getMetricFunction(name) {
      const lowerName = name.toLowerCase();

      switch (lowerName) {
        case 'accuracy':
          return this._accuracyMetric.bind(this);
        case 'mae':
        case 'meanabsoluteerror':
          return (y_true, y_pred) => {
            const { loss } = this._meanAbsoluteError(y_true, y_pred, false);
            return loss;
          };
        case 'mse':
        case 'meansquarederror':
          return (y_true, y_pred) => {
            const { loss } = this._meanSquaredError(y_true, y_pred, false);
            return loss;
          };
        default:
          throw new Error(`Unknown metric: ${name}`);
      }
    }

    /**
     * Mean Squared Error loss function
     * @private
     * @param {Array|TypedArray} y_true - True values
     * @param {Array|TypedArray} y_pred - Predicted values
     * @param {boolean} computeGradient - Whether to compute gradient
     * @returns {Object} Loss value and gradient
     */
    _meanSquaredError(y_true, y_pred, computeGradient = true) {
      let loss = 0;
      const gradient = computeGradient
        ? new Array(y_pred.length).fill(0)
        : null;
      const n = y_pred.length;

      for (let i = 0; i < n; i++) {
        const diff = y_pred[i] - y_true[i];
        loss += diff * diff;

        if (computeGradient) {
          gradient[i] = (2 * diff) / n;
        }
      }

      loss /= n;
      return { loss, gradient };
    }

    /**
     * Mean Absolute Error loss function
     * @private
     * @param {Array|TypedArray} y_true - True values
     * @param {Array|TypedArray} y_pred - Predicted values
     * @param {boolean} computeGradient - Whether to compute gradient
     * @returns {Object} Loss value and gradient
     */
    _meanAbsoluteError(y_true, y_pred, computeGradient = true) {
      let loss = 0;
      const gradient = computeGradient
        ? new Array(y_pred.length).fill(0)
        : null;
      const n = y_pred.length;

      for (let i = 0; i < n; i++) {
        const diff = y_pred[i] - y_true[i];
        loss += Math.abs(diff);

        if (computeGradient) {
          gradient[i] = (diff > 0 ? 1 : -1) / n;
        }
      }

      loss /= n;
      return { loss, gradient };
    }

    /**
     * Binary Cross Entropy loss function
     * @private
     * @param {Array|TypedArray} y_true - True values
     * @param {Array|TypedArray} y_pred - Predicted values
     * @param {boolean} computeGradient - Whether to compute gradient
     * @returns {Object} Loss value and gradient
     */
    _binaryCrossEntropy(y_true, y_pred, computeGradient = true) {
      let loss = 0;
      const gradient = computeGradient
        ? new Array(y_pred.length).fill(0)
        : null;
      const n = y_pred.length;
      const epsilon = 1e-7;

      for (let i = 0; i < n; i++) {
        // Clip prediction to avoid log(0)
        const pred = Math.max(Math.min(y_pred[i], 1 - epsilon), epsilon);
        const target = y_true[i];

        // Binary cross entropy formula: -t*log(p) - (1-t)*log(1-p)
        loss += -target * Math.log(pred) - (1 - target) * Math.log(1 - pred);

        if (computeGradient) {
          // Gradient: -t/p + (1-t)/(1-p)
          gradient[i] = -target / pred + (1 - target) / (1 - pred);
          gradient[i] /= n;
        }
      }

      loss /= n;
      return { loss, gradient };
    }

    /**
     * Categorical Cross Entropy loss function
     * @private
     * @param {Array|TypedArray} y_true - True values (one-hot encoded)
     * @param {Array|TypedArray} y_pred - Predicted values (probabilities)
     * @param {boolean} computeGradient - Whether to compute gradient
     * @returns {Object} Loss value and gradient
     */
    _categoricalCrossEntropy(y_true, y_pred, computeGradient = true) {
      let loss = 0;
      const gradient = computeGradient
        ? new Array(y_pred.length).fill(0)
        : null;
      const n = y_pred.length;
      const epsilon = 1e-7;

      for (let i = 0; i < n; i++) {
        // Clip prediction to avoid log(0)
        const pred = Math.max(Math.min(y_pred[i], 1 - epsilon), epsilon);
        const target = y_true[i];

        // Only add loss for positive targets (in one-hot encoding)
        if (target > 0) {
          loss += -target * Math.log(pred);
        }

        if (computeGradient) {
          // Gradient: -t/p
          gradient[i] = -target / pred;
          gradient[i] /= n;
        }
      }

      loss /= n;
      return { loss, gradient };
    }

    /**
     * Accuracy metric
     * @private
     * @param {Array|TypedArray} y_true - True values
     * @param {Array|TypedArray} y_pred - Predicted values
     * @returns {number} Accuracy value
     */
    _accuracyMetric(y_true, y_pred) {
      let correct = 0;
      let total = 0;

      // Handle 1D arrays (binary classification)
      if (!Array.isArray(y_true[0])) {
        for (let i = 0; i < y_true.length; i++) {
          const trueClass = y_true[i] > 0.5 ? 1 : 0;
          const predClass = y_pred[i] > 0.5 ? 1 : 0;
          if (trueClass === predClass) {
            correct++;
          }
          total++;
        }
      }
      // Handle 2D arrays (multi-class classification)
      else {
        for (let i = 0; i < y_true.length; i++) {
          let trueClass = 0;
          let predClass = 0;
          let maxTrue = y_true[i][0];
          let maxPred = y_pred[i][0];

          // Find class with highest value
          for (let j = 1; j < y_true[i].length; j++) {
            if (y_true[i][j] > maxTrue) {
              maxTrue = y_true[i][j];
              trueClass = j;
            }
            if (y_pred[i][j] > maxPred) {
              maxPred = y_pred[i][j];
              predClass = j;
            }
          }

          if (trueClass === predClass) {
            correct++;
          }
          total++;
        }
      }

      return total > 0 ? correct / total : 0;
    }

    /**
     * Serialize a matrix for storage
     * @private
     * @param {Array<Array>|TypedArray} matrix - Matrix to serialize
     * @returns {Array} Serialized matrix
     */
    _serializeMatrix(matrix) {
      // For testing purposes, handle undefined or null
      if (!matrix) {
        return [[]];
      }

      // Handle 2D arrays or typed arrays
      const result = [];

      // Add safety check for matrix.length
      const len = matrix.length || 0;

      for (let i = 0; i < len; i++) {
        // Skip if the row is undefined or null
        if (!matrix[i]) {
          result.push([]);
          continue;
        }

        if (
          matrix[i] instanceof Float32Array ||
          matrix[i] instanceof Float64Array
        ) {
          result.push(Array.from(matrix[i]));
        } else if (Array.isArray(matrix[i])) {
          result.push([...matrix[i]]);
        } else {
          // Handle scalar values
          result.push([matrix[i]]);
        }
      }

      return result;
    }

    /**
     * Serialize an array for storage
     * @private
     * @param {Array|TypedArray} array - Array to serialize
     * @returns {Array} Serialized array
     */
    _serializeArray(array) {
      // For testing purposes, handle undefined or null
      if (!array) {
        return [];
      }

      if (array instanceof Float32Array || array instanceof Float64Array) {
        return Array.from(array);
      }

      if (Array.isArray(array)) {
        return [...array];
      }

      // Handle scalar values
      return [array];
    }

    /**
     * Deserialize a matrix from storage
     * @private
     * @param {Array<Array>} serialized - Serialized matrix
     * @returns {Array<Array>} Deserialized matrix
     */
    static _deserializeMatrix(serialized) {
      return serialized.map((row) => [...row]);
    }

    /**
     * Deserialize an array from storage
     * @private
     * @param {Array} serialized - Serialized array
     * @returns {Array} Deserialized array
     */
    static _deserializeArray(serialized) {
      return [...serialized];
    }

    /**
     * Update forward pass performance metrics
     * @private
     * @param {number} time - Time in ms for this forward pass
     */
    _updateForwardTime(time) {
      this.performance.forwardTime =
        0.9 * this.performance.forwardTime + 0.1 * time;
      this.performance.iterationCount++;
    }

    /**
     * Update backward pass performance metrics
     * @private
     * @param {number} time - Time in ms for this backward pass
     */
    _updateBackwardTime(time) {
      this.performance.backwardTime =
        0.9 * this.performance.backwardTime + 0.1 * time;
    }

    /**
     * Get model summary
     * @returns {Object} Model summary
     */
    getSummary() {
      const layerSummaries = this.layers.map((layer, index) => {
        let layerType = layer.constructor.name;
        if (layerType.includes('Layer')) {
          layerType = layerType.replace('Layer', '');
        }

        return {
          index,
          type: layerType,
          input: layer.inputSize,
          output: layer.outputSize,
          activation: layer.activation,
          parameters:
            layer.weights.length * layer.weights[0].length +
            layer.biases.length,
        };
      });

      const totalParams = layerSummaries.reduce(
        (sum, layer) => sum + layer.parameters,
        0,
      );

      return {
        layers: layerSummaries,
        totalLayers: this.layers.length,
        totalParameters: totalParams,
        compiled: this.compiled,
        optimizer: this.optimizer ? this.optimizer.constructor.name : 'None',
        useTypedArrays: this.useTypedArrays,
        performance: { ...this.performance },
      };
    }
  }

  // Add to Prime.Neural namespace
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Model = Prime.Neural.Model || {};
  Prime.Neural.Model.NeuralModel = NeuralModel;
})();

// Export the enhanced Prime object
module.exports = Prime;
