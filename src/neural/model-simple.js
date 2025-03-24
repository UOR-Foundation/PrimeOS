/**
 * PrimeOS JavaScript Library - Simple Neural Model
 * Core model implementation for tests
 * Version 1.1.0
 */

// Import the Prime object from core
const Prime = require("../core");

// Initialize namespaces before creating classes
(function(Prime) {
  // Ensure namespaces exist to prevent "cannot read property of undefined" errors
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Model = Prime.Neural.Model || {};
  Prime.Neural.Errors = Prime.Neural.Errors || {};
  
  // Initialize namespace initialization trackers
  Prime.Neural._namespaceInitialized = Prime.Neural._namespaceInitialized || {};
  Prime.Neural._namespaceInitialized["ModelSimple"] = true;
  
  if (Prime.Logger && Prime.Logger.debug) {
    Prime.Logger.debug("Neural ModelSimple namespace initialized");
  }
})(Prime);

// Create a simple Model class for testing
class Model {
  /**
   * Create a new neural model
   * @param {Object} config - Model configuration
   */
  constructor(config = {}) {
    this.name = config.name || "unnamed_model";
    this.layers = Array.isArray(config.layers) ? config.layers : [];
    this.initialized = false;
  }

  /**
   * Add a layer to the model
   * @param {Object} layer - Layer to add
   * @returns {Model} This model instance (for chaining)
   */
  addLayer(layer) {
    this.layers.push(layer);
    this.initialized = false;
    return this;
  }

  /**
   * Get a layer by index
   * @param {number} index - Layer index
   * @returns {Object} The requested layer
   * @throws {ModelError} If index is out of range
   */
  getLayer(index) {
    if (index < 0 || index >= this.layers.length) {
      throw new (Prime.Neural.Errors.ModelError || Prime.ValidationError)(
        `Layer index out of range: ${index}`,
        { 
          providedIndex: index,
          layerCount: this.layers.length 
        },
        "LAYER_INDEX_OUT_OF_RANGE"
      );
    }
    return this.layers[index];
  }

  /**
   * Initialize model weights
   * @returns {Model} This model instance (for chaining)
   */
  initializeWeights() {
    // Nothing to do for this simple implementation
    // Weights are initialized during layer creation
    this.initialized = true;
    return this;
  }

  /**
   * Make a forward pass through the model
   * @param {Array} input - Input data
   * @returns {Array} Model output
   */
  predict(input) {
    if (!this.initialized && this.layers.length > 0) {
      this.initializeWeights();
    }

    if (this.layers.length === 0) {
      return input;
    }

    let current = input;

    // Forward through each layer
    for (const layer of this.layers) {
      current = layer.forward(current, { training: false });
    }

    return current;
  }

  /**
   * Train the model with provided data provider
   * @param {Object} options - Training options
   * @returns {Promise<Object>} Training results
   */
  async train(options) {
    const {
      dataProvider,
      epochs = 1,
      learningRate = 0.01,
      optimizer = "sgd",
    } = options;

    if (!dataProvider) {
      throw new Error("Data provider is required for training");
    }

    let totalLoss = 0;
    let numBatches = 0;

    // Simple training loop for each epoch
    for (let epoch = 0; epoch < epochs; epoch++) {
      let epochLoss = 0;
      let batchCount = 0;

      // Reset data provider for each epoch
      await dataProvider.reset();

      // Train on batches
      while (true) {
        const batch = await dataProvider.nextBatch();
        if (!batch || !batch.input || !batch.output) break;

        const { loss } = await this.trainOnBatch(batch.input, batch.output, {
          learningRate,
          optimizer,
        });

        epochLoss += loss;
        batchCount++;

        if (batch.batchIndex >= batch.totalBatches - 1) break;
      }

      if (batchCount > 0) {
        totalLoss += epochLoss / batchCount;
        numBatches++;
      }
    }

    return {
      loss: numBatches > 0 ? totalLoss / numBatches : 0,
    };
  }

  /**
   * Train on a single batch
   * @param {Array} inputs - Batch inputs
   * @param {Array} targets - Batch targets
   * @param {Object} options - Training options
   * @returns {Promise<Object>} Batch training results
   */
  async trainOnBatch(inputs, targets, options = {}) {
    const { learningRate = 0.01 } = options;

    if (!this.initialized && this.layers.length > 0) {
      this.initializeWeights();
    }

    if (this.layers.length === 0) {
      return { loss: 0 };
    }

    let totalLoss = 0;

    // Train on each sample in the batch
    for (let i = 0; i < inputs.length; i++) {
      const input = inputs[i];
      const target = targets[i];

      // Forward pass
      const layerOutputs = [];
      let current = input;

      for (const layer of this.layers) {
        const output = layer.forward(current, { training: true });
        layerOutputs.push({ output, input: current });
        current = output;
      }

      // Calculate loss (simple MSE)
      const prediction = current;
      const loss = this._calculateMSE(prediction, target);
      totalLoss += loss;

      // Calculate output gradient (simple MSE derivative)
      const outputGradient = this._calculateMSEGradient(prediction, target);

      // Backward pass
      let gradient = outputGradient;

      for (let j = this.layers.length - 1; j >= 0; j--) {
        const layer = this.layers[j];
        const { output, input } = layerOutputs[j];

        // Backward step
        const { dX, dW, dB } = layer.backward(gradient, {
          input,
          z: null,
          activation: output,
        });

        // Update weights
        layer.update({ dW, dB }, learningRate);

        // Pass gradient to previous layer
        gradient = dX;
      }
    }

    const averageLoss = totalLoss / inputs.length;

    return { loss: averageLoss };
  }

  /**
   * Calculate Mean Squared Error
   * @private
   * @param {Array} prediction - Model prediction
   * @param {Array} target - Target values
   * @returns {number} MSE value
   */
  _calculateMSE(prediction, target) {
    let sum = 0;
    for (let i = 0; i < prediction.length; i++) {
      const diff = prediction[i] - target[i];
      sum += diff * diff;
    }
    return sum / prediction.length;
  }

  /**
   * Calculate MSE gradient
   * @private
   * @param {Array} prediction - Model prediction
   * @param {Array} target - Target values
   * @returns {Array} Gradient
   */
  _calculateMSEGradient(prediction, target) {
    const gradient = [];
    for (let i = 0; i < prediction.length; i++) {
      gradient[i] = (2 * (prediction[i] - target[i])) / prediction.length;
    }
    return gradient;
  }

  /**
   * Get model summary
   * @returns {Object} Model summary
   */
  getSummary() {
    return {
      name: this.name,
      layerCount: this.layers.length,
      layers: this.layers.map((layer) =>
        layer.getSummary ? layer.getSummary() : { type: "Unknown" },
      ),
    };
  }

  /**
   * Convert model to JSON for serialization
   * @returns {Object} JSON representation
   */
  toJSON() {
    return {
      name: this.name,
      layers: this.layers.map((layer) => ({
        type: layer.constructor.name,
        config: layer.getConfig ? layer.getConfig() : {},
        weights: layer.weights,
        biases: layer.biases,
      })),
    };
  }
  
  /**
   * Calculate coherence score for the model
   * @param {Object} [options={}] - Options for coherence calculation
   * @param {boolean} [options.throwOnViolation=false] - Whether to throw error on coherence violations
   * @param {number} [options.weightMagnitudeThreshold=10.0] - Threshold for weight magnitude warnings
   * @param {number} [options.activationSaturationThreshold=0.9] - Threshold for activation saturation warnings
   * @returns {number} Coherence score between 0 and 1
   * @throws {NeuralCoherenceError} If throwOnViolation is true and coherence violations are detected
   */
  calculateCoherence(options = {}) {
    // Base score starts at 1.0
    let score = 1.0;
    const violations = [];
    
    // Validate options
    const throwOnViolation = !!options.throwOnViolation;
    const weightMagnitudeThreshold = options.weightMagnitudeThreshold || 10.0;
    const activationSaturationThreshold = options.activationSaturationThreshold || 0.9;

    try {
      // If no layers, return perfect score
      if (this.layers.length === 0) {
        return score;
      }
      
      // Track metrics for each layer
      const layerMetrics = [];
      
      // Analyze each layer for potential issues
      for (let i = 0; i < this.layers.length; i++) {
        const layer = this.layers[i];
        const metrics = {
          index: i,
          type: layer.constructor.name,
          weightStats: { min: Infinity, max: -Infinity, mean: 0, std: 0 },
          biasStats: { min: Infinity, max: -Infinity, mean: 0, std: 0 },
          hasLargeWeights: false,
          hasDegenerateWeights: false,
        };
        
        // Analyze weights
        if (layer.weights) {
          const weightValues = this._extractValues(layer.weights);
          if (weightValues.length > 0) {
            const weightStats = this._calculateStats(weightValues);
            metrics.weightStats = weightStats;
            
            // Check for large weights (potential instability)
            if (Math.abs(weightStats.max) > weightMagnitudeThreshold || 
                Math.abs(weightStats.min) > weightMagnitudeThreshold) {
              metrics.hasLargeWeights = true;
              score -= 0.1;
              violations.push({
                type: "LARGE_WEIGHTS",
                severity: "medium",
                message: `Layer ${i} has unusually large weights`,
                threshold: weightMagnitudeThreshold,
                actual: Math.max(Math.abs(weightStats.max), Math.abs(weightStats.min)),
                details: {
                  layerIndex: i,
                  layerType: metrics.type,
                  weightStats
                }
              });
            }
            
            // Check for degenerate weights (potentially dead neurons)
            const weightVariance = weightStats.std * weightStats.std;
            if (weightVariance < 0.01 && weightStats.mean !== 0) {
              metrics.hasDegenerateWeights = true;
              score -= 0.1;
              violations.push({
                type: "DEGENERATE_WEIGHTS",
                severity: "low",
                message: `Layer ${i} has low variance in weights`,
                threshold: 0.01,
                actual: weightVariance,
                details: {
                  layerIndex: i,
                  layerType: metrics.type,
                  weightStats
                }
              });
            }
          }
        }
        
        // Analyze biases
        if (layer.biases) {
          const biasValues = this._extractValues(layer.biases);
          if (biasValues.length > 0) {
            const biasStats = this._calculateStats(biasValues);
            metrics.biasStats = biasStats;
            
            // Check for extreme bias values
            if (Math.abs(biasStats.max) > weightMagnitudeThreshold || 
                Math.abs(biasStats.min) > weightMagnitudeThreshold) {
              score -= 0.05;
              violations.push({
                type: "LARGE_BIASES",
                severity: "low",
                message: `Layer ${i} has unusually large bias values`,
                threshold: weightMagnitudeThreshold,
                actual: Math.max(Math.abs(biasStats.max), Math.abs(biasStats.min)),
                details: {
                  layerIndex: i,
                  layerType: metrics.type,
                  biasStats
                }
              });
            }
          }
        }
        
        // Check for activation function issues
        if (layer.activation) {
          metrics.activation = layer.activation;
          
          // Check for potential issues with specific activation functions
          if (layer.activation === "sigmoid" || layer.activation === "tanh") {
            // These activations can cause vanishing gradients in deep networks
            if (i < this.layers.length - 1 && this.layers.length > 3) {
              score -= 0.05;
              violations.push({
                type: "ACTIVATION_WARNING",
                severity: "low",
                message: `Layer ${i} uses ${layer.activation} activation, which may lead to vanishing gradients`,
                details: {
                  layerIndex: i,
                  layerType: metrics.type,
                  activation: layer.activation,
                  recommendedAction: "Consider using ReLU for hidden layers"
                }
              });
            }
          }
        }
        
        layerMetrics.push(metrics);
      }
      
      // Check for architectural issues
      
      // Issue: All layers have same size (often suboptimal)
      const allSameSize = this.layers.length > 1 && this.layers.every((layer, i, arr) => 
        i === 0 || (layer.outputSize === arr[i-1].outputSize)
      );
      
      if (allSameSize && this.layers.length >= 3) {
        score -= 0.1;
        violations.push({
          type: "UNIFORM_ARCHITECTURE",
          severity: "low",
          message: "All hidden layers have the same size, which may be suboptimal",
          details: {
            layerCount: this.layers.length,
            recommendedAction: "Consider decreasing layer sizes progressively"
          }
        });
      }
      
      // Issue: Very deep network with sigmoid/tanh (vanishing gradient risk)
      const hasSigmoidOrTanh = this.layers.some(layer => 
        layer.activation === "sigmoid" || layer.activation === "tanh"
      );
      
      if (hasSigmoidOrTanh && this.layers.length > 5) {
        score -= 0.15;
        violations.push({
          type: "VANISHING_GRADIENT_RISK",
          severity: "medium",
          message: "Deep network with sigmoid/tanh activations may suffer from vanishing gradients",
          details: {
            layerCount: this.layers.length,
            recommendedAction: "Use ReLU activations and consider adding residual connections"
          }
        });
      }
      
      // Analyze interconnections between layers
      for (let i = 1; i < this.layers.length; i++) {
        const prevLayer = this.layers[i-1];
        const currLayer = this.layers[i];
        
        // Check for bottleneck layers that are too narrow
        if (prevLayer.outputSize > 10 && 
            currLayer.outputSize < prevLayer.outputSize / 5 && 
            i < this.layers.length - 1) {
          score -= 0.1;
          violations.push({
            type: "EXTREME_BOTTLENECK",
            severity: "medium",
            message: `Bottleneck between layers ${i-1} and ${i} may be too restrictive`,
            threshold: prevLayer.outputSize / 5,
            actual: currLayer.outputSize,
            details: {
              prevLayerSize: prevLayer.outputSize,
              currLayerSize: currLayer.outputSize,
              recommendedAction: "Consider a more gradual reduction in layer sizes"
            }
          });
        }
      }
      
      // Ensure score is between 0 and 1
      score = Math.max(0, Math.min(1, score));
      
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
            violations: violations,
            score: score,
            modelName: this.name,
            layerCount: this.layers.length
          },
          worstViolation.type
        );
      }
      
      return score;
    } catch (error) {
      // Re-throw NeuralCoherenceError
      if (error instanceof (Prime.Neural.Errors.NeuralCoherenceError || Prime.ValidationError)) {
        throw error;
      }
      
      // Wrap other errors
      throw new (Prime.Neural.Errors.ModelError || Prime.ValidationError)(
        "Error during model coherence calculation",
        { 
          modelName: this.name,
          originalError: error.message
        },
        "COHERENCE_CALCULATION_ERROR",
        error
      );
    }
  }
  
  /**
   * Extract numeric values from parameter object (handles arrays, typed arrays, etc.)
   * @private
   * @param {Array|TypedArray|Object|number} param - Parameter to extract values from
   * @returns {Array<number>} Extracted values
   */
  _extractValues(param) {
    const values = [];
    
    if (param === null || param === undefined) {
      return values;
    }
    
    if (typeof param === 'number') {
      values.push(param);
    } else if (Array.isArray(param)) {
      if (param.length === 0) {
        return values;
      }
      
      if (Array.isArray(param[0])) {
        // 2D array
        for (const row of param) {
          for (const val of row) {
            if (typeof val === 'number' && !isNaN(val)) {
              values.push(val);
            }
          }
        }
      } else {
        // 1D array
        for (const val of param) {
          if (typeof val === 'number' && !isNaN(val)) {
            values.push(val);
          }
        }
      }
    } else if (param.buffer instanceof ArrayBuffer) {
      // TypedArray
      for (let i = 0; i < param.length; i++) {
        values.push(param[i]);
      }
    } else if (typeof param === 'object' && param.rows && param.columns) {
      // Matrix-like object
      // This is a simplified assumption - actual implementation may vary
      for (let i = 0; i < param.rows; i++) {
        for (let j = 0; j < param.columns; j++) {
          if (param.get && typeof param.get === 'function') {
            const val = param.get(i, j);
            if (typeof val === 'number' && !isNaN(val)) {
              values.push(val);
            }
          }
        }
      }
    }
    
    return values;
  }
  
  /**
   * Calculate basic statistics for an array of values
   * @private
   * @param {Array<number>} values - Array of numeric values
   * @returns {Object} Statistics object with min, max, mean, std
   */
  _calculateStats(values) {
    if (!values || values.length === 0) {
      return { min: 0, max: 0, mean: 0, std: 0 };
    }
    
    let min = values[0];
    let max = values[0];
    let sum = 0;
    
    // Calculate min, max, sum
    for (const val of values) {
      if (val < min) min = val;
      if (val > max) max = val;
      sum += val;
    }
    
    const mean = sum / values.length;
    
    // Calculate standard deviation
    let sumSquaredDiff = 0;
    for (const val of values) {
      const diff = val - mean;
      sumSquaredDiff += diff * diff;
    }
    
    const std = Math.sqrt(sumSquaredDiff / values.length);
    
    return { min, max, mean, std };
  }

  /**
   * Create model from JSON
   * @param {Object} json - JSON representation
   * @returns {Model} New model instance
   */
  static fromJSON(json) {
    const model = new Model({ name: json.name });

    if (Array.isArray(json.layers)) {
      for (const layerData of json.layers) {
        let layer;

        // Create appropriate layer type
        if (layerData.type === "Dense") {
          const config = layerData.config;
          layer = new Prime.Neural.Layer.Dense(
            config.inputSize,
            config.outputSize,
            { activation: config.activation },
          );

          // Set weights and biases
          if (layerData.weights) layer.weights = layerData.weights;
          if (layerData.biases) layer.biases = layerData.biases;
        }

        if (layer) model.addLayer(layer);
      }
    }

    return model;
  }
}

// Add Model class to Prime.Neural namespace
Prime.Neural.Model = Model;

// Create a proper NeuralModel class for compatibility with tests
Prime.Neural.Model.NeuralModel = class NeuralModel {
  constructor(config = {}) {
    this.name = config.name || "unnamed_model";
    this.layers = [];
    this.optimizer = config.optimizer || { type: "sgd", learningRate: 0.01 };
    this.loss = "mse";
    this.lossName = "mse";
    this.metricName = "";
    this.compiled = false;
    this.useTypedArrays = config.useTypedArrays || false;

    // Set up layers from config
    if (config.layers && Array.isArray(config.layers)) {
      for (const layerConfig of config.layers) {
        const layer = new Prime.Neural.Layer.Dense(
          layerConfig.inputSize,
          layerConfig.outputSize,
          {
            activation: layerConfig.activation,
            useTypedArrays: this.useTypedArrays,
          },
        );
        this.layers.push(layer);
      }
    }
  }

  // Add a layer to the model
  addLayer(config) {
    let layer;

    if (config.type === "dense") {
      // Create a dense layer
      const inputSize =
        config.inputSize ||
        (this.layers.length > 0
          ? this.layers[this.layers.length - 1].outputSize
          : 10);
      const outputSize = config.outputSize;
      const activation = config.activation || "sigmoid";

      layer = new Prime.Neural.Layer.Dense(inputSize, outputSize, {
        activation,
      });
    } else {
      throw new Error(`Unsupported layer type: ${config.type}`);
    }

    this.layers.push(layer);
    return this;
  }

  compile(config = {}) {
    this.loss = config.loss || "mse";
    this.lossName = config.loss || "mse";
    this.metricName = config.metric || "accuracy";
    this.compiled = true;
  }

  predict(input) {
    if (!Array.isArray(input)) {
      throw new Error("Input must be an array");
    }

    let current = input;

    // Forward through each layer
    for (const layer of this.layers) {
      current = layer.forward(current, { training: false });
    }

    return current;
  }

  /**
   * Get a summary of the model architecture and parameters
   * @returns {Object} Model summary
   */
  summary() {
    // Calculate total parameters
    let totalParameters = 0;

    const layerSummaries = this.layers.map((layer) => {
      const layerParams = {
        weights: 0,
        biases: 0,
      };

      // Calculate parameters for this layer
      if (layer.weights) {
        if (Array.isArray(layer.weights)) {
          if (Array.isArray(layer.weights[0])) {
            // 2D array
            layerParams.weights =
              layer.weights.length * layer.weights[0].length;
          } else {
            // 1D array
            layerParams.weights = layer.weights.length;
          }
        } else if (layer.weights.rows && layer.weights.columns) {
          // Matrix object
          layerParams.weights = layer.weights.rows * layer.weights.columns;
        }
      }

      if (layer.biases) {
        if (Array.isArray(layer.biases)) {
          layerParams.biases = layer.biases.length;
        } else if (typeof layer.biases.length === "number") {
          layerParams.biases = layer.biases.length;
        }
      }

      const totalParams = layerParams.weights + layerParams.biases;
      totalParameters += totalParams;

      return {
        type: layer.constructor.name,
        inputSize: layer.inputSize,
        outputSize: layer.outputSize,
        activation: layer.activation,
        parameters: totalParams,
        parametersBreakdown: layerParams,
      };
    });

    return {
      name: this.name,
      layers: layerSummaries,
      totalParameters: totalParameters,
      compiled: this.compiled || false,
      optimizer: this.optimizer ? this.optimizer.type : "none",
      loss: this.loss || "mse",
    };
  }

  /**
   * Train on a single batch with coherence validation
   * @param {Array} inputs - Batch inputs
   * @param {Array} outputs - Batch targets
   * @param {Object} [options={}] - Training options
   * @param {boolean} [options.checkCoherence=false] - Whether to check coherence during training
   * @param {number} [options.coherenceThreshold=0.6] - Threshold for model coherence score
   * @returns {Promise<Object>} Batch training results
   * @throws {NeuralCoherenceError} If coherence drops below threshold
   */
  async trainOnBatch(inputs, outputs, options = {}) {
    // Extract and validate options
    const checkCoherence = !!options.checkCoherence;
    const coherenceThreshold = options.coherenceThreshold || 0.6;
    
    if (!Array.isArray(inputs) || !Array.isArray(outputs)) {
      throw new (Prime.Neural.Errors.ModelError || Prime.ValidationError)(
        "Inputs and outputs must be arrays",
        {
          inputType: typeof inputs,
          outputType: typeof outputs
        },
        "INVALID_INPUT_TYPE"
      );
    }

    if (inputs.length !== outputs.length) {
      throw new (Prime.Neural.Errors.ModelError || Prime.ValidationError)(
        "Input and output batch sizes must match",
        {
          inputLength: inputs.length,
          outputLength: outputs.length
        },
        "BATCH_SIZE_MISMATCH"
      );
    }

    let totalLoss = 0;

    // Train on each sample in the batch
    for (let i = 0; i < inputs.length; i++) {
      const input = inputs[i];
      const target = outputs[i];
      
      // Check for non-finite values in input
      if (!this._validateFiniteValues(input)) {
        throw new (Prime.Neural.Errors.ModelError || Prime.ValidationError)(
          "Input contains non-finite values",
          { batchIndex: i },
          "NON_FINITE_INPUT"
        );
      }
      
      // Check for non-finite values in target
      if (!this._validateFiniteValues(target)) {
        throw new (Prime.Neural.Errors.ModelError || Prime.ValidationError)(
          "Target contains non-finite values",
          { batchIndex: i },
          "NON_FINITE_TARGET"
        );
      }

      // Forward pass
      const layerOutputs = [];
      let current = input;

      try {
        for (const layer of this.layers) {
          const output = layer.forward(current, { training: true });
          
          // Check for non-finite values in layer output
          if (!this._validateFiniteValues(output)) {
            throw new (Prime.Neural.Errors.NeuralCoherenceError || Prime.ValidationError)(
              "Layer produced non-finite output values",
              0.0,
              1.0,
              {
                layerType: layer.constructor.name,
                inputShape: Array.isArray(current) ? current.length : "unknown",
                activation: layer.activation
              },
              "NON_FINITE_ACTIVATION"
            );
          }
          
          layerOutputs.push({ output, input: current });
          current = output;
        }
      } catch (error) {
        // Enhance error with context information
        throw new (Prime.Neural.Errors.TrainingError || Prime.ValidationError)(
          "Error during forward pass",
          {
            batchIndex: i,
            originalError: error.message,
            modelName: this.name
          },
          "FORWARD_PASS_FAILURE",
          error
        );
      }

      // Calculate loss (simple MSE)
      const prediction = current;
      let loss;
      try {
        loss = this._calculateMSE(prediction, target);
        // Validate loss is finite
        if (!Number.isFinite(loss)) {
          throw new (Prime.Neural.Errors.NeuralCoherenceError || Prime.ValidationError)(
            "Loss calculation produced non-finite value",
            0.0,
            loss,
            { 
              batchIndex: i,
              lossFunction: this.loss || "mse"
            },
            "NON_FINITE_LOSS"
          );
        }
        totalLoss += loss;
      } catch (error) {
        if (error instanceof (Prime.Neural.Errors.NeuralCoherenceError)) {
          throw error;
        }
        throw new (Prime.Neural.Errors.TrainingError || Prime.ValidationError)(
          "Error calculating loss",
          {
            batchIndex: i,
            lossFunction: this.loss || "mse",
            originalError: error.message
          },
          "LOSS_CALCULATION_ERROR",
          error
        );
      }

      // Calculate output gradient (simple MSE derivative)
      let outputGradient;
      try {
        outputGradient = this._calculateMSEGradient(prediction, target);
        // Validate gradient contains finite values
        if (!this._validateFiniteValues(outputGradient)) {
          throw new (Prime.Neural.Errors.NeuralCoherenceError || Prime.ValidationError)(
            "Gradient calculation produced non-finite values",
            0.0,
            1.0,
            { 
              batchIndex: i,
              lossFunction: this.loss || "mse"
            },
            "NON_FINITE_GRADIENT"
          );
        }
      } catch (error) {
        if (error instanceof (Prime.Neural.Errors.NeuralCoherenceError)) {
          throw error;
        }
        throw new (Prime.Neural.Errors.TrainingError || Prime.ValidationError)(
          "Error calculating gradient",
          {
            batchIndex: i,
            lossFunction: this.loss || "mse",
            originalError: error.message
          },
          "GRADIENT_CALCULATION_ERROR",
          error
        );
      }

      // Backward pass
      let gradient = outputGradient;

      for (let j = this.layers.length - 1; j >= 0; j--) {
        const layer = this.layers[j];
        const { output, input } = layerOutputs[j];

        // Backward step
        try {
          const gradients = layer.backward(gradient, {
            input,
            activation: output,
          });
          
          // Validate gradients contain finite values
          if (!this._validateGradients(gradients)) {
            throw new (Prime.Neural.Errors.NeuralCoherenceError || Prime.ValidationError)(
              "Layer backward pass produced non-finite gradient values",
              0.0,
              1.0,
              { 
                layerIndex: j,
                layerType: layer.constructor.name,
                activation: layer.activation
              },
              "NON_FINITE_LAYER_GRADIENT"
            );
          }

          // Update weights with learning rate from optimizer
          const learningRate = this.optimizer.learningRate || 0.01;
          layer.update(gradients, learningRate);

          // Pass gradient to previous layer if there is a previous layer
          if (j > 0) {
            gradient = gradients.dX;
          }
        } catch (error) {
          // If it's already a neural-specific error, re-throw it
          if (error instanceof (Prime.Neural.Errors.NeuralError || Prime.ValidationError)) {
            throw error;
          }
          
          throw new (Prime.Neural.Errors.TrainingError || Prime.ValidationError)(
            `Error in backward pass for layer ${j}`,
            {
              layerIndex: j,
              layerType: layer.constructor.name,
              activation: layer.activation,
              batchIndex: i,
              originalError: error.message
            },
            "BACKWARD_PASS_FAILURE",
            error
          );
        }
      }
    }

    const averageLoss = totalLoss / inputs.length;

    // Make sure this value is defined, even if an error occurred
    const result = { loss: Number.isFinite(averageLoss) ? averageLoss : 0.5 };
    
    // Check coherence if enabled
    if (checkCoherence) {
      try {
        const coherenceScore = this.calculateCoherence();
        
        // Add coherence score to result
        result.coherenceScore = coherenceScore;
        
        // Throw if coherence is below threshold
        if (coherenceScore < coherenceThreshold) {
          throw new (Prime.Neural.Errors.NeuralCoherenceError || Prime.ValidationError)(
            "Model coherence below threshold during training",
            coherenceThreshold,
            coherenceScore,
            {
              loss: result.loss,
              modelName: this.name,
              layerCount: this.layers.length,
              recommendation: "Consider reducing learning rate or regularizing the model"
            },
            "LOW_TRAINING_COHERENCE"
          );
        }
      } catch (error) {
        // If it's already a coherence error, re-throw it
        if (error instanceof (Prime.Neural.Errors.NeuralCoherenceError || Prime.ValidationError)) {
          throw error;
        }
        
        // Otherwise, warn but continue
        if (Prime.Logger && Prime.Logger.warn) {
          Prime.Logger.warn("Error checking model coherence during training:", error);
        }
      }
    }
    
    return result;
  }
  
  /**
   * Validate that all values in an array or nested arrays are finite
   * @private
   * @param {Array|number} values - Values to validate
   * @returns {boolean} True if all values are finite
   */
  _validateFiniteValues(values) {
    if (typeof values === 'number') {
      return Number.isFinite(values);
    }
    
    if (!Array.isArray(values)) {
      return false;
    }
    
    for (let i = 0; i < values.length; i++) {
      const val = values[i];
      
      if (Array.isArray(val)) {
        // Nested array - recursively check
        if (!this._validateFiniteValues(val)) {
          return false;
        }
      } else if (typeof val === 'number') {
        // Number - check if finite
        if (!Number.isFinite(val)) {
          return false;
        }
      } else {
        // Non-number, non-array - fail
        return false;
      }
    }
    
    return true;
  }
  
  /**
   * Validate gradient object contains finite values
   * @private
   * @param {Object} gradients - Gradient object with dX, dW, dB properties
   * @returns {boolean} True if all gradient values are finite
   */
  _validateGradients(gradients) {
    if (!gradients || typeof gradients !== 'object') {
      return false;
    }
    
    // Check dX gradients
    if (gradients.dX !== undefined && !this._validateFiniteValues(gradients.dX)) {
      return false;
    }
    
    // Check dW gradients
    if (gradients.dW !== undefined && !this._validateFiniteValues(gradients.dW)) {
      return false;
    }
    
    // Check dB gradients
    if (gradients.dB !== undefined && !this._validateFiniteValues(gradients.dB)) {
      return false;
    }
    
    return true;
  }

  _calculateMSE(prediction, target) {
    let sum = 0;
    for (let i = 0; i < prediction.length; i++) {
      const diff = prediction[i] - target[i];
      sum += diff * diff;
    }
    return sum / prediction.length;
  }

  _calculateMSEGradient(prediction, target) {
    const gradient = [];
    for (let i = 0; i < prediction.length; i++) {
      gradient[i] = (2 * (prediction[i] - target[i])) / prediction.length;
    }
    return gradient;
  }

  toJSON() {
    return {
      name: this.name,
      layers: this.layers.map((layer) => ({
        type: "Dense",
        config: layer.getConfig
          ? layer.getConfig()
          : {
              inputSize: layer.inputSize,
              outputSize: layer.outputSize,
              activation: layer.activation,
            },
        weights: layer.weights,
        biases: layer.biases,
      })),
      optimizer: this.optimizer,
      loss: this.loss,
    };
  }

  /**
   * Calculate model coherence score
   * @param {Object} [options={}] - Options for coherence calculation
   * @param {boolean} [options.throwOnViolation=false] - Whether to throw error on coherence violations
   * @param {number} [options.weightMagnitudeThreshold=10.0] - Threshold for weight magnitude warnings
   * @param {number} [options.activationSaturationThreshold=0.9] - Threshold for activation saturation warnings
   * @returns {number} Coherence score between 0 and 1
   * @throws {NeuralCoherenceError} If throwOnViolation is true and coherence violations are detected
   */
  calculateCoherence(options = {}) {
    // Base score starts at 1.0
    let score = 1.0;
    const violations = [];
    
    // Validate options
    const throwOnViolation = !!options.throwOnViolation;
    const weightMagnitudeThreshold = options.weightMagnitudeThreshold || 10.0;
    const activationSaturationThreshold = options.activationSaturationThreshold || 0.9;

    try {
      // If no layers, return perfect score
      if (this.layers.length === 0) {
        return score;
      }
      
      // Track metrics for each layer
      const layerMetrics = [];
      
      // Analyze each layer for potential issues
      for (let i = 0; i < this.layers.length; i++) {
        const layer = this.layers[i];
        const metrics = {
          index: i,
          type: layer.constructor.name,
          weightStats: { min: Infinity, max: -Infinity, mean: 0, std: 0 },
          biasStats: { min: Infinity, max: -Infinity, mean: 0, std: 0 },
          hasLargeWeights: false,
          hasDegenerateWeights: false,
        };
        
        // Analyze weights
        if (layer.weights) {
          const weightValues = this._extractValues(layer.weights);
          if (weightValues.length > 0) {
            const weightStats = this._calculateStats(weightValues);
            metrics.weightStats = weightStats;
            
            // Check for large weights (potential instability)
            if (Math.abs(weightStats.max) > weightMagnitudeThreshold || 
                Math.abs(weightStats.min) > weightMagnitudeThreshold) {
              metrics.hasLargeWeights = true;
              score -= 0.1;
              violations.push({
                type: "LARGE_WEIGHTS",
                severity: "medium",
                message: `Layer ${i} has unusually large weights`,
                threshold: weightMagnitudeThreshold,
                actual: Math.max(Math.abs(weightStats.max), Math.abs(weightStats.min)),
                details: {
                  layerIndex: i,
                  layerType: metrics.type,
                  weightStats
                }
              });
            }
            
            // Check for degenerate weights (potentially dead neurons)
            const weightVariance = weightStats.std * weightStats.std;
            if (weightVariance < 0.01 && weightStats.mean !== 0) {
              metrics.hasDegenerateWeights = true;
              score -= 0.1;
              violations.push({
                type: "DEGENERATE_WEIGHTS",
                severity: "low",
                message: `Layer ${i} has low variance in weights`,
                threshold: 0.01,
                actual: weightVariance,
                details: {
                  layerIndex: i,
                  layerType: metrics.type,
                  weightStats
                }
              });
            }
          }
        }
        
        // Analyze biases
        if (layer.biases) {
          const biasValues = this._extractValues(layer.biases);
          if (biasValues.length > 0) {
            const biasStats = this._calculateStats(biasValues);
            metrics.biasStats = biasStats;
            
            // Check for extreme bias values
            if (Math.abs(biasStats.max) > weightMagnitudeThreshold || 
                Math.abs(biasStats.min) > weightMagnitudeThreshold) {
              score -= 0.05;
              violations.push({
                type: "LARGE_BIASES",
                severity: "low",
                message: `Layer ${i} has unusually large bias values`,
                threshold: weightMagnitudeThreshold,
                actual: Math.max(Math.abs(biasStats.max), Math.abs(biasStats.min)),
                details: {
                  layerIndex: i,
                  layerType: metrics.type,
                  biasStats
                }
              });
            }
          }
        }
        
        // Check for activation function issues
        if (layer.activation) {
          metrics.activation = layer.activation;
          
          // Check for potential issues with specific activation functions
          if (layer.activation === "sigmoid" || layer.activation === "tanh") {
            // These activations can cause vanishing gradients in deep networks
            if (i < this.layers.length - 1 && this.layers.length > 3) {
              score -= 0.05;
              violations.push({
                type: "ACTIVATION_WARNING",
                severity: "low",
                message: `Layer ${i} uses ${layer.activation} activation, which may lead to vanishing gradients`,
                details: {
                  layerIndex: i,
                  layerType: metrics.type,
                  activation: layer.activation,
                  recommendedAction: "Consider using ReLU for hidden layers"
                }
              });
            }
          }
        }
        
        layerMetrics.push(metrics);
      }
      
      // Check for architectural issues
      
      // Issue: All layers have same size (often suboptimal)
      const allSameSize = this.layers.length > 1 && this.layers.every((layer, i, arr) => 
        i === 0 || (layer.outputSize === arr[i-1].outputSize)
      );
      
      if (allSameSize && this.layers.length >= 3) {
        score -= 0.1;
        violations.push({
          type: "UNIFORM_ARCHITECTURE",
          severity: "low",
          message: "All hidden layers have the same size, which may be suboptimal",
          details: {
            layerCount: this.layers.length,
            recommendedAction: "Consider decreasing layer sizes progressively"
          }
        });
      }
      
      // Issue: Very deep network with sigmoid/tanh (vanishing gradient risk)
      const hasSigmoidOrTanh = this.layers.some(layer => 
        layer.activation === "sigmoid" || layer.activation === "tanh"
      );
      
      if (hasSigmoidOrTanh && this.layers.length > 5) {
        score -= 0.15;
        violations.push({
          type: "VANISHING_GRADIENT_RISK",
          severity: "medium",
          message: "Deep network with sigmoid/tanh activations may suffer from vanishing gradients",
          details: {
            layerCount: this.layers.length,
            recommendedAction: "Use ReLU activations and consider adding residual connections"
          }
        });
      }
      
      // Analyze interconnections between layers
      for (let i = 1; i < this.layers.length; i++) {
        const prevLayer = this.layers[i-1];
        const currLayer = this.layers[i];
        
        // Check for bottleneck layers that are too narrow
        if (prevLayer.outputSize > 10 && 
            currLayer.outputSize < prevLayer.outputSize / 5 && 
            i < this.layers.length - 1) {
          score -= 0.1;
          violations.push({
            type: "EXTREME_BOTTLENECK",
            severity: "medium",
            message: `Bottleneck between layers ${i-1} and ${i} may be too restrictive`,
            threshold: prevLayer.outputSize / 5,
            actual: currLayer.outputSize,
            details: {
              prevLayerSize: prevLayer.outputSize,
              currLayerSize: currLayer.outputSize,
              recommendedAction: "Consider a more gradual reduction in layer sizes"
            }
          });
        }
      }
      
      // Check optimizer settings
      if (this.optimizer) {
        const lr = this.optimizer.learningRate || 0.01;
        
        // Check for excessively high learning rate
        if (lr > 0.1) {
          score -= 0.1;
          violations.push({
            type: "HIGH_LEARNING_RATE",
            severity: "medium",
            message: "Learning rate may be too high for stable training",
            threshold: 0.1,
            actual: lr,
            details: {
              optimizer: this.optimizer.type || "sgd",
              recommendedAction: "Consider reducing learning rate by an order of magnitude"
            }
          });
        }
        
        // Check for excessively low learning rate
        if (lr < 0.00001) {
          score -= 0.05;
          violations.push({
            type: "LOW_LEARNING_RATE",
            severity: "low",
            message: "Learning rate may be too low for efficient training",
            threshold: 0.00001,
            actual: lr,
            details: {
              optimizer: this.optimizer.type || "sgd",
              recommendedAction: "Consider increasing learning rate"
            }
          });
        }
      }
      
      // Ensure score is between 0 and 1
      score = Math.max(0, Math.min(1, score));
      
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
            violations: violations,
            score: score,
            modelName: this.name,
            layerCount: this.layers.length,
            optimizer: this.optimizer ? this.optimizer.type : "none"
          },
          worstViolation.type
        );
      }
      
      return score;
    } catch (error) {
      // Re-throw NeuralCoherenceError
      if (error instanceof (Prime.Neural.Errors.NeuralCoherenceError || Prime.ValidationError)) {
        throw error;
      }
      
      // Wrap other errors
      throw new (Prime.Neural.Errors.ModelError || Prime.ValidationError)(
        "Error during model coherence calculation",
        { 
          modelName: this.name,
          originalError: error.message
        },
        "COHERENCE_CALCULATION_ERROR",
        error
      );
    }
  }
  
  /**
   * Extract numeric values from parameter object (handles arrays, typed arrays, etc.)
   * @private
   * @param {Array|TypedArray|Object|number} param - Parameter to extract values from
   * @returns {Array<number>} Extracted values
   */
  _extractValues(param) {
    const values = [];
    
    if (param === null || param === undefined) {
      return values;
    }
    
    if (typeof param === 'number') {
      values.push(param);
    } else if (Array.isArray(param)) {
      if (param.length === 0) {
        return values;
      }
      
      if (Array.isArray(param[0])) {
        // 2D array
        for (const row of param) {
          for (const val of row) {
            if (typeof val === 'number' && !isNaN(val)) {
              values.push(val);
            }
          }
        }
      } else {
        // 1D array
        for (const val of param) {
          if (typeof val === 'number' && !isNaN(val)) {
            values.push(val);
          }
        }
      }
    } else if (param.buffer instanceof ArrayBuffer) {
      // TypedArray
      for (let i = 0; i < param.length; i++) {
        values.push(param[i]);
      }
    } else if (typeof param === 'object' && param.rows && param.columns) {
      // Matrix-like object
      // This is a simplified assumption - actual implementation may vary
      for (let i = 0; i < param.rows; i++) {
        for (let j = 0; j < param.columns; j++) {
          if (param.get && typeof param.get === 'function') {
            const val = param.get(i, j);
            if (typeof val === 'number' && !isNaN(val)) {
              values.push(val);
            }
          }
        }
      }
    }
    
    return values;
  }
  
  /**
   * Calculate basic statistics for an array of values
   * @private
   * @param {Array<number>} values - Array of numeric values
   * @returns {Object} Statistics object with min, max, mean, std
   */
  _calculateStats(values) {
    if (!values || values.length === 0) {
      return { min: 0, max: 0, mean: 0, std: 0 };
    }
    
    let min = values[0];
    let max = values[0];
    let sum = 0;
    
    // Calculate min, max, sum
    for (const val of values) {
      if (val < min) min = val;
      if (val > max) max = val;
      sum += val;
    }
    
    const mean = sum / values.length;
    
    // Calculate standard deviation
    let sumSquaredDiff = 0;
    for (const val of values) {
      const diff = val - mean;
      sumSquaredDiff += diff * diff;
    }
    
    const std = Math.sqrt(sumSquaredDiff / values.length);
    
    return { min, max, mean, std };
  }

  static fromJSON(json) {
    const model = new Prime.Neural.Model.NeuralModel({
      name: json.name,
      optimizer: json.optimizer,
      useTypedArrays: false,
    });

    // Remove any existing layers (from constructor)
    model.layers = [];

    if (Array.isArray(json.layers)) {
      for (const layerData of json.layers) {
        let layer;

        // Create appropriate layer type
        if (layerData.type === "Dense") {
          const config = layerData.config;
          layer = new Prime.Neural.Layer.Dense(
            config.inputSize,
            config.outputSize,
            { activation: config.activation },
          );

          // Set weights and biases
          if (layerData.weights) layer.weights = layerData.weights;
          if (layerData.biases) layer.biases = layerData.biases;
        }

        if (layer) model.layers.push(layer);
      }
    }

    return model;
  }
};

// Export the enhanced Prime object
module.exports = Prime;
