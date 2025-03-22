/**
 * PrimeOS JavaScript Library - Neural Model Module
 * Comprehensive neural network model implementation with coherence integration
 */

// Import the Prime object from core
const Prime = require("../../core");

// Create the Neural Model module using IIFE
(function () {
  /**
   * Neural Network Model
   * Complete neural network implementation with advanced features
   */
  class NeuralModel {
    /**
     * Create a new neural network model
     * @param {Object} config - Model configuration
     * @param {Array} [config.layers=[]] - Array of layer configurations
     * @param {Object} [config.optimizer={}] - Optimizer configuration
     * @param {Object} [config.coherence={}] - Coherence configuration
     * @param {Object} [config.metadata={}] - Model metadata
     */
    constructor(config = {}) {
      if (!Prime.Utils.isObject(config)) {
        throw new Prime.ValidationError("Model configuration must be an object");
      }

      // Store original configuration
      this.config = Prime.Utils.deepClone(config);
      
      // Initialize layers
      this.layers = [];
      if (Array.isArray(config.layers)) {
        for (const layerConfig of config.layers) {
          this.addLayer(layerConfig);
        }
      }
      
      // Initialize optimizer
      this.optimizer = this._createOptimizer(config.optimizer || {});
      
      // Set up coherence configuration
      this.coherenceConfig = {
        enabled: config.coherence?.enabled ?? true,
        minThreshold: config.coherence?.minThreshold ?? 0.7,
        checkFrequency: config.coherence?.checkFrequency ?? 100,
        autoCorrect: config.coherence?.autoCorrect ?? true,
        monitorGradients: config.coherence?.monitorGradients ?? true,
        strictMode: config.coherence?.strictMode ?? false
      };
      
      // Performance tracking
      this.metrics = {
        epoch: 0,
        iteration: 0,
        trainingLoss: [],
        validationLoss: [],
        trainingAccuracy: [],
        validationAccuracy: [],
        learningRate: this.optimizer.learningRate,
        coherenceScore: 1.0,
        lastCoherenceCheck: 0,
        layerCoherenceScores: []
      };
      
      // History of coherence violations for monitoring
      this.coherenceViolations = [];
      
      // Model metadata
      this.metadata = {
        name: config.metadata?.name || "NeuralModel",
        description: config.metadata?.description || "",
        version: config.metadata?.version || "1.0.0",
        created: config.metadata?.created || new Date().toISOString(),
        updated: new Date().toISOString()
      };
      
      // Compile status
      this.compiled = false;
    }

    /**
     * Add a layer to the model
     * @param {Object} layerConfig - Layer configuration
     * @returns {NeuralModel} This model instance (for chaining)
     */
    addLayer(layerConfig) {
      if (!Prime.Utils.isObject(layerConfig)) {
        throw new Prime.ValidationError("Layer configuration must be an object");
      }
      
      if (!layerConfig.type) {
        throw new Prime.ValidationError("Layer type must be specified");
      }
      
      // Connect to previous layer if needed
      if (this.layers.length > 0 && !layerConfig.inputSize && !layerConfig.inputShape) {
        const prevLayer = this.layers[this.layers.length - 1];
        
        // Determine input size from previous layer
        if (prevLayer.returnSequences) {
          layerConfig.sequenceLength = prevLayer.sequenceLength;
          layerConfig.inputSize = prevLayer.hiddenSize;
        } else if (prevLayer.outputShape) {
          layerConfig.inputShape = prevLayer.outputShape;
        } else {
          layerConfig.inputSize = prevLayer.outputSize;
        }
      }
      
      // Create the appropriate layer type
      let layer;
      switch (layerConfig.type.toLowerCase()) {
        case 'dense':
        case 'fully_connected':
          layer = new Prime.Neural.Layer.NeuralLayer(layerConfig);
          break;
          
        case 'self_optimizing':
          layer = new Prime.Neural.Layer.SelfOptimizingLayer(layerConfig);
          break;
          
        case 'convolutional':
        case 'conv2d':
          if (!Prime.Neural.Layer.ConvolutionalLayer) {
            throw new Prime.ValidationError("ConvolutionalLayer is not available");
          }
          layer = new Prime.Neural.Layer.ConvolutionalLayer(layerConfig);
          break;
          
        case 'recurrent':
        case 'rnn':
        case 'lstm':
        case 'gru':
          if (!Prime.Neural.Layer.RecurrentLayer) {
            throw new Prime.ValidationError("RecurrentLayer is not available");
          }
          layerConfig.cellType = layerConfig.cellType || 
            (layerConfig.type === 'lstm' ? 'lstm' : 
             layerConfig.type === 'gru' ? 'gru' : 'simple');
          layer = new Prime.Neural.Layer.RecurrentLayer(layerConfig);
          break;
          
        default:
          throw new Prime.ValidationError(`Unsupported layer type: ${layerConfig.type}`);
      }
      
      // Add layer to the model
      this.layers.push(layer);
      
      // Mark model as not compiled
      this.compiled = false;
      
      return this;
    }

    /**
     * Create an optimizer based on configuration
     * @private
     * @param {Object} config - Optimizer configuration
     * @returns {Object} Optimizer instance
     */
    _createOptimizer(config) {
      const optimizerType = config.type || 'adam';
      
      switch (optimizerType.toLowerCase()) {
        case 'sgd':
          return new Prime.Neural.Optimization.CoherenceSGD({
            learningRate: config.learningRate || 0.01,
            momentum: config.momentum || 0,
            coherenceWeight: config.coherenceWeight || 0.5,
            minCoherence: config.minCoherence || 0.7
          });
          
        case 'adam':
          return new Prime.Neural.Optimization.CoherenceAdam({
            learningRate: config.learningRate || 0.001,
            beta1: config.beta1 || 0.9,
            beta2: config.beta2 || 0.999,
            epsilon: config.epsilon || 1e-8,
            coherenceWeight: config.coherenceWeight || 0.5,
            minCoherence: config.minCoherence || 0.7
          });
          
        default:
          // Default to Adam
          return new Prime.Neural.Optimization.CoherenceAdam({
            learningRate: 0.001,
            coherenceWeight: 0.5,
            minCoherence: 0.7
          });
      }
    }

    /**
     * Compile the model for training
     * @param {Object} config - Compile configuration
     * @param {string} [config.loss='mse'] - Loss function
     * @param {string} [config.metric='accuracy'] - Evaluation metric
     * @returns {NeuralModel} This model instance (for chaining)
     */
    compile(config = {}) {
      if (!Prime.Utils.isObject(config)) {
        throw new Prime.ValidationError("Compile configuration must be an object");
      }
      
      // Store loss and metric configuration
      this.lossFunction = config.loss || 'mse';
      this.metric = config.metric || 'accuracy';
      
      // Verify layer connections
      this._validateLayerConnections();
      
      // Set up loss function
      this._setupLossFunction();
      
      // Set up metric function
      this._setupMetricFunction();
      
      // Mark as compiled
      this.compiled = true;
      
      return this;
    }

    /**
     * Validate connections between layers
     * @private
     * @throws {Error} If layer connections are invalid
     */
    _validateLayerConnections() {
      if (this.layers.length === 0) {
        throw new Prime.ValidationError("Model must have at least one layer");
      }
      
      // Check for compatible dimensions between layers
      for (let i = 1; i < this.layers.length; i++) {
        const prevLayer = this.layers[i - 1];
        const currentLayer = this.layers[i];
        
        let isCompatible = false;
        
        // Check compatibility based on layer types
        if (prevLayer.returnSequences) {
          // RNN/LSTM with return_sequences=true -> next layer
          if (currentLayer.inputSize === prevLayer.hiddenSize) {
            isCompatible = true;
          }
        } else if (prevLayer.outputShape && currentLayer.inputShape) {
          // Convolutional -> Convolutional
          const prevOutShape = prevLayer.outputShape;
          const currInShape = currentLayer.inputShape;
          
          if (
            prevOutShape.length === currInShape.length &&
            prevOutShape[0] === currInShape[0] &&
            prevOutShape[1] === currInShape[1] &&
            prevOutShape[2] === currInShape[2]
          ) {
            isCompatible = true;
          }
        } else if (prevLayer.outputShape && currentLayer.inputSize) {
          // Convolutional -> Dense (flattening happens automatically)
          const totalSize = prevLayer.outputShape.reduce((a, b) => a * b, 1);
          if (currentLayer.inputSize === totalSize) {
            isCompatible = true;
          }
        } else if (prevLayer.outputSize && currentLayer.inputSize) {
          // Dense -> Dense
          if (prevLayer.outputSize === currentLayer.inputSize) {
            isCompatible = true;
          }
        }
        
        if (!isCompatible) {
          throw new Prime.ValidationError(
            `Incompatible layer dimensions between layers ${i-1} and ${i}`
          );
        }
      }
    }

    /**
     * Set up loss function based on configuration
     * @private
     */
    _setupLossFunction() {
      // Implementation of common loss functions
      switch (this.lossFunction.toLowerCase()) {
        case 'mse':
        case 'mean_squared_error':
          this._calculateLoss = this._meanSquaredError;
          this._calculateLossGradient = this._meanSquaredErrorGradient;
          break;
          
        case 'mae':
        case 'mean_absolute_error':
          this._calculateLoss = this._meanAbsoluteError;
          this._calculateLossGradient = this._meanAbsoluteErrorGradient;
          break;
          
        case 'bce':
        case 'binary_crossentropy':
          this._calculateLoss = this._binaryCrossentropy;
          this._calculateLossGradient = this._binaryCrossentropyGradient;
          break;
          
        case 'cce':
        case 'categorical_crossentropy':
          this._calculateLoss = this._categoricalCrossentropy;
          this._calculateLossGradient = this._categoricalCrossentropyGradient;
          break;
          
        default:
          this._calculateLoss = this._meanSquaredError;
          this._calculateLossGradient = this._meanSquaredErrorGradient;
      }
    }

    /**
     * Set up metric function based on configuration
     * @private
     */
    _setupMetricFunction() {
      // Implementation of common metrics
      switch (this.metric.toLowerCase()) {
        case 'accuracy':
          this._calculateMetric = this._calculateAccuracy;
          break;
          
        case 'precision':
          this._calculateMetric = this._calculatePrecision;
          break;
          
        case 'recall':
          this._calculateMetric = this._calculateRecall;
          break;
          
        case 'f1':
          this._calculateMetric = this._calculateF1Score;
          break;
          
        default:
          this._calculateMetric = this._calculateAccuracy;
      }
    }

    /**
     * Mean squared error loss function
     * @private
     * @param {Array} yTrue - True values
     * @param {Array} yPred - Predicted values
     * @returns {number} Loss value
     */
    _meanSquaredError(yTrue, yPred) {
      // Handle null or undefined values
      if (!yTrue || !yPred) {
        Prime.Logger.warn("MSE received null or undefined input");
        return 0;
      }
      
      // Handle arrays of any dimension
      const flatten = (arr) => {
        if (!Array.isArray(arr)) return [];
        if (arr.length === 0) return [];
        if (!Array.isArray(arr[0])) return arr;
        return [].concat(...arr.map(a => flatten(a)));
      };
      
      const flatYTrue = flatten(yTrue);
      const flatYPred = flatten(yPred);
      
      if (flatYTrue.length === 0 || flatYPred.length === 0) {
        Prime.Logger.warn("MSE received empty array input");
        return 0;
      }
      
      if (flatYTrue.length !== flatYPred.length) {
        throw new Prime.ValidationError(
          `Incompatible dimensions: ${flatYTrue.length} vs ${flatYPred.length}`
        );
      }
      
      let sumSquaredError = 0;
      for (let i = 0; i < flatYTrue.length; i++) {
        const error = flatYTrue[i] - flatYPred[i];
        sumSquaredError += error * error;
      }
      
      return sumSquaredError / flatYTrue.length;
    }

    /**
     * Gradient of mean squared error
     * @private
     * @param {Array} yTrue - True values
     * @param {Array} yPred - Predicted values
     * @returns {Array} Gradient of loss with respect to predictions
     */
    _meanSquaredErrorGradient(yTrue, yPred) {
      // Handle null or undefined values
      if (!yTrue || !yPred) {
        Prime.Logger.warn("MSE gradient received null or undefined input");
        return [];
      }
      
      // Handle empty arrays
      if (!Array.isArray(yTrue) || !Array.isArray(yPred) || yTrue.length === 0 || yPred.length === 0) {
        Prime.Logger.warn("MSE gradient received empty array input");
        return [];
      }
      
      // Determine if working with multi-dimensional arrays
      const isNested = Array.isArray(yTrue[0]);
      
      if (!isNested) {
        // Handle 1D case
        const gradient = new Array(yPred.length);
        for (let i = 0; i < yPred.length; i++) {
          // d/dy (y - t)² = 2(y - t)
          gradient[i] = 2 * (yPred[i] - yTrue[i]) / yPred.length;
        }
        return gradient;
      } else {
        // Handle multi-dimensional case (recursively)
        return yTrue.map((subTrue, i) => {
          return this._meanSquaredErrorGradient(subTrue, yPred[i]);
        });
      }
    }

    /**
     * Mean absolute error loss function
     * @private
     * @param {Array} yTrue - True values
     * @param {Array} yPred - Predicted values
     * @returns {number} Loss value
     */
    _meanAbsoluteError(yTrue, yPred) {
      // Handle arrays of any dimension
      const flatten = (arr) => {
        if (!Array.isArray(arr[0])) return arr;
        return [].concat(...arr.map(a => flatten(a)));
      };
      
      const flatYTrue = flatten(yTrue);
      const flatYPred = flatten(yPred);
      
      if (flatYTrue.length !== flatYPred.length) {
        throw new Prime.ValidationError(
          `Incompatible dimensions: ${flatYTrue.length} vs ${flatYPred.length}`
        );
      }
      
      let sumAbsError = 0;
      for (let i = 0; i < flatYTrue.length; i++) {
        sumAbsError += Math.abs(flatYTrue[i] - flatYPred[i]);
      }
      
      return sumAbsError / flatYTrue.length;
    }

    /**
     * Gradient of mean absolute error
     * @private
     * @param {Array} yTrue - True values
     * @param {Array} yPred - Predicted values
     * @returns {Array} Gradient of loss with respect to predictions
     */
    _meanAbsoluteErrorGradient(yTrue, yPred) {
      // Determine if working with multi-dimensional arrays
      const isNested = Array.isArray(yTrue[0]);
      
      if (!isNested) {
        // Handle 1D case
        const gradient = new Array(yPred.length);
        for (let i = 0; i < yPred.length; i++) {
          // d/dy |y - t| = sgn(y - t)
          gradient[i] = Math.sign(yPred[i] - yTrue[i]) / yPred.length;
        }
        return gradient;
      } else {
        // Handle multi-dimensional case (recursively)
        return yTrue.map((subTrue, i) => {
          return this._meanAbsoluteErrorGradient(subTrue, yPred[i]);
        });
      }
    }

    /**
     * Binary cross-entropy loss function
     * @private
     * @param {Array} yTrue - True values (0 or 1)
     * @param {Array} yPred - Predicted probabilities
     * @returns {number} Loss value
     */
    _binaryCrossentropy(yTrue, yPred) {
      // Handle arrays of any dimension
      const flatten = (arr) => {
        if (!Array.isArray(arr[0])) return arr;
        return [].concat(...arr.map(a => flatten(a)));
      };
      
      const flatYTrue = flatten(yTrue);
      const flatYPred = flatten(yPred);
      
      if (flatYTrue.length !== flatYPred.length) {
        throw new Prime.ValidationError(
          `Incompatible dimensions: ${flatYTrue.length} vs ${flatYPred.length}`
        );
      }
      
      // Numerical stability: clip predictions to avoid log(0)
      const epsilon = 1e-15;
      
      let sumCrossEntropy = 0;
      for (let i = 0; i < flatYTrue.length; i++) {
        const p = Math.max(Math.min(flatYPred[i], 1 - epsilon), epsilon);
        sumCrossEntropy += 
          flatYTrue[i] * Math.log(p) + 
          (1 - flatYTrue[i]) * Math.log(1 - p);
      }
      
      return -sumCrossEntropy / flatYTrue.length;
    }

    /**
     * Gradient of binary cross-entropy
     * @private
     * @param {Array} yTrue - True values (0 or 1)
     * @param {Array} yPred - Predicted probabilities
     * @returns {Array} Gradient of loss with respect to predictions
     */
    _binaryCrossentropyGradient(yTrue, yPred) {
      // Determine if working with multi-dimensional arrays
      const isNested = Array.isArray(yTrue[0]);
      
      if (!isNested) {
        // Handle 1D case
        const gradient = new Array(yPred.length);
        const epsilon = 1e-15;
        
        for (let i = 0; i < yPred.length; i++) {
          // Clip predictions for numerical stability
          const p = Math.max(Math.min(yPred[i], 1 - epsilon), epsilon);
          // d/dy -[t*log(y) + (1-t)*log(1-y)] = (y-t)/(y*(1-y))
          gradient[i] = ((p - yTrue[i]) / (p * (1 - p))) / yPred.length;
        }
        return gradient;
      } else {
        // Handle multi-dimensional case (recursively)
        return yTrue.map((subTrue, i) => {
          return this._binaryCrossentropyGradient(subTrue, yPred[i]);
        });
      }
    }

    /**
     * Categorical cross-entropy loss function
     * @private
     * @param {Array} yTrue - True values (one-hot encoded)
     * @param {Array} yPred - Predicted probabilities
     * @returns {number} Loss value
     */
    _categoricalCrossentropy(yTrue, yPred) {
      // Handle different shapes (sample-wise vs batch)
      if (!Array.isArray(yTrue[0][0])) {
        // Single sample
        return this._categoricalCrossentropyPerSample(yTrue, yPred);
      } else {
        // Batch of samples
        let sumLoss = 0;
        for (let i = 0; i < yTrue.length; i++) {
          sumLoss += this._categoricalCrossentropyPerSample(yTrue[i], yPred[i]);
        }
        return sumLoss / yTrue.length;
      }
    }

    /**
     * Categorical cross-entropy for a single sample
     * @private
     * @param {Array} yTrue - True values (one-hot encoded)
     * @param {Array} yPred - Predicted probabilities
     * @returns {number} Loss value
     */
    _categoricalCrossentropyPerSample(yTrue, yPred) {
      if (yTrue.length !== yPred.length) {
        throw new Prime.ValidationError(
          `Incompatible dimensions: ${yTrue.length} vs ${yPred.length}`
        );
      }
      
      // Numerical stability: clip predictions to avoid log(0)
      const epsilon = 1e-15;
      
      let sumCrossEntropy = 0;
      for (let i = 0; i < yTrue.length; i++) {
        const p = Math.max(Math.min(yPred[i], 1 - epsilon), epsilon);
        sumCrossEntropy += yTrue[i] * Math.log(p);
      }
      
      return -sumCrossEntropy;
    }

    /**
     * Gradient of categorical cross-entropy
     * @private
     * @param {Array} yTrue - True values (one-hot encoded)
     * @param {Array} yPred - Predicted probabilities
     * @returns {Array} Gradient of loss with respect to predictions
     */
    _categoricalCrossentropyGradient(yTrue, yPred) {
      // Handle different shapes (sample-wise vs batch)
      if (!Array.isArray(yTrue[0][0])) {
        // Single sample
        const gradient = new Array(yPred.length);
        for (let i = 0; i < yPred.length; i++) {
          // d/dy -t*log(y) = -t/y
          gradient[i] = -yTrue[i] / (yPred[i] + 1e-15);
        }
        return gradient;
      } else {
        // Batch of samples
        return yTrue.map((subTrue, i) => {
          return this._categoricalCrossentropyGradient(subTrue, yPred[i]);
        });
      }
    }

    /**
     * Calculate accuracy metric
     * @private
     * @param {Array} yTrue - True values
     * @param {Array} yPred - Predicted values
     * @returns {number} Accuracy (0-1)
     */
    _calculateAccuracy(yTrue, yPred) {
      // Handle null or undefined values
      if (!yTrue || !yPred) {
        Prime.Logger.warn("Accuracy calculation received null or undefined input");
        return 0;
      }
      
      // Handle empty arrays
      if (!Array.isArray(yTrue) || !Array.isArray(yPred) || yTrue.length === 0 || yPred.length === 0) {
        Prime.Logger.warn("Accuracy calculation received empty array input");
        return 0;
      }
      
      // Handle arrays of any dimension
      const flatten = (arr) => {
        if (!Array.isArray(arr)) return [];
        if (arr.length === 0) return [];
        if (!Array.isArray(arr[0])) return arr;
        return [].concat(...arr.map(a => flatten(a)));
      };
      
      // Handle one-hot encoded categorical data
      const argmax = (arr) => {
        if (!Array.isArray(arr) || arr.length === 0) return -1;
        return arr.indexOf(Math.max(...arr));
      };
      
      const oneHot = Array.isArray(yTrue[0]) && Array.isArray(yPred[0]) && 
                    !Array.isArray(yTrue[0][0]) && !Array.isArray(yPred[0][0]);
      
      if (oneHot) {
        // Convert one-hot encoded values to class indices
        let correct = 0;
        for (let i = 0; i < yTrue.length; i++) {
          const trueClass = argmax(yTrue[i]);
          const predClass = argmax(yPred[i]);
          if (trueClass === predClass) {
            correct++;
          }
        }
        return correct / yTrue.length;
      } else {
        // Handle binary or regression values
        const flatYTrue = flatten(yTrue);
        const flatYPred = flatten(yPred);
        
        // Binary classification threshold
        const threshold = 0.5;
        
        let correct = 0;
        for (let i = 0; i < flatYTrue.length; i++) {
          const binaryTrue = flatYTrue[i] >= threshold ? 1 : 0;
          const binaryPred = flatYPred[i] >= threshold ? 1 : 0;
          if (binaryTrue === binaryPred) {
            correct++;
          }
        }
        
        return correct / flatYTrue.length;
      }
    }

    /**
     * Calculate precision metric
     * @private
     * @param {Array} yTrue - True values
     * @param {Array} yPred - Predicted values
     * @returns {number} Precision (0-1)
     */
    _calculatePrecision(yTrue, yPred) {
      // Handle arrays of any dimension
      const flatten = (arr) => {
        if (!Array.isArray(arr[0])) return arr;
        return [].concat(...arr.map(a => flatten(a)));
      };
      
      const flatYTrue = flatten(yTrue);
      const flatYPred = flatten(yPred);
      
      // Binary classification threshold
      const threshold = 0.5;
      
      let truePositives = 0;
      let falsePositives = 0;
      
      for (let i = 0; i < flatYTrue.length; i++) {
        const binaryTrue = flatYTrue[i] >= threshold ? 1 : 0;
        const binaryPred = flatYPred[i] >= threshold ? 1 : 0;
        
        if (binaryPred === 1) {
          if (binaryTrue === 1) {
            truePositives++;
          } else {
            falsePositives++;
          }
        }
      }
      
      if (truePositives + falsePositives === 0) {
        return 0;
      }
      
      return truePositives / (truePositives + falsePositives);
    }

    /**
     * Calculate recall metric
     * @private
     * @param {Array} yTrue - True values
     * @param {Array} yPred - Predicted values
     * @returns {number} Recall (0-1)
     */
    _calculateRecall(yTrue, yPred) {
      // Handle arrays of any dimension
      const flatten = (arr) => {
        if (!Array.isArray(arr[0])) return arr;
        return [].concat(...arr.map(a => flatten(a)));
      };
      
      const flatYTrue = flatten(yTrue);
      const flatYPred = flatten(yPred);
      
      // Binary classification threshold
      const threshold = 0.5;
      
      let truePositives = 0;
      let falseNegatives = 0;
      
      for (let i = 0; i < flatYTrue.length; i++) {
        const binaryTrue = flatYTrue[i] >= threshold ? 1 : 0;
        const binaryPred = flatYPred[i] >= threshold ? 1 : 0;
        
        if (binaryTrue === 1) {
          if (binaryPred === 1) {
            truePositives++;
          } else {
            falseNegatives++;
          }
        }
      }
      
      if (truePositives + falseNegatives === 0) {
        return 0;
      }
      
      return truePositives / (truePositives + falseNegatives);
    }

    /**
     * Calculate F1 score metric
     * @private
     * @param {Array} yTrue - True values
     * @param {Array} yPred - Predicted values
     * @returns {number} F1 score (0-1)
     */
    _calculateF1Score(yTrue, yPred) {
      const precision = this._calculatePrecision(yTrue, yPred);
      const recall = this._calculateRecall(yTrue, yPred);
      
      if (precision + recall === 0) {
        return 0;
      }
      
      return 2 * (precision * recall) / (precision + recall);
    }

    /**
     * Forward pass through the network
     * @param {Array} input - Input data
     * @param {Object} [options={}] - Options for the forward pass
     * @param {boolean} [options.training=false] - Whether we are in training mode
     * @returns {Object} Activation and layer caches
     */
    _forward(input, options = {}) {
      const isTraining = options.training === true;
      
      // Initialize layer activations and caches
      const layerActivations = new Array(this.layers.length + 1);
      const layerCaches = new Array(this.layers.length);
      
      // Input is the first "activation"
      layerActivations[0] = input;
      
      // Forward pass through each layer
      for (let i = 0; i < this.layers.length; i++) {
        const layer = this.layers[i];
        const result = layer.forward(layerActivations[i]);
        
        layerActivations[i + 1] = result.activation;
        layerCaches[i] = result.cache;
      }
      
      return {
        activation: layerActivations[this.layers.length],
        layerActivations,
        layerCaches
      };
    }

    /**
     * Backward pass through the network
     * @param {Array} dY - Gradient of loss with respect to output
     * @param {Object} forwardResult - Result from forward pass
     * @returns {Object} Gradients for all parameters
     */
    _backward(dY, forwardResult) {
      const { layerActivations, layerCaches } = forwardResult;
      
      // Initialize layer gradients
      const layerGradients = new Array(this.layers.length);
      
      // Output gradient is the starting point
      let currentGradient = dY;
      
      // Backward pass through each layer in reverse order
      for (let i = this.layers.length - 1; i >= 0; i--) {
        const layer = this.layers[i];
        
        // Backward pass through this layer
        const gradients = layer.backward(currentGradient, layerCaches[i]);
        
        // Store gradients for later use in optimization
        layerGradients[i] = {
          dWeights: gradients.dW,
          dBiases: gradients.dB
        };
        
        // Pass gradient to previous layer
        currentGradient = gradients.dX;
      }
      
      return layerGradients;
    }

    /**
     * Predict outputs for given inputs
     * @param {Array} input - Input data
     * @returns {Array} Predicted outputs
     */
    predict(input) {
      if (!this.compiled) {
        throw new Prime.ValidationError("Model must be compiled before prediction");
      }
      
      const forwardResult = this._forward(input, { training: false });
      return forwardResult.activation;
    }

    /**
     * Train the model for one batch of data
     * @param {Array} x - Input data
     * @param {Array} y - Target data
     * @param {Object} [options={}] - Training options
     * @returns {Object} Loss and metric values
     */
    trainOnBatch(x, y, options = {}) {
      if (!this.compiled) {
        throw new Prime.ValidationError("Model must be compiled before training");
      }
      
      // Forward pass
      const forwardResult = this._forward(x, { training: true });
      const predictions = forwardResult.activation;
      
      // Calculate loss and metric
      const loss = this._calculateLoss(y, predictions);
      const metricValue = this._calculateMetric(y, predictions);
      
      // Calculate loss gradient
      const dY = this._calculateLossGradient(y, predictions);
      
      // Backward pass to compute gradients
      const layerGradients = this._backward(dY, forwardResult);
      
      // Update model with computed gradients
      this._updateModel(layerGradients);
      
      // Update training metrics
      this.metrics.iteration++;
      
      // Check coherence if needed
      if (
        this.coherenceConfig.enabled && 
        this.metrics.iteration - this.metrics.lastCoherenceCheck >= this.coherenceConfig.checkFrequency
      ) {
        this._checkModelCoherence();
      }
      
      return {
        loss,
        metric: metricValue
      };
    }

    /**
     * Update model parameters using optimizer
     * @private
     * @param {Array} layerGradients - Gradients for each layer
     */
    _updateModel(layerGradients) {
      // Update each layer
      for (let i = 0; i < this.layers.length; i++) {
        const layer = this.layers[i];
        const gradients = layerGradients[i];
        
        // Skip if gradients are missing
        if (!gradients || !gradients.dWeights || !gradients.dBiases) {
          continue;
        }
        
        // Prepare parameters and gradients in format for optimizer
        const params = {
          weights: layer.weights,
          biases: layer.biases
        };
        
        // Define coherence function for optimizer
        const coherenceFn = (params) => {
          // Create a temporary layer with these parameters
          const tempLayer = { ...layer };
          tempLayer.weights = params.weights;
          tempLayer.biases = params.biases;
          
          // Use layer's own coherence calculation if available
          if (typeof tempLayer._calculateCoherenceScore === 'function') {
            return tempLayer._calculateCoherenceScore();
          }
          
          // Default coherence score (1.0 = fully coherent)
          return 1.0;
        };
        
        // Use optimizer to update parameters
        const updatedParams = this.optimizer.update(
          params,
          {
            weights: gradients.dWeights,
            biases: gradients.dBiases
          },
          coherenceFn
        );
        
        // Apply updated parameters to layer using the layer's own update method
        layer.update(gradients, this.optimizer.learningRate);
      }
      
      // Update learning rate metric
      this.metrics.learningRate = this.optimizer.learningRate;
    }

    /**
     * Check model coherence and take action if needed
     * @private
     */
    _checkModelCoherence() {
      this.metrics.lastCoherenceCheck = this.metrics.iteration;
      
      // Get coherence scores from each layer
      const layerScores = this.layers.map(layer => {
        const metrics = layer.getMetrics();
        return metrics.coherence || 1.0;
      });
      
      // Update layer coherence scores
      this.metrics.layerCoherenceScores = layerScores;
      
      // Calculate overall model coherence as minimum layer coherence
      const modelCoherence = Math.min(...layerScores);
      this.metrics.coherenceScore = modelCoherence;
      
      // Check for coherence violations
      if (modelCoherence < this.coherenceConfig.minThreshold) {
        // Detect which layer has the lowest coherence
        const worstLayerIndex = layerScores.indexOf(modelCoherence);
        
        // Record coherence violation
        const violation = {
          iteration: this.metrics.iteration,
          coherenceScore: modelCoherence,
          violatingLayer: worstLayerIndex,
          timestamp: new Date().toISOString()
        };
        
        this.coherenceViolations.push(violation);
        
        // Take action if auto-correct is enabled
        if (this.coherenceConfig.autoCorrect) {
          this._applyCoherenceCorrection(worstLayerIndex, modelCoherence);
        }
        
        // Strict mode - throw error on coherence violations
        if (this.coherenceConfig.strictMode) {
          throw new Prime.CoherenceError(
            `Coherence violation: score ${modelCoherence} is below threshold ${this.coherenceConfig.minThreshold}`
          );
        }
      }
    }

    /**
     * Apply coherence correction to a layer
     * @private
     * @param {number} layerIndex - Index of the problematic layer
     * @param {number} coherenceScore - Current coherence score
     */
    _applyCoherenceCorrection(layerIndex, coherenceScore) {
      const layer = this.layers[layerIndex];
      
      // Strategies for coherence correction
      
      // Strategy 1: If layer has self-optimization, trigger adaptation
      if (layer instanceof Prime.Neural.Layer.SelfOptimizingLayer) {
        // Force adaptation on next forward pass
        layer.adaptationState.lastOptimized = 0;
        return;
      }
      
      // Strategy 2: Reduce learning rate temporarily
      const originalLR = this.optimizer.learningRate;
      this.optimizer.learningRate *= 0.5;
      
      // Add log of correction
      this.coherenceViolations[this.coherenceViolations.length - 1].correction = {
        type: 'learning_rate_reduction',
        originalRate: originalLR,
        newRate: this.optimizer.learningRate
      };
    }

    /**
     * Train the model on a dataset
     * @param {Array} x - Input data
     * @param {Array} y - Target data
     * @param {Object} [options={}] - Training options
     * @param {number} [options.epochs=1] - Number of epochs
     * @param {number} [options.batchSize=32] - Batch size
     * @param {number} [options.validationSplit=0] - Validation split (0-1)
     * @param {Function} [options.callbacks] - Callbacks during training
     * @returns {Object} Training history
     */
    fit(x, y, options = {}) {
      if (!this.compiled) {
        throw new Prime.ValidationError("Model must be compiled before training");
      }
      
      // Training options
      const epochs = options.epochs || 1;
      const batchSize = options.batchSize || 32;
      const validationSplit = options.validationSplit || 0;
      const callbacks = options.callbacks || function() {};
      
      // Split data into training and validation sets
      let trainX, trainY, valX, valY;
      if (validationSplit > 0) {
        const splitIndex = Math.floor(x.length * (1 - validationSplit));
        trainX = x.slice(0, splitIndex);
        trainY = y.slice(0, splitIndex);
        valX = x.slice(splitIndex);
        valY = y.slice(splitIndex);
      } else {
        trainX = x;
        trainY = y;
      }
      
      // Training history
      const history = {
        loss: [],
        [this.metric]: []
      };
      
      if (validationSplit > 0) {
        history.valLoss = [];
        history[`val_${this.metric}`] = [];
      }
      
      // Train for specified number of epochs
      for (let epoch = 0; epoch < epochs; epoch++) {
        // Update epoch counter
        this.metrics.epoch = epoch + 1;
        
        // Shuffle training data
        if (trainX.length > 1) {
          [trainX, trainY] = this._shuffleData(trainX, trainY);
        }
        
        // Train on batches
        let epochLoss = 0;
        let epochMetric = 0;
        
        for (let batchStart = 0; batchStart < trainX.length; batchStart += batchSize) {
          const batchEnd = Math.min(batchStart + batchSize, trainX.length);
          const batchX = trainX.slice(batchStart, batchEnd);
          const batchY = trainY.slice(batchStart, batchEnd);
          
          // Train on this batch
          const { loss, metric } = this.trainOnBatch(batchX, batchY);
          
          // Accumulate metrics
          epochLoss += loss * (batchEnd - batchStart);
          epochMetric += metric * (batchEnd - batchStart);
          
          // Call batch callback
          callbacks({
            type: 'batchEnd',
            epoch,
            batch: Math.floor(batchStart / batchSize),
            totalBatches: Math.ceil(trainX.length / batchSize),
            loss,
            metric
          });
        }
        
        // Calculate epoch averages
        epochLoss /= trainX.length;
        epochMetric /= trainX.length;
        
        // Save to history
        history.loss.push(epochLoss);
        history[this.metric].push(epochMetric);
        
        // Store in model metrics
        this.metrics.trainingLoss.push(epochLoss);
        this.metrics.trainingAccuracy.push(epochMetric);
        
        // Evaluate on validation set if provided
        if (validationSplit > 0) {
          const { loss: valLoss, metric: valMetric } = this.evaluate(valX, valY);
          
          history.valLoss.push(valLoss);
          history[`val_${this.metric}`].push(valMetric);
          
          // Store in model metrics
          this.metrics.validationLoss.push(valLoss);
          this.metrics.validationAccuracy.push(valMetric);
          
          // Call epoch callback
          callbacks({
            type: 'epochEnd',
            epoch,
            totalEpochs: epochs,
            loss: epochLoss,
            metric: epochMetric,
            valLoss,
            valMetric
          });
        } else {
          // Call epoch callback
          callbacks({
            type: 'epochEnd',
            epoch,
            totalEpochs: epochs,
            loss: epochLoss,
            metric: epochMetric
          });
        }
      }
      
      // Update metadata
      this.metadata.updated = new Date().toISOString();
      
      return history;
    }

    /**
     * Evaluate the model on a dataset
     * @param {Array} x - Input data
     * @param {Array} y - Target data
     * @returns {Object} Loss and metric values
     */
    evaluate(x, y) {
      if (!this.compiled) {
        throw new Prime.ValidationError("Model must be compiled before evaluation");
      }
      
      // Forward pass with training mode off
      const forwardResult = this._forward(x, { training: false });
      const predictions = forwardResult.activation;
      
      // Calculate loss and metric
      const loss = this._calculateLoss(y, predictions);
      const metricValue = this._calculateMetric(y, predictions);
      
      return {
        loss,
        metric: metricValue
      };
    }

    /**
     * Helper method to shuffle training data
     * @private
     * @param {Array} x - Input data
     * @param {Array} y - Target data
     * @returns {Array} Shuffled data [shuffledX, shuffledY]
     */
    _shuffleData(x, y) {
      // Create index array
      const indices = Array.from({ length: x.length }, (_, i) => i);
      
      // Shuffle indices
      for (let i = indices.length - 1; i > 0; i--) {
        const j = Math.floor(Math.random() * (i + 1));
        [indices[i], indices[j]] = [indices[j], indices[i]];
      }
      
      // Create shuffled arrays
      const shuffledX = indices.map(i => x[i]);
      const shuffledY = indices.map(i => y[i]);
      
      return [shuffledX, shuffledY];
    }

    /**
     * Get model summary
     * @returns {Object} Model summary information
     */
    summary() {
      const layerInfo = this.layers.map((layer, index) => {
        let outputShape;
        
        if (layer.outputShape) {
          outputShape = layer.outputShape;
        } else if (layer.returnSequences) {
          outputShape = [layer.sequenceLength, layer.hiddenSize];
        } else {
          outputShape = [layer.outputSize];
        }
        
        let inputShape;
        if (layer.inputShape) {
          inputShape = layer.inputShape;
        } else if (layer.sequenceLength) {
          inputShape = [layer.sequenceLength, layer.inputSize];
        } else {
          inputShape = [layer.inputSize];
        }
        
        let parameters = 0;
        if (typeof layer._countParameters === 'function') {
          parameters = layer._countParameters();
        } else {
          // Estimate parameters for standard layers
          parameters = (inputShape[0] * outputShape[0]) + outputShape[0];
        }
        
        let layerType = layer.constructor.name;
        if (layer.cellType) {
          layerType = `${layer.cellType.toUpperCase()} (${layerType})`;
        }
        
        return {
          index,
          type: layerType,
          inputShape,
          outputShape,
          parameters,
          coherence: layer.getMetrics().coherence || 1.0
        };
      });
      
      // Count total parameters
      const totalParameters = layerInfo.reduce((sum, layer) => sum + layer.parameters, 0);
      
      return {
        layers: layerInfo,
        totalParameters,
        compiled: this.compiled,
        optimizer: this.optimizer.constructor.name,
        loss: this.lossFunction,
        metric: this.metric,
        coherenceScore: this.metrics.coherenceScore
      };
    }

    /**
     * Save model to JSON format
     * @returns {Object} Serialized model
     */
    toJSON() {
      // Serialize layers
      const layers = this.layers.map(layer => {
        // Get layer type
        let layerType;
        if (layer instanceof Prime.Neural.Layer.NeuralLayer) {
          layerType = 'dense';
        } else if (layer instanceof Prime.Neural.Layer.SelfOptimizingLayer) {
          layerType = 'selfOptimizing';
        } else if (layer instanceof Prime.Neural.Layer.ConvolutionalLayer) {
          layerType = 'convolutional';
        } else if (layer instanceof Prime.Neural.Layer.RecurrentLayer) {
          layerType = layer.cellType || 'recurrent';
        } else {
          layerType = 'custom';
        }
        
        // Get layer configuration
        const config = {};
        
        // Common properties
        if (layer.inputSize !== undefined) config.inputSize = layer.inputSize;
        if (layer.outputSize !== undefined) config.outputSize = layer.outputSize;
        if (layer.activation !== undefined) config.activation = layer.activation;
        
        // Layer-specific properties
        if (layer.inputShape !== undefined) config.inputShape = layer.inputShape;
        if (layer.outputShape !== undefined) config.outputShape = layer.outputShape;
        if (layer.filters !== undefined) config.filters = layer.filters;
        if (layer.kernelSize !== undefined) config.kernelSize = layer.kernelSize;
        if (layer.strides !== undefined) config.strides = layer.strides;
        if (layer.padding !== undefined) config.padding = layer.padding;
        if (layer.hiddenSize !== undefined) config.hiddenSize = layer.hiddenSize;
        if (layer.cellType !== undefined) config.cellType = layer.cellType;
        if (layer.sequenceLength !== undefined) config.sequenceLength = layer.sequenceLength;
        if (layer.returnSequences !== undefined) config.returnSequences = layer.returnSequences;
        if (layer.optimization !== undefined) config.optimization = layer.optimization;
        
        // Serialize weights and biases
        const weights = JSON.stringify(layer.weights);
        const biases = JSON.stringify(layer.biases);
        
        return {
          type: layerType,
          config,
          weights,
          biases
        };
      });
      
      // Serialize optimizer
      const optimizerConfig = {
        type: this.optimizer.constructor.name.replace('Coherence', '').toLowerCase(),
        learningRate: this.optimizer.learningRate
      };
      
      if (this.optimizer.momentum !== undefined) {
        optimizerConfig.momentum = this.optimizer.momentum;
      }
      
      if (this.optimizer.beta1 !== undefined) {
        optimizerConfig.beta1 = this.optimizer.beta1;
        optimizerConfig.beta2 = this.optimizer.beta2;
        optimizerConfig.epsilon = this.optimizer.epsilon;
      }
      
      // Create serialized model
      return {
        metadata: this.metadata,
        config: {
          coherence: this.coherenceConfig,
          optimizer: optimizerConfig,
          loss: this.lossFunction,
          metric: this.metric
        },
        layers,
        metrics: this.metrics
      };
    }

    /**
     * Load model from JSON format
     * @param {Object} json - Serialized model
     * @returns {NeuralModel} Loaded model
     */
    static fromJSON(json) {
      // Create empty model
      const model = new NeuralModel();
      
      // Load metadata
      model.metadata = json.metadata;
      
      // Load configuration
      model.coherenceConfig = json.config.coherence;
      model.lossFunction = json.config.loss;
      model.metric = json.config.metric;
      
      // Create layers
      for (const layerData of json.layers) {
        // Create layer instance based on type
        let layer;
        
        switch (layerData.type.toLowerCase()) {
          case 'dense':
            layer = new Prime.Neural.Layer.NeuralLayer(layerData.config);
            break;
            
          case 'selfoptimizing':
            layer = new Prime.Neural.Layer.SelfOptimizingLayer(layerData.config);
            break;
            
          case 'convolutional':
          case 'conv2d':
            if (!Prime.Neural.Layer.ConvolutionalLayer) {
              throw new Prime.ValidationError("ConvolutionalLayer is not available");
            }
            layer = new Prime.Neural.Layer.ConvolutionalLayer(layerData.config);
            break;
            
          case 'recurrent':
          case 'lstm':
          case 'gru':
            if (!Prime.Neural.Layer.RecurrentLayer) {
              throw new Prime.ValidationError("RecurrentLayer is not available");
            }
            layer = new Prime.Neural.Layer.RecurrentLayer(layerData.config);
            break;
            
          default:
            throw new Prime.ValidationError(`Unsupported layer type: ${layerData.type}`);
        }
        
        // Load weights and biases
        if (layerData.weights && layerData.biases) {
          layer.weights = JSON.parse(layerData.weights);
          layer.biases = JSON.parse(layerData.biases);
        }
        
        // Add layer to model
        model.layers.push(layer);
      }
      
      // Create optimizer
      model.optimizer = model._createOptimizer(json.config.optimizer);
      
      // Set up functions
      model._setupLossFunction();
      model._setupMetricFunction();
      
      // Load metrics
      model.metrics = json.metrics;
      
      // Mark as compiled
      model.compiled = true;
      
      return model;
    }
    
    /**
     * Get visualization data for the network architecture
     * @returns {Object} Visualization data
     */
    getVisualizationData() {
      // Create nodes for each layer
      const nodes = this.layers.map((layer, index) => {
        // Determine layer type and shape
        let layerType = layer.constructor.name;
        if (layer.cellType) {
          layerType = `${layer.cellType.toUpperCase()}`;
        }
        
        // Determine input/output shapes
        let inputShape, outputShape;
        
        if (layer.inputShape) {
          inputShape = layer.inputShape;
        } else if (layer.sequenceLength) {
          inputShape = [layer.sequenceLength, layer.inputSize];
        } else {
          inputShape = [layer.inputSize];
        }
        
        if (layer.outputShape) {
          outputShape = layer.outputShape;
        } else if (layer.returnSequences) {
          outputShape = [layer.sequenceLength, layer.hiddenSize];
        } else {
          outputShape = [layer.outputSize];
        }
        
        // Determine activation function
        const activation = layer.activation || 'linear';
        
        // Get coherence score
        const coherence = layer.getMetrics().coherence || 1.0;
        
        return {
          id: `layer_${index}`,
          type: layerType,
          inputShape,
          outputShape,
          activation,
          coherence
        };
      });
      
      // Create input node
      nodes.unshift({
        id: 'input',
        type: 'Input',
        outputShape: this.layers[0].inputShape || [this.layers[0].inputSize]
      });
      
      // Create connections between nodes
      const edges = [];
      
      // Connect input to first layer
      edges.push({
        source: 'input',
        target: 'layer_0',
        type: 'forward'
      });
      
      // Connect layers
      for (let i = 0; i < this.layers.length - 1; i++) {
        edges.push({
          source: `layer_${i}`,
          target: `layer_${i + 1}`,
          type: 'forward'
        });
      }
      
      return {
        nodes,
        edges,
        metadata: {
          loss: this.lossFunction,
          optimizer: this.optimizer.constructor.name,
          coherenceScore: this.metrics.coherenceScore,
          learningRate: this.optimizer.learningRate
        }
      };
    }
  }

  /**
   * Neural Architecture Search
   * Automated discovery of optimal neural network architectures
   */
  class NeuralArchitectureSearch {
    /**
     * Create a new neural architecture search
     * @param {Object} config - Search configuration
     * @param {Object} config.searchSpace - Search space definition
     * @param {Function} config.evaluationFunction - Function to evaluate architectures
     * @param {number} [config.maxTrials=10] - Maximum number of trials
     * @param {Object} [config.coherenceConfig={}] - Coherence configuration
     */
    constructor(config = {}) {
      if (!Prime.Utils.isObject(config)) {
        throw new Prime.ValidationError("Search configuration must be an object");
      }
      
      if (!Prime.Utils.isObject(config.searchSpace)) {
        throw new Prime.ValidationError("Search space must be defined");
      }
      
      if (typeof config.evaluationFunction !== 'function') {
        throw new Prime.ValidationError("Evaluation function must be provided");
      }
      
      this.searchSpace = config.searchSpace;
      this.evaluationFunction = config.evaluationFunction;
      this.maxTrials = config.maxTrials || 10;
      
      // Coherence configuration for guiding the search
      this.coherenceConfig = {
        minCoherence: config.coherenceConfig?.minCoherence ?? 0.7,
        coherenceWeight: config.coherenceConfig?.coherenceWeight ?? 0.3,
        enforceCoherence: config.coherenceConfig?.enforceCoherence ?? true
      };
      
      // Search state
      this.trials = [];
      this.bestArchitecture = null;
      this.bestScore = -Infinity;
      
      // Initialize search space parser
      this._initializeSearchSpace();
    }

    /**
     * Initialize and validate search space
     * @private
     */
    _initializeSearchSpace() {
      // Validate layer types in search space
      const validLayerTypes = ['dense', 'convolutional', 'recurrent', 'lstm', 'gru'];
      
      // Check required search space parameters
      if (!Array.isArray(this.searchSpace.layerTypes)) {
        throw new Prime.ValidationError("Search space must define layerTypes array");
      }
      
      for (const layerType of this.searchSpace.layerTypes) {
        if (!validLayerTypes.includes(layerType.toLowerCase())) {
          throw new Prime.ValidationError(`Invalid layer type in search space: ${layerType}`);
        }
      }
      
      // Check numeric ranges
      const requiredRanges = ['layerCount', 'units', 'learningRate'];
      for (const range of requiredRanges) {
        if (
          !this.searchSpace[range] || 
          typeof this.searchSpace[range].min !== 'number' || 
          typeof this.searchSpace[range].max !== 'number'
        ) {
          throw new Prime.ValidationError(`Search space must define range for ${range}`);
        }
      }
      
      // Set default activation functions if not provided
      if (!Array.isArray(this.searchSpace.activations)) {
        this.searchSpace.activations = ['relu', 'sigmoid', 'tanh'];
      }
      
      // Set default optimizer types if not provided
      if (!Array.isArray(this.searchSpace.optimizers)) {
        this.searchSpace.optimizers = ['adam', 'sgd'];
      }
    }

    /**
     * Generate a random architecture from the search space
     * @private
     * @returns {Object} Random architecture configuration
     */
    _generateRandomArchitecture() {
      // Helper to select random item from array
      const randomChoice = arr => arr[Math.floor(Math.random() * arr.length)];
      
      // Helper to select random integer in range [min, max]
      const randomInt = (min, max) => Math.floor(min + Math.random() * (max - min + 1));
      
      // Helper to select random float in range [min, max]
      const randomFloat = (min, max) => min + Math.random() * (max - min);
      
      // Generate architecture parameters
      const layerCount = randomInt(
        this.searchSpace.layerCount.min,
        this.searchSpace.layerCount.max
      );
      
      const optimizer = randomChoice(this.searchSpace.optimizers);
      const learningRate = randomFloat(
        this.searchSpace.learningRate.min,
        this.searchSpace.learningRate.max
      );
      
      // Generate layers
      const layers = [];
      for (let i = 0; i < layerCount; i++) {
        const layerType = randomChoice(this.searchSpace.layerTypes);
        const activation = randomChoice(this.searchSpace.activations);
        
        // Base layer configuration
        const layer = {
          type: layerType,
          activation
        };
        
        // Layer-specific parameters
        if (layerType === 'dense') {
          layer.outputSize = randomInt(
            this.searchSpace.units.min,
            this.searchSpace.units.max
          );
        }
        else if (layerType === 'convolutional') {
          layer.filters = randomInt(16, 64);
          layer.kernelSize = [randomChoice([3, 5]), randomChoice([3, 5])];
          layer.strides = [randomChoice([1, 2]), randomChoice([1, 2])];
          layer.padding = randomChoice(['valid', 'same']);
        }
        else if (['recurrent', 'lstm', 'gru'].includes(layerType)) {
          layer.hiddenSize = randomInt(
            this.searchSpace.units.min,
            this.searchSpace.units.max
          );
          layer.returnSequences = i < layerCount - 1 ? 
            randomChoice([true, false]) : false;
        }
        
        layers.push(layer);
      }
      
      // Generate architecture
      return {
        layers,
        optimizer: {
          type: optimizer,
          learningRate
        },
        coherence: {
          enabled: true,
          minThreshold: this.coherenceConfig.minCoherence
        },
        metadata: {
          generated: true,
          timestamp: new Date().toISOString()
        }
      };
    }

    /**
     * Evaluate architecture with comprehensive coherence guidance
     * @private
     * @param {Object} architecture - Architecture to evaluate
     * @returns {Promise<Object>} Evaluation results
     */
    async _evaluateArchitecture(architecture) {
      // Create the model
      const model = new NeuralModel(architecture);
      
      try {
        // Analyze the architecture for coherence-friendliness before evaluation
        const coherenceEstimate = this._estimateArchitectureCoherence(architecture);
        
        // If architecture is likely to be incoherent, adjust it before evaluation
        if (coherenceEstimate < this.coherenceConfig.minCoherence) {
          architecture = this._enhanceArchitectureCoherence(architecture, coherenceEstimate);
          
          // Recreate model with enhanced architecture
          model = new NeuralModel(architecture);
        }
        
        // Run user's evaluation function
        const evaluationResult = await this.evaluationFunction(model);
        
        if (!Prime.Utils.isObject(evaluationResult)) {
          throw new Prime.ValidationError(
            "Evaluation function must return an object with metrics"
          );
        }
        
        // Get model coherence scores from all layers and overall model
        const layerCoherenceScores = model.metrics.layerCoherenceScores || [];
        const coherenceScore = model.metrics.coherenceScore || 1.0;
        
        // Get additional coherence metrics
        const coherenceViolations = model.coherenceViolations || [];
        const stableTraining = evaluationResult.epochs > 1 && !coherenceViolations.length;
        
        // Calculate stability factor based on layer coherence variance
        let stabilityFactor = 1.0;
        if (layerCoherenceScores.length > 1) {
          const meanCoherence = layerCoherenceScores.reduce((a, b) => a + b, 0) / layerCoherenceScores.length;
          const varianceSum = layerCoherenceScores.reduce((sum, score) => sum + Math.pow(score - meanCoherence, 2), 0);
          const variance = varianceSum / layerCoherenceScores.length;
          
          // Lower variance is better (more consistent coherence across layers)
          stabilityFactor = Math.exp(-variance * 5);
        }
        
        // Calculate combined score with multi-factor coherence weighting
        let score = evaluationResult.primaryMetric || 0;
        
        if (this.coherenceConfig.enforceCoherence && coherenceScore < this.coherenceConfig.minCoherence) {
          // Significantly penalize incoherent models (non-linear penalty increases as coherence drops)
          const coherenceRatio = coherenceScore / this.coherenceConfig.minCoherence;
          score *= Math.pow(coherenceRatio, 2); // Quadratic penalty
        } else {
          // Apply coherence weighting to score with multiple factors
          const baseMetricWeight = 1 - this.coherenceConfig.coherenceWeight;
          const coherenceWeight = this.coherenceConfig.coherenceWeight;
          
          // Weighted score combines:
          // 1. Raw performance metric
          // 2. Overall coherence score
          // 3. Stability factor (layer coherence consistency)
          // 4. Training stability bonus
          score = (baseMetricWeight * score) + 
                 (coherenceWeight * 0.6 * coherenceScore) +
                 (coherenceWeight * 0.3 * stabilityFactor) +
                 (coherenceWeight * 0.1 * (stableTraining ? 1.0 : 0.5));
        }
        
        return {
          architecture,
          model,
          rawMetrics: evaluationResult,
          coherenceScore,
          layerCoherenceScores,
          stabilityFactor,
          violations: coherenceViolations.length,
          score
        };
      } catch (error) {
        // Handle evaluation failures
        return {
          architecture,
          error: error.message,
          coherenceScore: 0,
          score: -Infinity
        };
      }
    }
    
    /**
     * Estimate architecture coherence before training
     * @private
     * @param {Object} architecture - Architecture to analyze
     * @returns {number} Estimated coherence score (0-1)
     */
    _estimateArchitectureCoherence(architecture) {
      // Static heuristics to estimate if an architecture will be coherent
      let score = 1.0;
      const layers = architecture.layers || [];
      
      if (layers.length === 0) return 0;
      
      // Check for extreme layer size ratios (detect bottlenecks or explosions)
      for (let i = 1; i < layers.length; i++) {
        const prevSize = this._getLayerSize(layers[i-1]);
        const currSize = this._getLayerSize(layers[i]);
        
        if (prevSize && currSize) {
          const ratio = Math.max(prevSize / currSize, currSize / prevSize);
          
          // Penalize extreme ratios
          if (ratio > 10) {
            score *= 0.8;
          } else if (ratio > 5) {
            score *= 0.9;
          }
        }
      }
      
      // Check for overly deep networks with similar layer sizes
      if (layers.length > 5) {
        const similarLayers = layers.filter((layer, i) => 
          i > 0 && 
          this._getLayerSize(layer) === this._getLayerSize(layers[i-1])
        ).length;
        
        if (similarLayers > 3) {
          score *= 0.9; // Potential for vanishing gradients
        }
      }
      
      // Check for appropriate activation functions
      for (let i = 0; i < layers.length; i++) {
        const isOutputLayer = i === layers.length - 1;
        const activation = layers[i].activation;
        
        // Check for inappropriate activation use
        if (!isOutputLayer && activation === 'sigmoid') {
          score *= 0.9; // Sigmoid in hidden layers can cause vanishing gradients
        }
        
        // Check for activation/layer type mismatches
        if (layers[i].type === 'convolutional' && activation === 'tanh') {
          score *= 0.95; // tanh not ideal for conv layers
        }
      }
      
      // Check optimizer configuration
      const optimizer = architecture.optimizer || {};
      if (optimizer.learningRate) {
        if (optimizer.learningRate > 0.1) {
          score *= 0.9; // Too high learning rate
        } else if (optimizer.learningRate < 0.0001) {
          score *= 0.95; // Too low learning rate
        }
      }
      
      return score;
    }
    
    /**
     * Enhance architecture for better coherence
     * @private
     * @param {Object} architecture - Original architecture
     * @param {number} estimatedCoherence - Estimated coherence score
     * @returns {Object} Enhanced architecture
     */
    _enhanceArchitectureCoherence(architecture, estimatedCoherence) {
      // Clone the architecture
      const enhanced = Prime.Utils.deepClone(architecture);
      const layers = enhanced.layers || [];
      
      // Apply coherence-enhancing modifications
      
      // 1. Adjust layer sizes to avoid extreme ratios
      for (let i = 1; i < layers.length; i++) {
        const prevSize = this._getLayerSize(layers[i-1]);
        const currSize = this._getLayerSize(layers[i]);
        
        if (prevSize && currSize) {
          const ratio = Math.max(prevSize / currSize, currSize / prevSize);
          
          if (ratio > 8) {
            // Add intermediate layer to create smoother transition
            if (prevSize > currSize) {
              // Shrinking too quickly - add intermediate layer
              const intermediateSize = Math.round(Math.sqrt(prevSize * currSize));
              
              layers.splice(i, 0, {
                type: 'dense',
                outputSize: intermediateSize,
                activation: 'relu'
              });
              
              // Skip the newly added layer in next iteration
              i++;
            }
          }
        }
      }
      
      // 2. Optimize activation functions
      for (let i = 0; i < layers.length; i++) {
        const isOutputLayer = i === layers.length - 1;
        
        // Replace sigmoid in hidden layers with ReLU or tanh
        if (!isOutputLayer && layers[i].activation === 'sigmoid') {
          layers[i].activation = 'relu';
        }
        
        // Fix conv layer activations
        if (layers[i].type === 'convolutional') {
          layers[i].activation = 'relu'; // Best practice for conv layers
        }
      }
      
      // 3. Adjust learning rate if needed
      if (enhanced.optimizer) {
        if (enhanced.optimizer.learningRate > 0.1) {
          enhanced.optimizer.learningRate = 0.1;
        } else if (enhanced.optimizer.learningRate < 0.0001) {
          enhanced.optimizer.learningRate = 0.0001;
        }
      }
      
      // 4. Ensure coherence configuration is set
      enhanced.coherence = enhanced.coherence || {};
      enhanced.coherence.enabled = true;
      enhanced.coherence.minThreshold = this.coherenceConfig.minCoherence;
      
      return enhanced;
    }
    
    /**
     * Get layer output size (helper method)
     * @private
     * @param {Object} layer - Layer configuration
     * @returns {number|null} Layer size or null if not determinable
     */
    _getLayerSize(layer) {
      if (layer.outputSize) {
        return layer.outputSize;
      } else if (layer.filters) {
        return layer.filters;
      } else if (layer.hiddenSize) {
        return layer.hiddenSize;
      }
      return null;
    }

    /**
     * Run the neural architecture search
     * @param {Object} [options={}] - Search options
     * @param {Function} [options.progressCallback] - Callback for progress updates
     * @returns {Promise<Object>} Search results
     */
    async search(options = {}) {
      const progressCallback = options.progressCallback || function() {};
      
      // Notify start
      progressCallback({
        status: 'started',
        progress: 0,
        trials: 0,
        maxTrials: this.maxTrials
      });
      
      // Run trials
      for (let i = 0; i < this.maxTrials; i++) {
        // Generate random architecture
        const architecture = this._generateRandomArchitecture();
        
        // Evaluate architecture
        const result = await this._evaluateArchitecture(architecture);
        
        // Store trial result
        this.trials.push(result);
        
        // Update best architecture if better
        if (result.score > this.bestScore) {
          this.bestArchitecture = architecture;
          this.bestScore = result.score;
          this.bestModel = result.model;
          this.bestMetrics = result.rawMetrics;
        }
        
        // Notify progress
        progressCallback({
          status: 'running',
          progress: (i + 1) / this.maxTrials,
          trials: i + 1,
          maxTrials: this.maxTrials,
          currentScore: result.score,
          bestScore: this.bestScore
        });
      }
      
      // Notify completion
      progressCallback({
        status: 'completed',
        progress: 1,
        trials: this.maxTrials,
        maxTrials: this.maxTrials,
        bestScore: this.bestScore
      });
      
      // Return results
      return {
        bestArchitecture: this.bestArchitecture,
        bestModel: this.bestModel,
        bestScore: this.bestScore,
        bestMetrics: this.bestMetrics,
        trials: this.trials
      };
    }
  }

  // Add models to Prime.Neural namespace
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Model = {
    NeuralModel,
    NeuralArchitectureSearch
  };
})();

// Export the enhanced Prime object
module.exports = Prime;