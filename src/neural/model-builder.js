/**
 * PrimeOS JavaScript Library - Neural Network Model Builder
 * Fluent API for constructing neural network models with ease
 */

// Import the Prime object from core
const Prime = require("../core");

// Create the Neural Model Builder module using IIFE
(function () {
  /**
   * Neural Network Model Builder
   * Provides a fluent API for constructing neural network models
   */
  class ModelBuilder {
    /**
     * Create a new model builder
     * @param {Object} [config={}] - Global model configuration
     * @param {boolean} [config.useTypedArrays=true] - Whether to use TypedArrays for memory efficiency
     * @param {Object} [config.coherence={}] - Coherence monitoring configuration
     * @param {Object} [config.metadata={}] - Model metadata
     */
    constructor(config = {}) {
      this.config = {
        useTypedArrays: config.useTypedArrays !== false,
        coherence: config.coherence || {
          enabled: true,
          minThreshold: 0.7,
          checkFrequency: 10,
          autoCorrect: true,
        },
        metadata: config.metadata || {},
      };

      this.layers = [];
      this.optimizer = null;
      this.loss = null;
      this.metric = null;
      this.initialInputSize = null;
    }

    /**
     * Set the input size for the first layer
     * @param {number} size - Input size
     * @returns {ModelBuilder} This builder instance for chaining
     */
    input(size) {
      this.initialInputSize = size;
      return this;
    }

    /**
     * Add a dense (fully connected) layer
     * @param {Object} config - Layer configuration
     * @param {number} config.units - Number of neurons in the layer
     * @param {string} [config.activation='sigmoid'] - Activation function
     * @param {Object} [config.initParams={}] - Weight initialization parameters
     * @returns {ModelBuilder} This builder instance for chaining
     */
    dense(config) {
      // Validate configuration
      if (!config || typeof config.units !== "number") {
        throw new Error("Dense layer requires units parameter");
      }

      // Get input size
      const inputSize = this._getInputSize();

      // Create layer configuration
      const layerConfig = {
        type: "dense",
        inputSize: inputSize,
        outputSize: config.units,
        activation: config.activation || "sigmoid",
        initParams: config.initParams || {},
        useTypedArrays: this.config.useTypedArrays,
      };

      // Add to layers
      this.layers.push(layerConfig);

      return this;
    }

    /**
     * Add a convolutional layer
     * @param {Object} config - Layer configuration
     * @param {number} config.filters - Number of filters
     * @param {number|Array<number>} config.kernelSize - Size of the convolution kernel
     * @param {number|Array<number>} [config.strides=[1,1]] - Strides of the convolution
     * @param {string} [config.padding='valid'] - Padding type
     * @param {string} [config.activation='relu'] - Activation function
     * @returns {ModelBuilder} This builder instance for chaining
     */
    convolutional(config) {
      // Validate configuration
      if (!config || typeof config.filters !== "number" || !config.kernelSize) {
        throw new Error(
          "Convolutional layer requires filters and kernelSize parameters",
        );
      }

      // Get input size/shape
      const inputSize = this._getInputSize();

      // Create layer configuration
      const layerConfig = {
        type: "convolutional",
        inputSize: inputSize,
        filters: config.filters,
        kernelSize: config.kernelSize,
        strides: config.strides || [1, 1],
        padding: config.padding || "valid",
        activation: config.activation || "relu",
        useTypedArrays: this.config.useTypedArrays,
      };

      // Add to layers
      this.layers.push(layerConfig);

      return this;
    }

    /**
     * Add a recurrent layer
     * @param {Object} config - Layer configuration
     * @param {number} config.units - Number of units in the layer
     * @param {string} [config.cellType='lstm'] - Type of recurrent cell ('lstm', 'gru', 'simple')
     * @param {boolean} [config.returnSequences=false] - Whether to return the full sequence
     * @param {string} [config.activation='tanh'] - Activation function
     * @returns {ModelBuilder} This builder instance for chaining
     */
    recurrent(config) {
      // Validate configuration
      if (!config || typeof config.units !== "number") {
        throw new Error("Recurrent layer requires units parameter");
      }

      // Get input size
      const inputSize = this._getInputSize();

      // Create layer configuration
      const layerConfig = {
        type: "recurrent",
        inputSize: inputSize,
        outputSize: config.units,
        cellType: config.cellType || "lstm",
        returnSequences: config.returnSequences || false,
        activation: config.activation || "tanh",
        useTypedArrays: this.config.useTypedArrays,
      };

      // Add to layers
      this.layers.push(layerConfig);

      return this;
    }

    /**
     * Add a self-optimizing layer
     * @param {Object} config - Layer configuration
     * @param {number} config.units - Number of neurons in the layer
     * @param {string} [config.activation='sigmoid'] - Activation function
     * @param {Object} [config.optimization={}] - Optimization parameters
     * @returns {ModelBuilder} This builder instance for chaining
     */
    selfOptimizing(config) {
      // Validate configuration
      if (!config || typeof config.units !== "number") {
        throw new Error("Self-optimizing layer requires units parameter");
      }

      // Get input size
      const inputSize = this._getInputSize();

      // Create layer configuration
      const layerConfig = {
        type: "selfOptimizing",
        inputSize: inputSize,
        outputSize: config.units,
        activation: config.activation || "sigmoid",
        optimization: config.optimization || {
          enabled: true,
          adaptThreshold: 100,
          coherenceThreshold: 0.8,
          adaptationRate: 0.01,
        },
        useTypedArrays: this.config.useTypedArrays,
      };

      // Add to layers
      this.layers.push(layerConfig);

      return this;
    }

    /**
     * Add a dropout layer
     * @param {Object} config - Layer configuration
     * @param {number} config.rate - Dropout rate (0-1)
     * @returns {ModelBuilder} This builder instance for chaining
     */
    dropout(config) {
      // Validate configuration
      if (
        !config ||
        typeof config.rate !== "number" ||
        config.rate < 0 ||
        config.rate >= 1
      ) {
        throw new Error(
          "Dropout layer requires rate parameter between 0 and 1",
        );
      }

      // Get input size
      const inputSize = this._getInputSize();

      // Create layer configuration
      const layerConfig = {
        type: "dropout",
        inputSize: inputSize,
        outputSize: inputSize, // Dropout doesn't change dimensions
        rate: config.rate,
        useTypedArrays: this.config.useTypedArrays,
      };

      // Add to layers
      this.layers.push(layerConfig);

      return this;
    }

    /**
     * Set optimizer for the model
     * @param {string|Object} optimizer - Optimizer type or configuration
     * @param {Object} [config={}] - Optimizer configuration if type is a string
     * @returns {ModelBuilder} This builder instance for chaining
     */
    withOptimizer(optimizer, config = {}) {
      if (typeof optimizer === "string") {
        this.optimizer = {
          type: optimizer,
          ...config,
        };
      } else if (typeof optimizer === "object") {
        this.optimizer = optimizer;
      } else {
        throw new Error("Invalid optimizer configuration");
      }

      return this;
    }

    /**
     * Set loss function for the model
     * @param {string} loss - Loss function name
     * @returns {ModelBuilder} This builder instance for chaining
     */
    withLoss(loss) {
      this.loss = loss;
      return this;
    }

    /**
     * Set evaluation metric for the model
     * @param {string} metric - Metric name
     * @returns {ModelBuilder} This builder instance for chaining
     */
    withMetric(metric) {
      this.metric = metric;
      return this;
    }

    /**
     * Set coherence configuration for the model
     * @param {Object} config - Coherence configuration
     * @returns {ModelBuilder} This builder instance for chaining
     */
    withCoherence(config) {
      this.config.coherence = {
        ...this.config.coherence,
        ...config,
      };

      return this;
    }

    /**
     * Add custom metadata to the model
     * @param {Object} metadata - Metadata key-value pairs
     * @returns {ModelBuilder} This builder instance for chaining
     */
    withMetadata(metadata) {
      this.config.metadata = {
        ...this.config.metadata,
        ...metadata,
      };

      return this;
    }

    /**
     * Build and return the neural network model
     * @returns {Prime.Neural.Model.NeuralModel} Constructed model
     */
    build() {
      // Validate that we have layers
      if (this.layers.length === 0) {
        throw new Error("Cannot build model with no layers");
      }

      // Create model with configuration
      const model = new Prime.Neural.Model.NeuralModel({
        useTypedArrays: this.config.useTypedArrays,
        coherence: this.config.coherence,
        metadata: this.config.metadata,
      });

      // Add layers to model
      this.layers.forEach((layerConfig) => {
        model.addLayer(layerConfig);
      });

      // Set optimizer if configured
      if (this.optimizer) {
        model.setOptimizer(this.optimizer);
      }

      // Compile model if loss is set
      if (this.loss) {
        model.compile({
          loss: this.loss,
          metric: this.metric,
        });
      }

      return model;
    }

    /**
     * Get the current input size for the next layer
     * @private
     * @returns {number} Input size
     */
    _getInputSize() {
      if (this.layers.length === 0) {
        if (this.initialInputSize === null) {
          throw new Error("Input size must be specified");
        }
        return this.initialInputSize;
      }

      // Get output size of last layer
      const lastLayer = this.layers[this.layers.length - 1];
      return lastLayer.outputSize;
    }

    /**
     * Create a sequential model with simplified configuration
     * @static
     * @param {Array} layers - Array of layer configurations
     * @param {Object} [config={}] - Model configuration
     * @returns {Prime.Neural.Model.NeuralModel} Constructed model
     */
    static sequential(layers, config = {}) {
      // Validate layers
      if (!Array.isArray(layers) || layers.length === 0) {
        throw new Error("Sequential model requires an array of layers");
      }

      const builder = new ModelBuilder(config);

      // Set input size from first layer if provided
      if (layers[0].inputSize) {
        builder.input(layers[0].inputSize);
      }

      // Add layers based on type
      layers.forEach((layer) => {
        switch (layer.type.toLowerCase()) {
          case "dense":
            builder.dense({
              units: layer.units,
              activation: layer.activation,
            });
            break;
          case "conv":
          case "convolutional":
            builder.convolutional({
              filters: layer.filters,
              kernelSize: layer.kernelSize,
              strides: layer.strides,
              padding: layer.padding,
              activation: layer.activation,
            });
            break;
          case "recurrent":
          case "lstm":
          case "gru":
            builder.recurrent({
              units: layer.units,
              cellType: layer.cellType || layer.type.toLowerCase(),
              returnSequences: layer.returnSequences,
              activation: layer.activation,
            });
            break;
          case "dropout":
            builder.dropout({
              rate: layer.rate,
            });
            break;
          case "self_optimizing":
          case "selfoptimizing":
            builder.selfOptimizing({
              units: layer.units,
              activation: layer.activation,
              optimization: layer.optimization,
            });
            break;
          default:
            throw new Error(`Unknown layer type: ${layer.type}`);
        }
      });

      // Set optimizer, loss, and metric if provided
      if (config.optimizer) {
        builder.withOptimizer(config.optimizer);
      }

      if (config.loss) {
        builder.withLoss(config.loss);
      }

      if (config.metric) {
        builder.withMetric(config.metric);
      }

      // Build and return model
      return builder.build();
    }

    /**
     * Create a model from a predefined architecture
     * @static
     * @param {string} architecture - Predefined architecture name
     * @param {Object} [config={}] - Model configuration
     * @returns {Prime.Neural.Model.NeuralModel} Constructed model
     */
    static fromArchitecture(architecture, config = {}) {
      const lowerArch = architecture.toLowerCase();

      switch (lowerArch) {
        case "mlp":
        case "perceptron":
          // Simple MLP with 2 hidden layers
          return ModelBuilder.sequential(
            [
              {
                type: "dense",
                inputSize: config.inputSize || 10,
                units: 64,
                activation: "relu",
              },
              { type: "dense", units: 32, activation: "relu" },
              {
                type: "dense",
                units: config.outputSize || 1,
                activation: config.outputActivation || "sigmoid",
              },
            ],
            {
              optimizer: { type: "adam", learningRate: 0.001 },
              loss: config.loss || "mse",
              metric: config.metric || "accuracy",
              ...config,
            },
          );

        case "cnn":
          // Simple CNN for image processing
          return ModelBuilder.sequential(
            [
              {
                type: "convolutional",
                inputSize: config.inputSize || 784,
                filters: 32,
                kernelSize: 3,
                activation: "relu",
              },
              {
                type: "convolutional",
                filters: 64,
                kernelSize: 3,
                activation: "relu",
              },
              { type: "dense", units: 128, activation: "relu" },
              { type: "dropout", rate: 0.2 },
              {
                type: "dense",
                units: config.outputSize || 10,
                activation: "softmax",
              },
            ],
            {
              optimizer: { type: "adam", learningRate: 0.001 },
              loss: config.loss || "categoricalCrossEntropy",
              metric: config.metric || "accuracy",
              ...config,
            },
          );

        case "rnn":
        case "lstm":
          // Simple RNN for sequence processing
          return ModelBuilder.sequential(
            [
              {
                type: "recurrent",
                inputSize: config.inputSize || 20,
                units: 64,
                cellType: "lstm",
                returnSequences: false,
                activation: "tanh",
              },
              { type: "dense", units: 32, activation: "relu" },
              {
                type: "dense",
                units: config.outputSize || 1,
                activation: config.outputActivation || "sigmoid",
              },
            ],
            {
              optimizer: { type: "adam", learningRate: 0.001 },
              loss: config.loss || "mse",
              metric: config.metric || "accuracy",
              ...config,
            },
          );

        case "autoencoder": {
          // Simple autoencoder
          const encoderSize = config.encoderSize || 32;
          const inputSize = config.inputSize || 784;

          return ModelBuilder.sequential(
            [
              // Encoder
              {
                type: "dense",
                inputSize: inputSize,
                units: 128,
                activation: "relu",
              },
              { type: "dense", units: encoderSize, activation: "relu" },
              // Decoder
              { type: "dense", units: 128, activation: "relu" },
              { type: "dense", units: inputSize, activation: "sigmoid" },
            ],
            {
              optimizer: { type: "adam", learningRate: 0.001 },
              loss: config.loss || "mse",
              ...config,
            },
          );
        }

        case "self_optimizing":
        case "selfoptimizing": {
          // Network with self-optimizing layers
          return ModelBuilder.sequential(
            [
              {
                type: "dense",
                inputSize: config.inputSize || 10,
                units: 32,
                activation: "relu",
              },
              { type: "selfOptimizing", units: 32, activation: "relu" },
              {
                type: "dense",
                units: config.outputSize || 1,
                activation: config.outputActivation || "sigmoid",
              },
            ],
            {
              optimizer: { type: "adam", learningRate: 0.001 },
              loss: config.loss || "mse",
              metric: config.metric || "accuracy",
              coherence: {
                enabled: true,
                minThreshold: 0.7,
                autoCorrect: true,
              },
              ...config,
            },
          );
        }

        default:
          throw new Error(`Unknown architecture: ${architecture}`);
      }
    }
  }

  // Add to Prime.Neural namespace
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Model = Prime.Neural.Model || {};
  Prime.Neural.Model.ModelBuilder = ModelBuilder;
})();

// Export the enhanced Prime object
module.exports = Prime;
