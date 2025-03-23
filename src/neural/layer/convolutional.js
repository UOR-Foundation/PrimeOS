/**
 * PrimeOS JavaScript Library - Convolutional Neural Layer Module
 * Advanced convolutional layer implementation with coherence integration
 */

// Import the Prime object from core
const Prime = require("../../core");

// Create the Convolutional Layer module using IIFE
(function () {
  /**
   * Convolutional Neural Layer class
   * Implements 2D convolutional operations with full coherence integration
   */
  class ConvolutionalLayer {
    /**
     * Create a new convolutional layer
     * @param {Object} config - Layer configuration
     * @param {number[]} config.inputShape - Input shape [height, width, channels]
     * @param {number} config.filters - Number of filters (output channels)
     * @param {number[]} config.kernelSize - Kernel size [height, width]
     * @param {number[]} [config.strides=[1,1]] - Strides [y, x]
     * @param {string} [config.padding='valid'] - Padding type ('valid' or 'same')
     * @param {string} [config.activation='relu'] - Activation function
     * @param {Object} [config.initParams={}] - Weight initialization parameters
     */
    constructor(config) {
      if (!Prime.Utils.isObject(config)) {
        throw new Prime.ValidationError(
          "Layer configuration must be an object",
        );
      }

      if (!Array.isArray(config.inputShape) || config.inputShape.length !== 3) {
        throw new Prime.ValidationError(
          "Input shape must be an array [height, width, channels]",
        );
      }

      if (!Array.isArray(config.kernelSize) || config.kernelSize.length !== 2) {
        throw new Prime.ValidationError(
          "Kernel size must be an array [height, width]",
        );
      }

      this.inputShape = [...config.inputShape]; // [height, width, channels]
      this.kernelSize = [...config.kernelSize]; // [height, width]
      this.filters = config.filters;
      this.strides = config.strides || [1, 1];
      this.padding = config.padding || "valid";
      this.activation = config.activation || "relu";

      // Calculate output shape
      this.outputShape = this._calculateOutputShape();

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
        memoryUsage: 0,
        computeEfficiency: 1.0,
      };

      // Usage pattern tracking
      this.usagePatterns = {
        activationDistribution: new Array(this.filters).fill(0),
        kernelUtilization: null, // Will be initialized in _updateKernelUtilization
        spatialSensitivity: null, // Will be initialized separately
        sampleCount: 0,
      };

      // Initialize spatialSensitivity properly
      this.usagePatterns.spatialSensitivity =
        this._createSpatialSensitivityArray();

      // Initialize kernelUtilization properly
      this._initializeKernelUtilization();

      // Initialize tensor operations manager
      this.tensorOps = this._createTensorOperations();
    }

    /**
     * Create a tensor with specified shape initialized to zero
     * @private
     * @param {number[]} shape - Shape dimensions
     * @returns {Array} Multi-dimensional array
     */
    _createTensor(shape) {
      if (shape.length === 0) return 0;

      const dimension = shape[0];
      const restShape = shape.slice(1);

      const result = new Array(dimension);

      if (restShape.length === 0) {
        for (let i = 0; i < dimension; i++) {
          result[i] = 0;
        }
      } else {
        for (let i = 0; i < dimension; i++) {
          result[i] = this._createTensor(restShape);
        }
      }

      return result;
    }

    /**
     * Initialize kernel utilization array
     * @private
     */
    _initializeKernelUtilization() {
      // Create a properly initialized array for kernel utilization
      const kernelUtilization = new Array(this.filters);

      for (let f = 0; f < this.filters; f++) {
        kernelUtilization[f] = new Array(this.kernelSize[0]);

        for (let ky = 0; ky < this.kernelSize[0]; ky++) {
          kernelUtilization[f][ky] = new Array(this.kernelSize[1]);

          for (let kx = 0; kx < this.kernelSize[1]; kx++) {
            kernelUtilization[f][ky][kx] = new Array(this.inputShape[2]).fill(
              0,
            );
          }
        }
      }

      this.usagePatterns.kernelUtilization = kernelUtilization;
    }

    /**
     * Create a properly initialized spatial sensitivity array
     * @private
     * @returns {Array} Initialized spatial sensitivity array
     */
    _createSpatialSensitivityArray() {
      const [outputHeight, outputWidth] = [
        this.outputShape[0],
        this.outputShape[1],
      ];
      const spatialSensitivity = new Array(outputHeight);

      for (let y = 0; y < outputHeight; y++) {
        spatialSensitivity[y] = new Array(outputWidth).fill(0);
      }

      return spatialSensitivity;
    }

    /**
     * Calculate the output shape of the convolution
     * @private
     * @returns {number[]} Output shape [height, width, channels]
     */
    _calculateOutputShape() {
      const [inputHeight, inputWidth, inputChannels] = this.inputShape;
      const [kernelHeight, kernelWidth] = this.kernelSize;
      const [strideY, strideX] = this.strides;

      let outputHeight, outputWidth;

      if (this.padding === "same") {
        outputHeight = Math.ceil(inputHeight / strideY);
        outputWidth = Math.ceil(inputWidth / strideX);
      } else {
        // Valid padding - no padding added
        outputHeight = Math.floor((inputHeight - kernelHeight) / strideY + 1);
        outputWidth = Math.floor((inputWidth - kernelWidth) / strideX + 1);
      }

      return [outputHeight, outputWidth, this.filters];
    }

    /**
     * Create tensor operations manager with coherence validation
     * @private
     * @returns {Object} Tensor operations interface
     */
    _createTensorOperations() {
      // Use the framework math module if available
      if (Prime.Mathematics && Prime.Mathematics.Tensor) {
        return Prime.Mathematics.Tensor;
      }

      // Create our own tensor operations with coherence checks
      return {
        /**
         * Perform 2D convolution operation with coherence validation
         * @param {Array} input - Input tensor [height, width, channels]
         * @param {Array} kernels - Kernel tensor [filters, height, width, channels]
         * @param {Array} biases - Bias array
         * @param {Object} options - Convolution options
         * @returns {Array} Output tensor [height, width, filters]
         */
        convolve2d: (input, kernels, biases, options) => {
          const { strides, padding } = options;
          const [strideY, strideX] = strides;
          const [inputHeight, inputWidth, inputChannels] = [
            input.length,
            input[0].length,
            input[0][0].length,
          ];
          const [filterCount, kernelHeight, kernelWidth, kernelChannels] = [
            kernels.length,
            kernels[0].length,
            kernels[0][0].length,
            kernels[0][0][0].length,
          ];

          // Ensure kernel channels match input channels for coherence
          if (kernelChannels !== inputChannels) {
            throw new Prime.CoherenceError(
              `Kernel channels (${kernelChannels}) do not match input channels (${inputChannels})`,
            );
          }

          let outputHeight, outputWidth;
          let paddedInput = input;

          if (padding === "same") {
            const padHeight = (kernelHeight - 1) / 2;
            const padWidth = (kernelWidth - 1) / 2;
            paddedInput = this._padArray(
              input,
              [padHeight, padWidth],
              inputChannels,
            );
            outputHeight = Math.ceil(inputHeight / strideY);
            outputWidth = Math.ceil(inputWidth / strideX);
          } else {
            outputHeight = Math.floor(
              (inputHeight - kernelHeight) / strideY + 1,
            );
            outputWidth = Math.floor((inputWidth - kernelWidth) / strideX + 1);
          }

          // Create output tensor
          const output = this._createTensor([
            outputHeight,
            outputWidth,
            filterCount,
          ]);

          // Perform convolution
          for (let f = 0; f < filterCount; f++) {
            const filter = kernels[f];
            const bias = biases[f];

            for (let y = 0; y < outputHeight; y++) {
              for (let x = 0; x < outputWidth; x++) {
                let sum = bias;

                // Apply filter at each position
                for (let fy = 0; fy < kernelHeight; fy++) {
                  for (let fx = 0; fx < kernelWidth; fx++) {
                    for (let c = 0; c < inputChannels; c++) {
                      const inputY = y * strideY + fy;
                      const inputX = x * strideX + fx;

                      if (
                        inputY >= 0 &&
                        inputY < paddedInput.length &&
                        inputX >= 0 &&
                        inputX < paddedInput[0].length
                      ) {
                        sum +=
                          paddedInput[inputY][inputX][c] * filter[fy][fx][c];
                      }
                    }
                  }
                }

                output[y][x][f] = sum;
              }
            }
          }

          // Validate output for mathematical coherence
          this._validateTensorCoherence(output);

          return output;
        },

        /**
         * Apply chosen activation function to tensor
         * @param {Array} tensor - Input tensor
         * @param {string} activationType - Type of activation function
         * @returns {Array} Activated tensor
         */
        activate: (tensor, activationType) => {
          const activated = this._deepClone(tensor);

          const applyActivation = (value) => {
            switch (activationType) {
              case "relu":
                return Math.max(0, value);
              case "sigmoid":
                return 1 / (1 + Math.exp(-value));
              case "tanh":
                return Math.tanh(value);
              case "linear":
                return value;
              default:
                return Math.max(0, value); // Default to ReLU
            }
          };

          // Apply activation function to each element
          this._traverseTensor(
            activated,
            (value, indices) => applyActivation(value),
            (newValue, indices) =>
              this._setTensorValue(activated, indices, newValue),
          );

          return activated;
        },

        /**
         * Calculate gradient of activation function
         * @param {Array} tensor - Input tensor (pre-activation values)
         * @param {Array} outputGradient - Gradient from next layer
         * @param {string} activationType - Type of activation function
         * @returns {Array} Gradient tensor
         */
        activationGradient: (tensor, outputGradient, activationType) => {
          const gradient = this._deepClone(outputGradient);

          const applyGradient = (value, outputGrad) => {
            let derivValue;
            switch (activationType) {
              case "relu":
                derivValue = value > 0 ? 1 : 0;
                break;
              case "sigmoid":
                const sigValue = 1 / (1 + Math.exp(-value));
                derivValue = sigValue * (1 - sigValue);
                break;
              case "tanh":
                const tanhValue = Math.tanh(value);
                derivValue = 1 - tanhValue * tanhValue;
                break;
              case "linear":
                derivValue = 1;
                break;
              default:
                derivValue = value > 0 ? 1 : 0; // Default to ReLU
            }
            return outputGrad * derivValue;
          };

          // Apply gradient function to each element
          this._traverseTensor(
            gradient,
            (gradValue, indices) => {
              const tensorValue = this._getTensorValue(tensor, indices);
              return applyGradient(tensorValue, gradValue);
            },
            (newValue, indices) =>
              this._setTensorValue(gradient, indices, newValue),
          );

          return gradient;
        },

        /**
         * Calculate transpose convolution for backpropagation
         * @param {Array} outputGradient - Gradient from next layer
         * @param {Array} kernels - Kernel tensor
         * @param {Object} options - Convolution options
         * @returns {Array} Input gradient tensor
         */
        transposeConvolve2d: (outputGradient, kernels, options) => {
          const { strides, inputShape } = options;
          const [strideY, strideX] = strides;
          const [inputHeight, inputWidth, inputChannels] = inputShape;
          const [outputHeight, outputWidth, filterCount] = [
            outputGradient.length,
            outputGradient[0].length,
            outputGradient[0][0].length,
          ];
          const [filterCount2, kernelHeight, kernelWidth, kernelChannels] = [
            kernels.length,
            kernels[0].length,
            kernels[0][0].length,
            kernels[0][0][0].length,
          ];

          // Ensure filter count matches gradient channels for coherence
          if (filterCount !== filterCount2) {
            throw new Prime.CoherenceError(
              `Filter count (${filterCount2}) does not match gradient channels (${filterCount})`,
            );
          }

          // Create input gradient tensor
          const inputGradient = this._createTensor([
            inputHeight,
            inputWidth,
            inputChannels,
          ]);

          // Perform transpose convolution
          for (let f = 0; f < filterCount; f++) {
            const filter = kernels[f];

            for (let y = 0; y < outputHeight; y++) {
              for (let x = 0; x < outputWidth; x++) {
                // Get gradient at this position
                const gradValue = outputGradient[y][x][f];

                // Distribute gradient to input positions
                for (let fy = 0; fy < kernelHeight; fy++) {
                  for (let fx = 0; fx < kernelWidth; fx++) {
                    for (let c = 0; c < inputChannels; c++) {
                      const inputY = y * strideY + fy;
                      const inputX = x * strideX + fx;

                      if (
                        inputY >= 0 &&
                        inputY < inputHeight &&
                        inputX >= 0 &&
                        inputX < inputWidth
                      ) {
                        inputGradient[inputY][inputX][c] +=
                          gradValue * filter[fy][fx][c];
                      }
                    }
                  }
                }
              }
            }
          }

          // Validate gradient for mathematical coherence
          this._validateTensorCoherence(inputGradient);

          return inputGradient;
        },

        /**
         * Calculate kernel gradient for weight updates
         * @param {Array} input - Input tensor
         * @param {Array} outputGradient - Gradient from next layer
         * @param {Object} options - Convolution options
         * @returns {Array} Kernel gradient tensor
         */
        calculateKernelGradient: (input, outputGradient, options) => {
          const { strides, kernelSize, filters } = options;
          const [strideY, strideX] = strides;
          const [kernelHeight, kernelWidth] = kernelSize;
          const [inputHeight, inputWidth, inputChannels] = [
            input.length,
            input[0].length,
            input[0][0].length,
          ];
          const [outputHeight, outputWidth, filterCount] = [
            outputGradient.length,
            outputGradient[0].length,
            outputGradient[0][0].length,
          ];

          // Create kernel gradient tensor
          const kernelGradient = this._createTensor([
            filters,
            kernelHeight,
            kernelWidth,
            inputChannels,
          ]);

          // Calculate gradient for each filter
          for (let f = 0; f < filterCount; f++) {
            for (let y = 0; y < outputHeight; y++) {
              for (let x = 0; x < outputWidth; x++) {
                const gradValue = outputGradient[y][x][f];

                for (let fy = 0; fy < kernelHeight; fy++) {
                  for (let fx = 0; fx < kernelWidth; fx++) {
                    for (let c = 0; c < inputChannels; c++) {
                      const inputY = y * strideY + fy;
                      const inputX = x * strideX + fx;

                      if (
                        inputY >= 0 &&
                        inputY < inputHeight &&
                        inputX >= 0 &&
                        inputX < inputWidth
                      ) {
                        kernelGradient[f][fy][fx][c] +=
                          gradValue * input[inputY][inputX][c];
                      }
                    }
                  }
                }
              }
            }
          }

          return kernelGradient;
        },

        /**
         * Calculate bias gradient
         * @param {Array} outputGradient - Gradient from next layer
         * @returns {Array} Bias gradient array
         */
        calculateBiasGradient: (outputGradient) => {
          const [outputHeight, outputWidth, filterCount] = [
            outputGradient.length,
            outputGradient[0].length,
            outputGradient[0][0].length,
          ];

          // Create bias gradient array
          const biasGradient = new Array(filterCount).fill(0);

          // Sum gradients for each filter
          for (let f = 0; f < filterCount; f++) {
            for (let y = 0; y < outputHeight; y++) {
              for (let x = 0; x < outputWidth; x++) {
                biasGradient[f] += outputGradient[y][x][f];
              }
            }
          }

          return biasGradient;
        },
      };
    }

    /**
     * Initialize weights with appropriate distribution
     * @private
     * @param {Object} params - Initialization parameters
     * @returns {Array} Initialized weights tensor
     */
    _initializeWeights(params) {
      const scale =
        params.scale ||
        Math.sqrt(
          2 / (this.kernelSize[0] * this.kernelSize[1] * this.inputShape[2]),
        );
      const distribution = params.distribution || "he";

      // Create weights tensor [filters, kernel_height, kernel_width, input_channels]
      const weights = this._createTensor([
        this.filters,
        this.kernelSize[0],
        this.kernelSize[1],
        this.inputShape[2],
      ]);

      // Initialize with appropriate distribution
      this._traverseTensor(
        weights,
        () => {
          let value;

          if (distribution === "xavier") {
            // Xavier/Glorot initialization
            value = (Math.random() * 2 - 1) * scale;
          } else if (distribution === "he") {
            // He initialization
            value = Math.random() * scale;
          } else if (distribution === "zeros") {
            value = 0;
          } else {
            // Default to small random values
            value = Math.random() * 0.2 - 0.1;
          }

          return value;
        },
        (newValue, indices) => this._setTensorValue(weights, indices, newValue),
      );

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
      return new Array(this.filters).fill(biasValue);
    }

    /**
     * Pad input tensor for "same" padding
     * @private
     * @param {Array} input - Input tensor
     * @param {number[]} padding - Padding amount [height, width]
     * @param {number} channels - Number of channels
     * @returns {Array} Padded tensor
     */
    _padArray(input, padding, channels) {
      const [padHeight, padWidth] = padding;
      const [inputHeight, inputWidth] = [input.length, input[0].length];

      const paddedHeight = inputHeight + 2 * padHeight;
      const paddedWidth = inputWidth + 2 * padWidth;

      // Create padded tensor
      const padded = this._createTensor([paddedHeight, paddedWidth, channels]);

      // Copy input values to padded tensor
      for (let y = 0; y < inputHeight; y++) {
        for (let x = 0; x < inputWidth; x++) {
          for (let c = 0; c < channels; c++) {
            padded[y + padHeight][x + padWidth][c] = input[y][x][c];
          }
        }
      }

      return padded;
    }

    /**
     * Deep clone a tensor or array
     * @private
     * @param {Array} tensor - Input tensor
     * @returns {Array} Cloned tensor
     */
    _deepClone(tensor) {
      return JSON.parse(JSON.stringify(tensor));
    }

    /**
     * Traverse tensor with callback functions
     * @private
     * @param {Array} tensor - Tensor to traverse
     * @param {Function} getValueFn - Function to get new value
     * @param {Function} setValueFn - Function to set new value
     */
    _traverseTensor(tensor, getValueFn, setValueFn) {
      const traverse = (t, indices = []) => {
        if (!Array.isArray(t)) {
          const newValue = getValueFn(t, indices);
          setValueFn(newValue, indices);
          return;
        }

        for (let i = 0; i < t.length; i++) {
          const newIndices = [...indices, i];
          traverse(t[i], newIndices);
        }
      };

      traverse(tensor);
    }

    /**
     * Get value from tensor at specified indices
     * @private
     * @param {Array} tensor - Input tensor
     * @param {number[]} indices - Indices to access
     * @returns {number} Value at indices
     */
    _getTensorValue(tensor, indices) {
      let value = tensor;
      for (const idx of indices) {
        if (value === undefined) return 0;
        value = value[idx];
      }
      return value === undefined ? 0 : value;
    }

    /**
     * Set value in tensor at specified indices
     * @private
     * @param {Array} tensor - Input tensor
     * @param {number[]} indices - Indices to set
     * @param {number} value - Value to set
     */
    _setTensorValue(tensor, indices, value) {
      let current = tensor;
      for (let i = 0; i < indices.length - 1; i++) {
        if (current[indices[i]] === undefined) {
          current[indices[i]] = [];
        }
        current = current[indices[i]];
      }
      current[indices[indices.length - 1]] = value;
    }

    /**
     * Validate tensor for numerical coherence
     * @private
     * @param {Array} tensor - Tensor to validate
     * @throws {Error} If tensor contains non-finite values
     */
    _validateTensorCoherence(tensor) {
      let valid = true;

      this._traverseTensor(
        tensor,
        (value) => {
          if (!Number.isFinite(value)) {
            valid = false;
          }
          return value;
        },
        () => {},
      );

      if (!valid) {
        throw new Prime.CoherenceError("Tensor contains non-finite values");
      }
    }

    /**
     * Forward pass through the convolutional layer
     * @param {Array} input - Input activation tensor [height, width, channels]
     * @returns {Object} Output with activation and cache for backprop
     */
    forward(input) {
      if (
        !Array.isArray(input) ||
        input.length !== this.inputShape[0] ||
        input[0].length !== this.inputShape[1] ||
        input[0][0].length !== this.inputShape[2]
      ) {
        throw new Prime.ValidationError(
          `Input must be a tensor with shape [${this.inputShape.join(", ")}]`,
        );
      }

      const startTime = performance.now();

      // Update usage pattern tracking
      this._updateInputDistribution(input);

      // Perform convolution
      const z = this.tensorOps.convolve2d(input, this.weights, this.biases, {
        strides: this.strides,
        padding: this.padding,
      });

      // Apply activation function
      const activation = this.tensorOps.activate(z, this.activation);

      // Update activation distribution
      this._updateActivationDistribution(activation);

      // Update performance metrics
      const endTime = performance.now();
      this._updateForwardMetrics(endTime - startTime);

      // Calculate memory usage estimate
      this._updateMemoryUsage(input, z, activation);

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
      if (
        !Array.isArray(dY) ||
        dY.length !== this.outputShape[0] ||
        dY[0].length !== this.outputShape[1] ||
        dY[0][0].length !== this.outputShape[2]
      ) {
        throw new Prime.ValidationError(
          `Output gradient must have shape [${this.outputShape.join(", ")}]`,
        );
      }

      const startTime = performance.now();
      const { input, z } = cache;

      // Compute gradient of activation function
      const dZ = this.tensorOps.activationGradient(z, dY, this.activation);

      // Compute gradients for weights
      const dW = this.tensorOps.calculateKernelGradient(input, dZ, {
        strides: this.strides,
        kernelSize: this.kernelSize,
        filters: this.filters,
      });

      // Compute gradients for biases
      const dB = this.tensorOps.calculateBiasGradient(dZ);

      // Compute gradients for inputs (for backprop to previous layer)
      const dX = this.tensorOps.transposeConvolve2d(dZ, this.weights, {
        strides: this.strides,
        inputShape: this.inputShape,
      });

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
     * Update estimated memory usage
     * @private
     * @param {Array} input - Input tensor
     * @param {Array} z - Pre-activation output
     * @param {Array} activation - Activated output
     */
    _updateMemoryUsage(input, z, activation) {
      // Estimate memory usage based on tensor sizes
      const inputSize =
        this.inputShape[0] * this.inputShape[1] * this.inputShape[2];
      const outputSize =
        this.outputShape[0] * this.outputShape[1] * this.outputShape[2];
      const weightSize =
        this.filters *
        this.kernelSize[0] *
        this.kernelSize[1] *
        this.inputShape[2];

      // Total parameters in floats
      const parameterCount = weightSize + this.filters;

      // Total memory in floats (inputs, outputs, intermediate)
      const memoryUsage = inputSize + 2 * outputSize + parameterCount;

      // Update metrics
      this.metrics.memoryUsage = memoryUsage;

      // Calculate compute efficiency based on utilization
      this.metrics.computeEfficiency = this._calculateComputeEfficiency();
    }

    /**
     * Calculate compute efficiency based on filter utilization
     * @private
     * @returns {number} Efficiency score between 0 and 1
     */
    _calculateComputeEfficiency() {
      // Calculate how evenly the filters are used
      const activationDist = this.usagePatterns.activationDistribution;
      const mean = activationDist.reduce((a, b) => a + b, 0) / this.filters;

      if (mean === 0) return 1.0; // No activations yet

      const variance =
        activationDist.reduce((sum, val) => sum + Math.pow(val - mean, 2), 0) /
        this.filters;

      // Normalize variance to get efficiency (lower variance = higher efficiency)
      const normalizedVariance = variance / (mean * mean);
      return Math.max(0, 1 - Math.min(1, normalizedVariance));
    }

    /**
     * Update input distribution statistics
     * @private
     * @param {Array} input - Input tensor
     */
    _updateInputDistribution(input) {
      this.usagePatterns.sampleCount++;

      // For convolutional layers, track spatial sensitivity
      // (which input regions activate the filters most)
      const [height, width, channels] = this.inputShape;

      // Adaptive sampling strategy: balance between full computation and random sampling
      const fullScanThreshold = 50; // Only do full scans occasionally
      const isFullScan =
        this.usagePatterns.sampleCount % fullScanThreshold === 0;

      if (isFullScan) {
        // Full scan of input volume (expensive but comprehensive)
        for (let y = 0; y < height; y++) {
          for (let x = 0; x < width; x++) {
            let total = 0;
            let maxActivation = 0;

            for (let c = 0; c < channels; c++) {
              const value = Math.abs(input[y][x][c]);
              total += value;
              maxActivation = Math.max(maxActivation, value);
            }

            // Update spatial sensitivity map - decay existing values slightly
            if (
              this.usagePatterns.spatialSensitivity &&
              y < this.usagePatterns.spatialSensitivity.length &&
              this.usagePatterns.spatialSensitivity[y] &&
              x < this.usagePatterns.spatialSensitivity[y].length
            ) {
              // Use both total and max activation with a focus on high activations
              const activationSignal =
                0.8 * maxActivation + 0.2 * (total / channels);
              this.usagePatterns.spatialSensitivity[y][x] =
                0.95 * this.usagePatterns.spatialSensitivity[y][x] +
                0.05 * activationSignal;
            }
          }
        }

        // Also track channel importance
        const channelImportance = new Array(channels).fill(0);
        for (let c = 0; c < channels; c++) {
          let channelSum = 0;
          for (let y = 0; y < height; y++) {
            for (let x = 0; x < width; x++) {
              channelSum += Math.abs(input[y][x][c]);
            }
          }
          channelImportance[c] = channelSum / (height * width);
        }

        // Store in kernelUtilization statistics - update per input channel
        if (!this.usagePatterns.channelImportance) {
          this.usagePatterns.channelImportance = channelImportance;
        } else {
          for (let c = 0; c < channels; c++) {
            this.usagePatterns.channelImportance[c] =
              0.9 * this.usagePatterns.channelImportance[c] +
              0.1 * channelImportance[c];
          }
        }
      } else {
        // Smarter random sampling: include both random points and high gradient areas
        // Calculate gradient magnitude to find important areas
        const gradientMap = this._calculateInputGradientMap(input);
        const topPoints = this._findTopGradientPoints(gradientMap, 5);

        // Combine with random points for exploration
        const randomPoints = 5;
        const allPoints = [...topPoints];

        for (let i = 0; i < randomPoints; i++) {
          allPoints.push({
            y: Math.floor(Math.random() * height),
            x: Math.floor(Math.random() * width),
          });
        }

        // Process all points
        for (const point of allPoints) {
          const { x, y } = point;

          if (y >= 0 && y < height && x >= 0 && x < width) {
            let total = 0;
            for (let c = 0; c < channels; c++) {
              total += Math.abs(input[y][x][c]);
            }

            // Update spatial sensitivity map
            if (
              this.usagePatterns.spatialSensitivity &&
              y < this.usagePatterns.spatialSensitivity.length &&
              this.usagePatterns.spatialSensitivity[y] &&
              x < this.usagePatterns.spatialSensitivity[y].length
            ) {
              this.usagePatterns.spatialSensitivity[y][x] =
                0.99 * this.usagePatterns.spatialSensitivity[y][x] +
                0.01 * total;
            }
          }
        }
      }
    }

    /**
     * Calculate gradient magnitude map for input
     * @private
     * @param {Array} input - Input tensor
     * @returns {Array} Gradient magnitude map [height, width]
     */
    _calculateInputGradientMap(input) {
      const [height, width, channels] = this.inputShape;
      const gradientMap = new Array(height);
      for (let y = 0; y < height; y++) {
        gradientMap[y] = new Array(width).fill(0);
      }

      // Simple Sobel-like edge detection
      for (let y = 1; y < height - 1; y++) {
        for (let x = 1; x < width - 1; x++) {
          let gradientMagnitude = 0;

          for (let c = 0; c < channels; c++) {
            // Horizontal and vertical gradients
            const gx = input[y][x + 1][c] - input[y][x - 1][c];
            const gy = input[y + 1][x][c] - input[y - 1][x][c];

            // Gradient magnitude
            gradientMagnitude += Math.sqrt(gx * gx + gy * gy);
          }

          gradientMap[y][x] = gradientMagnitude / channels;
        }
      }

      return gradientMap;
    }

    /**
     * Find points with highest gradient magnitude
     * @private
     * @param {Array} gradientMap - Gradient magnitude map
     * @param {number} count - Number of points to find
     * @returns {Array} Array of {x, y} coordinates
     */
    _findTopGradientPoints(gradientMap, count) {
      const points = [];
      const height = gradientMap.length;
      const width = gradientMap[0].length;

      // Flatten gradient map into (x,y,value) tuples
      const flatGradients = [];
      for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
          flatGradients.push({
            x,
            y,
            value: gradientMap[y][x],
          });
        }
      }

      // Sort by gradient magnitude (descending)
      flatGradients.sort((a, b) => b.value - a.value);

      // Take top N points
      for (let i = 0; i < Math.min(count, flatGradients.length); i++) {
        points.push({
          x: flatGradients[i].x,
          y: flatGradients[i].y,
        });
      }

      return points;
    }

    /**
     * Update activation distribution statistics
     * @private
     * @param {Array} activation - Output activation tensor
     */
    _updateActivationDistribution(activation) {
      // For each filter, track overall activation level
      for (let f = 0; f < this.filters; f++) {
        let total = 0;
        let count = 0;

        // Sample the activation map
        const [height, width] = [activation.length, activation[0].length];

        for (let y = 0; y < height; y++) {
          for (let x = 0; x < width; x++) {
            total += activation[y][x][f];
            count++;
          }
        }

        const average = count > 0 ? total / count : 0;

        // Update exponential moving average of activation
        this.usagePatterns.activationDistribution[f] =
          0.99 * this.usagePatterns.activationDistribution[f] + 0.01 * average;
      }

      // Also track kernel utilization (which parts of the kernel are most important)
      // This is an expensive operation, so we'll only do it occasionally
      if (this.metrics.forwardCount % 100 === 0) {
        this._updateKernelUtilization();
      }
    }

    /**
     * Update kernel utilization statistics
     * @private
     */
    _updateKernelUtilization() {
      // Ensure kernelUtilization array is properly initialized
      if (
        !this.usagePatterns.kernelUtilization ||
        !Array.isArray(this.usagePatterns.kernelUtilization) ||
        this.usagePatterns.kernelUtilization.length !== this.filters
      ) {
        // Reinitialize the kernelUtilization array with proper dimensions
        this.usagePatterns.kernelUtilization = this._createTensor([
          this.filters,
          this.kernelSize[0],
          this.kernelSize[1],
          this.inputShape[2],
        ]).map(() => 0);
      }

      // Calculate importance of each kernel weight based on magnitude
      for (let f = 0; f < this.filters; f++) {
        if (!this.usagePatterns.kernelUtilization[f]) continue;

        for (let ky = 0; ky < this.kernelSize[0]; ky++) {
          if (!this.usagePatterns.kernelUtilization[f][ky]) continue;

          for (let kx = 0; kx < this.kernelSize[1]; kx++) {
            if (!this.usagePatterns.kernelUtilization[f][ky][kx]) continue;

            for (let c = 0; c < this.inputShape[2]; c++) {
              if (
                this.usagePatterns.kernelUtilization[f][ky][kx][c] === undefined
              ) {
                this.usagePatterns.kernelUtilization[f][ky][kx][c] = 0;
              }

              const weight = Math.abs(this.weights[f][ky][kx][c]);

              // Update exponential moving average of weight importance
              this.usagePatterns.kernelUtilization[f][ky][kx][c] =
                0.99 * this.usagePatterns.kernelUtilization[f][ky][kx][c] +
                0.01 * weight;
            }
          }
        }
      }
    }

    /**
     * Update layer parameters with given gradients
     * @param {Object} gradients - Weight and bias gradients
     * @param {number} learningRate - Learning rate for update
     */
    update(gradients, learningRate) {
      const { dW, dB } = gradients;

      // Update weights
      for (let f = 0; f < this.filters; f++) {
        for (let ky = 0; ky < this.kernelSize[0]; ky++) {
          for (let kx = 0; kx < this.kernelSize[1]; kx++) {
            for (let c = 0; c < this.inputShape[2]; c++) {
              this.weights[f][ky][kx][c] -= learningRate * dW[f][ky][kx][c];
            }
          }
        }
      }

      // Update biases
      for (let f = 0; f < this.filters; f++) {
        this.biases[f] -= learningRate * dB[f];
      }
    }

    /**
     * Get layer performance metrics
     * @returns {Object} Current performance metrics
     */
    getMetrics() {
      // Calculate coherence metric based on filter utilization
      const activationBalance = this._calculateCoherenceScore();
      this.metrics.coherence = activationBalance;

      return { ...this.metrics };
    }

    /**
     * Calculate coherence score of the layer
     * @private
     * @returns {number} Coherence score between 0 and 1
     */
    _calculateCoherenceScore() {
      // Component 1: Activation distribution uniformity (0-1)
      // Higher is better - we want balanced filter activations
      const activationDistribution = this.usagePatterns.activationDistribution;
      const meanActivation =
        activationDistribution.reduce((a, b) => a + b, 0) / this.filters;

      if (meanActivation === 0) return 1.0; // No activations yet

      const activationVariance =
        activationDistribution.reduce(
          (sum, act) => sum + Math.pow(act - meanActivation, 2),
          0,
        ) / this.filters;

      const maxVariance = Math.pow(meanActivation, 2); // Theoretical max variance
      const activationBalance = Math.max(
        0,
        1 - Math.sqrt(activationVariance / (maxVariance + 1e-10)),
      );

      // Component 2: Spatial sensitivity distribution (0-1)
      // This measures how evenly the layer responds to different input regions
      let spatialVariance = 0;
      let spatialMean = 0;
      let spatialCount = 0;

      // Ensure spatialSensitivity is properly initialized
      if (
        !this.usagePatterns.spatialSensitivity ||
        !Array.isArray(this.usagePatterns.spatialSensitivity)
      ) {
        this.usagePatterns.spatialSensitivity =
          this._createSpatialSensitivityArray();
      }

      if (
        this.usagePatterns.spatialSensitivity &&
        this.usagePatterns.spatialSensitivity.length > 0 &&
        this.usagePatterns.spatialSensitivity[0].length > 0
      ) {
        for (let y = 0; y < this.usagePatterns.spatialSensitivity.length; y++) {
          if (!this.usagePatterns.spatialSensitivity[y]) continue;

          for (
            let x = 0;
            x < this.usagePatterns.spatialSensitivity[0].length;
            x++
          ) {
            if (this.usagePatterns.spatialSensitivity[y][x] !== undefined) {
              spatialMean += this.usagePatterns.spatialSensitivity[y][x];
              spatialCount++;
            }
          }
        }

        if (spatialCount > 0) {
          spatialMean /= spatialCount;

          for (
            let y = 0;
            y < this.usagePatterns.spatialSensitivity.length;
            y++
          ) {
            if (!this.usagePatterns.spatialSensitivity[y]) continue;

            for (
              let x = 0;
              x < this.usagePatterns.spatialSensitivity[0].length;
              x++
            ) {
              if (this.usagePatterns.spatialSensitivity[y][x] !== undefined) {
                spatialVariance += Math.pow(
                  this.usagePatterns.spatialSensitivity[y][x] - spatialMean,
                  2,
                );
              }
            }
          }

          spatialVariance /= spatialCount;
        }
      }

      const spatialBalance =
        spatialMean > 0
          ? Math.max(0, 1 - Math.sqrt(spatialVariance) / spatialMean)
          : 1.0;

      // Component 3: Compute efficiency (0-1)
      const computeEfficiency = this.metrics.computeEfficiency;

      // Component 4: Kernel utilization (0-1)
      // Measures if kernels are utilizing their weights effectively
      let kernelUtilization = 1.0;

      if (this.metrics.forwardCount > 10) {
        // Calculate kernel sparsity and magnitude distribution
        let totalElements = 0;
        let zeroElements = 0;
        let kernelMagnitudeVariance = 0;
        let kernelMagnitudeSum = 0;

        // Analyze weights across all filters
        for (let f = 0; f < this.filters; f++) {
          for (let ky = 0; ky < this.kernelSize[0]; ky++) {
            for (let kx = 0; kx < this.kernelSize[1]; kx++) {
              for (let c = 0; c < this.inputShape[2]; c++) {
                const magnitude = Math.abs(this.weights[f][ky][kx][c]);
                totalElements++;

                if (magnitude < 1e-5) {
                  zeroElements++;
                }

                kernelMagnitudeSum += magnitude;
              }
            }
          }
        }

        // Calculate average magnitude
        const avgMagnitude = kernelMagnitudeSum / totalElements;

        // Calculate magnitude variance
        if (avgMagnitude > 0) {
          for (let f = 0; f < this.filters; f++) {
            for (let ky = 0; ky < this.kernelSize[0]; ky++) {
              for (let kx = 0; kx < this.kernelSize[1]; kx++) {
                for (let c = 0; c < this.inputShape[2]; c++) {
                  const magnitude = Math.abs(this.weights[f][ky][kx][c]);
                  kernelMagnitudeVariance += Math.pow(
                    magnitude - avgMagnitude,
                    2,
                  );
                }
              }
            }
          }

          kernelMagnitudeVariance /= totalElements;
        }

        // Calculate kernel sparsity score (0-1)
        // Some sparsity is good, but too much indicates dead filters
        const sparsity = zeroElements / totalElements;
        const optimalSparsity = 0.3; // Ideal sparsity level
        const sparsityScore =
          1 - Math.min(1, Math.abs(sparsity - optimalSparsity) * 2);

        // Calculate magnitude variance score (0-1)
        // Some variance is good, but too much indicates instability
        const varianceScore =
          avgMagnitude > 0
            ? Math.max(0, 1 - Math.sqrt(kernelMagnitudeVariance) / avgMagnitude)
            : 0;

        // Combine into kernel utilization score
        kernelUtilization = 0.6 * sparsityScore + 0.4 * varianceScore;
      }

      // Component 5: Feature specialization (0-1)
      // Measures if filters are specializing in different features
      let featureSpecialization = 1.0;

      if (this.metrics.forwardCount > 20) {
        // Calculate correlation between filter activations
        let totalPairs = 0;
        let correlationSum = 0;

        // Check correlations between filter activations
        for (let i = 0; i < this.filters; i++) {
          for (let j = i + 1; j < this.filters; j++) {
            // High correlation means redundant filters
            const correlation =
              Math.abs(
                (activationDistribution[i] - meanActivation) *
                  (activationDistribution[j] - meanActivation),
              ) /
              (maxVariance + 1e-10);

            correlationSum += correlation;
            totalPairs++;
          }
        }

        if (totalPairs > 0) {
          const avgCorrelation = correlationSum / totalPairs;
          featureSpecialization = 1 - avgCorrelation;
        }
      }

      // Combine all components with weights
      return (
        0.3 * activationBalance +
        0.2 * spatialBalance +
        0.2 * computeEfficiency +
        0.15 * kernelUtilization +
        0.15 * featureSpecialization
      );
    }

    /**
     * Get layer usage patterns
     * @returns {Object} Current usage patterns
     */
    getUsagePatterns() {
      return {
        activationDistribution: [...this.usagePatterns.activationDistribution],
        spatialSensitivity: this._deepClone(
          this.usagePatterns.spatialSensitivity,
        ),
        sampleCount: this.usagePatterns.sampleCount,
        kernelUtilization: this._deepClone(
          this.usagePatterns.kernelUtilization,
        ),
      };
    }

    /**
     * Get information about the layer architecture
     * @returns {Object} Layer architecture information
     */
    getArchitecture() {
      return {
        type: "convolutional",
        inputShape: [...this.inputShape],
        outputShape: [...this.outputShape],
        kernelSize: [...this.kernelSize],
        filters: this.filters,
        strides: [...this.strides],
        padding: this.padding,
        activation: this.activation,
        parameterCount:
          this.filters *
            this.kernelSize[0] *
            this.kernelSize[1] *
            this.inputShape[2] +
          this.filters,
      };
    }
  }

  // Add class to Prime.Neural namespace
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Layer = Prime.Neural.Layer || {};
  Prime.Neural.Layer.ConvolutionalLayer = ConvolutionalLayer;
})();

// Export the enhanced Prime object
module.exports = Prime;
