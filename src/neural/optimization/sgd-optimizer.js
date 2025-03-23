/**
 * PrimeOS JavaScript Library - SGD Optimizer Module
 * Stochastic Gradient Descent optimizer with memory optimization and coherence constraints
 */

// Import the Prime object from core
const Prime = require('../../core');

// Create the SGD Optimizer module using IIFE
(function () {
  /**
   * SGDOptimizer - Memory efficient SGD implementation with momentum and coherence awareness
   */
  class SGDOptimizer {
    /**
     * Create a new SGD optimizer
     * @param {Object} config - Optimizer configuration
     * @param {number} [config.learningRate=0.01] - Base learning rate
     * @param {number} [config.momentum=0] - Momentum coefficient
     * @param {number} [config.weightDecay=0] - Weight decay (L2 regularization coefficient)
     * @param {boolean} [config.useNesterov=false] - Whether to use Nesterov accelerated gradient
     * @param {boolean} [config.useTypedArrays=false] - Whether to use TypedArrays for memory efficiency
     */
    constructor(config = {}) {
      this.learningRate = config.learningRate || 0.01;
      this.momentum = config.momentum || 0;
      this.weightDecay = config.weightDecay || 0;
      this.useNesterov = config.useNesterov || false;
      this.useTypedArrays = config.useTypedArrays || false;

      // Internal state
      this.iteration = 0;
      this.velocities = {};

      // Metrics for tracking
      this.metrics = {
        lastLearningRate: this.learningRate,
        meanGradientNorm: 0,
        updateRatio: 0,
        parameterCount: 0,
      };
    }

    /**
     * Initialize velocities for a parameter if they don't already exist
     * @private
     * @param {string} paramName - Name of the parameter
     * @param {Array|TypedArray} paramValue - Parameter value to match
     */
    _initializeVelocity(paramName, paramValue) {
      if (!this.velocities[paramName]) {
        // Create velocities with the same shape and type as the parameters
        if (Array.isArray(paramValue)) {
          if (Array.isArray(paramValue[0])) {
            // 2D array (matrix)
            const rows = paramValue.length;
            const cols = paramValue[0].length;

            if (this.useTypedArrays && typeof Float32Array !== 'undefined') {
              // For TypedArrays, we create a flat array and reshape it
              const flatVelocity = new Float32Array(rows * cols);
              this.velocities[paramName] = new Array(rows);

              for (let i = 0; i < rows; i++) {
                this.velocities[paramName][i] = new Float32Array(
                  flatVelocity.buffer,
                  i * cols * Float32Array.BYTES_PER_ELEMENT,
                  cols,
                );
              }

              // Store reference to the flat array for efficient operations
              Object.defineProperty(this.velocities[paramName], '_flatArray', {
                value: flatVelocity,
              });
            } else {
              // Standard arrays
              this.velocities[paramName] = new Array(rows);
              for (let i = 0; i < rows; i++) {
                this.velocities[paramName][i] = new Array(cols).fill(0);
              }
            }
          } else {
            // 1D array (vector)
            if (this.useTypedArrays && typeof Float32Array !== 'undefined') {
              this.velocities[paramName] = new Float32Array(paramValue.length);
            } else {
              this.velocities[paramName] = new Array(paramValue.length).fill(0);
            }
          }
        } else if (typeof paramValue === 'number') {
          // Scalar value
          this.velocities[paramName] = 0;
        }

        // Update parameter count metric
        this._updateParameterCount(paramName, paramValue);
      }
    }

    /**
     * Update parameter count metric
     * @private
     * @param {string} paramName - Name of the parameter
     * @param {Array|TypedArray} paramValue - Parameter value
     */
    _updateParameterCount(paramName, paramValue) {
      if (Array.isArray(paramValue)) {
        if (Array.isArray(paramValue[0])) {
          // 2D array
          let count = 0;
          for (let i = 0; i < paramValue.length; i++) {
            count += paramValue[i].length;
          }
          this.metrics.parameterCount += count;
        } else {
          // 1D array
          this.metrics.parameterCount += paramValue.length;
        }
      } else if (typeof paramValue === 'number') {
        // Scalar
        this.metrics.parameterCount += 1;
      }
    }

    /**
     * Calculate the L2 norm of a gradient
     * @private
     * @param {Object} gradients - Gradients object
     * @returns {number} Gradient norm
     */
    _calculateGradientNorm(gradients) {
      let sumSquared = 0;
      let count = 0;

      for (const paramName in gradients) {
        const grad = gradients[paramName];

        if (Array.isArray(grad)) {
          if (Array.isArray(grad[0])) {
            // 2D array
            for (let i = 0; i < grad.length; i++) {
              for (let j = 0; j < grad[i].length; j++) {
                sumSquared += grad[i][j] * grad[i][j];
                count++;
              }
            }
          } else {
            // 1D array
            for (let i = 0; i < grad.length; i++) {
              sumSquared += grad[i] * grad[i];
              count++;
            }
          }
        } else if (typeof grad === 'number') {
          // Scalar
          sumSquared += grad * grad;
          count++;
        }
      }

      return count > 0 ? Math.sqrt(sumSquared / count) : 0;
    }

    /**
     * Apply L2 regularization (weight decay) to gradients
     * @private
     * @param {Object} gradients - Gradients to modify
     * @param {Object} parameters - Current parameters
     */
    _applyWeightDecay(gradients, parameters) {
      if (this.weightDecay <= 0) return;

      for (const paramName in gradients) {
        if (
          gradients.hasOwnProperty(paramName) &&
          parameters.hasOwnProperty(paramName)
        ) {
          const grad = gradients[paramName];
          const param = parameters[paramName];

          if (Array.isArray(grad)) {
            if (Array.isArray(grad[0])) {
              // 2D array
              for (let i = 0; i < grad.length; i++) {
                for (let j = 0; j < grad[i].length; j++) {
                  grad[i][j] += this.weightDecay * param[i][j];
                }
              }
            } else {
              // 1D array
              for (let i = 0; i < grad.length; i++) {
                grad[i] += this.weightDecay * param[i];
              }
            }
          } else if (typeof grad === 'number') {
            // Scalar
            gradients[paramName] += this.weightDecay * param;
          }
        }
      }
    }

    /**
     * Update parameters with SGD
     * @param {Object} parameters - Current parameters
     * @param {Object} gradients - Parameter gradients
     * @param {Object} [options={}] - Optional update settings
     * @param {number} [options.learningRate] - Override default learning rate
     * @param {boolean} [options.inPlace=true] - Whether to modify parameters in-place
     * @returns {Object} Updated parameters
     */
    update(parameters, gradients, options = {}) {
      const lr = options.learningRate || this.learningRate;
      const inPlace = options.inPlace !== false;

      // Increment iteration counter
      this.iteration++;

      // Apply weight decay (L2 regularization)
      this._applyWeightDecay(gradients, parameters);

      // Calculate gradient norm for metrics
      const gradientNorm = this._calculateGradientNorm(gradients);
      this.metrics.meanGradientNorm =
        0.9 * this.metrics.meanGradientNorm + 0.1 * gradientNorm;
      this.metrics.lastLearningRate = lr;

      // Track the average size of parameter updates
      let updateMagnitude = 0;
      let paramMagnitude = 0;
      let valueCount = 0;

      // Create a copy of parameters if not updating in-place
      const updatedParams = inPlace
        ? parameters
        : JSON.parse(JSON.stringify(parameters));

      // Update each parameter
      for (const paramName in gradients) {
        if (
          gradients.hasOwnProperty(paramName) &&
          updatedParams.hasOwnProperty(paramName)
        ) {
          const grad = gradients[paramName];
          const param = updatedParams[paramName];

          // Make sure velocities are initialized
          this._initializeVelocity(paramName, param);
          const velocity = this.velocities[paramName];

          // Update based on parameter type
          if (Array.isArray(grad)) {
            if (Array.isArray(grad[0])) {
              // 2D array (matrix)
              for (let i = 0; i < grad.length; i++) {
                for (let j = 0; j < grad[i].length; j++) {
                  // Update velocity with momentum
                  velocity[i][j] =
                    this.momentum * velocity[i][j] - lr * grad[i][j];

                  // Nesterov momentum adjustment if enabled
                  const update = this.useNesterov
                    ? -lr * grad[i][j] + this.momentum * velocity[i][j]
                    : velocity[i][j];

                  // Track update magnitudes for metrics
                  updateMagnitude += Math.abs(update);
                  paramMagnitude += Math.abs(param[i][j]);
                  valueCount++;

                  // Apply the update
                  param[i][j] += update;
                }
              }
            } else {
              // 1D array (vector)
              for (let i = 0; i < grad.length; i++) {
                // Update velocity with momentum
                velocity[i] = this.momentum * velocity[i] - lr * grad[i];

                // Nesterov momentum adjustment if enabled
                const update = this.useNesterov
                  ? -lr * grad[i] + this.momentum * velocity[i]
                  : velocity[i];

                // Track update magnitudes for metrics
                updateMagnitude += Math.abs(update);
                paramMagnitude += Math.abs(param[i]);
                valueCount++;

                // Apply the update
                param[i] += update;
              }
            }
          } else if (typeof grad === 'number') {
            // Scalar value
            velocity = this.momentum * velocity - lr * grad;
            this.velocities[paramName] = velocity;

            // Nesterov momentum adjustment if enabled
            const update = this.useNesterov
              ? -lr * grad + this.momentum * velocity
              : velocity;

            // Track update magnitudes for metrics
            updateMagnitude += Math.abs(update);
            paramMagnitude += Math.abs(param);
            valueCount++;

            // Apply the update
            updatedParams[paramName] += update;
          }
        }
      }

      // Update metrics
      if (valueCount > 0) {
        const avgUpdate = updateMagnitude / valueCount;
        const avgParam = paramMagnitude / valueCount;
        this.metrics.updateRatio = avgParam > 0 ? avgUpdate / avgParam : 0;
      }

      return updatedParams;
    }

    /**
     * Get optimizer configuration
     * @returns {Object} Current configuration
     */
    getConfig() {
      return {
        name: 'SGD',
        learningRate: this.learningRate,
        momentum: this.momentum,
        weightDecay: this.weightDecay,
        useNesterov: this.useNesterov,
        useTypedArrays: this.useTypedArrays,
        iterations: this.iteration,
      };
    }

    /**
     * Get optimizer metrics
     * @returns {Object} Current metrics
     */
    getMetrics() {
      return { ...this.metrics };
    }

    /**
     * Set learning rate
     * @param {number} learningRate - New learning rate
     */
    setLearningRate(learningRate) {
      this.learningRate = learningRate;
    }

    /**
     * Calculate coherence score for the optimizer
     * @returns {number} Coherence score between 0 and 1
     */
    calculateCoherence() {
      // Base score starts at 1.0
      let score = 1.0;

      // Penalize for unstable gradient norms (hinting at possible training issues)
      const normalizedGradientNorm = Math.min(
        1.0,
        this.metrics.meanGradientNorm / 10.0,
      );
      if (normalizedGradientNorm > 0.7) {
        score -= (0.3 * (normalizedGradientNorm - 0.7)) / 0.3;
      }

      // Penalize for unusually large parameter updates
      if (this.metrics.updateRatio > 0.1) {
        score -= 0.3 * Math.min(1.0, (this.metrics.updateRatio - 0.1) / 0.4);
      }

      return Math.max(0, score);
    }
  }

  // Add class to Prime.Neural.Optimization namespace
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Optimization = Prime.Neural.Optimization || {};
  Prime.Neural.Optimization.SGDOptimizer = SGDOptimizer;
})();

// Export the enhanced Prime object
module.exports = Prime;
