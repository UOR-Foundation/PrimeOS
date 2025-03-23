/**
 * PrimeOS JavaScript Library - Adam Optimizer Module
 * Memory-efficient Adam optimizer implementation with coherence awareness
 */

// Import the Prime object from core
const Prime = require('../../core');

// Create the Adam Optimizer module using IIFE
(function () {
  /**
   * AdamOptimizer - Memory efficient implementation of Adam with coherence monitoring
   */
  class AdamOptimizer {
    /**
     * Create a new Adam optimizer
     * @param {Object} config - Optimizer configuration
     * @param {number} [config.learningRate=0.001] - Base learning rate
     * @param {number} [config.beta1=0.9] - Exponential decay rate for first moment
     * @param {number} [config.beta2=0.999] - Exponential decay rate for second moment
     * @param {number} [config.epsilon=1e-8] - Small constant for numerical stability
     * @param {number} [config.weightDecay=0] - Weight decay (L2 regularization coefficient)
     * @param {boolean} [config.amsgrad=false] - Whether to use AMSGrad variant
     * @param {boolean} [config.useTypedArrays=false] - Whether to use TypedArrays for memory efficiency
     */
    constructor(config = {}) {
      this.learningRate = config.learningRate || 0.001;
      this.beta1 = config.beta1 || 0.9;
      this.beta2 = config.beta2 || 0.999;
      this.epsilon = config.epsilon || 1e-8;
      this.weightDecay = config.weightDecay || 0;
      this.amsgrad = config.amsgrad || false;
      this.useTypedArrays = config.useTypedArrays || false;

      // Internal state
      this.iteration = 0;
      this.m = {}; // First moment estimates
      this.v = {}; // Second moment estimates
      this.vMax = {}; // Maximum second moments (for AMSGrad)

      // Metrics for tracking
      this.metrics = {
        lastLearningRate: this.learningRate,
        meanGradientNorm: 0,
        maxSecondMoment: 0,
        updateRatio: 0,
        parameterCount: 0,
      };
    }

    /**
     * Initialize moment estimates for a parameter if they don't already exist
     * @private
     * @param {string} paramName - Name of the parameter
     * @param {Array|TypedArray} paramValue - Parameter value to match
     */
    _initializeMomentEstimates(paramName, paramValue) {
      if (!this.m[paramName]) {
        // Create moment estimates with the same shape and type as the parameters
        if (Array.isArray(paramValue)) {
          if (Array.isArray(paramValue[0])) {
            // 2D array (matrix)
            const rows = paramValue.length;
            const cols = paramValue[0].length;

            if (this.useTypedArrays && typeof Float32Array !== 'undefined') {
              // For TypedArrays, we create flat arrays and reshape them
              // First moment (m)
              const flatM = new Float32Array(rows * cols);
              this.m[paramName] = new Array(rows);
              // Second moment (v)
              const flatV = new Float32Array(rows * cols);
              this.v[paramName] = new Array(rows);

              // If using AMSGrad, create vMax as well
              let flatVMax = null;
              if (this.amsgrad) {
                flatVMax = new Float32Array(rows * cols);
                this.vMax[paramName] = new Array(rows);
              }

              for (let i = 0; i < rows; i++) {
                // Create views into the flat arrays
                this.m[paramName][i] = new Float32Array(
                  flatM.buffer,
                  i * cols * Float32Array.BYTES_PER_ELEMENT,
                  cols,
                );
                this.v[paramName][i] = new Float32Array(
                  flatV.buffer,
                  i * cols * Float32Array.BYTES_PER_ELEMENT,
                  cols,
                );

                if (this.amsgrad) {
                  this.vMax[paramName][i] = new Float32Array(
                    flatVMax.buffer,
                    i * cols * Float32Array.BYTES_PER_ELEMENT,
                    cols,
                  );
                }
              }

              // Store references to the flat arrays for efficient operations
              Object.defineProperty(this.m[paramName], '_flatArray', {
                value: flatM,
              });
              Object.defineProperty(this.v[paramName], '_flatArray', {
                value: flatV,
              });
              if (this.amsgrad) {
                Object.defineProperty(this.vMax[paramName], '_flatArray', {
                  value: flatVMax,
                });
              }
            } else {
              // Standard arrays
              this.m[paramName] = new Array(rows);
              this.v[paramName] = new Array(rows);
              if (this.amsgrad) {
                this.vMax[paramName] = new Array(rows);
              }

              for (let i = 0; i < rows; i++) {
                this.m[paramName][i] = new Array(cols).fill(0);
                this.v[paramName][i] = new Array(cols).fill(0);
                if (this.amsgrad) {
                  this.vMax[paramName][i] = new Array(cols).fill(0);
                }
              }
            }
          } else {
            // 1D array (vector)
            if (this.useTypedArrays && typeof Float32Array !== 'undefined') {
              this.m[paramName] = new Float32Array(paramValue.length);
              this.v[paramName] = new Float32Array(paramValue.length);
              if (this.amsgrad) {
                this.vMax[paramName] = new Float32Array(paramValue.length);
              }
            } else {
              this.m[paramName] = new Array(paramValue.length).fill(0);
              this.v[paramName] = new Array(paramValue.length).fill(0);
              if (this.amsgrad) {
                this.vMax[paramName] = new Array(paramValue.length).fill(0);
              }
            }
          }
        } else if (typeof paramValue === 'number') {
          // Scalar value
          this.m[paramName] = 0;
          this.v[paramName] = 0;
          if (this.amsgrad) {
            this.vMax[paramName] = 0;
          }
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
     * Update parameters with Adam
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

      // Compute bias correction terms
      const bias1 = 1 - Math.pow(this.beta1, this.iteration);
      const bias2 = 1 - Math.pow(this.beta2, this.iteration);

      // Track the average size of parameter updates
      let updateMagnitude = 0;
      let paramMagnitude = 0;
      let valueCount = 0;
      let maxSecondMoment = 0;

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

          // Make sure moment estimates are initialized
          this._initializeMomentEstimates(paramName, param);
          const m = this.m[paramName];
          const v = this.v[paramName];
          const vMax = this.amsgrad ? this.vMax[paramName] : null;

          // Update based on parameter type
          if (Array.isArray(grad)) {
            if (Array.isArray(grad[0])) {
              // 2D array (matrix)
              for (let i = 0; i < grad.length; i++) {
                for (let j = 0; j < grad[i].length; j++) {
                  // Update biased first moment estimate
                  m[i][j] =
                    this.beta1 * m[i][j] + (1 - this.beta1) * grad[i][j];

                  // Update biased second raw moment estimate
                  v[i][j] =
                    this.beta2 * v[i][j] +
                    (1 - this.beta2) * grad[i][j] * grad[i][j];

                  // If using AMSGrad, maintain max of second moments
                  if (this.amsgrad) {
                    vMax[i][j] = Math.max(vMax[i][j], v[i][j]);
                    maxSecondMoment = Math.max(maxSecondMoment, vMax[i][j]);
                  } else {
                    maxSecondMoment = Math.max(maxSecondMoment, v[i][j]);
                  }

                  // Compute bias-corrected first moment estimate
                  const mHat = m[i][j] / bias1;

                  // Compute bias-corrected second raw moment estimate
                  const vHat = (this.amsgrad ? vMax[i][j] : v[i][j]) / bias2;

                  // Compute update
                  const update =
                    -(lr * mHat) / (Math.sqrt(vHat) + this.epsilon);

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
                // Update biased first moment estimate
                m[i] = this.beta1 * m[i] + (1 - this.beta1) * grad[i];

                // Update biased second raw moment estimate
                v[i] = this.beta2 * v[i] + (1 - this.beta2) * grad[i] * grad[i];

                // If using AMSGrad, maintain max of second moments
                if (this.amsgrad) {
                  vMax[i] = Math.max(vMax[i], v[i]);
                  maxSecondMoment = Math.max(maxSecondMoment, vMax[i]);
                } else {
                  maxSecondMoment = Math.max(maxSecondMoment, v[i]);
                }

                // Compute bias-corrected first moment estimate
                const mHat = m[i] / bias1;

                // Compute bias-corrected second raw moment estimate
                const vHat = (this.amsgrad ? vMax[i] : v[i]) / bias2;

                // Compute update
                const update = -(lr * mHat) / (Math.sqrt(vHat) + this.epsilon);

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
            // Update biased first moment estimate
            this.m[paramName] = this.beta1 * m + (1 - this.beta1) * grad;

            // Update biased second raw moment estimate
            this.v[paramName] = this.beta2 * v + (1 - this.beta2) * grad * grad;

            // If using AMSGrad, maintain max of second moments
            if (this.amsgrad) {
              this.vMax[paramName] = Math.max(vMax, v);
              maxSecondMoment = Math.max(maxSecondMoment, this.vMax[paramName]);
            } else {
              maxSecondMoment = Math.max(maxSecondMoment, v);
            }

            // Compute bias-corrected first moment estimate
            const mHat = this.m[paramName] / bias1;

            // Compute bias-corrected second raw moment estimate
            const vHat =
              (this.amsgrad ? this.vMax[paramName] : this.v[paramName]) / bias2;

            // Compute update
            const update = -(lr * mHat) / (Math.sqrt(vHat) + this.epsilon);

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
      this.metrics.maxSecondMoment = maxSecondMoment;

      return updatedParams;
    }

    /**
     * Get optimizer configuration
     * @returns {Object} Current configuration
     */
    getConfig() {
      return {
        name: 'Adam',
        learningRate: this.learningRate,
        beta1: this.beta1,
        beta2: this.beta2,
        epsilon: this.epsilon,
        weightDecay: this.weightDecay,
        amsgrad: this.amsgrad,
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

      // Penalize for excessive second moments (can indicate exploding gradients)
      const normalizedSecondMoment = Math.min(
        1.0,
        this.metrics.maxSecondMoment / 100.0,
      );
      if (normalizedSecondMoment > 0.5) {
        score -= (0.4 * (normalizedSecondMoment - 0.5)) / 0.5;
      }

      return Math.max(0, score);
    }
  }

  // Add class to Prime.Neural.Optimization namespace
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Optimization = Prime.Neural.Optimization || {};
  Prime.Neural.Optimization.AdamOptimizer = AdamOptimizer;
})();

// Export the enhanced Prime object
module.exports = Prime;
