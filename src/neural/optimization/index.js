/**
 * PrimeOS JavaScript Library - Neural Optimization Module
 * Advanced optimization algorithms with coherence constraints
 */

// Import the Prime object from core
const Prime = require("../../core");

// Create the Neural Optimization module using IIFE
(function () {
  /**
   * CoherenceOptimizer - Base class for optimizers with coherence awareness
   */
  class CoherenceOptimizer {
    /**
     * Create a new coherence-aware optimizer
     * @param {Object} config - Optimizer configuration
     * @param {number} [config.learningRate=0.01] - Base learning rate
     * @param {number} [config.coherenceWeight=0.5] - Weight for coherence constraint
     * @param {number} [config.minCoherence=0.7] - Minimum acceptable coherence
     */
    constructor(config = {}) {
      this.learningRate = config.learningRate || 0.01;
      this.coherenceWeight = config.coherenceWeight || 0.5;
      this.minCoherence = config.minCoherence || 0.7;

      // Internal state
      this.iteration = 0;
      this.state = {};
      this.coherenceHistory = [];
    }

    /**
     * Update parameters with coherence constraints
     * @param {Object} params - Current parameters
     * @param {Object} gradients - Parameter gradients
     * @param {Function} coherenceFn - Function to calculate coherence
     * @returns {Object} Updated parameters
     */
    update(params, gradients, coherenceFn) {
      throw new Prime.ValidationError("Method must be implemented by subclass");
    }

    /**
     * Calculate effective learning rate based on coherence
     * @param {number} coherence - Current coherence score
     * @returns {number} Adjusted learning rate
     */
    _getEffectiveLearningRate(coherence) {
      // Reduce learning rate as coherence approaches minimum threshold
      const coherenceRatio =
        (coherence - this.minCoherence) / (1 - this.minCoherence);

      const coherenceFactor = Math.max(0.1, Math.min(1, coherenceRatio));
      return this.learningRate * coherenceFactor;
    }

    /**
     * Track coherence changes
     * @param {number} coherence - Current coherence score
     */
    _trackCoherence(coherence) {
      this.iteration++;
      this.coherenceHistory.push({
        iteration: this.iteration,
        coherence,
        timestamp: new Date().toISOString(),
      });

      // Keep history size manageable
      if (this.coherenceHistory.length > 1000) {
        this.coherenceHistory = this.coherenceHistory.slice(-1000);
      }
    }

    /**
     * Get optimizer statistics and history
     * @returns {Object} Optimization statistics
     */
    getStatistics() {
      return {
        iterations: this.iteration,
        coherenceHistory: [...this.coherenceHistory],
        currentLearningRate: this.learningRate,
      };
    }
  }

  /**
   * CoherenceSGD - Stochastic Gradient Descent with coherence constraints
   * Extends the CoherenceOptimizer with standard SGD implementation
   */
  class CoherenceSGD extends CoherenceOptimizer {
    /**
     * Create a new SGD optimizer with coherence constraints
     * @param {Object} config - Optimizer configuration
     * @param {number} [config.learningRate=0.01] - Base learning rate
     * @param {number} [config.momentum=0] - Momentum coefficient
     * @param {number} [config.coherenceWeight=0.5] - Weight for coherence constraint
     * @param {number} [config.minCoherence=0.7] - Minimum acceptable coherence
     */
    constructor(config = {}) {
      super(config);
      this.momentum = config.momentum || 0;
      this.state.velocities = {};
    }

    /**
     * Update parameters with coherence constraints
     * @param {Object} params - Current parameters
     * @param {Object} gradients - Parameter gradients
     * @param {Function} coherenceFn - Function to calculate coherence
     * @returns {Object} Updated parameters
     */
    update(params, gradients, coherenceFn) {
      // Calculate current coherence
      const currentCoherence = coherenceFn(params);
      this._trackCoherence(currentCoherence);

      // Determine effective learning rate based on coherence
      const effectiveLR = this._getEffectiveLearningRate(currentCoherence);

      // Create a copy of parameters for updates
      const updatedParams = Prime.Utils.deepClone(params);

      // Initialize velocities if needed
      if (Object.keys(this.state.velocities).length === 0) {
        // For each parameter in gradients, create a matching velocity object
        for (const key in gradients) {
          if (gradients.hasOwnProperty(key)) {
            this.state.velocities[key] = this._createZeroLike(gradients[key]);
          }
        }
      }

      // Update each parameter with momentum
      for (const key in gradients) {
        if (gradients.hasOwnProperty(key) && params.hasOwnProperty(key)) {
          const gradient = gradients[key];
          const velocity = this.state.velocities[key];

          // Apply update based on parameter type
          if (Array.isArray(gradient)) {
            if (Array.isArray(gradient[0])) {
              // Handle 2D arrays (matrices)
              for (let i = 0; i < gradient.length; i++) {
                for (let j = 0; j < gradient[i].length; j++) {
                  // Update velocity with momentum
                  velocity[i][j] =
                    this.momentum * velocity[i][j] -
                    effectiveLR * gradient[i][j];

                  // Update parameter
                  updatedParams[key][i][j] += velocity[i][j];
                }
              }
            } else {
              // Handle 1D arrays (vectors)
              for (let i = 0; i < gradient.length; i++) {
                // Update velocity with momentum
                velocity[i] =
                  this.momentum * velocity[i] - effectiveLR * gradient[i];

                // Update parameter
                updatedParams[key][i] += velocity[i];
              }
            }
          } else if (typeof gradient === "number") {
            // Handle scalar values
            velocity.value =
              this.momentum * velocity.value - effectiveLR * gradient;

            updatedParams[key] += velocity.value;
          }
        }
      }

      // Check if update maintains minimum coherence
      const updatedCoherence = coherenceFn(updatedParams);

      // If coherence would drop too much, adjust the update
      if (updatedCoherence < this.minCoherence) {
        // Calculate how much to scale back the update
        const coherenceDiff = currentCoherence - updatedCoherence;
        const scaleFactor = Math.max(
          0.1,
          (currentCoherence - this.minCoherence) / coherenceDiff,
        );

        // Apply scaled update
        for (const key in gradients) {
          if (gradients.hasOwnProperty(key) && params.hasOwnProperty(key)) {
            const velocity = this.state.velocities[key];

            if (Array.isArray(params[key])) {
              if (Array.isArray(params[key][0])) {
                // Handle 2D arrays (matrices)
                for (let i = 0; i < params[key].length; i++) {
                  for (let j = 0; j < params[key][i].length; j++) {
                    const scaledVelocity = velocity[i][j] * scaleFactor;
                    updatedParams[key][i][j] =
                      params[key][i][j] + scaledVelocity;
                  }
                }
              } else {
                // Handle 1D arrays (vectors)
                for (let i = 0; i < params[key].length; i++) {
                  const scaledVelocity = velocity[i] * scaleFactor;
                  updatedParams[key][i] = params[key][i] + scaledVelocity;
                }
              }
            } else if (typeof params[key] === "number") {
              // Handle scalar values
              const scaledVelocity = velocity.value * scaleFactor;
              updatedParams[key] = params[key] + scaledVelocity;
            }
          }
        }
      }

      return updatedParams;
    }

    /**
     * Create a zero-filled object with the same structure as the input
     * @private
     * @param {*} obj - Object to match structure
     * @returns {*} Zero-filled object with same structure
     */
    _createZeroLike(obj) {
      if (Array.isArray(obj)) {
        if (Array.isArray(obj[0])) {
          // Handle 2D arrays (matrices)
          return obj.map((row) => row.map(() => 0));
        } else {
          // Handle 1D arrays (vectors)
          return obj.map(() => 0);
        }
      } else if (typeof obj === "number") {
        // Handle scalar values
        return { value: 0 };
      }

      // Default case
      return {};
    }
  }

  /**
   * CoherenceAdam - Adam optimizer with coherence constraints
   * Implements the Adam algorithm with additional coherence protection
   */
  class CoherenceAdam extends CoherenceOptimizer {
    /**
     * Create a new Adam optimizer with coherence constraints
     * @param {Object} config - Optimizer configuration
     * @param {number} [config.learningRate=0.001] - Base learning rate
     * @param {number} [config.beta1=0.9] - Exponential decay rate for first moment
     * @param {number} [config.beta2=0.999] - Exponential decay rate for second moment
     * @param {number} [config.epsilon=1e-8] - Small constant for numerical stability
     * @param {number} [config.coherenceWeight=0.5] - Weight for coherence constraint
     * @param {number} [config.minCoherence=0.7] - Minimum acceptable coherence
     */
    constructor(config = {}) {
      super({
        ...config,
        learningRate: config.learningRate || 0.001,
      });

      this.beta1 = config.beta1 || 0.9;
      this.beta2 = config.beta2 || 0.999;
      this.epsilon = config.epsilon || 1e-8;

      // Initialize Adam-specific state
      this.state = {
        m: {}, // First moment vectors
        v: {}, // Second moment vectors
      };
    }

    /**
     * Update parameters with coherence constraints
     * @param {Object} params - Current parameters
     * @param {Object} gradients - Parameter gradients
     * @param {Function} coherenceFn - Function to calculate coherence
     * @returns {Object} Updated parameters
     */
    update(params, gradients, coherenceFn) {
      // Calculate current coherence
      const currentCoherence = coherenceFn(params);
      this._trackCoherence(currentCoherence);

      // Determine effective learning rate based on coherence
      const effectiveLR = this._getEffectiveLearningRate(currentCoherence);

      // Create a copy of parameters for updates
      const updatedParams = Prime.Utils.deepClone(params);

      // Initialize moment vectors if needed
      if (Object.keys(this.state.m).length === 0) {
        for (const key in gradients) {
          if (gradients.hasOwnProperty(key)) {
            this.state.m[key] = this._createZeroLike(gradients[key]);
            this.state.v[key] = this._createZeroLike(gradients[key]);
          }
        }
      }

      // Increment iteration
      this.iteration++;

      // Compute bias correction terms
      const bias1 = 1 - Math.pow(this.beta1, this.iteration);
      const bias2 = 1 - Math.pow(this.beta2, this.iteration);

      // Update each parameter using Adam algorithm
      for (const key in gradients) {
        if (gradients.hasOwnProperty(key) && params.hasOwnProperty(key)) {
          const gradient = gradients[key];
          const m = this.state.m[key];
          const v = this.state.v[key];

          // Apply update based on parameter type
          if (Array.isArray(gradient)) {
            if (Array.isArray(gradient[0])) {
              // Handle 2D arrays (matrices)
              for (let i = 0; i < gradient.length; i++) {
                for (let j = 0; j < gradient[i].length; j++) {
                  // Update biased first moment estimate
                  m[i][j] =
                    this.beta1 * m[i][j] + (1 - this.beta1) * gradient[i][j];

                  // Update biased second raw moment estimate
                  v[i][j] =
                    this.beta2 * v[i][j] +
                    (1 - this.beta2) * gradient[i][j] * gradient[i][j];

                  // Compute bias-corrected moment estimates
                  const mHat = m[i][j] / bias1;
                  const vHat = v[i][j] / bias2;

                  // Update parameter
                  updatedParams[key][i][j] =
                    params[key][i][j] -
                    (effectiveLR * mHat) / (Math.sqrt(vHat) + this.epsilon);
                }
              }
            } else {
              // Handle 1D arrays (vectors)
              for (let i = 0; i < gradient.length; i++) {
                // Update biased first moment estimate
                m[i] = this.beta1 * m[i] + (1 - this.beta1) * gradient[i];

                // Update biased second raw moment estimate
                v[i] =
                  this.beta2 * v[i] +
                  (1 - this.beta2) * gradient[i] * gradient[i];

                // Compute bias-corrected moment estimates
                const mHat = m[i] / bias1;
                const vHat = v[i] / bias2;

                // Update parameter
                updatedParams[key][i] =
                  params[key][i] -
                  (effectiveLR * mHat) / (Math.sqrt(vHat) + this.epsilon);
              }
            }
          } else if (typeof gradient === "number") {
            // Handle scalar values
            // Update biased first moment estimate
            m.value = this.beta1 * m.value + (1 - this.beta1) * gradient;

            // Update biased second raw moment estimate
            v.value =
              this.beta2 * v.value + (1 - this.beta2) * gradient * gradient;

            // Compute bias-corrected moment estimates
            const mHat = m.value / bias1;
            const vHat = v.value / bias2;

            // Update parameter
            updatedParams[key] =
              params[key] -
              (effectiveLR * mHat) / (Math.sqrt(vHat) + this.epsilon);
          }
        }
      }

      // Check if update maintains minimum coherence
      const updatedCoherence = coherenceFn(updatedParams);

      // If coherence would drop too much, adjust the update
      if (updatedCoherence < this.minCoherence) {
        // Calculate interpolation factor to maintain minimum coherence
        // This creates a line search to find the largest update that maintains coherence
        let alpha = 1.0;
        const minAlpha = 0.1;
        const steps = 5;

        // Binary search for largest acceptable alpha
        for (let step = 0; step < steps; step++) {
          alpha *= 0.5;

          // Interpolate between original and updated parameters
          const testParams = this._interpolateParams(
            params,
            updatedParams,
            alpha,
          );
          const testCoherence = coherenceFn(testParams);

          // If coherence is acceptable, use this alpha
          if (testCoherence >= this.minCoherence) {
            // Apply interpolated update
            return testParams;
          }

          // If we've reached minimum step size, accept lower coherence
          if (alpha <= minAlpha) {
            break;
          }
        }

        // Use minimum alpha as fallback
        return this._interpolateParams(params, updatedParams, minAlpha);
      }

      return updatedParams;
    }

    /**
     * Interpolate between two parameter sets
     * @private
     * @param {Object} params1 - First parameter set
     * @param {Object} params2 - Second parameter set
     * @param {number} alpha - Interpolation factor (0-1)
     * @returns {Object} Interpolated parameters
     */
    _interpolateParams(params1, params2, alpha) {
      const result = Prime.Utils.deepClone(params1);

      for (const key in params1) {
        if (params1.hasOwnProperty(key) && params2.hasOwnProperty(key)) {
          if (Array.isArray(params1[key])) {
            if (Array.isArray(params1[key][0])) {
              // Handle 2D arrays (matrices)
              for (let i = 0; i < params1[key].length; i++) {
                for (let j = 0; j < params1[key][i].length; j++) {
                  if (
                    params1[key][i] &&
                    params2[key][i] &&
                    params1[key][i][j] !== undefined &&
                    params2[key][i][j] !== undefined
                  ) {
                    result[key][i][j] =
                      (1 - alpha) * params1[key][i][j] +
                      alpha * params2[key][i][j];
                  }
                }
              }
            } else {
              // Handle 1D arrays (vectors)
              for (let i = 0; i < params1[key].length; i++) {
                if (
                  params1[key][i] !== undefined &&
                  params2[key][i] !== undefined
                ) {
                  result[key][i] =
                    (1 - alpha) * params1[key][i] + alpha * params2[key][i];
                }
              }
            }
          } else if (typeof params1[key] === "number") {
            // Handle scalar values
            if (typeof params2[key] === "number") {
              result[key] = (1 - alpha) * params1[key] + alpha * params2[key];
            }
          }
        }
      }

      return result;
    }

    /**
     * Create a zero-filled object with the same structure as the input
     * @private
     * @param {*} obj - Object to match structure
     * @returns {*} Zero-filled object with same structure
     */
    _createZeroLike(obj) {
      if (Array.isArray(obj)) {
        if (Array.isArray(obj[0])) {
          // Handle 2D arrays (matrices)
          return obj.map((row) => row.map(() => 0));
        } else {
          // Handle 1D arrays (vectors)
          return obj.map(() => 0);
        }
      } else if (typeof obj === "number") {
        // Handle scalar values
        return { value: 0 };
      }

      // Default case
      return {};
    }
  }

  // Add optimizers to Prime.Neural.Optimization namespace
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Optimization = {
    CoherenceOptimizer,
    CoherenceSGD,
    CoherenceAdam,
  };
})();

// Export the enhanced Prime object
module.exports = Prime;
