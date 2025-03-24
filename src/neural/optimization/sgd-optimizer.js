/**
 * PrimeOS JavaScript Library - SGD Optimizer Module
 * Stochastic Gradient Descent optimizer with memory optimization and coherence constraints
 */

// Import the Prime object from core
const Prime = require("../../core");

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
      // Validate config object
      if (config !== null && typeof config !== "object") {
        throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
          "Optimizer configuration must be an object",
          { providedConfig: config },
          "INVALID_OPTIMIZER_CONFIG"
        );
      }
      
      // Get config parameters with validation
      this.learningRate = this._validateLearningRate(config.learningRate || 0.01);
      this.momentum = this._validateMomentum(config.momentum || 0);
      this.weightDecay = this._validateWeightDecay(config.weightDecay || 0);
      this.useNesterov = !!config.useNesterov;
      this.useTypedArrays = !!config.useTypedArrays;

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
     * Validate learning rate parameter
     * @private
     * @param {any} lr - Learning rate to validate
     * @returns {number} Validated learning rate
     */
    _validateLearningRate(lr) {
      const numLr = Number(lr);
      
      if (isNaN(numLr)) {
        throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
          "Learning rate must be a number",
          { providedValue: lr },
          "INVALID_LEARNING_RATE"
        );
      }
      
      if (numLr <= 0) {
        throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
          "Learning rate must be positive",
          { providedValue: numLr },
          "NEGATIVE_LEARNING_RATE"
        );
      }
      
      return numLr;
    }
    
    /**
     * Validate momentum parameter
     * @private
     * @param {any} momentum - Momentum to validate
     * @returns {number} Validated momentum
     */
    _validateMomentum(momentum) {
      const numMomentum = Number(momentum);
      
      if (isNaN(numMomentum)) {
        throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
          "Momentum must be a number",
          { providedValue: momentum },
          "INVALID_MOMENTUM"
        );
      }
      
      if (numMomentum < 0 || numMomentum >= 1) {
        throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
          "Momentum must be between 0 and 1 (exclusive)",
          { providedValue: numMomentum },
          "MOMENTUM_OUT_OF_RANGE"
        );
      }
      
      return numMomentum;
    }
    
    /**
     * Validate weight decay parameter
     * @private
     * @param {any} decay - Weight decay to validate
     * @returns {number} Validated weight decay
     */
    _validateWeightDecay(decay) {
      const numDecay = Number(decay);
      
      if (isNaN(numDecay)) {
        throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
          "Weight decay must be a number",
          { providedValue: decay },
          "INVALID_WEIGHT_DECAY"
        );
      }
      
      if (numDecay < 0) {
        throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
          "Weight decay must be non-negative",
          { providedValue: numDecay },
          "NEGATIVE_WEIGHT_DECAY"
        );
      }
      
      return numDecay;
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

            if (this.useTypedArrays && typeof Float32Array !== "undefined") {
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
              Object.defineProperty(this.velocities[paramName], "_flatArray", {
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
            if (this.useTypedArrays && typeof Float32Array !== "undefined") {
              this.velocities[paramName] = new Float32Array(paramValue.length);
            } else {
              this.velocities[paramName] = new Array(paramValue.length).fill(0);
            }
          }
        } else if (typeof paramValue === "number") {
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
      } else if (typeof paramValue === "number") {
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
        } else if (typeof grad === "number") {
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
          } else if (typeof grad === "number") {
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
      try {
        // Validate inputs
        if (!parameters || typeof parameters !== "object") {
          throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
            "Parameters must be an object",
            { providedType: typeof parameters },
            "INVALID_PARAMETERS"
          );
        }
        
        if (!gradients || typeof gradients !== "object") {
          throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
            "Gradients must be an object",
            { providedType: typeof gradients },
            "INVALID_GRADIENTS"
          );
        }
        
        // Validate options
        if (options !== null && typeof options !== "object") {
          throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
            "Options must be an object",
            { providedType: typeof options },
            "INVALID_OPTIONS"
          );
        }
        
        // Extract and validate learning rate from options
        let lr = this.learningRate;
        if (options.learningRate !== undefined) {
          lr = this._validateLearningRate(options.learningRate);
        }
        
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

        // Check for NaN gradients, which indicate numerical issues
        if (isNaN(gradientNorm)) {
          throw new (Prime.Neural.Errors.NeuralCoherenceError || Prime.ValidationError)(
            "NaN gradients detected during update",
            null, // threshold
            null, // actual
            { iteration: this.iteration },
            "NAN_GRADIENTS"
          );
        }

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
                // Validate array shape matches
                if (!Array.isArray(param) || !Array.isArray(param[0])) {
                  throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
                    `Parameter and gradient shapes don't match for ${paramName}`,
                    { 
                      paramShape: Array.isArray(param) ? (Array.isArray(param[0]) ? '2D' : '1D') : typeof param,
                      gradShape: '2D'
                    },
                    "SHAPE_MISMATCH"
                  );
                }
                
                // Validate array dimensions match
                if (grad.length !== param.length || grad[0].length !== param[0].length) {
                  throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
                    `Parameter and gradient dimensions don't match for ${paramName}`,
                    { 
                      paramDimensions: [param.length, param[0].length],
                      gradDimensions: [grad.length, grad[0].length]
                    },
                    "DIMENSION_MISMATCH"
                  );
                }
                
                // 2D array (matrix)
                for (let i = 0; i < grad.length; i++) {
                  for (let j = 0; j < grad[i].length; j++) {
                    // Check for non-finite gradient values
                    if (!Number.isFinite(grad[i][j])) {
                      throw new (Prime.Neural.Errors.NeuralCoherenceError || Prime.ValidationError)(
                        `Non-finite gradient detected at ${paramName}[${i}][${j}]`,
                        null, // threshold
                        grad[i][j], // actual
                        { iteration: this.iteration },
                        "NON_FINITE_GRADIENT"
                      );
                    }
                    
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
                    
                    // Check for numerical issues after update
                    if (!Number.isFinite(param[i][j])) {
                      throw new (Prime.Neural.Errors.NeuralCoherenceError || Prime.ValidationError)(
                        `Parameter became non-finite after update at ${paramName}[${i}][${j}]`,
                        null, // threshold
                        param[i][j], // actual
                        { 
                          originalParam: param[i][j] - update,
                          update: update,
                          gradient: grad[i][j]
                        },
                        "NON_FINITE_PARAMETER"
                      );
                    }
                  }
                }
              } else {
                // Validate array shape matches
                if (!Array.isArray(param) || Array.isArray(param[0])) {
                  throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
                    `Parameter and gradient shapes don't match for ${paramName}`,
                    { 
                      paramShape: Array.isArray(param) ? (Array.isArray(param[0]) ? '2D' : '1D') : typeof param,
                      gradShape: '1D'
                    },
                    "SHAPE_MISMATCH"
                  );
                }
                
                // Validate array dimensions match
                if (grad.length !== param.length) {
                  throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
                    `Parameter and gradient dimensions don't match for ${paramName}`,
                    { 
                      paramDimensions: [param.length],
                      gradDimensions: [grad.length]
                    },
                    "DIMENSION_MISMATCH"
                  );
                }
                
                // 1D array (vector)
                for (let i = 0; i < grad.length; i++) {
                  // Check for non-finite gradient values
                  if (!Number.isFinite(grad[i])) {
                    throw new (Prime.Neural.Errors.NeuralCoherenceError || Prime.ValidationError)(
                      `Non-finite gradient detected at ${paramName}[${i}]`,
                      null, // threshold
                      grad[i], // actual
                      { iteration: this.iteration },
                      "NON_FINITE_GRADIENT"
                    );
                  }
                  
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
                  
                  // Check for numerical issues after update
                  if (!Number.isFinite(param[i])) {
                    throw new (Prime.Neural.Errors.NeuralCoherenceError || Prime.ValidationError)(
                      `Parameter became non-finite after update at ${paramName}[${i}]`,
                      null, // threshold
                      param[i], // actual
                      { 
                        originalParam: param[i] - update,
                        update: update,
                        gradient: grad[i]
                      },
                      "NON_FINITE_PARAMETER"
                    );
                  }
                }
              }
            } else if (typeof grad === "number") {
              // Validate parameter is a number
              if (typeof param !== "number") {
                throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
                  `Parameter and gradient types don't match for ${paramName}`,
                  { 
                    paramType: typeof param,
                    gradType: typeof grad
                  },
                  "TYPE_MISMATCH"
                );
              }
              
              // Check for non-finite gradient value
              if (!Number.isFinite(grad)) {
                throw new (Prime.Neural.Errors.NeuralCoherenceError || Prime.ValidationError)(
                  `Non-finite gradient detected at ${paramName}`,
                  null, // threshold
                  grad, // actual
                  { iteration: this.iteration },
                  "NON_FINITE_GRADIENT"
                );
              }
              
              // Scalar value
              let newVelocity = this.momentum * this.velocities[paramName] - lr * grad;
              this.velocities[paramName] = newVelocity;

              // Nesterov momentum adjustment if enabled
              const update = this.useNesterov
                ? -lr * grad + this.momentum * newVelocity
                : newVelocity;

              // Track update magnitudes for metrics
              updateMagnitude += Math.abs(update);
              paramMagnitude += Math.abs(param);
              valueCount++;

              // Apply the update
              updatedParams[paramName] += update;
              
              // Check for numerical issues after update
              if (!Number.isFinite(updatedParams[paramName])) {
                throw new (Prime.Neural.Errors.NeuralCoherenceError || Prime.ValidationError)(
                  `Parameter became non-finite after update at ${paramName}`,
                  null, // threshold
                  updatedParams[paramName], // actual
                  { 
                    originalParam: param,
                    update: update,
                    gradient: grad
                  },
                  "NON_FINITE_PARAMETER"
                );
              }
            } else {
              // Handle unexpected gradient type
              throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
                `Unsupported gradient type for ${paramName}`,
                { gradientType: typeof grad },
                "UNSUPPORTED_GRADIENT_TYPE"
              );
            }
          }
        }

        // Update metrics
        if (valueCount > 0) {
          const avgUpdate = updateMagnitude / valueCount;
          const avgParam = paramMagnitude / valueCount;
          this.metrics.updateRatio = avgParam > 0 ? avgUpdate / avgParam : 0;
          
          // Check for unusually large updates that might indicate instability
          if (this.metrics.updateRatio > 0.5) {
            console.warn(`SGDOptimizer: Large update ratio detected (${this.metrics.updateRatio.toFixed(3)}). Consider reducing learning rate.`);
          }
        }

        return updatedParams;
      } catch (error) {
        // Wrap lower-level errors in OptimizerError to provide context
        if (!(error instanceof Prime.Neural.Errors.OptimizerError || 
              error instanceof Prime.Neural.Errors.NeuralCoherenceError)) {
          throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
            "Error during optimizer update",
            { 
              iteration: this.iteration,
              originalError: error.message
            },
            "UPDATE_ERROR",
            error
          );
        }
        throw error;
      }
    }

    /**
     * Get optimizer configuration
     * @returns {Object} Current configuration
     */
    getConfig() {
      return {
        name: "SGD",
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
     * @param {Object} [options={}] - Options for coherence calculation
     * @param {boolean} [options.throwOnViolation=false] - Whether to throw error on coherence violations
     * @returns {number} Coherence score between 0 and 1
     * @throws {NeuralCoherenceError} If throwOnViolation is true and coherence violations are detected
     */
    calculateCoherence(options = {}) {
      // Base score starts at 1.0
      let score = 1.0;
      const violations = [];
  
      // Validate options
      const throwOnViolation = !!options.throwOnViolation;

      try {
        // Check for unstable gradient norms (hinting at possible training issues)
        const normalizedGradientNorm = Math.min(
          1.0,
          this.metrics.meanGradientNorm / 10.0,
        );
        
        const gradientNormThreshold = 0.7;
        if (normalizedGradientNorm > gradientNormThreshold) {
          score -= (0.3 * (normalizedGradientNorm - gradientNormThreshold)) / 0.3;
          violations.push({
            type: "HIGH_GRADIENT_NORM",
            severity: "medium",
            message: "Unusually high gradient norm detected",
            threshold: gradientNormThreshold,
            actual: normalizedGradientNorm,
            details: {
              meanGradientNorm: this.metrics.meanGradientNorm,
              iteration: this.iteration
            }
          });
        }
  
        // Check for unusually large parameter updates (could indicate instability)
        const updateRatioThreshold = 0.1;
        if (this.metrics.updateRatio > updateRatioThreshold) {
          score -= 0.3 * Math.min(1.0, (this.metrics.updateRatio - updateRatioThreshold) / 0.4);
          violations.push({
            type: "HIGH_UPDATE_RATIO",
            severity: this.metrics.updateRatio > 0.3 ? "high" : "medium",
            message: "Unusually large parameter updates detected",
            threshold: updateRatioThreshold,
            actual: this.metrics.updateRatio,
            details: {
              learningRate: this.metrics.lastLearningRate,
              iteration: this.iteration
            }
          });
        }
  
        // Check for learning rate stability
        if (this.metrics.updateRatio > 0.5 && this.metrics.meanGradientNorm > 5.0) {
          score -= 0.5;
          violations.push({
            type: "LEARNING_RATE_INSTABILITY",
            severity: "high",
            message: "Learning rate may be too high for stable convergence",
            threshold: 0.5,
            actual: this.metrics.updateRatio,
            details: {
              learningRate: this.metrics.lastLearningRate,
              meanGradientNorm: this.metrics.meanGradientNorm,
              recommendedAction: "Reduce learning rate by factor of 5-10",
              iteration: this.iteration
            }
          });
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
              iteration: this.iteration,
              optimizer: "SGD",
              learningRate: this.metrics.lastLearningRate
            },
            worstViolation.type
          );
        }
  
        return score;
      } catch (error) {
        // Re-throw NeuralCoherenceError
        if (error instanceof Prime.Neural.Errors.NeuralCoherenceError) {
          throw error;
        }
        
        // Wrap other errors
        throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
          "Error during coherence calculation",
          { 
            iteration: this.iteration,
            originalError: error.message
          },
          "COHERENCE_CALCULATION_ERROR",
          error
        );
      }
    }
  }

  // Add class to Prime.Neural.Optimization namespace
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Optimization = Prime.Neural.Optimization || {};
  Prime.Neural.Optimization.SGDOptimizer = SGDOptimizer;
})();

// Export the enhanced Prime object
module.exports = Prime;
