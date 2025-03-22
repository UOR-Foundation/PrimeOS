/**
 * PrimeOS Neural Distributed - Dimension Validator
 * 
 * Utility to validate matrix and layer dimensions for distributed neural models.
 * Helps prevent cryptic errors by providing clear validation messages.
 */

const Prime = require('../../core.js');

// Ensure we have Prime.ValidationError available
if (!Prime.ValidationError) {
  Prime.ValidationError = class ValidationError extends Error {
    constructor(message) {
      super(message);
      this.name = 'ValidationError';
    }
  };
}

// Create the DimensionValidator namespace
Prime.Neural = Prime.Neural || {};
Prime.Neural.Distributed = Prime.Neural.Distributed || {};
Prime.Neural.Distributed.DimensionValidator = {

  /**
   * Validates model configuration dimensions
   * @param {Object} config - The model configuration
   * @returns {Boolean} True if valid
   * @throws {ValidationError} If dimensions are invalid
   */
  validateModelConfig(config) {
    if (!config) {
      throw new Prime.ValidationError('Model configuration is required');
    }
    
    // Validate inputSize
    if (!Number.isInteger(config.inputSize) || config.inputSize <= 0) {
      throw new Prime.ValidationError(`Invalid input size: ${config.inputSize}. Must be a positive integer.`);
    }
    
    // Validate layers if provided
    if (Array.isArray(config.layers)) {
      for (let i = 0; i < config.layers.length; i++) {
        this.validateLayerConfig(config.layers[i], i);
      }
    }
    
    return true;
  },
  
  /**
   * Validates a single layer configuration
   * @param {Object} layerConfig - The layer configuration
   * @param {Number} index - Layer index for error reporting
   * @returns {Boolean} True if valid
   * @throws {ValidationError} If dimensions are invalid
   */
  validateLayerConfig(layerConfig, index) {
    if (!layerConfig) {
      throw new Prime.ValidationError(`Layer configuration at index ${index} is undefined`);
    }
    
    // Validate outputSize (required)
    if (!Number.isInteger(layerConfig.outputSize) || layerConfig.outputSize <= 0) {
      throw new Prime.ValidationError(
        `Invalid output size: ${layerConfig.outputSize} at layer ${index}. Must be a positive integer.`
      );
    }
    
    // Validate inputSize if specified
    if (layerConfig.inputSize !== undefined && 
        (!Number.isInteger(layerConfig.inputSize) || layerConfig.inputSize <= 0)) {
      throw new Prime.ValidationError(
        `Invalid input size: ${layerConfig.inputSize} at layer ${index}. Must be a positive integer.`
      );
    }
    
    return true;
  },
  
  /**
   * Validates matrix dimensions for weights
   * @param {Number} rows - Number of rows (outputSize)
   * @param {Number} cols - Number of columns (inputSize)
   * @param {String} context - Context for error reporting
   * @returns {Boolean} True if valid
   * @throws {ValidationError} If dimensions are invalid
   */
  validateMatrixDimensions(rows, cols, context = 'weights') {
    if (!Number.isInteger(rows) || rows <= 0) {
      throw new Prime.ValidationError(
        `Invalid ${context} matrix rows: ${rows}. Must be a positive integer.`
      );
    }
    
    if (!Number.isInteger(cols) || cols <= 0) {
      throw new Prime.ValidationError(
        `Invalid ${context} matrix columns: ${cols}. Must be a positive integer.`
      );
    }
    
    return true;
  },
  
  /**
   * Validates vector dimensions for biases
   * @param {Number} size - Vector size
   * @param {String} context - Context for error reporting
   * @returns {Boolean} True if valid
   * @throws {ValidationError} If dimensions are invalid
   */
  validateVectorDimensions(size, context = 'biases') {
    if (!Number.isInteger(size) || size <= 0) {
      throw new Prime.ValidationError(
        `Invalid ${context} vector size: ${size}. Must be a positive integer.`
      );
    }
    
    return true;
  },
  
  /**
   * Validates parameter coherence by checking for NaN, Infinity, and very large values
   * @param {Object} parameters - Model parameters (weights and biases)
   * @param {Number} maxValue - Maximum allowed absolute value
   * @returns {Boolean} True if parameters are coherent
   */
  validateParameterCoherence(parameters, maxValue = 1e6) {
    if (!parameters) {
      return false;
    }
    
    // Check weights for invalid values
    if (parameters.weights) {
      for (const weightMatrix of parameters.weights) {
        if (!weightMatrix) continue;
        
        for (const row of weightMatrix) {
          for (const value of row) {
            if (!Number.isFinite(value) || Math.abs(value) > maxValue) {
              if (Prime.Logger && Prime.Logger.warn) {
                Prime.Logger.warn(`Invalid weight value detected: ${value}`);
              }
              return false;
            }
          }
        }
      }
    }
    
    // Check biases for invalid values
    if (parameters.biases) {
      for (const biasVector of parameters.biases) {
        if (!biasVector) continue;
        
        for (const value of biasVector) {
          if (!Number.isFinite(value) || Math.abs(value) > maxValue) {
            if (Prime.Logger && Prime.Logger.warn) {
              Prime.Logger.warn(`Invalid bias value detected: ${value}`);
            }
            return false;
          }
        }
      }
    }
    
    return true;
  },
  
  /**
   * Logs layer dimensions for debugging
   * @param {Array} layers - Array of layer objects
   */
  logLayerDimensions(layers) {
    if (!Array.isArray(layers) || layers.length === 0) {
      if (Prime.Logger && Prime.Logger.warn) {
        Prime.Logger.warn('No layers to log dimensions for');
      }
      return;
    }
    
    if (Prime.Logger && Prime.Logger.info) {
      Prime.Logger.info('Neural Network Layer Dimensions:');
      
      for (let i = 0; i < layers.length; i++) {
        const layer = layers[i];
        Prime.Logger.info(
          `  Layer ${i}: Type=${layer.type || 'dense'}, Input=${layer.inputSize}, Output=${layer.outputSize}`
        );
        
        // Log weight dimensions if available
        if (layer.weights && Prime.Logger.debug) {
          const rows = layer.weights.length;
          const cols = rows > 0 ? layer.weights[0].length : 0;
          Prime.Logger.debug(`    Weights: [${rows}x${cols}]`);
        }
        
        // Log bias dimensions if available
        if (layer.biases && Prime.Logger.debug) {
          Prime.Logger.debug(`    Biases: [${layer.biases.length}]`);
        }
      }
    }
  },
  
  /**
   * Verifies dimensions for all layers in a model
   * @param {Object} model - Neural model with layers array
   * @returns {Boolean} True if all dimensions are consistent
   */
  verifyModelDimensions(model) {
    if (!model || !Array.isArray(model.layers) || model.layers.length === 0) {
      return false;
    }
    
    // Check each layer
    for (let i = 0; i < model.layers.length; i++) {
      const layer = model.layers[i];
      
      // Check if layer has required dimensions
      if (!Number.isInteger(layer.inputSize) || layer.inputSize <= 0) {
        if (Prime.Logger && Prime.Logger.error) {
          Prime.Logger.error(`Layer ${i} has invalid inputSize: ${layer.inputSize}`);
        }
        return false;
      }
      
      if (!Number.isInteger(layer.outputSize) || layer.outputSize <= 0) {
        if (Prime.Logger && Prime.Logger.error) {
          Prime.Logger.error(`Layer ${i} has invalid outputSize: ${layer.outputSize}`);
        }
        return false;
      }
      
      // Check weight dimensions
      if (layer.weights) {
        if (layer.weights.length !== layer.outputSize) {
          if (Prime.Logger && Prime.Logger.error) {
            Prime.Logger.error(`Layer ${i} weights rows (${layer.weights.length}) don't match outputSize (${layer.outputSize})`);
          }
          return false;
        }
        
        if (layer.weights[0].length !== layer.inputSize) {
          if (Prime.Logger && Prime.Logger.error) {
            Prime.Logger.error(`Layer ${i} weights columns (${layer.weights[0].length}) don't match inputSize (${layer.inputSize})`);
          }
          return false;
        }
      }
      
      // Check bias dimensions
      if (layer.biases && layer.biases.length !== layer.outputSize) {
        if (Prime.Logger && Prime.Logger.error) {
          Prime.Logger.error(`Layer ${i} biases length (${layer.biases.length}) doesn't match outputSize (${layer.outputSize})`);
        }
        return false;
      }
      
      // Check consistency with next layer
      if (i < model.layers.length - 1) {
        const nextLayer = model.layers[i + 1];
        if (layer.outputSize !== nextLayer.inputSize) {
          if (Prime.Logger && Prime.Logger.error) {
            Prime.Logger.error(`Dimension mismatch between layers ${i} and ${i+1}: ${layer.outputSize} != ${nextLayer.inputSize}`);
          }
          return false;
        }
      }
    }
    
    return true;
  }
};

// Export the module
module.exports = { Neural: Prime.Neural };