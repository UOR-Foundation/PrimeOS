/**
 * PrimeOS JavaScript Library - Neural Networks
 * Neural network implementation with coherence integration
 * Version 1.0.0
 */

// Import core using CommonJS to avoid circular dependency
const Prime = require("./core.js");

// Ensure the Prime object exists
if (!Prime) {
  throw new Error("Core Prime module not loaded properly");
}

// Make sure Math module is loaded (needed by neural layers)
require("./mathematics");

// Create the Neural namespace if it doesn't exist
Prime.Neural = Prime.Neural || {};

// Create the Layer namespace if it doesn't exist
Prime.Neural.Layer = Prime.Neural.Layer || {};

// Create the Errors namespace if it doesn't exist
Prime.Neural.Errors = Prime.Neural.Errors || {};

// Import modules in the correct dependency order
// 1. First the error module for error handling
require("./neural/error");

// 2. Then base layer and activation modules
require("./neural/layer/index");
require("./neural/activation/index");
require("./neural/optimization/index");

// 3. Then specific layer implementations
require("./neural/layer/dense-unified");
require("./neural/layer/convolutional");
require("./neural/layer/recurrent");

// 4. Then model and higher-level components
require("./neural/model");
require("./neural/model-builder");
require("./neural/training-loop");
require("./neural/model-io");
require("./neural/model/index");
require("./neural/model-simple");

// 5. Finally, the main index file that ties everything together
require("./neural/index");

// Layer creation facade
Prime.Neural.createLayer = function(type, config) {
  if (!Prime.Neural.Neural) {
    // If Neural factory class isn't available, create a simple factory
    console.warn("Using fallback layer creation method - Neural factory not fully loaded");
    
    try {
      // Basic type mapping
      const layerMap = {
        'dense': Prime.Neural.Layer.Dense || Prime.Neural.Layer.DenseLayer,
        'convolutional': Prime.Neural.Layer.ConvolutionalLayer,
        'recurrent': Prime.Neural.Layer.RecurrentLayer,
        'lstm': Prime.Neural.Layer.RecurrentLayer,
        'gru': Prime.Neural.Layer.RecurrentLayer,
      };
      
      const Constructor = layerMap[type.toLowerCase()];
      if (!Constructor) {
        throw new (Prime.Neural.Errors.LayerError || Error)(`Unknown layer type: ${type}`, {
          requestedType: type,
          availableTypes: Object.keys(layerMap)
        });
      }
      
      // Handle special cases
      if (type.toLowerCase() === 'lstm') {
        return new Constructor({...config, cellType: 'lstm'});
      } else if (type.toLowerCase() === 'gru') {
        return new Constructor({...config, cellType: 'gru'});
      }
      
      return new Constructor(config);
    } catch (error) {
      // Wrap generic errors in a LayerError
      if (!(error instanceof (Prime.Neural.Errors.NeuralError || Error))) {
        throw new (Prime.Neural.Errors.LayerError || Error)(
          `Error creating layer of type ${type}: ${error.message}`,
          { originalError: error, requestedType: type, config },
          "LAYER_CREATION_ERROR",
          error
        );
      }
      throw error;
    }
  }
  
  // Use the proper factory method if available
  try {
    return Prime.Neural.Neural.createLayer(type, config);
  } catch (error) {
    // Wrap generic errors in a LayerError
    if (!(error instanceof (Prime.Neural.Errors.NeuralError || Error))) {
      throw new (Prime.Neural.Errors.LayerError || Error)(
        `Error creating layer of type ${type}: ${error.message}`,
        { originalError: error, requestedType: type, config },
        "LAYER_CREATION_ERROR",
        error
      );
    }
    throw error;
  }
};

// Export the enhanced Prime object
module.exports = Prime;