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
require("./math");

// Create the Neural namespace if it doesn't exist
Prime.Neural = Prime.Neural || {};

// Create the Layer namespace if it doesn't exist
Prime.Neural.Layer = Prime.Neural.Layer || {};

// Import all neural module components
require("./neural/layer/index");
require("./neural/activation/index");
require("./neural/optimization/index");
require("./neural/layer/dense-unified");
require("./neural/layer/convolutional");
require("./neural/layer/recurrent");
require("./neural/model");
require("./neural/model-builder");
require("./neural/training-loop");
require("./neural/model-io");
require("./neural/model/index");
require("./neural/model-simple");
require("./neural/index");

// Layer creation facade
Prime.Neural.createLayer = function(type, config) {
  if (!Prime.Neural.Neural) {
    // If Neural factory class isn't available, create a simple factory
    console.warn("Using fallback layer creation method - Neural factory not fully loaded");
    
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
      throw new Error(`Unknown layer type: ${type}`);
    }
    
    // Handle special cases
    if (type.toLowerCase() === 'lstm') {
      return new Constructor({...config, cellType: 'lstm'});
    } else if (type.toLowerCase() === 'gru') {
      return new Constructor({...config, cellType: 'gru'});
    }
    
    return new Constructor(config);
  }
  
  // Use the proper factory method if available
  return Prime.Neural.Neural.createLayer(type, config);
};

// Export the enhanced Prime object
module.exports = Prime;