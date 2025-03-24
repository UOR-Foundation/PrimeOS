/**
 * PrimeOS JavaScript Library - Neural Network Module
 * Main entry point for the neural network functionality
 * Version 1.1.0
 */

// Import the Prime object from core
const Prime = require("../core");

// Ensure the Prime object exists
if (!Prime) {
  throw new Error("Core Prime module not loaded properly");
}

// Initialize Neural namespace
(function(Prime) {
  // Create the Neural namespace if it doesn't exist
  Prime.Neural = Prime.Neural || {};
  
  // Create necessary sub-namespaces
  Prime.Neural.Layer = Prime.Neural.Layer || {};
  Prime.Neural.Activation = Prime.Neural.Activation || {};
  Prime.Neural.Optimization = Prime.Neural.Optimization || {};
  Prime.Neural.Model = Prime.Neural.Model || {};
  Prime.Neural.Errors = Prime.Neural.Errors || {};
  
  // Create the Neural Distributed namespace
  Prime.Neural.Distributed = Prime.Neural.Distributed || {};
  
  // Core initialization complete
  if (Prime.Logger && Prime.Logger.debug) {
    Prime.Logger.debug("Neural namespace initialized successfully");
  }
})(Prime);

// Import neural error definitions first to ensure error types exist
require("./error");

// Import layer base (important for module loading order)
require("./layer/index");

// Import specialized modules in proper dependency order
require("./activation/index");
require("./optimization/index");

// Import unified layer implementations
require("./layer/dense-unified"); // Unified implementation that handles both DenseLayer and Dense
require("./layer/convolutional");
require("./layer/recurrent");

// Import model management modules
require("./model");
require("./model-builder");
require("./training-loop");
require("./model-io");
require("./model/index");
require("./model-simple"); // Simple model for tests

// Create the Neural module using IIFE
(function (Prime) {
  /**
   * Neural - Main facade for neural network functionality
   * Provides a unified interface to access neural network components
   */
  class Neural {
    /**
     * Create a new neural network layer
     * @param {string} type - Type of layer to create ('dense', 'conv', 'recurrent', 'self-optimizing', etc.)
     * @param {Object} config - Layer configuration
     * @returns {Object} Created layer
     */
    static createLayer(type, config) {
      const lowerType = type.toLowerCase();

      // Registry of layer types and their constructors
      const layerRegistry = {
        // Core layers
        "dense": Prime.Neural.Layer.Dense,
        "denselayer": Prime.Neural.Layer.DenseLayer, // For backward compatibility 
        
        // Advanced layers
        "conv": Prime.Neural.Layer.ConvolutionalLayer,
        "convolutional": Prime.Neural.Layer.ConvolutionalLayer,
        "rnn": Prime.Neural.Layer.RecurrentLayer,
        "recurrent": Prime.Neural.Layer.RecurrentLayer,
        "lstm": Prime.Neural.Layer.RecurrentLayer, // Alias for RecurrentLayer with cellType=lstm
        "gru": Prime.Neural.Layer.RecurrentLayer, // Alias for RecurrentLayer with cellType=gru
        
        // Special layers
        "self-optimizing": Prime.Neural.Layer.SelfOptimizingLayer,
        "selfoptimizing": Prime.Neural.Layer.SelfOptimizingLayer,
        "adaptive": Prime.Neural.Layer.SelfOptimizingLayer, // Alias for self-optimizing
        
        // Utility layers
        "flatten": Prime.Neural.Layer.FlattenLayer,
        "dropout": Prime.Neural.Layer.DropoutLayer,
        "normalization": Prime.Neural.Layer.NormalizationLayer,
        "batchnorm": Prime.Neural.Layer.BatchNormalizationLayer
      };
      
      // Ensure all layer classes are properly loaded
      this._ensureLayersLoaded();
      
      // Get the constructor for the requested layer type
      const LayerConstructor = layerRegistry[lowerType];
      
      if (!LayerConstructor) {
        // Check if it's a dynamically registered layer 
        if (Prime.Neural.Layer[`${type}Layer`]) {
          return new Prime.Neural.Layer[`${type}Layer`](config);
        }
        
        throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
          `Unknown layer type: ${type}. Available types: ${Object.keys(layerRegistry).join(', ')}`,
          { providedType: type, availableTypes: Object.keys(layerRegistry) },
          "UNKNOWN_LAYER_TYPE"
        );
      }
      
      // Special handling for aliases
      if (lowerType === "lstm") {
        const lstmConfig = { ...config, cellType: "lstm" };
        return new LayerConstructor(lstmConfig);
      } else if (lowerType === "gru") {
        const gruConfig = { ...config, cellType: "gru" };
        return new LayerConstructor(gruConfig);
      }
      
      // Create and return the layer
      return new LayerConstructor(config);
    }
    
    /**
     * Internal method to ensure all layer classes are loaded
     * @private
     */
    static _ensureLayersLoaded() {
      // Ensure ConvolutionalLayer is loaded
      if (!Prime.Neural.Layer.ConvolutionalLayer && typeof window !== 'undefined') {
        try {
          require('./layer/convolutional.js');
        } catch (e) {
          // Silently ignore errors in browser environment
        }
      }

      // Ensure RecurrentLayer is loaded
      if (!Prime.Neural.Layer.RecurrentLayer && typeof window !== 'undefined') {
        try {
          require('./layer/recurrent.js');
        } catch (e) {
          // Silently ignore errors in browser environment
        }
      }
      
      // Check for required base layers and notify if missing
      if (!Prime.Neural.Layer.NeuralLayer) {
        Prime.Logger.warn("Base NeuralLayer not found. Some functionality may be limited.");
      }
    }
    
    /**
     * Register a custom layer type with the factory
     * @param {string} typeName - Name to register the layer under
     * @param {Function} constructor - Layer constructor function
     * @param {Object} [options={}] - Registration options
     * @param {Array<string>} [options.aliases=[]] - Alternative names for this layer
     * @returns {boolean} Registration success
     */
    static registerLayerType(typeName, constructor, options = {}) {
      if (!typeName || typeof typeName !== 'string') {
        throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
          'Layer type name must be a non-empty string',
          { providedType: typeof typeName, providedValue: typeName },
          "INVALID_LAYER_TYPE_NAME"
        );
      }
      
      if (!constructor || typeof constructor !== 'function') {
        throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
          'Layer constructor must be a function',
          { providedType: typeof constructor },
          "INVALID_LAYER_CONSTRUCTOR"
        );
      }
      
      // Register in the namespace
      const layerName = typeName.endsWith('Layer') ? typeName : `${typeName}Layer`;
      Prime.Neural.Layer[layerName] = constructor;
      
      // Register aliases if provided
      if (options.aliases && Array.isArray(options.aliases)) {
        for (const alias of options.aliases) {
          if (alias && typeof alias === 'string') {
            const aliasLayerName = alias.endsWith('Layer') ? alias : `${alias}Layer`;
            Prime.Neural.Layer[aliasLayerName] = constructor;
          }
        }
      }
      
      // Publish event for extensions to listen
      if (Prime.EventBus && Prime.EventBus.publish) {
        Prime.EventBus.publish('neural:layer:registered', {
          type: typeName,
          constructor,
          options
        });
      }
      
      return true;
    }

    /**
     * Create a new optimizer
     * @param {string} type - Type of optimizer ('sgd', 'adam', etc.)
     * @param {Object} config - Optimizer configuration
     * @returns {Object} Created optimizer
     */
    static createOptimizer(type, config) {
      try {
        // Ensure namespace exists to prevent errors
        Prime.Neural.Optimization = Prime.Neural.Optimization || {};
        Prime.Neural.Optimization.OptimizerFactory = Prime.Neural.Optimization.OptimizerFactory || {
          create: function() {
            throw new Error("OptimizerFactory not properly initialized");
          }
        };
        
        return Prime.Neural.Optimization.OptimizerFactory.create(type, config);
      } catch (error) {
        // Wrap error with context
        throw new (Prime.Neural.Errors.OptimizerError || Prime.ValidationError)(
          `Error creating optimizer: ${error.message}`,
          { type, config, originalError: error.message },
          "OPTIMIZER_CREATION_ERROR",
          error
        );
      }
    }

    /**
     * Get activation function
     * @param {string} name - Name of activation function
     * @returns {Object} Activation function interface
     */
    static getActivation(name) {
      try {
        // Ensure namespace exists
        Prime.Neural.Activation = Prime.Neural.Activation || { 
          get: function() {
            throw new Error("Activation module not properly initialized");
          }
        };
        
        return Prime.Neural.Activation.get(name);
      } catch (error) {
        // Wrap error with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          `Error getting activation function: ${error.message}`,
          { name, originalError: error.message },
          "ACTIVATION_ACCESS_ERROR",
          error
        );
      }
    }

    /**
     * Apply activation function to input
     * @param {Array|TypedArray} input - Input values
     * @param {string} activationType - Type of activation function
     * @param {boolean} [inPlace=false] - Whether to modify input in-place
     * @returns {Array|TypedArray} Activated values
     */
    static activate(input, activationType, inPlace = false) {
      try {
        const activation = this.getActivation(activationType);
        
        if (inPlace && activation.inPlace) {
          activation.inPlace(input);
          return input;
        } else {
          return activation.forward(input);
        }
      } catch (error) {
        // Wrap error with context
        throw new (Prime.Neural.Errors.ActivationError || Prime.ValidationError)(
          `Error applying activation: ${error.message}`,
          { 
            activationType, 
            inPlace,
            inputShape: input ? input.length : null,
            originalError: error.message 
          },
          "ACTIVATION_APPLICATION_ERROR",
          error
        );
      }
    }

    /**
     * Check if a neural component is coherent
     * @param {Object} component - Neural component to check
     * @returns {Object} Coherence information
     */
    static checkCoherence(component) {
      try {
        if (!component) {
          throw new (Prime.Neural.Errors.NeuralCoherenceError || Prime.ValidationError)(
            "Cannot check coherence of null or undefined component",
            { providedValue: component },
            "NULL_COMPONENT"
          );
        }
        
        if (typeof component.calculateCoherence === "function") {
          const score = component.calculateCoherence();
          return {
            score,
            component: component.constructor ? component.constructor.name : "Unknown",
            isCoherent: score > 0.8 // Default threshold
          };
        }

        // If no coherence function, assume coherent
        return { 
          score: 1.0, 
          component: component.constructor ? component.constructor.name : "Unknown",
          isCoherent: true
        };
      } catch (error) {
        // For coherence checks, we don't throw but return a coherence failure
        return {
          score: 0.0,
          component: component ? (component.constructor ? component.constructor.name : "Unknown") : "Null",
          isCoherent: false,
          error: error.message
        };
      }
    }

    /**
     * Convert a standard JS array to a typed array for better performance
     * @param {Array} array - Input array
     * @param {string} [type='float32'] - Type of typed array ('float32', 'float64')
     * @returns {TypedArray} Typed array
     */
    static toTypedArray(array, type = "float32") {
      if (!Array.isArray(array)) {
        throw new (Prime.Neural.Errors.NeuralError || Prime.ValidationError)(
          "Input must be an array",
          { providedType: typeof array, isArray: Array.isArray(array) },
          "INVALID_ARRAY_TYPE"
        );
      }

      if (array.length === 0) {
        return type === "float64" ? new Float64Array(0) : new Float32Array(0);
      }

      // Handle nested arrays (2D)
      if (Array.isArray(array[0])) {
        const rows = array.length;
        const cols = array[0].length;

        // Check if all rows have the same length
        for (let i = 1; i < rows; i++) {
          if (!Array.isArray(array[i]) || array[i].length !== cols) {
            throw new (Prime.Neural.Errors.NeuralError || Prime.ValidationError)(
              "All rows must have the same length for 2D arrays",
              { 
                rowIndex: i, 
                expectedLength: cols, 
                actualLength: array[i] ? array[i].length : null,
                isArray: array[i] ? Array.isArray(array[i]) : false
              },
              "INCONSISTENT_ARRAY_DIMENSIONS"
            );
          }
        }

        // Create a flat typed array
        const flatArray =
          type === "float64"
            ? new Float64Array(rows * cols)
            : new Float32Array(rows * cols);

        // Fill the flat array with values from the input array
        for (let i = 0; i < rows; i++) {
          for (let j = 0; j < cols; j++) {
            flatArray[i * cols + j] = array[i][j];
          }
        }

        // Create 2D view with the same structure as the input array
        const result = new Array(rows);
        const TypedArrayClass =
          type === "float64" ? Float64Array : Float32Array;
        const bytesPerElement = type === "float64" ? 8 : 4;

        for (let i = 0; i < rows; i++) {
          result[i] = new TypedArrayClass(
            flatArray.buffer,
            i * cols * bytesPerElement,
            cols,
          );
        }

        // Store reference to the flat array for efficient operations
        Object.defineProperty(result, "_flatArray", { value: flatArray });

        return result;
      } else {
        // Handle 1D arrays
        return type === "float64"
          ? new Float64Array(array)
          : new Float32Array(array);
      }
    }

    /**
     * Convert a typed array to a standard JS array
     * @param {TypedArray|Array} typedArray - Input typed array
     * @returns {Array} Standard JS array
     */
    static fromTypedArray(typedArray) {
      // If already a standard array, return a copy
      if (Array.isArray(typedArray)) {
        if (Array.isArray(typedArray[0])) {
          // 2D array
          return typedArray.map((row) => [...row]);
        } else {
          // 1D array
          return [...typedArray];
        }
      }

      // Convert TypedArray to standard array
      return Array.from(typedArray);
    }
    
    /**
     * Creates a neural model with specified configuration
     * @param {Object} config - Model configuration
     * @returns {Object} Neural model instance
     */
    static createModel(config = {}) {
      try {
        // Ensure namespace exists
        Prime.Neural.Model = Prime.Neural.Model || {};
        
        // Default to basic model if no type specified
        const modelType = (config.type || "sequential").toLowerCase();
        let ModelClass;
        
        switch (modelType) {
          case "sequential":
            ModelClass = Prime.Neural.Model.Sequential || Prime.Neural.SequentialModel;
            break;
          case "functional":
            ModelClass = Prime.Neural.Model.Functional || Prime.Neural.FunctionalModel;
            break;
          case "distributed":
            ModelClass = Prime.Neural.Distributed.Model || Prime.Neural.DistributedModel;
            break;
          default:
            throw new Error(`Unknown model type: ${modelType}`);
        }
        
        if (!ModelClass) {
          throw new Error(`Model class for type '${modelType}' not found`);
        }
        
        return new ModelClass(config);
      } catch (error) {
        // Wrap error with context
        throw new (Prime.Neural.Errors.ModelError || Prime.ValidationError)(
          `Error creating neural model: ${error.message}`,
          { config, modelType: config.type, originalError: error.message },
          "MODEL_CREATION_ERROR",
          error
        );
      }
    }
  }

  // Add Neural class to Prime namespace
  Object.assign(Prime.Neural, { Neural });
  
  /**
   * Reset the Neural module state for testing
   * This helps test environments clear and rebuild the state
   */
  Prime.Neural.resetForTesting = function() {
    console.log("[Testing] Resetting Neural module state...");
    
    // Re-initialize namespaces
    Prime.Neural.Layer = Prime.Neural.Layer || {};
    Prime.Neural.Activation = Prime.Neural.Activation || {};
    Prime.Neural.Optimization = Prime.Neural.Optimization || {};
    Prime.Neural.Model = Prime.Neural.Model || {};
    Prime.Neural.Errors = Prime.Neural.Errors || {};
    Prime.Neural.Distributed = Prime.Neural.Distributed || {};
    
    // Re-require all the core modules to ensure proper initialization
    try {
      // Clear require cache for neural modules to force reload
      Object.keys(require.cache).forEach(key => {
        if (key.includes('/neural/')) {
          delete require.cache[key];
        }
      });
      
      // Re-import in proper order
      require("./error");
      require("./layer/index");
      require("./activation/index");
      require("./optimization/index");
      require("./layer/dense-unified");
      require("./layer/convolutional");
      require("./layer/recurrent"); 
      require("./model");
      
      console.log("[Testing] Neural module reset complete");
    } catch (error) {
      console.error("[Testing] Error during neural module reset:", error.message);
    }
  };
  
  // Utility methods for namespace management
  Prime.Neural._ensureNamespace = function(path) {
    // Takes a string like "Neural.Layer.Dense" and ensures all objects in the path exist
    const parts = path.split('.');
    let current = Prime;
    
    for (const part of parts) {
      current[part] = current[part] || {};
      current = current[part];
    }
    
    return current;
  };
})(Prime);

// Ensure modules are ready at test time
if (process.env.NODE_ENV === 'test') {
  console.log("[Testing] Eagerly loading neural modules...");
  
  // Force eager module loading in correct order
  require("./error");
  require("./layer/index");
  require("./activation/index");
  require("./optimization/index");
  require("./layer/dense-unified");
  require("./layer/convolutional");
  require("./layer/recurrent");
  require("./model");
  
  console.log("[Testing] Neural eager loading complete");
}

// Export the Prime object with all neural modules initialized
module.exports = Prime;