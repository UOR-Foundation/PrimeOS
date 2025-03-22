/**
 * PrimeOS JavaScript Library - Neural Network Model I/O
 * Model serialization, deserialization, and storage utilities
 */

// Import the Prime object from core
const Prime = require("../core");

// Create the Neural Model I/O module using IIFE
(function () {
  /**
   * Neural Network Model I/O
   * Handles model serialization, deserialization, and storage
   */
  class ModelIO {
    /**
     * Serialize a model to a JSON string
     * @param {Prime.Neural.Model.NeuralModel} model - Model to serialize
     * @param {Object} [options={}] - Serialization options
     * @param {boolean} [options.pretty=false] - Whether to format JSON with spaces
     * @param {boolean} [options.includeWeights=true] - Whether to include weights in serialization
     * @param {boolean} [options.includeHistory=false] - Whether to include training history
     * @returns {string} Serialized model as JSON string
     */
    static serialize(model, options = {}) {
      if (!model || !model.toJSON) {
        throw new Error('Invalid model provided for serialization');
      }
      
      // Get model data
      const modelData = model.toJSON();
      
      // Apply serialization options
      if (options.includeWeights === false) {
        // Remove weights and biases
        if (modelData.layers) {
          modelData.layers.forEach(layer => {
            delete layer.weights;
            delete layer.biases;
          });
        }
      }
      
      if (options.includeHistory === false) {
        delete modelData.history;
      }
      
      // Add serialization metadata
      modelData.serializationInfo = {
        library: 'PrimeOS Neural',
        version: Prime.version || '1.0.0',
        timestamp: new Date().toISOString(),
        options: { ...options }
      };
      
      // Serialize to JSON
      return JSON.stringify(modelData, null, options.pretty ? 2 : 0);
    }
    
    /**
     * Deserialize a model from a JSON string
     * @param {string} json - Serialized model JSON string
     * @param {Object} [options={}] - Deserialization options
     * @param {boolean} [options.strict=false] - Whether to strictly validate model structure
     * @returns {Prime.Neural.Model.NeuralModel} Deserialized model
     */
    static deserialize(json, options = {}) {
      try {
        const modelData = JSON.parse(json);
        
        // Validate model data
        if (!modelData.layers) {
          throw new Error('Invalid model data: missing layers');
        }
        
        // Check version compatibility if in strict mode
        if (options.strict && modelData.serializationInfo) {
          const currentVersion = Prime.version || '1.0.0';
          const serializedVersion = modelData.serializationInfo.version;
          
          // Simple version check (in real implementation, would do proper semver comparison)
          if (currentVersion !== serializedVersion) {
            console.warn(`Model was serialized with version ${serializedVersion}, ` +
                         `but current library version is ${currentVersion}`);
          }
        }
        
        // Create model from data
        return Prime.Neural.Model.NeuralModel.fromJSON(modelData);
      } catch (error) {
        throw new Error(`Failed to deserialize model: ${error.message}`);
      }
    }
    
    /**
     * Save model to a file (in Node.js environment)
     * @param {Prime.Neural.Model.NeuralModel} model - Model to save
     * @param {string} filePath - Path to save file
     * @param {Object} [options={}] - Serialization options
     * @returns {Promise<void>}
     */
    static async saveToFile(model, filePath, options = {}) {
      // Check if running in Node.js
      if (typeof process === 'undefined' || !process.versions || !process.versions.node) {
        throw new Error('saveToFile is only available in Node.js environment');
      }
      
      // Dynamically import fs module
      const fs = require('fs').promises;
      
      try {
        // Serialize model
        const json = this.serialize(model, options);
        
        // Write to file
        await fs.writeFile(filePath, json, 'utf8');
      } catch (error) {
        throw new Error(`Failed to save model: ${error.message}`);
      }
    }
    
    /**
     * Load model from a file (in Node.js environment)
     * @param {string} filePath - Path to model file
     * @param {Object} [options={}] - Deserialization options
     * @returns {Promise<Prime.Neural.Model.NeuralModel>} Loaded model
     */
    static async loadFromFile(filePath, options = {}) {
      // Check if running in Node.js
      if (typeof process === 'undefined' || !process.versions || !process.versions.node) {
        throw new Error('loadFromFile is only available in Node.js environment');
      }
      
      // Dynamically import fs module
      const fs = require('fs').promises;
      
      try {
        // Read file
        const json = await fs.readFile(filePath, 'utf8');
        
        // Deserialize model
        return this.deserialize(json, options);
      } catch (error) {
        throw new Error(`Failed to load model: ${error.message}`);
      }
    }
    
    /**
     * Save model weights to an array
     * @param {Prime.Neural.Model.NeuralModel} model - Model to extract weights from
     * @returns {Object} Extracted weights
     */
    static extractWeights(model) {
      if (!model || !model.layers) {
        throw new Error('Invalid model provided for weight extraction');
      }
      
      const weights = {
        layers: [],
        metadata: {
          timestamp: new Date().toISOString(),
          structure: model.layers.map(layer => ({
            type: layer.constructor.name,
            inputSize: layer.inputSize,
            outputSize: layer.outputSize
          }))
        }
      };
      
      // Extract weights from each layer
      model.layers.forEach((layer, index) => {
        weights.layers.push({
          index,
          weights: Array.isArray(layer.weights[0]) ?
            layer.weights.map(w => [...w]) :
            [...layer.weights],
          biases: [...layer.biases]
        });
      });
      
      return weights;
    }
    
    /**
     * Apply weights to a model
     * @param {Prime.Neural.Model.NeuralModel} model - Model to apply weights to
     * @param {Object} weights - Weights to apply
     * @param {boolean} [validateStructure=true] - Whether to validate weights structure against model
     * @returns {Prime.Neural.Model.NeuralModel} Model with applied weights
     */
    static applyWeights(model, weights, validateStructure = true) {
      if (!model || !model.layers) {
        throw new Error('Invalid model provided for weight application');
      }
      
      if (!weights || !weights.layers) {
        throw new Error('Invalid weights object');
      }
      
      // Validate weights structure against model if required
      if (validateStructure) {
        if (weights.layers.length !== model.layers.length) {
          throw new Error(`Weights structure doesn't match model: expected ${model.layers.length} layers, got ${weights.layers.length}`);
        }
        
        // Check each layer dimensions
        for (let i = 0; i < model.layers.length; i++) {
          const modelLayer = model.layers[i];
          const weightLayer = weights.layers[i];
          
          if (!weightLayer.weights || !weightLayer.biases) {
            throw new Error(`Missing weights or biases for layer ${i}`);
          }
          
          // For 2D weights
          if (Array.isArray(modelLayer.weights[0])) {
            if (modelLayer.weights.length !== weightLayer.weights.length ||
                modelLayer.weights[0].length !== weightLayer.weights[0].length) {
              throw new Error(`Weight dimensions mismatch for layer ${i}`);
            }
          } else {
            // For 1D weights
            if (modelLayer.weights.length !== weightLayer.weights.length) {
              throw new Error(`Weight dimensions mismatch for layer ${i}`);
            }
          }
          
          if (modelLayer.biases.length !== weightLayer.biases.length) {
            throw new Error(`Bias dimensions mismatch for layer ${i}`);
          }
        }
      }
      
      // Apply weights to model
      for (let i = 0; i < Math.min(model.layers.length, weights.layers.length); i++) {
        const modelLayer = model.layers[i];
        const weightLayer = weights.layers[i];
        
        // Apply weights
        if (Array.isArray(modelLayer.weights[0])) {
          // 2D weights
          for (let j = 0; j < modelLayer.weights.length; j++) {
            for (let k = 0; k < modelLayer.weights[j].length; k++) {
              modelLayer.weights[j][k] = weightLayer.weights[j][k];
            }
          }
        } else {
          // 1D weights
          for (let j = 0; j < modelLayer.weights.length; j++) {
            modelLayer.weights[j] = weightLayer.weights[j];
          }
        }
        
        // Apply biases
        for (let j = 0; j < modelLayer.biases.length; j++) {
          modelLayer.biases[j] = weightLayer.biases[j];
        }
      }
      
      return model;
    }
    
    /**
     * Merge weights from multiple models using averaging
     * @param {Array<Object>} weightsArray - Array of weights objects
     * @returns {Object} Merged weights
     */
    static mergeWeights(weightsArray) {
      if (!Array.isArray(weightsArray) || weightsArray.length === 0) {
        throw new Error('Invalid weights array');
      }
      
      // Use first weights object as template
      const result = JSON.parse(JSON.stringify(weightsArray[0]));
      
      // Skip if only one set of weights
      if (weightsArray.length === 1) {
        return result;
      }
      
      // Average weights and biases from all models
      for (let layerIndex = 0; layerIndex < result.layers.length; layerIndex++) {
        const layerResult = result.layers[layerIndex];
        
        // Process weights
        if (Array.isArray(layerResult.weights[0])) {
          // 2D weights
          for (let i = 0; i < layerResult.weights.length; i++) {
            for (let j = 0; j < layerResult.weights[i].length; j++) {
              let sum = 0;
              
              // Sum values from all models
              for (let modelIndex = 0; modelIndex < weightsArray.length; modelIndex++) {
                const modelWeights = weightsArray[modelIndex].layers[layerIndex].weights;
                sum += modelWeights[i][j];
              }
              
              // Average
              layerResult.weights[i][j] = sum / weightsArray.length;
            }
          }
        } else {
          // 1D weights
          for (let i = 0; i < layerResult.weights.length; i++) {
            let sum = 0;
            
            // Sum values from all models
            for (let modelIndex = 0; modelIndex < weightsArray.length; modelIndex++) {
              const modelWeights = weightsArray[modelIndex].layers[layerIndex].weights;
              sum += modelWeights[i];
            }
            
            // Average
            layerResult.weights[i] = sum / weightsArray.length;
          }
        }
        
        // Process biases
        for (let i = 0; i < layerResult.biases.length; i++) {
          let sum = 0;
          
          // Sum values from all models
          for (let modelIndex = 0; modelIndex < weightsArray.length; modelIndex++) {
            const modelBiases = weightsArray[modelIndex].layers[layerIndex].biases;
            sum += modelBiases[i];
          }
          
          // Average
          layerResult.biases[i] = sum / weightsArray.length;
        }
      }
      
      // Update metadata
      result.metadata = {
        ...result.metadata,
        timestamp: new Date().toISOString(),
        merged: true,
        models: weightsArray.length
      };
      
      return result;
    }
    
    /**
     * Convert model to a web format (for saving in browser environments)
     * @param {Prime.Neural.Model.NeuralModel} model - Model to convert
     * @returns {Object} Web-ready model data
     */
    static toWebFormat(model) {
      if (!model || !model.toJSON) {
        throw new Error('Invalid model provided for web format conversion');
      }
      
      // Get base model data
      const modelData = model.toJSON();
      
      // Convert arrays to TypedArrays for efficient storage
      for (const layer of modelData.layers) {
        // Convert weights to Float32Array
        if (layer.weights) {
          if (Array.isArray(layer.weights[0])) {
            // 2D weights
            const rows = layer.weights.length;
            const cols = layer.weights[0].length;
            const flatWeights = new Float32Array(rows * cols);
            
            for (let i = 0; i < rows; i++) {
              for (let j = 0; j < cols; j++) {
                flatWeights[i * cols + j] = layer.weights[i][j];
              }
            }
            
            // Store dimensions for reconstruction
            layer.weights = {
              data: flatWeights,
              shape: [rows, cols]
            };
          } else {
            // 1D weights
            layer.weights = {
              data: new Float32Array(layer.weights),
              shape: [layer.weights.length]
            };
          }
        }
        
        // Convert biases to Float32Array
        if (layer.biases) {
          layer.biases = {
            data: new Float32Array(layer.biases),
            shape: [layer.biases.length]
          };
        }
      }
      
      // Add web format metadata
      modelData.format = {
        type: 'primeos-web',
        version: '1.0',
        timestamp: new Date().toISOString()
      };
      
      return modelData;
    }
    
    /**
     * Load model from web format
     * @param {Object} webModel - Model data in web format
     * @returns {Prime.Neural.Model.NeuralModel} Restored model
     */
    static fromWebFormat(webModel) {
      if (!webModel || !webModel.layers || !webModel.format) {
        throw new Error('Invalid web format model data');
      }
      
      // Verify format
      if (webModel.format.type !== 'primeos-web') {
        throw new Error(`Unsupported model format: ${webModel.format.type}`);
      }
      
      // Convert TypedArrays back to regular arrays
      const modelData = JSON.parse(JSON.stringify(webModel));
      
      for (const layer of modelData.layers) {
        // Restore weights
        if (layer.weights && layer.weights.data && layer.weights.shape) {
          if (layer.weights.shape.length > 1) {
            // Reconstruct 2D array
            const [rows, cols] = layer.weights.shape;
            const weights = [];
            
            for (let i = 0; i < rows; i++) {
              const row = [];
              for (let j = 0; j < cols; j++) {
                row.push(webModel.layers[layer.index].weights.data[i * cols + j]);
              }
              weights.push(row);
            }
            
            layer.weights = weights;
          } else {
            // Reconstruct 1D array
            layer.weights = Array.from(webModel.layers[layer.index].weights.data);
          }
        }
        
        // Restore biases
        if (layer.biases && layer.biases.data) {
          layer.biases = Array.from(webModel.layers[layer.index].biases.data);
        }
      }
      
      // Create model from restored data
      return Prime.Neural.Model.NeuralModel.fromJSON(modelData);
    }
  }
  
  // Add to Prime.Neural namespace
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Model = Prime.Neural.Model || {};
  Prime.Neural.Model.ModelIO = ModelIO;
})();

// Export the enhanced Prime object
module.exports = Prime;