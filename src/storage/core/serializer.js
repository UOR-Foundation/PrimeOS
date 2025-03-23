/**
 * PrimeOS JavaScript Library - Storage Serializer
 * Utilities for serializing and deserializing data for storage
 */

const Prime = require('../../core');
const { PrimeStorageError } = require('./provider');

/**
 * Serializer class for encoding and decoding data for storage
 */
class Serializer {
  /**
   * Creates a new serializer
   * @param {Object} options - Serializer options
   * @param {boolean} [options.preserveInstances=true] - Whether to preserve class instances
   * @param {boolean} [options.compression=false] - Whether to compress data
   * @param {string} [options.format='json'] - Serialization format: 'json' or 'binary'
   */
  constructor(options = {}) {
    this.options = {
      preserveInstances: true,
      compression: false,
      format: 'json',
      ...options
    };
    
    // Initialize registered class map for instance serialization
    this.registeredClasses = new Map();
    
    // Register built-in PrimeOS classes
    this.registerBuiltinClasses();
  }

  /**
   * Registers PrimeOS built-in classes for serialization
   * @private
   */
  registerBuiltinClasses() {
    // Register Math classes
    if (Prime.Math && Prime.Math.Matrix) {
      this.registerClass('Matrix', Prime.Math.Matrix, {
        serialize: (instance) => ({
          rows: instance.rows,
          columns: instance.columns,
          data: instance.data
        }),
        deserialize: (data) => {
          const matrix = new Prime.Math.Matrix(data.rows, data.columns);
          matrix.data = data.data;
          return matrix;
        }
      });
    }
    
    if (Prime.Math && Prime.Math.Vector) {
      this.registerClass('Vector', Prime.Math.Vector, {
        serialize: (instance) => ({
          dimension: instance.dimension,
          data: instance.data
        }),
        deserialize: (data) => {
          const vector = new Prime.Math.Vector(data.dimension);
          vector.data = data.data;
          return vector;
        }
      });
    }
    
    // Register Neural classes if available
    if (Prime.Neural && Prime.Neural.Model) {
      this.registerClass('NeuralModel', Prime.Neural.Model, {
        serialize: (instance) => ({
          name: instance.name,
          layers: instance.layers.map(layer => ({
            type: layer.constructor.name,
            config: layer.getConfig(),
            weights: layer.weights ? {
              rows: layer.weights.rows,
              columns: layer.weights.columns,
              data: layer.weights.data
            } : null,
            biases: layer.biases ? {
              dimension: layer.biases.dimension,
              data: layer.biases.data
            } : null
          }))
        }),
        deserialize: (data) => {
          const model = new Prime.Neural.Model({
            name: data.name
          });
          
          data.layers.forEach(layerData => {
            let layer;
            
            // Create the correct layer type
            switch (layerData.type) {
              case 'DenseLayer':
                layer = new Prime.Neural.Layer.Dense(
                  layerData.config.inputSize,
                  layerData.config.outputSize,
                  layerData.config.options
                );
                break;
              case 'ConvolutionalLayer':
                layer = new Prime.Neural.Layer.Convolutional(
                  layerData.config.inputShape,
                  layerData.config.filterShape,
                  layerData.config.options
                );
                break;
              case 'RecurrentLayer':
                layer = new Prime.Neural.Layer.Recurrent(
                  layerData.config.inputSize,
                  layerData.config.hiddenSize,
                  layerData.config.options
                );
                break;
              default:
                throw new Error(`Unknown layer type: ${layerData.type}`);
            }
            
            // Set weights and biases if available
            if (layerData.weights) {
              layer.weights = new Prime.Math.Matrix(
                layerData.weights.rows,
                layerData.weights.columns
              );
              layer.weights.data = layerData.weights.data;
            }
            
            if (layerData.biases) {
              layer.biases = new Prime.Math.Vector(layerData.biases.dimension);
              layer.biases.data = layerData.biases.data;
            }
            
            model.addLayer(layer);
          });
          
          return model;
        }
      });
    }
    
    // Register Base0 classes if available
    if (Prime.Base0 && Prime.Base0.Manifold) {
      this.registerClass('Manifold', Prime.Base0.Manifold, {
        serialize: (instance) => ({
          dimensions: instance.dimensions,
          metric: instance.metric ? {
            rows: instance.metric.rows,
            columns: instance.metric.columns,
            data: instance.metric.data
          } : null,
          properties: instance.properties
        }),
        deserialize: (data) => {
          let metric = null;
          if (data.metric) {
            metric = new Prime.Math.Matrix(data.metric.rows, data.metric.columns);
            metric.data = data.metric.data;
          }
          
          return new Prime.Base0.Manifold({
            dimensions: data.dimensions,
            metric,
            properties: data.properties
          });
        }
      });
    }
  }

  /**
   * Registers a class for serialization
   * @param {string} className - Name to identify the class
   * @param {Function} classConstructor - Class constructor
   * @param {Object} handlers - Serialization handlers
   * @param {Function} handlers.serialize - Function to serialize an instance
   * @param {Function} handlers.deserialize - Function to deserialize to an instance
   */
  registerClass(className, classConstructor, handlers) {
    this.registeredClasses.set(className, {
      constructor: classConstructor,
      serialize: handlers.serialize,
      deserialize: handlers.deserialize
    });
  }

  /**
   * Serializes data to a string or buffer
   * @param {*} data - Data to serialize
   * @returns {Promise<{serialized: string|Buffer, metadata: Object}>} Serialized data and metadata
   */
  async serialize(data) {
    try {
      const metadata = {
        type: typeof data,
        format: this.options.format,
        compressed: this.options.compression,
        timestamp: Date.now()
      };
      
      // Handle primitives directly
      if (data === null || data === undefined) {
        return {
          serialized: JSON.stringify(data),
          metadata: { ...metadata, isPrimitive: true }
        };
      }
      
      if (typeof data === 'number' || typeof data === 'string' || typeof data === 'boolean') {
        return {
          serialized: JSON.stringify(data),
          metadata: { ...metadata, isPrimitive: true }
        };
      }
      
      // Special handling for Buffer or TypedArray
      if (typeof Buffer !== 'undefined' && Buffer.isBuffer(data)) {
        metadata.type = 'Buffer';
        return {
          serialized: data,
          metadata
        };
      }
      
      if (ArrayBuffer.isView(data) || data instanceof ArrayBuffer) {
        metadata.type = data.constructor.name;
        const buffer = data instanceof ArrayBuffer ? data : data.buffer;
        
        return {
          serialized: new Uint8Array(buffer),
          metadata
        };
      }
      
      // Try to identify and serialize instances of registered classes
      if (this.options.preserveInstances) {
        try {
          for (const [className, { constructor, serialize }] of this.registeredClasses.entries()) {
            // Check if data is an instance of the constructor
            // Use a safer check to avoid circular dependency issues
            const isInstance = constructor && 
              typeof constructor === 'function' &&
              (data instanceof constructor || 
              (data && data.constructor && data.constructor.name === constructor.name));
              
            if (isInstance) {
              const serializedInstance = serialize(data);
              metadata.className = className;
              
              return {
                serialized: JSON.stringify(serializedInstance),
                metadata
              };
            }
          }
        } catch (instanceError) {
          // Ignore instance check errors and continue with regular serialization
          Prime.Logger.warn('Instance check error during serialization, continuing with default serialization', {
            error: instanceError.message
          });
        }
      }
      
      // Default to JSON for objects and arrays
      return {
        serialized: JSON.stringify(data),
        metadata
      };
    } catch (error) {
      throw new PrimeStorageError(
        `Failed to serialize data: ${error.message}`,
        { originalError: error },
        'STORAGE_SERIALIZATION_ERROR',
        error
      );
    }
  }

  /**
   * Deserializes data from a string or buffer
   * @param {string|Buffer} serialized - Serialized data
   * @param {Object} metadata - Metadata about the serialized data
   * @returns {Promise<*>} Deserialized data
   */
  async deserialize(serialized, metadata) {
    try {
      // Handle null or undefined
      if (serialized === 'null' || serialized === 'undefined') {
        return JSON.parse(serialized);
      }
      
      // Handle Buffer or TypedArray
      if (metadata.type === 'Buffer' || metadata.type.includes('Array')) {
        return serialized;
      }
      
      // Handle instance of registered class
      if (metadata.className && this.registeredClasses.has(metadata.className)) {
        const { deserialize } = this.registeredClasses.get(metadata.className);
        const parsed = JSON.parse(serialized);
        return deserialize(parsed);
      }
      
      // Default to JSON parsing
      return JSON.parse(serialized);
    } catch (error) {
      throw new PrimeStorageError(
        `Failed to deserialize data: ${error.message}`,
        { originalError: error, metadata },
        'STORAGE_DESERIALIZATION_ERROR',
        error
      );
    }
  }

  /**
   * Splits data into chunks for storage
   * @param {*} data - Data to chunk
   * @param {number} chunkSize - Size of each chunk in bytes
   * @returns {Promise<Array<{data: *, metadata: Object}>>} Array of data chunks with metadata
   */
  async chunkData(data, chunkSize) {
    const { serialized, metadata } = await this.serialize(data);
    
    // If serialized data is small enough, return as a single chunk
    if (serialized.length <= chunkSize) {
      return [{
        data: serialized,
        metadata: {
          ...metadata,
          index: 0,
          totalChunks: 1,
          isLastChunk: true
        }
      }];
    }
    
    // Split serialized data into chunks
    const chunks = [];
    let index = 0;
    
    if (typeof serialized === 'string') {
      for (let i = 0; i < serialized.length; i += chunkSize) {
        const chunk = serialized.substring(i, i + chunkSize);
        chunks.push({
          data: chunk,
          metadata: {
            ...metadata,
            index,
            totalChunks: Math.ceil(serialized.length / chunkSize),
            isLastChunk: i + chunkSize >= serialized.length
          }
        });
        index++;
      }
    } else {
      // Handle Buffer or TypedArray
      for (let i = 0; i < serialized.length; i += chunkSize) {
        const chunk = serialized.slice(i, i + chunkSize);
        chunks.push({
          data: chunk,
          metadata: {
            ...metadata,
            index,
            totalChunks: Math.ceil(serialized.length / chunkSize),
            isLastChunk: i + chunkSize >= serialized.length
          }
        });
        index++;
      }
    }
    
    return chunks;
  }

  /**
   * Reconstructs data from chunks
   * @param {Array<{data: *, metadata: Object}>} chunks - Array of data chunks with metadata
   * @returns {Promise<*>} Reconstructed data
   */
  async reconstructFromChunks(chunks) {
    if (!chunks || chunks.length === 0) {
      throw new PrimeStorageError(
        'No chunks provided for reconstruction',
        {},
        'STORAGE_EMPTY_CHUNKS'
      );
    }
    
    // Sort chunks by index
    chunks.sort((a, b) => a.metadata.index - b.metadata.index);
    
    // Check if chunks are complete
    const totalChunks = chunks[0].metadata.totalChunks;
    if (chunks.length !== totalChunks) {
      throw new PrimeStorageError(
        `Incomplete chunks: expected ${totalChunks}, got ${chunks.length}`,
        { expected: totalChunks, received: chunks.length },
        'STORAGE_INCOMPLETE_CHUNKS'
      );
    }
    
    // Combine chunks
    let combined;
    
    if (typeof chunks[0].data === 'string') {
      combined = chunks.map(chunk => chunk.data).join('');
    } else {
      // Handle Buffer or TypedArray
      const totalLength = chunks.reduce((sum, chunk) => sum + chunk.data.length, 0);
      const combinedBuffer = new Uint8Array(totalLength);
      
      let offset = 0;
      for (const chunk of chunks) {
        combinedBuffer.set(new Uint8Array(chunk.data), offset);
        offset += chunk.data.length;
      }
      
      combined = combinedBuffer;
    }
    
    // Deserialize combined data
    return this.deserialize(combined, chunks[0].metadata);
  }
}

module.exports = Serializer;