/**
 * PrimeOS JavaScript Library - Vector Math
 * Vector operations and utilities
 * 
 * This file serves as the main entry point for vector operations,
 * importing functionality from the modular components while maintaining
 * backward compatibility.
 */

// Import the modular vector components
require("./vector-core");
require("./vector-advanced");
require("./vector-validation");

// Import the Prime object with all vector components loaded
const Prime = require("../core");

// Create a Vector object that maintains the original API
(function () {
  // Ensure all required vector namespaces exist
  if (!Prime.Math.VectorCore || !Prime.Math.VectorAdvanced || !Prime.Math.VectorValidation) {
    throw new Error("Vector components must be loaded before Vector");
  }

  // Get references to the modular components
  const VectorCore = Prime.Math.VectorCore;
  const VectorAdvanced = Prime.Math.VectorAdvanced;
  const VectorValidation = Prime.Math.VectorValidation;

  /**
   * Vector operations for mathematical computations
   * Combines core, advanced, and validation functionality
   * while maintaining backward compatibility
   */
  const Vector = {
    /**
     * Create a new vector with specified dimensions
     * @param {number} dimensions - Number of dimensions
     * @param {number} [initialValue=0] - Initial value for all elements
     * @returns {Array} - New vector with specified dimensions
     */
    create: function (dimensions, initialValue = 0) {
      return VectorCore.create(dimensions, initialValue);
    },

    /**
     * Add two vectors element-wise
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {Array} - Result of addition
     */
    add: function (a, b) {
      return VectorCore.add(a, b);
    },

    /**
     * Subtract vector b from vector a element-wise
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {Array} - Result of subtraction
     */
    subtract: function (a, b) {
      return VectorCore.subtract(a, b);
    },

    /**
     * Calculate the dot product of two vectors
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {number} - Dot product
     */
    dot: function (a, b) {
      return VectorCore.dot(a, b);
    },

    /**
     * Scale a vector by a scalar
     * @param {Array} vector - Vector to scale
     * @param {number} scalar - Scaling factor
     * @returns {Array} - Scaled vector
     */
    scale: function (vector, scalar) {
      return VectorCore.scale(vector, scalar);
    },

    /**
     * Calculate the magnitude (norm) of a vector
     * @param {Array} vector - Input vector
     * @returns {number} - Vector magnitude
     */
    magnitude: function (vector) {
      return VectorCore.magnitude(vector);
    },

    /**
     * Normalize a vector to unit length
     * @param {Array} vector - Vector to normalize
     * @returns {Array} - Normalized vector
     */
    normalize: function (vector) {
      return VectorCore.normalize(vector);
    },

    /**
     * Calculate the cross product of two 3D vectors
     * @param {Array} a - First 3D vector
     * @param {Array} b - Second 3D vector
     * @returns {Array} - Cross product
     */
    cross: function (a, b) {
      return VectorAdvanced.cross(a, b);
    },

    /**
     * Calculate the angle between two vectors in radians
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {number} - Angle in radians
     */
    angle: function (a, b) {
      return VectorAdvanced.angle(a, b);
    },

    /**
     * Project vector a onto vector b
     * @param {Array} a - Vector to project
     * @param {Array} b - Vector to project onto
     * @returns {Array} - Projection result
     */
    project: function (a, b) {
      return VectorAdvanced.project(a, b);
    },

    /**
     * Calculate the distance between two vectors
     * @param {Array} a - First vector
     * @param {Array} b - Second vector
     * @returns {number} - Distance between vectors
     */
    distance: function (a, b) {
      return VectorCore.distance(a, b);
    },
    
    /**
     * Linear interpolation between two vectors
     * @param {Array} a - Start vector
     * @param {Array} b - End vector
     * @param {number} t - Interpolation parameter (0-1)
     * @returns {Array} - Interpolated vector
     */
    lerp: function (a, b, t) {
      return VectorAdvanced.lerp(a, b, t);
    },
    
    /**
     * Calculate the norm (magnitude) of a vector
     * @param {Array} vector - Input vector
     * @returns {number} - Vector norm
     */
    norm: function (vector) {
      return VectorCore.magnitude(vector);
    },

    // Add new methods not in the original API
    
    /**
     * Create a vector using TypedArray for improved memory efficiency
     * @param {number} dimensions - Number of dimensions
     * @param {number} [initialValue=0] - Initial value for all elements
     * @param {string} [arrayType='float64'] - Type of TypedArray ('float64', 'float32', etc.)
     * @returns {TypedArray} - New vector with specified dimensions
     */
    createTyped: function (dimensions, initialValue = 0, arrayType = 'float64') {
      return VectorCore.create(dimensions, initialValue, { 
        useTypedArray: true, 
        arrayType 
      });
    },
    
    /**
     * Apply an operation to vector(s) in-place to avoid memory allocation
     * @param {string} operation - Operation name ('add', 'subtract', 'scale', etc.)
     * @param {...any} args - Arguments for the operation
     * @param {Array|TypedArray} result - Vector to store the result in
     * @returns {Array|TypedArray} - The result vector (same as the last argument)
     */
    applyInPlace: function (operation, ...args) {
      const result = args.pop(); // Last argument is the result vector
      
      if (!VectorCore.isVector(result)) {
        throw new Prime.ValidationError("Last argument must be a vector to store the result");
      }
      
      switch (operation) {
        case 'add':
          if (args.length !== 2) {
            throw new Prime.ValidationError("Add operation requires two vectors");
          }
          return VectorCore.add(args[0], args[1], result);
          
        case 'subtract':
          if (args.length !== 2) {
            throw new Prime.ValidationError("Subtract operation requires two vectors");
          }
          return VectorCore.subtract(args[0], args[1], result);
          
        case 'scale':
          if (args.length !== 2) {
            throw new Prime.ValidationError("Scale operation requires a vector and a scalar");
          }
          return VectorCore.scale(args[0], args[1], result);
          
        case 'normalize':
          if (args.length !== 1) {
            throw new Prime.ValidationError("Normalize operation requires one vector");
          }
          return VectorCore.normalize(args[0], result);
          
        case 'lerp':
          if (args.length !== 3) {
            throw new Prime.ValidationError("Lerp operation requires two vectors and a parameter");
          }
          return VectorAdvanced.lerp(args[0], args[1], args[2], result);
          
        default:
          throw new Prime.ValidationError(`Unknown operation: ${operation}`);
      }
    },
    
    /**
     * Check if a value is a valid vector
     * @param {*} v - Value to check
     * @returns {boolean} - True if v is a valid vector
     */
    isVector: VectorCore.isVector,
    
    /**
     * Get detailed diagnostics about a vector
     * @param {*} v - Vector to diagnose
     * @returns {Object} - Diagnostic information
     */
    getDiagnostics: function(v) {
      // We need to call this through VectorValidation to ensure 'this' binding is correct
      return VectorValidation.getDiagnostics(v);
    }
  };

  // Add Vector to the Prime.Math namespace
  Prime.Math = Prime.Math || {};
  Prime.Math.Vector = Vector;
})();

// Export the enhanced Prime object
module.exports = Prime;