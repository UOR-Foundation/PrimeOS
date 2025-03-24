/**
 * PrimeOS JavaScript Library - Component Coherence Checks
 * Mathematical coherence validation for components
 * Version 1.0.0
 */

// Import Prime using CommonJS to avoid circular dependency
const Prime = require("../core.js");
// Ensure mathematics module is loaded
require("../mathematics.js");
require("../coherence.js");

(function (Prime) {
  /**
   * Mathematical coherence checks for components
   */
  const CoherenceCheck = {
    /**
     * Check if a value is coherent based on its type
     * @param {*} value - Value to check
     * @param {Object} [options] - Check options
     * @returns {boolean} True if value is coherent
     */
    isCoherent: function(value, options = {}) {
      // Handle different types
      if (value === null || value === undefined) {
        return true; // Null values are considered coherent
      }
      
      if (Prime.Utils.isArray(value)) {
        return this.isArrayCoherent(value, options);
      }
      
      if (Prime.Math && Prime.Math.Matrix && value instanceof Prime.Math.Matrix) {
        return this.isMatrixCoherent(value, options);
      }
      
      if (Prime.Math && Prime.Math.Vector && value instanceof Prime.Math.Vector) {
        return this.isVectorCoherent(value, options);
      }
      
      if (Prime.Math && Prime.Math.Tensor && value instanceof Prime.Math.Tensor) {
        return this.isTensorCoherent(value, options);
      }
      
      if (Prime.Clifford && Prime.Clifford.isMultivector && 
          Prime.Clifford.isMultivector(value)) {
        return this.isMultivectorCoherent(value, options);
      }
      
      if (Prime.Utils.isObject(value)) {
        return this.isObjectCoherent(value, options);
      }
      
      // Primitive values are coherent by default
      return true;
    },
    
    /**
     * Check if an array is coherent
     * @param {Array} array - Array to check
     * @param {Object} [options] - Check options
     * @param {boolean} [options.checkElements=true] - Whether to check array elements
     * @param {boolean} [options.uniformType=false] - Whether array should have uniform type
     * @returns {boolean} True if array is coherent
     */
    isArrayCoherent: function(array, options = {}) {
      const opts = {
        checkElements: options.checkElements !== false,
        uniformType: options.uniformType === true,
        ...options
      };
      
      // Empty arrays are coherent
      if (array.length === 0) {
        return true;
      }
      
      // Check for NaN, Infinity, etc.
      if (array.some(item => 
        typeof item === 'number' && 
        (isNaN(item) || !isFinite(item))
      )) {
        return false;
      }
      
      // Check for uniform type if required
      if (opts.uniformType) {
        const firstType = typeof array[0];
        if (!array.every(item => typeof item === firstType)) {
          return false;
        }
      }
      
      // Recursively check array elements
      if (opts.checkElements) {
        return array.every(item => this.isCoherent(item, options));
      }
      
      return true;
    },
    
    /**
     * Check if a matrix is coherent
     * @param {Prime.Math.Matrix} matrix - Matrix to check
     * @param {Object} [options] - Check options
     * @param {boolean} [options.checkCondition=false] - Whether to check condition number
     * @param {number} [options.maxCondition=1e14] - Maximum acceptable condition number
     * @returns {boolean} True if matrix is coherent
     */
    isMatrixCoherent: function(matrix, options = {}) {
      const opts = {
        checkCondition: options.checkCondition === true,
        maxCondition: options.maxCondition || 1e14,
        ...options
      };
      
      // Check basic matrix properties
      if (!matrix.isValid || (matrix.isValid && !matrix.isValid())) {
        return false;
      }
      
      // Check for zeros on the diagonal if this is a diagonal matrix 
      // and that's not allowed
      if (options.noDiagonalZeros && matrix.isDiagonal && matrix.isDiagonal()) {
        const diag = matrix.getDiagonal();
        if (diag.some(v => v === 0)) {
          return false;
        }
      }
      
      // Check for NaN or Infinity values
      for (let i = 0; i < matrix.rows; i++) {
        for (let j = 0; j < matrix.cols; j++) {
          const val = matrix.get(i, j);
          if (isNaN(val) || !isFinite(val)) {
            return false;
          }
        }
      }
      
      // Check condition number if required
      if (opts.checkCondition && matrix.rows === matrix.cols) {
        try {
          // We only attempt this for square matrices
          const condition = matrix.condition();
          if (condition > opts.maxCondition) {
            return false;
          }
        } catch (e) {
          // If condition calculation fails, the matrix is likely singular
          return false;
        }
      }
      
      return true;
    },
    
    /**
     * Check if a vector is coherent
     * @param {Prime.Math.Vector} vector - Vector to check
     * @param {Object} [options] - Check options
     * @param {boolean} [options.checkNorm=false] - Whether to check vector norm
     * @param {number} [options.maxNorm=1e10] - Maximum acceptable norm
     * @returns {boolean} True if vector is coherent
     */
    isVectorCoherent: function(vector, options = {}) {
      const opts = {
        checkNorm: options.checkNorm === true,
        maxNorm: options.maxNorm || 1e10,
        ...options
      };
      
      // Check for NaN or Infinity
      for (let i = 0; i < vector.dimension; i++) {
        const val = vector.get(i);
        if (isNaN(val) || !isFinite(val)) {
          return false;
        }
      }
      
      // Check norm if required
      if (opts.checkNorm) {
        try {
          const norm = vector.norm();
          if (isNaN(norm) || !isFinite(norm) || norm > opts.maxNorm) {
            return false;
          }
        } catch (e) {
          // If norm calculation fails, the vector is not coherent
          return false;
        }
      }
      
      return true;
    },
    
    /**
     * Check if a tensor is coherent
     * @param {Prime.Math.Tensor} tensor - Tensor to check
     * @param {Object} [options] - Check options
     * @returns {boolean} True if tensor is coherent
     */
    isTensorCoherent: function(tensor, options = {}) {
      // Check for NaN or Infinity values
      try {
        const flattened = tensor.flatten();
        return flattened.every(val => 
          !isNaN(val) && isFinite(val)
        );
      } catch (e) {
        return false;
      }
    },
    
    /**
     * Check if a multivector is coherent
     * @param {Object} multivector - Multivector to check
     * @param {Object} [options] - Check options
     * @returns {boolean} True if multivector is coherent
     */
    isMultivectorCoherent: function(multivector, options = {}) {
      try {
        // Extract components to check values
        const components = Prime.Clifford.extractComponents(multivector);
        
        // Check each component value
        return components.every(comp => {
          const { value } = comp;
          return !isNaN(value) && isFinite(value);
        });
      } catch (e) {
        return false;
      }
    },
    
    /**
     * Check if an object is coherent
     * @param {Object} obj - Object to check
     * @param {Object} [options] - Check options
     * @param {boolean} [options.recursive=true] - Whether to check recursively
     * @returns {boolean} True if object is coherent
     */
    isObjectCoherent: function(obj, options = {}) {
      const opts = {
        recursive: options.recursive !== false,
        ...options
      };
      
      // Check all properties
      if (opts.recursive) {
        for (const key in obj) {
          if (Object.prototype.hasOwnProperty.call(obj, key)) {
            if (!this.isCoherent(obj[key], options)) {
              return false;
            }
          }
        }
      }
      
      return true;
    },
    
    /**
     * Create a coherence constraint for mathematical properties
     * @param {function} check - Check function
     * @param {string} name - Constraint name
     * @param {Object} [options] - Constraint options
     * @returns {Object} Constraint object
     */
    createConstraint: function(check, name, options = {}) {
      return {
        name: name || 'MathCoherenceConstraint',
        type: options.type || 'hard',
        weight: options.weight || 1.0,
        check: check
      };
    },
    
    /**
     * Create a constraint to check array uniformity
     * @param {string} path - Path to array property
     * @param {string} name - Constraint name
     * @returns {Object} Constraint object
     */
    createUniformArrayConstraint: function(path, name) {
      const self = this;
      return this.createConstraint(
        function(obj) {
          const array = Prime.Utils.getPath(obj, path);
          if (!array || !Array.isArray(array)) {
            return true; // Nothing to check
          }
          return self.isArrayCoherent(array, { uniformType: true });
        },
        name || `Uniform array constraint (${path})`
      );
    },
    
    /**
     * Create a constraint to check matrix properties
     * @param {string} path - Path to matrix property
     * @param {Object} options - Matrix check options
     * @param {string} name - Constraint name
     * @returns {Object} Constraint object
     */
    createMatrixConstraint: function(path, options, name) {
      const self = this;
      return this.createConstraint(
        function(obj) {
          const matrix = Prime.Utils.getPath(obj, path);
          if (!matrix || !(Prime.Math && Prime.Math.Matrix && matrix instanceof Prime.Math.Matrix)) {
            return true; // Nothing to check
          }
          return self.isMatrixCoherent(matrix, options);
        },
        name || `Matrix constraint (${path})`
      );
    },
    
    /**
     * Create a constraint for custom mathematical validation
     * @param {Function} validate - Validation function
     * @param {string} name - Constraint name
     * @param {Object} options - Constraint options
     * @returns {Object} Constraint object
     */
    createMathConstraint: function(validate, name, options = {}) {
      return this.createConstraint(validate, name, options);
    }
  };
  
  // Add coherence checks to Prime.Components namespace
  Prime.Components = Prime.Components || {};
  Prime.Components.CoherenceCheck = CoherenceCheck;
  
  // Add event publishing wrapped in a try-catch to handle potential initialization issues
  try {
    if (Prime.EventBus && typeof Prime.EventBus.publish === 'function') {
      Prime.EventBus.publish("module:loaded", { name: "component-coherence-check" });
    }
  } catch (err) {
    console.error('Error publishing module:loaded event for component-coherence-check:', err);
  }
})(Prime);

// CommonJS export (no ES module export to avoid circular dependency)
if (typeof module !== "undefined" && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== "undefined") {
  window.Prime = Prime;
}