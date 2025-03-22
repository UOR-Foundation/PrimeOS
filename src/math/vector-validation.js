/**
 * PrimeOS JavaScript Library - Math
 * Vector Validation
 * Validation utilities for vector operations
 */

// Import the Prime object with VectorCore
const Prime = require("./vector-core");

// Ensure VectorCore exists
if (!Prime.Math.VectorCore) {
  throw new Error("VectorCore must be loaded before VectorValidation");
}

// Get reference to VectorCore
const VectorCore = Prime.Math.VectorCore;

/**
 * Vector validation utilities with enhanced functionality
 */
const VectorValidation = {
  /**
   * Check if a value is a valid vector with numerical elements
   * @param {*} v - Value to check
   * @returns {boolean} - True if v is a valid vector with numerical elements
   */
  isNumericVector: function (v) {
    if (!VectorCore.isVector(v)) {
      return false;
    }

    // Check if all elements are numbers
    for (let i = 0; i < v.length; i++) {
      if (typeof v[i] !== "number" || Number.isNaN(v[i])) {
        return false;
      }
    }

    return true;
  },

  /**
   * Check if a value is a valid vector with finite elements
   * @param {*} v - Value to check
   * @returns {boolean} - True if v is a valid vector with finite elements
   */
  isFiniteVector: function (v) {
    if (!VectorCore.isVector(v)) {
      return false;
    }

    // Check if all elements are finite numbers
    for (let i = 0; i < v.length; i++) {
      if (!Number.isFinite(v[i])) {
        return false;
      }
    }

    return true;
  },

  /**
   * Check if a value is a zero vector (all elements are zero)
   * @param {*} v - Value to check
   * @param {Object} [options={}] - Options
   * @param {number} [options.tolerance=1e-10] - Tolerance for near-zero values
   * @returns {boolean} - True if v is a zero vector
   */
  isZeroVector: function (v, options = {}) {
    if (!VectorCore.isVector(v)) {
      return false;
    }

    const tolerance = options.tolerance || 1e-10;

    // Check if all elements are zero
    for (let i = 0; i < v.length; i++) {
      if (Math.abs(v[i]) > tolerance) {
        return false;
      }
    }

    return true;
  },

  /**
   * Check if a value is a unit vector (magnitude approximately 1)
   * @param {*} v - Value to check
   * @param {Object} [options={}] - Options
   * @param {number} [options.tolerance=1e-10] - Tolerance for near-unity magnitude
   * @returns {boolean} - True if v is a unit vector
   */
  isUnitVector: function (v, options = {}) {
    if (!VectorCore.isVector(v)) {
      return false;
    }

    const tolerance = options.tolerance || 1e-10;
    const magnitude = VectorCore.magnitude(v);

    return Math.abs(magnitude - 1) < tolerance;
  },

  /**
   * Check if two vectors have the same dimension
   * @param {*} a - First vector
   * @param {*} b - Second vector
   * @returns {boolean} - True if both are vectors with the same dimension
   */
  haveSameDimension: function (a, b) {
    if (!VectorCore.isVector(a) || !VectorCore.isVector(b)) {
      return false;
    }

    return a.length === b.length;
  },

  /**
   * Check if two vectors are equal (element-wise)
   * @param {*} a - First vector
   * @param {*} b - Second vector
   * @param {Object} [options={}] - Options
   * @param {number} [options.tolerance=1e-10] - Tolerance for element comparison
   * @returns {boolean} - True if vectors are equal
   */
  areEqual: function (a, b, options = {}) {
    if (!VectorCore.isVector(a) || !VectorCore.isVector(b)) {
      return false;
    }

    if (a.length !== b.length) {
      return false;
    }

    const tolerance = options.tolerance || 1e-10;

    // Check if all elements are equal within tolerance
    for (let i = 0; i < a.length; i++) {
      if (Math.abs(a[i] - b[i]) > tolerance) {
        return false;
      }
    }

    return true;
  },

  /**
   * Get validation diagnostics for a vector
   * @param {*} v - Vector to diagnose
   * @returns {Object} - Diagnostic information
   */
  getDiagnostics: function (v) {
    const isVector = VectorCore.isVector(v);
    
    if (!isVector) {
      return {
        isVector: false,
        diagnostics: "Not a vector (array or TypedArray required)",
      };
    }
    
    // Check if all elements are numbers
    let allNumbers = true;
    let allFinite = true;
    let anyNaN = false;
    let anyInfinity = false;
    let anyZero = false;
    
    for (let i = 0; i < v.length; i++) {
      if (typeof v[i] !== "number") {
        allNumbers = false;
      } else {
        if (Number.isNaN(v[i])) {
          anyNaN = true;
          allFinite = false;
        } else if (!Number.isFinite(v[i])) {
          anyInfinity = true;
          allFinite = false;
        } else if (v[i] === 0) {
          anyZero = true;
        }
      }
    }
    
    // Calculate additional metrics
    let magnitude = 0;
    let minValue = Infinity;
    let maxValue = -Infinity;
    let meanValue = 0;
    
    if (allNumbers) {
      try {
        magnitude = VectorCore.magnitude(v);
        
        // Calculate statistics
        let sum = 0;
        for (let i = 0; i < v.length; i++) {
          sum += v[i];
          minValue = Math.min(minValue, v[i]);
          maxValue = Math.max(maxValue, v[i]);
        }
        
        meanValue = sum / v.length;
      } catch (e) {
        // If magnitude calculation fails, set appropriate flags
        allFinite = false;
      }
    }
    
    return {
      isVector: true,
      isTypedArray: ArrayBuffer.isView(v),
      type: ArrayBuffer.isView(v) ? v.constructor.name : "Array",
      dimension: v.length,
      allNumbers,
      allFinite,
      anyNaN,
      anyInfinity,
      anyZero,
      isZero: this.isZeroVector(v, { tolerance: 1e-10 }),
      isUnit: this.isUnitVector(v),
      magnitude: allFinite ? magnitude : "N/A",
      min: allFinite ? minValue : "N/A",
      max: allFinite ? maxValue : "N/A",
      mean: allFinite ? meanValue : "N/A",
      valueRange: allFinite ? maxValue - minValue : "N/A",
    };
  },

  /**
   * Validate a vector for numeric operations and throw detailed errors for problems
   * @param {*} v - Vector to validate
   * @param {Object} [options={}] - Options
   * @param {boolean} [options.requireFinite=true] - Require all elements to be finite
   * @param {boolean} [options.allowZero=true] - Allow zero vectors
   * @throws {Error} - If validation fails
   */
  validateVector: function (v, options = {}) {
    const requireFinite = options.requireFinite !== false;
    const allowZero = options.allowZero !== false;
    
    if (!VectorCore.isVector(v)) {
      throw new Prime.ValidationError("Value is not a vector (array or TypedArray required)");
    }
    
    // Check if all elements are numbers and finite if required
    for (let i = 0; i < v.length; i++) {
      if (typeof v[i] !== "number") {
        throw new Prime.ValidationError(`Element at index ${i} is not a number`);
      }
      
      if (Number.isNaN(v[i])) {
        throw new Prime.ValidationError(`Element at index ${i} is NaN`);
      }
      
      if (requireFinite && !Number.isFinite(v[i])) {
        throw new Prime.ValidationError(`Element at index ${i} is not finite`);
      }
    }
    
    // Check for zero vector if not allowed
    if (!allowZero && this.isZeroVector(v)) {
      throw new Prime.ValidationError("Zero vector is not allowed for this operation");
    }
    
    return true;
  },

  /**
   * Validate two vectors for binary operations (add, subtract, dot, etc.)
   * @param {*} a - First vector
   * @param {*} b - Second vector
   * @param {Object} [options={}] - Options
   * @param {boolean} [options.requireSameDimension=true] - Require vectors to have the same dimension
   * @throws {Error} - If validation fails
   */
  validateVectorPair: function (a, b, options = {}) {
    const requireSameDimension = options.requireSameDimension !== false;
    
    // Validate each vector individually
    this.validateVector(a, options);
    this.validateVector(b, options);
    
    // Check dimensions if required
    if (requireSameDimension && a.length !== b.length) {
      throw new Prime.ValidationError(
        `Vectors must have the same dimension: ${a.length} vs ${b.length}`
      );
    }
    
    return true;
  },

  /**
   * Create a safe copy of a vector, correcting potential issues
   * @param {*} v - Vector to sanitize
   * @param {Object} [options={}] - Options
   * @param {boolean} [options.replaceNaN=true] - Replace NaN values with 0
   * @param {boolean} [options.replaceInfinity=true] - Replace Infinity values with large finite values
   * @returns {Array|TypedArray} - Sanitized vector
   */
  sanitizeVector: function (v, options = {}) {
    if (!VectorCore.isVector(v)) {
      throw new Prime.ValidationError("Value is not a vector (array or TypedArray required)");
    }
    
    const replaceNaN = options.replaceNaN !== false;
    const replaceInfinity = options.replaceInfinity !== false;
    const safeInfValue = 1e16; // Large but finite value
    
    // Create a copy of the vector
    const result = VectorCore.clone(v);
    
    // Replace problematic values
    for (let i = 0; i < result.length; i++) {
      if (typeof result[i] !== "number") {
        // Convert non-numbers to 0
        result[i] = 0;
      } else if (replaceNaN && Number.isNaN(result[i])) {
        // Replace NaN with 0
        result[i] = 0;
      } else if (replaceInfinity && !Number.isFinite(result[i])) {
        // Replace Infinity/-Infinity with large finite values
        result[i] = result[i] > 0 ? safeInfValue : -safeInfValue;
      }
    }
    
    return result;
  }
};

// Add vector-validation to the Prime.Math namespace
Prime.Math = Prime.Math || {};

// Check if VectorValidation already has a getter defined, if so, use it
if (Object.getOwnPropertyDescriptor(Prime.Math, 'VectorValidation') && 
    Object.getOwnPropertyDescriptor(Prime.Math, 'VectorValidation').get) {
  // Use a more careful approach to update the property
  const descriptor = Object.getOwnPropertyDescriptor(Prime.Math, 'VectorValidation');
  const originalGetter = descriptor.get;
  
  Object.defineProperty(Prime.Math, 'VectorValidation', {
    get: function() {
      const result = originalGetter.call(this);
      // If result is an empty object (placeholder), return our implementation
      if (Object.keys(result).length === 0) {
        return VectorValidation;
      }
      // Otherwise, preserve what's already there
      return result;
    },
    configurable: true
  });
} else {
  // Direct assignment if no getter exists
  Prime.Math.VectorValidation = VectorValidation;
}

// Export the enhanced Prime object
module.exports = Prime;