/**
 * Coherence Validator for the Prime Framework
 * Enhanced version with formal UOR (Universal Object Reference) constraints
 */

// Import core if available
let Prime;
try {
  Prime = require("../../core.js");
} catch (e) {
  // Handle case where core isn't available yet
  Prime = {};
}

/**
 * CoherenceValidator implements formal coherence checking for mathematical operations
 * Based on UOR framework principles with constraint satisfaction verification
 */
class CoherenceValidator {
  /**
   * Create a new coherence validator
   * 
   * @param {Object} options - Configuration options
   * @param {boolean} options.strictMode - Whether to enforce strict coherence (default: false)
   * @param {number} options.toleranceLevel - Numerical tolerance for coherence checks (default: 1e-10)
   * @param {boolean} options.enforceUorConstraints - Whether to enforce UOR constraints (default: true)
   */
  constructor(options = {}) {
    this.strictMode = options.strictMode || false;
    this.toleranceLevel = options.toleranceLevel || 1e-10;
    this.enforceUorConstraints = options.enforceUorConstraints !== false;
    this.validators = {};
    this.constraintRegistry = new Map();
    this.coherenceNorms = new Map();
    
    // Performance tracking
    this._validationStats = {
      totalChecks: 0,
      passedChecks: 0,
      failedChecks: 0,
      totalTime: 0
    };
  }
  
  /**
   * Register a coherence constraint for a specific domain
   * 
   * @param {string} domain - Domain for the constraint (e.g., 'numeric', 'algebraic', 'geometric')
   * @param {Object} constraint - Constraint object
   * @param {Function} constraint.validator - Function that checks if a value satisfies the constraint
   * @param {string} constraint.name - Human-readable name for the constraint
   * @param {number} constraint.priority - Priority level (higher values = higher priority)
   * @returns {string} Constraint ID
   */
  registerConstraint(domain, constraint) {
    if (!constraint || typeof constraint.validator !== 'function') {
      throw new Error('Constraint must have a validator function');
    }
    
    // Generate a unique ID for this constraint
    const id = `${domain}_${constraint.name || 'constraint'}_${Date.now()}`;
    
    // Ensure domain exists in registry
    if (!this.constraintRegistry.has(domain)) {
      this.constraintRegistry.set(domain, new Map());
    }
    
    // Store the constraint
    this.constraintRegistry.get(domain).set(id, {
      validator: constraint.validator,
      name: constraint.name || id,
      priority: constraint.priority || 0,
      domain
    });
    
    return id;
  }
  
  /**
   * Remove a registered constraint
   * 
   * @param {string} id - Constraint ID
   * @returns {boolean} Whether the constraint was successfully removed
   */
  removeConstraint(id) {
    for (const [domain, constraints] of this.constraintRegistry.entries()) {
      if (constraints.has(id)) {
        constraints.delete(id);
        return true;
      }
    }
    return false;
  }
  
  /**
   * Register a custom validator function for a specific type
   * 
   * @param {string} type - Type to validate (e.g., 'number', 'array', 'matrix')
   * @param {Function} validator - Validation function
   */
  registerValidator(type, validator) {
    if (typeof validator !== 'function') {
      throw new Error('Validator must be a function');
    }
    this.validators[type] = validator;
  }
  
  /**
   * Define a coherence norm for a specific domain
   * 
   * @param {string} domain - Domain for the norm
   * @param {Function} normFn - Function to compute the coherence norm
   */
  defineCoherenceNorm(domain, normFn) {
    if (typeof normFn !== 'function') {
      throw new Error('Coherence norm must be a function');
    }
    this.coherenceNorms.set(domain, normFn);
  }
  
  /**
   * Validate a mathematical operation according to UOR constraints
   * 
   * @param {string} domain - Domain for validation (e.g., 'numeric', 'algebraic')
   * @param {*} value - Value to validate
   * @param {Object} context - Additional context for validation
   * @returns {Object} Validation result with coherence measure
   */
  validate(domain, value, context = {}) {
    const startTime = Date.now();
    this._validationStats.totalChecks++;
    
    // Get constraints for this domain
    const domainConstraints = this.constraintRegistry.get(domain);
    
    if (!domainConstraints || domainConstraints.size === 0) {
      // No registered constraints for this domain
      this._validationStats.passedChecks++;
      
      const endTime = Date.now();
      this._validationStats.totalTime += (endTime - startTime);
      
      return {
        valid: true,
        coherence: 1.0,
        message: 'No constraints defined for this domain'
      };
    }
    
    // Sort constraints by priority (descending)
    const sortedConstraints = Array.from(domainConstraints.values())
      .sort((a, b) => b.priority - a.priority);
    
    // Track constraint satisfaction
    const results = [];
    let allSatisfied = true;
    
    // Execute constraints in priority order
    for (const constraint of sortedConstraints) {
      try {
        const satisfied = constraint.validator(value, context);
        
        results.push({
          name: constraint.name,
          satisfied,
          priority: constraint.priority
        });
        
        if (!satisfied) {
          allSatisfied = false;
          
          // In strict mode, fail on first violated constraint
          if (this.strictMode) {
            break;
          }
        }
      } catch (error) {
        results.push({
          name: constraint.name,
          satisfied: false,
          priority: constraint.priority,
          error: error.message
        });
        
        allSatisfied = false;
        if (this.strictMode) {
          break;
        }
      }
    }
    
    // Compute coherence score based on constraint satisfaction
    let coherence = 0;
    
    // If we have a registered coherence norm for this domain, use it
    if (this.coherenceNorms.has(domain)) {
      try {
        coherence = this.coherenceNorms.get(domain)(results, value, context);
      } catch (e) {
        // Fallback to simple coherence calculation on error
        coherence = this._computeSimpleCoherence(results);
      }
    } else {
      // Otherwise, use a simple coherence measure
      coherence = this._computeSimpleCoherence(results);
    }
    
    // Track statistics
    if (allSatisfied) {
      this._validationStats.passedChecks++;
    } else {
      this._validationStats.failedChecks++;
    }
    
    const endTime = Date.now();
    this._validationStats.totalTime += (endTime - startTime);
    
    // Return validation result
    return {
      valid: allSatisfied,
      coherence,
      constraintResults: results,
      message: allSatisfied ? 'All constraints satisfied' : 'Some constraints violated'
    };
  }
  
  /**
   * Compute a simple coherence measure based on constraint satisfaction
   * 
   * @private
   * @param {Array} results - Constraint validation results
   * @returns {number} Coherence measure between 0 and 1
   */
  _computeSimpleCoherence(results) {
    if (results.length === 0) return 1.0;
    
    // Weight results by priority
    const totalPriority = results.reduce((sum, r) => sum + r.priority, 0);
    
    if (totalPriority === 0) {
      // Equal weighting if no priorities specified
      return results.filter(r => r.satisfied).length / results.length;
    }
    
    // Weight by priority
    let weightedSum = 0;
    for (const result of results) {
      weightedSum += (result.satisfied ? 1 : 0) * (result.priority / totalPriority);
    }
    
    return weightedSum;
  }
  
  /**
   * Get validation performance statistics
   * 
   * @returns {Object} Validation statistics
   */
  getStats() {
    const successRate = this._validationStats.totalChecks > 0 
      ? this._validationStats.passedChecks / this._validationStats.totalChecks 
      : 0;
    
    return {
      ...this._validationStats,
      successRate,
      averageTime: this._validationStats.totalChecks > 0 
        ? this._validationStats.totalTime / this._validationStats.totalChecks 
        : 0
    };
  }
  
  /**
   * Reset validation statistics
   */
  resetStats() {
    this._validationStats = {
      totalChecks: 0,
      passedChecks: 0,
      failedChecks: 0,
      totalTime: 0
    };
  }
  
  /**
   * Validate a value with UOR formal constraints
   * 
   * @param {*} value - Value to validate
   * @param {string} type - Expected type of value
   * @param {Object} constraints - Additional UOR constraints
   * @returns {Object} Validation result
   */
  validateWithUorConstraints(value, type, constraints = {}) {
    if (!this.enforceUorConstraints) {
      return { valid: true, coherence: 1.0 };
    }
    
    // Basic type validation
    const typeValid = this._validateType(value, type);
    
    if (!typeValid) {
      return {
        valid: false,
        coherence: 0,
        message: `Value is not of expected type ${type}`
      };
    }
    
    // Specific validators for different types
    let domainValid = true;
    let domainCoherence = 1.0;
    
    // Choose appropriate validator based on type
    switch (type) {
      case 'number':
        return this.validate('numeric', value, constraints);
      case 'array':
      case 'vector':
        return this.validate('vectorSpace', value, constraints);
      case 'matrix':
        return this.validate('matrixAlgebra', value, constraints);
      case 'function':
        return this.validate('functional', value, constraints);
      case 'tensor':
        return this.validate('tensorAlgebra', value, constraints);
      default:
        // Use custom validator if registered
        if (this.validators[type]) {
          try {
            const result = this.validators[type](value, constraints);
            return {
              valid: result.valid !== false,
              coherence: result.coherence || (result.valid !== false ? 1.0 : 0.0),
              message: result.message || `Validated ${type} value`
            };
          } catch (e) {
            return {
              valid: false,
              coherence: 0,
              message: `Error in custom validator: ${e.message}`
            };
          }
        }
        
        // Default behavior for unknown types
        return {
          valid: true,
          coherence: 1.0,
          message: `No specific validation for type ${type}`
        };
    }
  }
  
  /**
   * Validate type of a value
   * 
   * @private
   * @param {*} value - Value to check
   * @param {string} expectedType - Expected type
   * @returns {boolean} Whether the value matches the expected type
   */
  _validateType(value, expectedType) {
    switch (expectedType) {
      case 'number':
        return typeof value === 'number' && !isNaN(value);
      case 'string':
        return typeof value === 'string';
      case 'boolean':
        return typeof value === 'boolean';
      case 'function':
        return typeof value === 'function';
      case 'object':
        return value !== null && typeof value === 'object' && !Array.isArray(value);
      case 'array':
      case 'vector':
        return Array.isArray(value);
      case 'matrix':
        return Array.isArray(value) && value.every(row => Array.isArray(row));
      case 'tensor':
        // Recursive check for multi-dimensional arrays
        const checkTensor = (arr, depth = 0) => {
          if (depth > 0 && !Array.isArray(arr)) return true;
          if (depth === 0 && !Array.isArray(arr)) return false;
          if (arr.length === 0) return true;
          const allArrays = arr.every(item => Array.isArray(item));
          return allArrays && arr.every(subArr => checkTensor(subArr, depth + 1));
        };
        return checkTensor(value);
      default:
        // For custom types, check against registered validators
        if (this.validators[expectedType]) {
          try {
            return this.validators[expectedType](value).valid !== false;
          } catch (e) {
            return false;
          }
        }
        // Default fallback
        return true;
    }
  }
}

/**
 * Class for validating the coherence of mathematical operations
 * Simplified version for basic coherence checks
 */
class MathematicalCoherenceValidator {
  /**
   * Create a new mathematical coherence validator
   * 
   * @param {Object} options - Configuration options
   */
  constructor(options = {}) {
    this.numericalTolerance = options.numericalTolerance || 1e-10;
    this.validator = new CoherenceValidator({
      strictMode: options.strictMode,
      toleranceLevel: this.numericalTolerance,
      enforceUorConstraints: options.enforceUorConstraints
    });
    
    // Register built-in constraints
    this._registerBuiltInConstraints();
  }
  
  /**
   * Register built-in mathematical constraints
   * 
   * @private
   */
  _registerBuiltInConstraints() {
    // Numeric domain constraints
    this.validator.registerConstraint('numeric', {
      name: 'finiteness',
      validator: (value) => Number.isFinite(value),
      priority: 10
    });
    
    this.validator.registerConstraint('numeric', {
      name: 'non_nan',
      validator: (value) => !Number.isNaN(value),
      priority: 10
    });
    
    // Vector space constraints
    this.validator.registerConstraint('vectorSpace', {
      name: 'array_elements',
      validator: (value) => Array.isArray(value) && value.every(item => typeof item === 'number'),
      priority: 8
    });
    
    this.validator.registerConstraint('vectorSpace', {
      name: 'finite_elements',
      validator: (value) => Array.isArray(value) && value.every(item => Number.isFinite(item)),
      priority: 7
    });
    
    // Matrix algebra constraints
    this.validator.registerConstraint('matrixAlgebra', {
      name: 'matrix_structure',
      validator: (value) => {
        if (!Array.isArray(value) || value.length === 0) return false;
        if (!value.every(row => Array.isArray(row))) return false;
        
        // Check that all rows have the same length
        const rowLength = value[0].length;
        return value.every(row => row.length === rowLength);
      },
      priority: 9
    });
    
    this.validator.registerConstraint('matrixAlgebra', {
      name: 'matrix_elements',
      validator: (value) => {
        if (!Array.isArray(value)) return false;
        return value.every(row => 
          Array.isArray(row) && row.every(item => typeof item === 'number' && Number.isFinite(item))
        );
      },
      priority: 8
    });
    
    // Define coherence norms
    this.validator.defineCoherenceNorm('numeric', (results) => {
      // For numeric values, coherence is binary - either fully coherent or not
      return results.every(r => r.satisfied) ? 1.0 : 0.0;
    });
    
    this.validator.defineCoherenceNorm('vectorSpace', (results, value) => {
      // For vectors, consider partial coherence based on the proportion of valid elements
      if (!Array.isArray(value)) return 0.0;
      
      // If fundamental constraints are violated, coherence is 0
      if (!results.find(r => r.name === 'array_elements')?.satisfied) {
        return 0.0;
      }
      
      // Count finite elements
      const finiteCount = value.filter(v => Number.isFinite(v)).length;
      return value.length > 0 ? finiteCount / value.length : 0.0;
    });
    
    this.validator.defineCoherenceNorm('matrixAlgebra', (results, value) => {
      // For matrices, consider structure and element validity
      if (!results.find(r => r.name === 'matrix_structure')?.satisfied) {
        return 0.0;
      }
      
      // Count valid elements
      let validCount = 0;
      let totalCount = 0;
      
      for (const row of value) {
        for (const element of row) {
          totalCount++;
          if (typeof element === 'number' && Number.isFinite(element)) {
            validCount++;
          }
        }
      }
      
      return totalCount > 0 ? validCount / totalCount : 0.0;
    });
  }
  
  /**
   * Validate a numeric operation
   * 
   * @param {number} value - Result to validate
   * @param {Object} context - Additional context
   * @returns {Object} Validation result
   */
  validateNumeric(value, context = {}) {
    return this.validator.validate('numeric', value, context);
  }
  
  /**
   * Validate a vector operation
   * 
   * @param {Array} vector - Vector to validate
   * @param {Object} context - Additional context
   * @returns {Object} Validation result
   */
  validateVector(vector, context = {}) {
    return this.validator.validate('vectorSpace', vector, context);
  }
  
  /**
   * Validate a matrix operation
   * 
   * @param {Array} matrix - Matrix to validate
   * @param {Object} context - Additional context
   * @returns {Object} Validation result
   */
  validateMatrix(matrix, context = {}) {
    return this.validator.validate('matrixAlgebra', matrix, context);
  }
  
  /**
   * Get validation statistics
   * 
   * @returns {Object} Validation statistics
   */
  getStats() {
    return this.validator.getStats();
  }
  
  /**
   * Get the underlying CoherenceValidator
   * 
   * @returns {CoherenceValidator} The underlying validator
   */
  getValidator() {
    return this.validator;
  }
}

// Export the module
module.exports = {
  CoherenceValidator,
  MathematicalCoherenceValidator
};