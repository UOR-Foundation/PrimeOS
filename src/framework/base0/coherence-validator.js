/**
 * Coherence Validator for the Prime Framework
 * Enhanced version with formal UOR (Universal Object Reference) constraints
 * Includes specialized validation for manifolds and cross-manifold coherence
 */

// Import core if available
let Prime;
try {
  Prime = require("../../core.js");
} catch (e) {
  // Handle case where core isn't available yet
  Prime = {};
}

// Try to import Manifold if available
let Manifold;
try {
  const manifestModule = require("./manifold.js");
  Manifold = manifestModule.Manifold;
} catch (e) {
  // Handle case where Manifold isn't available yet
  Manifold = null;
}

/**
 * CoherenceValidator implements formal coherence checking for mathematical operations
 * Based on UOR framework principles with constraint satisfaction verification
 * Provides specialized validation for manifolds and cross-manifold operations
 */
class CoherenceValidator {
  /**
   * Create a new coherence validator
   *
   * @param {Object} options - Configuration options
   * @param {boolean} options.strictMode - Whether to enforce strict coherence (default: false)
   * @param {number} options.toleranceLevel - Numerical tolerance for coherence checks (default: 1e-10)
   * @param {boolean} options.enforceUorConstraints - Whether to enforce UOR constraints (default: true)
   * @param {boolean} options.enableManifoldValidation - Whether to enable manifold validation (default: true)
   * @param {number} options.manifoldCoherenceThreshold - Threshold for manifold coherence (default: 0.8)
   */
  constructor(options = {}) {
    this.strictMode = options.strictMode || false;
    this.toleranceLevel = options.toleranceLevel || 1e-10;
    this.enforceUorConstraints = options.enforceUorConstraints !== false;
    this.enableManifoldValidation = options.enableManifoldValidation !== false;
    this.manifoldCoherenceThreshold = options.manifoldCoherenceThreshold || 0.8;
    this.validators = {};
    this.constraintRegistry = new Map();
    this.coherenceNorms = new Map();
    this.manifoldConstraints = new Map();
    this.crossManifoldMetrics = new Map();

    // Performance tracking
    this._validationStats = {
      totalChecks: 0,
      passedChecks: 0,
      failedChecks: 0,
      totalTime: 0,
      manifoldChecks: 0,
      crossManifoldChecks: 0,
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
    if (!constraint || typeof constraint.validator !== "function") {
      throw new Error("Constraint must have a validator function");
    }

    // Generate a unique ID for this constraint
    const id = `${domain}_${constraint.name || "constraint"}_${Date.now()}`;

    // Ensure domain exists in registry
    if (!this.constraintRegistry.has(domain)) {
      this.constraintRegistry.set(domain, new Map());
    }

    // Store the constraint
    this.constraintRegistry.get(domain).set(id, {
      validator: constraint.validator,
      name: constraint.name || id,
      priority: constraint.priority || 0,
      domain,
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
    if (typeof validator !== "function") {
      throw new Error("Validator must be a function");
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
    if (typeof normFn !== "function") {
      throw new Error("Coherence norm must be a function");
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
      this._validationStats.totalTime += endTime - startTime;

      return {
        valid: true,
        coherence: 1.0,
        message: "No constraints defined for this domain",
      };
    }

    // Sort constraints by priority (descending)
    const sortedConstraints = Array.from(domainConstraints.values()).sort(
      (a, b) => b.priority - a.priority,
    );

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
          priority: constraint.priority,
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
          error: error.message,
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
    this._validationStats.totalTime += endTime - startTime;

    // Return validation result
    return {
      valid: allSatisfied,
      coherence,
      constraintResults: results,
      message: allSatisfied
        ? "All constraints satisfied"
        : "Some constraints violated",
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
      return results.filter((r) => r.satisfied).length / results.length;
    }

    // Weight by priority
    let weightedSum = 0;
    for (const result of results) {
      weightedSum +=
        (result.satisfied ? 1 : 0) * (result.priority / totalPriority);
    }

    return weightedSum;
  }

  /**
   * Register a manifold constraint for validation
   *
   * @param {string} constraintName - Name of the constraint
   * @param {Function} validator - Function that checks if a manifold satisfies the constraint
   * @param {Object} options - Options for the constraint
   * @param {number} options.priority - Priority level (higher values = higher priority)
   * @param {string} options.type - Constraint type ('hard' or 'soft')
   * @returns {string} Constraint ID
   */
  registerManifoldConstraint(constraintName, validator, options = {}) {
    if (!this.enableManifoldValidation) {
      throw new Error("Manifold validation is not enabled");
    }

    if (typeof validator !== "function") {
      throw new Error("Manifold constraint validator must be a function");
    }

    // Generate a unique ID for this constraint
    const id = `manifold_${constraintName}_${Date.now()}`;

    // Ensure manifold constraint registry exists
    if (!this.manifoldConstraints.has(constraintName)) {
      this.manifoldConstraints.set(constraintName, new Map());
    }

    // Store the constraint
    this.manifoldConstraints.get(constraintName).set(id, {
      validator,
      name: constraintName,
      priority: options.priority || 1,
      type: options.type || "soft",
    });

    return id;
  }

  /**
   * Register a cross-manifold coherence metric
   *
   * @param {string} metricName - Name of the metric
   * @param {Function} metricFn - Function that calculates coherence between manifolds
   * @param {Object} options - Options for the metric
   * @returns {string} Metric ID
   */
  registerCrossManifoldMetric(metricName, metricFn, options = {}) {
    if (!this.enableManifoldValidation) {
      throw new Error("Manifold validation is not enabled");
    }

    if (typeof metricFn !== "function") {
      throw new Error("Cross-manifold metric must be a function");
    }

    // Generate a unique ID for this metric
    const id = `cross_manifold_${metricName}_${Date.now()}`;

    // Store the metric
    this.crossManifoldMetrics.set(id, {
      name: metricName,
      fn: metricFn,
      weight: options.weight || 1,
      description: options.description || "",
    });

    return id;
  }

  /**
   * Validate a manifold against registered constraints
   *
   * @param {Object} manifold - The manifold to validate
   * @param {Object} options - Validation options
   * @returns {Object} Validation result with coherence measure
   */
  validateManifold(manifold, options = {}) {
    if (!this.enableManifoldValidation) {
      return { valid: true, coherence: 1.0, message: "Manifold validation is not enabled" };
    }

    const startTime = Date.now();
    this._validationStats.totalChecks++;
    this._validationStats.manifoldChecks++;

    // Check if we have a valid manifold
    if (!Manifold || !(manifold instanceof Manifold)) {
      this._validationStats.failedChecks++;
      return {
        valid: false,
        coherence: 0,
        message: "Invalid manifold object",
      };
    }

    // Collect all constraints from all categories
    const allConstraints = [];
    for (const [_, constraints] of this.manifoldConstraints.entries()) {
      for (const constraint of constraints.values()) {
        allConstraints.push(constraint);
      }
    }

    if (allConstraints.length === 0) {
      // No registered constraints for manifolds
      this._validationStats.passedChecks++;
      const endTime = Date.now();
      this._validationStats.totalTime += endTime - startTime;
      return {
        valid: true,
        coherence: 1.0,
        message: "No constraints defined for manifolds",
      };
    }

    // Sort constraints by priority (descending)
    const sortedConstraints = allConstraints.sort(
      (a, b) => b.priority - a.priority
    );

    // Track constraint satisfaction
    const results = [];
    let allHardConstraintsSatisfied = true;
    let allSoftConstraintsSatisfied = true;

    // Execute constraints in priority order
    for (const constraint of sortedConstraints) {
      try {
        const satisfied = constraint.validator(manifold, options);

        results.push({
          name: constraint.name,
          satisfied,
          priority: constraint.priority,
          type: constraint.type,
        });

        if (!satisfied) {
          if (constraint.type === "hard") {
            allHardConstraintsSatisfied = false;
            
            // In strict mode, fail on first violated hard constraint
            if (this.strictMode) {
              break;
            }
          } else {
            allSoftConstraintsSatisfied = false;
          }
        }
      } catch (error) {
        results.push({
          name: constraint.name,
          satisfied: false,
          priority: constraint.priority,
          type: constraint.type,
          error: error.message,
        });

        if (constraint.type === "hard") {
          allHardConstraintsSatisfied = false;
          if (this.strictMode) {
            break;
          }
        } else {
          allSoftConstraintsSatisfied = false;
        }
      }
    }

    // A manifold is valid if all hard constraints are satisfied
    const valid = allHardConstraintsSatisfied;

    // Compute coherence score based on constraint satisfaction
    // This gives more weight to hard constraints
    let coherence = 0;
    let hardPrioritySum = 0;
    let softPrioritySum = 0;
    let hardSatisfiedPrioritySum = 0;
    let softSatisfiedPrioritySum = 0;

    for (const result of results) {
      if (result.type === "hard") {
        hardPrioritySum += result.priority;
        if (result.satisfied) {
          hardSatisfiedPrioritySum += result.priority;
        }
      } else {
        softPrioritySum += result.priority;
        if (result.satisfied) {
          softSatisfiedPrioritySum += result.priority;
        }
      }
    }

    // Calculate coherence scores for hard and soft constraints
    const hardCoherence = hardPrioritySum > 0
      ? hardSatisfiedPrioritySum / hardPrioritySum
      : 1.0;

    const softCoherence = softPrioritySum > 0
      ? softSatisfiedPrioritySum / softPrioritySum
      : 1.0;

    // Final coherence is weighted average, with hard constraints having more weight
    coherence = (hardCoherence * 0.7) + (softCoherence * 0.3);

    // Update statistics
    if (valid) {
      this._validationStats.passedChecks++;
    } else {
      this._validationStats.failedChecks++;
    }

    const endTime = Date.now();
    this._validationStats.totalTime += endTime - startTime;

    // Return validation result
    return {
      valid,
      coherence,
      hardCoherence,
      softCoherence,
      constraintResults: results,
      message: valid
        ? allSoftConstraintsSatisfied 
          ? "All constraints satisfied" 
          : "All hard constraints satisfied, some soft constraints violated"
        : "Some hard constraints violated",
    };
  }

  /**
   * Validate coherence between two manifolds
   *
   * @param {Object} manifold1 - First manifold
   * @param {Object} manifold2 - Second manifold
   * @param {Object} options - Validation options
   * @returns {Object} Cross-manifold coherence metrics
   */
  validateCrossManifold(manifold1, manifold2, options = {}) {
    if (!this.enableManifoldValidation) {
      return { valid: true, coherence: 1.0, message: "Manifold validation is not enabled" };
    }

    const startTime = Date.now();
    this._validationStats.totalChecks++;
    this._validationStats.crossManifoldChecks++;

    // Check if we have valid manifolds
    if (!Manifold || !(manifold1 instanceof Manifold) || !(manifold2 instanceof Manifold)) {
      this._validationStats.failedChecks++;
      return {
        valid: false,
        coherence: 0,
        message: "Invalid manifold objects",
      };
    }

    // Check if manifolds have compatible types
    if (manifold1.getType() !== manifold2.getType() && !options.allowDifferentTypes) {
      // For different types, coherence is lower but may still be valid
      const baseCoherence = 0.4; // Lower base coherence for different types
      this._validationStats.passedChecks++;
      
      const endTime = Date.now();
      this._validationStats.totalTime += endTime - startTime;
      
      return {
        valid: true,
        coherence: baseCoherence,
        message: "Manifolds have different types",
        metrics: {
          typeCompatibility: 0,
        },
      };
    }

    // If no custom metrics are registered, use default comparison
    if (this.crossManifoldMetrics.size === 0) {
      // Use manifold's built-in coherence check if available
      try {
        const coherenceCheck = manifold1.checkCoherenceWith(manifold2, options);
        const coherence = coherenceCheck.score;
        const valid = coherence >= this.manifoldCoherenceThreshold;
        
        if (valid) {
          this._validationStats.passedChecks++;
        } else {
          this._validationStats.failedChecks++;
        }
        
        const endTime = Date.now();
        this._validationStats.totalTime += endTime - startTime;
        
        return {
          valid,
          coherence,
          message: valid 
            ? "Manifolds are coherent" 
            : "Manifolds are not sufficiently coherent",
          metrics: coherenceCheck.metrics || {},
        };
      } catch (e) {
        // If built-in check fails, fall back to basic comparison
        // Compare invariant properties
        const invariant1 = manifold1.getInvariant() || {};
        const invariant2 = manifold2.getInvariant() || {};
        
        // Calculate similarity between invariants
        const keys1 = Object.keys(invariant1);
        const keys2 = Object.keys(invariant2);
        const commonKeys = keys1.filter(key => keys2.includes(key));
        
        let invariantSimilarity = 0;
        if (commonKeys.length > 0) {
          let matchingValues = 0;
          for (const key of commonKeys) {
            if (invariant1[key] === invariant2[key]) {
              matchingValues++;
            }
          }
          invariantSimilarity = matchingValues / commonKeys.length;
        }
        
        // Calculate space overlap
        const spaces1 = manifold1.getSpaces() || [];
        const spaces2 = manifold2.getSpaces() || [];
        const commonSpaces = spaces1.filter(space => spaces2.includes(space));
        const spaceOverlap = (spaces1.length + spaces2.length > 0)
          ? commonSpaces.length / Math.max(1, (spaces1.length + spaces2.length) / 2)
          : 0;
        
        // Overall coherence
        const coherence = (invariantSimilarity * 0.7) + (spaceOverlap * 0.3);
        const valid = coherence >= this.manifoldCoherenceThreshold;
        
        if (valid) {
          this._validationStats.passedChecks++;
        } else {
          this._validationStats.failedChecks++;
        }
        
        const endTime = Date.now();
        this._validationStats.totalTime += endTime - startTime;
        
        return {
          valid,
          coherence,
          message: valid 
            ? "Manifolds are coherent" 
            : "Manifolds are not sufficiently coherent",
          metrics: {
            invariantSimilarity,
            spaceOverlap,
          },
        };
      }
    } else {
      // Use registered cross-manifold metrics
      const metricResults = [];
      let weightedSum = 0;
      let totalWeight = 0;
      
      // Apply each metric
      for (const [id, metric] of this.crossManifoldMetrics.entries()) {
        try {
          const result = metric.fn(manifold1, manifold2, options);
          const metricValue = typeof result === 'number' ? result : result.value || 0;
          
          metricResults.push({
            id,
            name: metric.name,
            value: metricValue,
            weight: metric.weight,
            details: typeof result === 'object' ? result : null,
          });
          
          weightedSum += metricValue * metric.weight;
          totalWeight += metric.weight;
        } catch (e) {
          metricResults.push({
            id,
            name: metric.name,
            error: e.message,
            weight: metric.weight,
          });
          
          // Use zero for failed metrics
          totalWeight += metric.weight;
        }
      }
      
      // Calculate overall coherence
      const coherence = totalWeight > 0 ? weightedSum / totalWeight : 0;
      const valid = coherence >= this.manifoldCoherenceThreshold;
      
      if (valid) {
        this._validationStats.passedChecks++;
      } else {
        this._validationStats.failedChecks++;
      }
      
      const endTime = Date.now();
      this._validationStats.totalTime += endTime - startTime;
      
      return {
        valid,
        coherence,
        message: valid 
          ? "Manifolds are coherent according to registered metrics" 
          : "Manifolds are not sufficiently coherent",
        metrics: metricResults,
      };
    }
  }

  /**
   * Get validation performance statistics
   *
   * @returns {Object} Validation statistics
   */
  getStats() {
    const successRate =
      this._validationStats.totalChecks > 0
        ? this._validationStats.passedChecks / this._validationStats.totalChecks
        : 0;

    return {
      ...this._validationStats,
      successRate,
      averageTime:
        this._validationStats.totalChecks > 0
          ? this._validationStats.totalTime / this._validationStats.totalChecks
          : 0,
      manifoldSuccessRate:
        this._validationStats.manifoldChecks > 0
          ? (this._validationStats.passedChecks - this._validationStats.failedChecks) / this._validationStats.manifoldChecks
          : 0,
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
      totalTime: 0,
      manifoldChecks: 0,
      crossManifoldChecks: 0,
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
        message: `Value is not of expected type ${type}`,
      };
    }

    // Specific validators for different types
    let domainValid = true;
    let domainCoherence = 1.0;

    // Choose appropriate validator based on type
    switch (type) {
      case "number":
        return this.validate("numeric", value, constraints);
      case "array":
      case "vector":
        return this.validate("vectorSpace", value, constraints);
      case "matrix":
        return this.validate("matrixAlgebra", value, constraints);
      case "function":
        return this.validate("functional", value, constraints);
      case "tensor":
        return this.validate("tensorAlgebra", value, constraints);
      default:
        // Use custom validator if registered
        if (this.validators[type]) {
          try {
            const result = this.validators[type](value, constraints);
            return {
              valid: result.valid !== false,
              coherence:
                result.coherence || (result.valid !== false ? 1.0 : 0.0),
              message: result.message || `Validated ${type} value`,
            };
          } catch (e) {
            return {
              valid: false,
              coherence: 0,
              message: `Error in custom validator: ${e.message}`,
            };
          }
        }

        // Default behavior for unknown types
        return {
          valid: true,
          coherence: 1.0,
          message: `No specific validation for type ${type}`,
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
      case "number":
        return typeof value === "number" && !isNaN(value);
      case "string":
        return typeof value === "string";
      case "boolean":
        return typeof value === "boolean";
      case "function":
        return typeof value === "function";
      case "object":
        return (
          value !== null && typeof value === "object" && !Array.isArray(value)
        );
      case "array":
      case "vector":
        return Array.isArray(value);
      case "matrix":
        return Array.isArray(value) && value.every((row) => Array.isArray(row));
      case "tensor":
        // Recursive check for multi-dimensional arrays
        const checkTensor = (arr, depth = 0) => {
          if (depth > 0 && !Array.isArray(arr)) return true;
          if (depth === 0 && !Array.isArray(arr)) return false;
          if (arr.length === 0) return true;
          const allArrays = arr.every((item) => Array.isArray(item));
          return (
            allArrays && arr.every((subArr) => checkTensor(subArr, depth + 1))
          );
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
 * Enhanced version with support for manifolds and fiber algebra
 */
class MathematicalCoherenceValidator {
  /**
   * Create a new mathematical coherence validator
   *
   * @param {Object} options - Configuration options
   * @param {number} options.numericalTolerance - Numerical tolerance (default: 1e-10)
   * @param {boolean} options.strictMode - Whether to enforce strict coherence
   * @param {boolean} options.enforceUorConstraints - Whether to enforce UOR constraints
   * @param {boolean} options.enableManifoldValidation - Whether to enable manifold validation
   * @param {number} options.manifoldCoherenceThreshold - Manifold coherence threshold
   */
  constructor(options = {}) {
    this.numericalTolerance = options.numericalTolerance || 1e-10;
    this.validator = new CoherenceValidator({
      strictMode: options.strictMode,
      toleranceLevel: this.numericalTolerance,
      enforceUorConstraints: options.enforceUorConstraints,
      enableManifoldValidation: options.enableManifoldValidation !== false,
      manifoldCoherenceThreshold: options.manifoldCoherenceThreshold || 0.8,
    });

    // Register built-in constraints
    this._registerBuiltInConstraints();
    
    // Register built-in manifold constraints if enabled
    if (options.enableManifoldValidation !== false) {
      this._registerManifoldConstraints();
    }
  }

  /**
   * Register built-in mathematical constraints
   *
   * @private
   */
  _registerBuiltInConstraints() {
    // Numeric domain constraints
    this.validator.registerConstraint("numeric", {
      name: "finiteness",
      validator: (value) => Number.isFinite(value),
      priority: 10,
    });

    this.validator.registerConstraint("numeric", {
      name: "non_nan",
      validator: (value) => !Number.isNaN(value),
      priority: 10,
    });

    // Vector space constraints
    this.validator.registerConstraint("vectorSpace", {
      name: "array_elements",
      validator: (value) =>
        Array.isArray(value) && value.every((item) => typeof item === "number"),
      priority: 8,
    });

    this.validator.registerConstraint("vectorSpace", {
      name: "finite_elements",
      validator: (value) =>
        Array.isArray(value) && value.every((item) => Number.isFinite(item)),
      priority: 7,
    });

    // Matrix algebra constraints
    this.validator.registerConstraint("matrixAlgebra", {
      name: "matrix_structure",
      validator: (value) => {
        if (!Array.isArray(value) || value.length === 0) return false;
        if (!value.every((row) => Array.isArray(row))) return false;

        // Check that all rows have the same length
        const rowLength = value[0].length;
        return value.every((row) => row.length === rowLength);
      },
      priority: 9,
    });

    this.validator.registerConstraint("matrixAlgebra", {
      name: "matrix_elements",
      validator: (value) => {
        if (!Array.isArray(value)) return false;
        return value.every(
          (row) =>
            Array.isArray(row) &&
            row.every(
              (item) => typeof item === "number" && Number.isFinite(item),
            ),
        );
      },
      priority: 8,
    });

    // Define coherence norms
    this.validator.defineCoherenceNorm("numeric", (results) => {
      // For numeric values, coherence is binary - either fully coherent or not
      return results.every((r) => r.satisfied) ? 1.0 : 0.0;
    });

    this.validator.defineCoherenceNorm("vectorSpace", (results, value) => {
      // For vectors, consider partial coherence based on the proportion of valid elements
      if (!Array.isArray(value)) return 0.0;

      // If fundamental constraints are violated, coherence is 0
      if (!results.find((r) => r.name === "array_elements")?.satisfied) {
        return 0.0;
      }

      // Count finite elements
      const finiteCount = value.filter((v) => Number.isFinite(v)).length;
      return value.length > 0 ? finiteCount / value.length : 0.0;
    });

    this.validator.defineCoherenceNorm("matrixAlgebra", (results, value) => {
      // For matrices, consider structure and element validity
      if (!results.find((r) => r.name === "matrix_structure")?.satisfied) {
        return 0.0;
      }

      // Count valid elements
      let validCount = 0;
      let totalCount = 0;

      for (const row of value) {
        for (const element of row) {
          totalCount++;
          if (typeof element === "number" && Number.isFinite(element)) {
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
    return this.validator.validate("numeric", value, context);
  }

  /**
   * Validate a vector operation
   *
   * @param {Array} vector - Vector to validate
   * @param {Object} context - Additional context
   * @returns {Object} Validation result
   */
  validateVector(vector, context = {}) {
    return this.validator.validate("vectorSpace", vector, context);
  }

  /**
   * Validate a matrix operation
   *
   * @param {Array} matrix - Matrix to validate
   * @param {Object} context - Additional context
   * @returns {Object} Validation result
   */
  validateMatrix(matrix, context = {}) {
    return this.validator.validate("matrixAlgebra", matrix, context);
  }

  /**
   * Register built-in manifold constraints
   * 
   * @private
   */
  _registerManifoldConstraints() {
    if (!Manifold) {
      return; // Skip if Manifold class is not available
    }

    // Register basic manifold type constraint
    this.validator.registerManifoldConstraint(
      "valid_manifold_type",
      (manifold) => {
        const type = manifold.getType();
        return typeof type === "string" && type.length > 0;
      },
      {
        priority: 10,
        type: "hard",
      }
    );

    // Register manifold space constraint
    this.validator.registerManifoldConstraint(
      "has_valid_spaces",
      (manifold) => {
        const spaces = manifold.getSpaces();
        return Array.isArray(spaces) && spaces.length > 0;
      },
      {
        priority: 8,
        type: "hard",
      }
    );

    // Register invariant properties constraint
    this.validator.registerManifoldConstraint(
      "has_invariant_properties",
      (manifold) => {
        const invariant = manifold.getInvariant();
        return (
          typeof invariant === "object" &&
          invariant !== null &&
          Object.keys(invariant).length > 0
        );
      },
      {
        priority: 7,
        type: "soft",
      }
    );

    // Register variant properties constraint
    this.validator.registerManifoldConstraint(
      "has_variant_properties",
      (manifold) => {
        const variant = manifold.getVariant();
        return (
          typeof variant === "object" &&
          variant !== null &&
          Object.keys(variant).length > 0
        );
      },
      {
        priority: 6,
        type: "soft",
      }
    );

    // Register coherence threshold constraint
    this.validator.registerManifoldConstraint(
      "coherence_threshold_valid",
      (manifold) => {
        const threshold = manifold._coherenceThreshold;
        return (
          typeof threshold === "number" &&
          threshold >= 0 &&
          threshold <= 1
        );
      },
      {
        priority: 5,
        type: "soft",
      }
    );

    // Register cross-manifold metric for topological similarity
    this.validator.registerCrossManifoldMetric(
      "topological_similarity",
      (manifold1, manifold2) => {
        // Check if manifolds have the same dimension based on variant properties
        const variant1 = manifold1.getVariant() || {};
        const variant2 = manifold2.getVariant() || {};
        
        const numericKeys1 = Object.keys(variant1).filter(
          key => typeof variant1[key] === "number"
        );
        
        const numericKeys2 = Object.keys(variant2).filter(
          key => typeof variant2[key] === "number"
        );
        
        // Calculate dimension similarity
        const dimSimilarity = 
          Math.min(numericKeys1.length, numericKeys2.length) / 
          Math.max(1, Math.max(numericKeys1.length, numericKeys2.length));
        
        // Check space compatibility
        const spaces1 = manifold1.getSpaces() || [];
        const spaces2 = manifold2.getSpaces() || [];
        const commonSpaces = spaces1.filter(space => spaces2.includes(space));
        const spaceSimilarity = commonSpaces.length / 
          Math.max(1, Math.max(spaces1.length, spaces2.length));
        
        // Combined similarity with weight towards space compatibility
        return {
          value: dimSimilarity * 0.3 + spaceSimilarity * 0.7,
          details: {
            dimensionSimilarity: dimSimilarity,
            spaceSimilarity: spaceSimilarity,
            commonSpaces: commonSpaces
          }
        };
      },
      {
        weight: 1.5,
        description: "Measures topological similarity between manifolds"
      }
    );

    // Register cross-manifold metric for invariant compatibility
    this.validator.registerCrossManifoldMetric(
      "invariant_compatibility",
      (manifold1, manifold2) => {
        const invariant1 = manifold1.getInvariant() || {};
        const invariant2 = manifold2.getInvariant() || {};
        
        const keys1 = Object.keys(invariant1);
        const keys2 = Object.keys(invariant2);
        
        if (keys1.length === 0 && keys2.length === 0) {
          return { value: 1.0, details: { reason: "Both manifolds have no invariants" } };
        }
        
        const commonKeys = keys1.filter(key => keys2.includes(key));
        
        if (commonKeys.length === 0) {
          return { value: 0.0, details: { reason: "No common invariant properties" } };
        }
        
        // Count matching values
        let matchCount = 0;
        for (const key of commonKeys) {
          if (invariant1[key] === invariant2[key]) {
            matchCount++;
          }
        }
        
        const invariantSimilarity = matchCount / commonKeys.length;
        
        return {
          value: invariantSimilarity,
          details: {
            commonKeys: commonKeys.length,
            totalKeys1: keys1.length,
            totalKeys2: keys2.length,
            matchingValues: matchCount
          }
        };
      },
      {
        weight: 2.0,
        description: "Measures compatibility between manifold invariants"
      }
    );
  }

  /**
   * Validate a manifold
   *
   * @param {Object} manifold - Manifold to validate
   * @param {Object} context - Additional context
   * @returns {Object} Validation result
   */
  validateManifold(manifold, context = {}) {
    if (!Manifold || !(manifold instanceof Manifold)) {
      return {
        valid: false,
        coherence: 0,
        message: "Not a valid manifold object",
      };
    }
    
    return this.validator.validateManifold(manifold, context);
  }

  /**
   * Validate coherence between two manifolds
   *
   * @param {Object} manifold1 - First manifold
   * @param {Object} manifold2 - Second manifold
   * @param {Object} options - Validation options
   * @returns {Object} Cross-manifold coherence metrics
   */
  validateCrossManifold(manifold1, manifold2, options = {}) {
    if (!Manifold || !(manifold1 instanceof Manifold) || !(manifold2 instanceof Manifold)) {
      return {
        valid: false,
        coherence: 0,
        message: "Not valid manifold objects",
      };
    }
    
    return this.validator.validateCrossManifold(manifold1, manifold2, options);
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
  MathematicalCoherenceValidator,
};
