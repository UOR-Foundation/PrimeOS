/**
 * PrimeOS JavaScript Library - Framework
 * Base 0: Manifold Validator
 * Specialized validation for manifolds and cross-manifold operations
 */

// Import core if available
let Prime;
try {
  Prime = require("../../core.js");
} catch (e) {
  // Handle case where core isn't available yet
  Prime = {};
}

// Import Manifold if available
let Manifold;
try {
  const manifestModule = require("./manifold.js");
  Manifold = manifestModule.Manifold;
} catch (e) {
  // Handle case where Manifold isn't available yet
  Manifold = null;
}

// Import the base validator
const { CoherenceValidator } = require('./coherence-validation.js');

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
    
    // Register manifold constraints if enabled
    if (options.enableManifoldValidation !== false) {
      this._registerManifoldConstraints();
    }
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

module.exports = {
  MathematicalCoherenceValidator
};