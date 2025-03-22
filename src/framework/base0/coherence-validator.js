/**
 * Coherence Validator for the Prime Framework
 * Enhanced version with formal UOR (Universal Object Reference) constraints
 * Includes specialized validation for manifolds and cross-manifold coherence
 * 
 * This file serves as the main entry point for coherence validation
 * and re-exports functionality from modular components
 */

// Define a safe require function to prevent circular dependencies
const safeRequire = function(path) {
  try {
    return require(path);
  } catch (error) {
    console.error(`Error loading module ${path}:`, error.message);
    return {};
  }
};

// Import modular components with protection against circular dependencies
const constraintsModule = safeRequire('./coherence-constraints.js');
const validationModule = safeRequire('./coherence-validation.js');
const manifoldValidatorModule = safeRequire('./manifold-validator.js');

// Extract components with fallbacks
const CoherenceConstraints = constraintsModule.CoherenceConstraints || {};
const CoherenceNorms = constraintsModule.CoherenceNorms || {};
const CoherenceValidator = validationModule.CoherenceValidator || {};
const MathematicalCoherenceValidator = manifoldValidatorModule.MathematicalCoherenceValidator || {};

// Export the module with lazy-loading wrapper support
module.exports = {
  // Core validators
  get CoherenceValidator() {
    return validationModule.CoherenceValidator || {};
  },
  
  get MathematicalCoherenceValidator() {
    return manifoldValidatorModule.MathematicalCoherenceValidator || {};
  },
  
  // Re-export constraints and norms with lazy loading
  get CoherenceConstraints() {
    return constraintsModule.CoherenceConstraints || {};
  },
  
  get CoherenceNorms() {
    return constraintsModule.CoherenceNorms || {};
  }
};