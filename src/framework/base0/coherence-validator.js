/**
 * Coherence Validator for the Prime Framework
 * Enhanced version with formal UOR (Universal Object Reference) constraints
 * Includes specialized validation for manifolds and cross-manifold coherence
 * 
 * This file serves as the main entry point for coherence validation
 * and re-exports functionality from modular components
 */

// Import modular components
const { CoherenceConstraints, CoherenceNorms } = require('./coherence-constraints.js');
const { CoherenceValidator } = require('./coherence-validation.js');
const { MathematicalCoherenceValidator } = require('./manifold-validator.js');

// Export the module
module.exports = {
  CoherenceValidator,
  MathematicalCoherenceValidator,
  
  // Re-export constraints and norms for backwards compatibility
  CoherenceConstraints,
  CoherenceNorms
};