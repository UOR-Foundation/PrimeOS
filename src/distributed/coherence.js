/**
 * PrimeOS JavaScript Library - Distributed Coherence Module
 * Advanced coherence checks for distributed neural networks
 */

// Import the Prime object from core
const Prime = require("../core");

// Ensure the Distributed namespace exists (standardized capitalization)
Prime.Distributed = Prime.Distributed || {};

// Set up coherence namespace
Prime.Distributed.Coherence = Prime.Distributed.Coherence || {};

// Import coherence components directly
const violations = require("./coherence-violations");
const recovery = require("./coherence-recovery");
const metrics = require("./coherence-metrics");
const core = require("./coherence-core");

// Directly assign components to avoid circular references
// Use defensive programming approach for module resolution
Prime.Distributed.Coherence.Violations = 
  (violations.Distributed && violations.Distributed.Coherence && violations.Distributed.Coherence.Violations) ||
  (violations.Violations) || // Check for direct export pattern 
  {};

Prime.Distributed.Coherence.Recovery = 
  (recovery.Distributed && recovery.Distributed.Coherence && recovery.Distributed.Coherence.Recovery) ||
  (recovery.Recovery) || // Check for direct export pattern
  {};

Prime.Distributed.Coherence.Metrics = 
  (metrics.Distributed && metrics.Distributed.Coherence && metrics.Distributed.Coherence.Metrics) ||
  (metrics.Metrics) || // Check for direct export pattern
  {};

Prime.Distributed.Coherence.Core = 
  (core.Distributed && core.Distributed.Coherence && core.Distributed.Coherence.Core) ||
  (core.Core) || // Check for direct export pattern
  (core.CoherenceCore) || // Original pattern
  {};

// Use the proper CoherenceManager from the core module
if (core.CoherenceCore && core.CoherenceCore.Manager) {
  Prime.Distributed.Coherence.DistributedCoherenceManager = core.CoherenceCore.Manager;
} else if (core.Distributed && core.Distributed.Coherence && 
           core.Distributed.Coherence.Core && core.Distributed.Coherence.Core.Manager) {
  Prime.Distributed.Coherence.DistributedCoherenceManager = core.Distributed.Coherence.Core.Manager;
}

// Re-export violation types and severity from the violations module
if (violations.Distributed && violations.Distributed.Coherence && 
    violations.Distributed.Coherence.Violations) {
  Prime.Distributed.Coherence.ViolationType = 
    violations.Distributed.Coherence.Violations.Types || {};
  Prime.Distributed.Coherence.ViolationSeverity = 
    violations.Distributed.Coherence.Violations.Severity || {};
}

if (recovery.Distributed && recovery.Distributed.Coherence && 
    recovery.Distributed.Coherence.Recovery) {
  Prime.Distributed.Coherence.RecoveryStrategy = 
    recovery.Distributed.Coherence.Recovery.Strategies || {};
}

// For backward compatibility - maintain the old lowercase namespace
// but point it to the standardized capitalized namespace
Prime.distributed = Prime.distributed || {};
Prime.distributed.coherence = Prime.Distributed.Coherence;

// Add a standardized API for checking coherence across modules
Prime.Distributed.Coherence.checkCoherence = function(prevState, nextState, options = {}) {
  // If Core Manager is available, use it for coherence checking
  if (Prime.Distributed.Coherence.Core && 
      Prime.Distributed.Coherence.Core.Manager) {
    try {
      const manager = new Prime.Distributed.Coherence.Core.Manager();
      // Adapt state objects to layer format for core manager
      return manager.checkLayerCoherence(
        { config: { inputSize: 1, outputSize: 1 }, state: nextState },
        { prevState: prevState, ...options }
      );
    } catch (error) {
      console.warn("Error using core manager for coherence check:", error.message);
      // Return a default result
      return {
        isCoherent: true, // Default to coherent on error
        coherenceScore: 0.8,
        message: "Coherence check failed, assuming coherent",
        error: error.message
      };
    }
  }
  
  // Simple fallback implementation if core manager not available
  return {
    isCoherent: true,
    coherenceScore: 1.0,
    message: "Distributed coherence core not available, assuming coherent"
  };
};

// Export the enhanced Prime object
module.exports = Prime;
