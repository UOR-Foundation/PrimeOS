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
// Use direct property assignments instead of descriptors and getters
Prime.Distributed.Coherence.Violations = violations.Distributed && 
  violations.Distributed.Coherence && 
  violations.Distributed.Coherence.Violations || {};

Prime.Distributed.Coherence.Recovery = recovery.Distributed && 
  recovery.Distributed.Coherence && 
  recovery.Distributed.Coherence.Recovery || {};

Prime.Distributed.Coherence.Metrics = metrics.Distributed && 
  metrics.Distributed.Coherence && 
  metrics.Distributed.Coherence.Metrics || {};

Prime.Distributed.Coherence.Core = core.CoherenceCore || 
  (core.Distributed && core.Distributed.Coherence && core.Distributed.Coherence.Core) || {};

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

// Export the enhanced Prime object
module.exports = Prime;
