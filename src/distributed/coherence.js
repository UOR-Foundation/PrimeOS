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

// Set up component references with proper circular dependency handling
const components = [
  {
    name: "Violations",
    module:
      violations.Distributed && violations.Distributed.Coherence
        ? violations.Distributed.Coherence.Violations
        : {},
  },
  {
    name: "Recovery",
    module:
      recovery.Distributed && recovery.Distributed.Coherence
        ? recovery.Distributed.Coherence.Recovery
        : {},
  },
  {
    name: "Metrics",
    module:
      metrics.Distributed && metrics.Distributed.Coherence
        ? metrics.Distributed.Coherence.Metrics
        : {},
  },
  { name: "Core", module: core.CoherenceCore || {} },
];

// Add each component to the namespace with circular dependency protection
components.forEach((component) => {
  if (
    Object.getOwnPropertyDescriptor(
      Prime.Distributed.Coherence,
      component.name,
    ) &&
    Object.getOwnPropertyDescriptor(Prime.Distributed.Coherence, component.name)
      .get
  ) {
    // Use a more careful approach to update properties that already have getters
    const descriptor = Object.getOwnPropertyDescriptor(
      Prime.Distributed.Coherence,
      component.name,
    );
    const originalGetter = descriptor.get;

    Object.defineProperty(Prime.Distributed.Coherence, component.name, {
      get: function () {
        const result = originalGetter.call(this);
        if (!result || Object.keys(result).length === 0) {
          return component.module;
        }
        return result;
      },
      configurable: true,
    });
  } else {
    // Direct assignment if no getter exists
    Prime.Distributed.Coherence[component.name] = component.module;
  }
});

// Use the proper CoherenceManager from the core module
if (core.CoherenceCore && core.CoherenceCore.Manager) {
  Prime.Distributed.Coherence.DistributedCoherenceManager =
    core.CoherenceCore.Manager;
}

// Re-export violation types and severity from the violations module
if (
  violations.Distributed &&
  violations.Distributed.Coherence &&
  violations.Distributed.Coherence.Violations
) {
  Prime.Distributed.Coherence.ViolationType =
    violations.Distributed.Coherence.Violations.Types || {};
  Prime.Distributed.Coherence.ViolationSeverity =
    violations.Distributed.Coherence.Violations.Severity || {};
}

if (
  recovery.Distributed &&
  recovery.Distributed.Coherence &&
  recovery.Distributed.Coherence.Recovery
) {
  Prime.Distributed.Coherence.RecoveryStrategy =
    recovery.Distributed.Coherence.Recovery.Strategies || {};
}

// For backward compatibility - maintain the old lowercase namespace
// but point it to the standardized capitalized namespace
Prime.distributed = Prime.distributed || {};
Prime.distributed.coherence = Prime.Distributed.Coherence;

// Export the enhanced Prime object
module.exports = Prime;
