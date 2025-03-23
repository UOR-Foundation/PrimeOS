/**
 * PrimeOS JavaScript Library - Distributed Coherence Module
 * Advanced coherence checks for distributed neural networks
 */

// Import the Prime object from core
const Prime = require('../core');

// Ensure the distributed namespace exists
Prime.distributed = Prime.distributed || {};

// Set up coherence namespace
Prime.distributed.coherence = Prime.distributed.coherence || {};

// Import coherence components directly
const violations = require('./coherence-violations');
const recovery = require('./coherence-recovery');
const metrics = require('./coherence-metrics');
const core = require('./coherence-core');

// Set up component references with proper circular dependency handling
const components = [
  {
    name: 'CoherenceViolations',
    module:
      violations.Distributed && violations.Distributed.Coherence
        ? violations.Distributed.Coherence.Violations
        : {},
  },
  {
    name: 'CoherenceRecovery',
    module:
      recovery.Distributed && recovery.Distributed.Coherence
        ? recovery.Distributed.Coherence.Recovery
        : {},
  },
  {
    name: 'CoherenceMetrics',
    module:
      metrics.Distributed && metrics.Distributed.Coherence
        ? metrics.Distributed.Coherence.Metrics
        : {},
  },
  { name: 'CoherenceCore', module: core.CoherenceCore || {} },
];

// Add each component to the namespace with circular dependency protection
components.forEach((component) => {
  if (
    Object.getOwnPropertyDescriptor(
      Prime.distributed.coherence,
      component.name,
    ) &&
    Object.getOwnPropertyDescriptor(Prime.distributed.coherence, component.name)
      .get
  ) {
    // Use a more careful approach to update properties that already have getters
    const descriptor = Object.getOwnPropertyDescriptor(
      Prime.distributed.coherence,
      component.name,
    );
    const originalGetter = descriptor.get;

    Object.defineProperty(Prime.distributed.coherence, component.name, {
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
    Prime.distributed.coherence[component.name] = component.module;
  }
});

// Ensure Prime.Distributed namespace exists
Prime.Distributed = Prime.Distributed || {};
Prime.Distributed.Coherence = Prime.Distributed.Coherence || {};

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
  Prime.Distributed.Coherence.CoherenceViolationType =
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

// For backward compatibility
if (
  violations.Distributed &&
  violations.Distributed.Coherence &&
  violations.Distributed.Coherence.Violations
) {
  Prime.Distributed.Coherence.ViolationType =
    violations.Distributed.Coherence.Violations.Types || {};
  Prime.Distributed.CoherenceViolationType =
    violations.Distributed.Coherence.Violations.Types || {};
}

// Export the enhanced Prime object
module.exports = Prime;
