/**
 * PrimeOS JavaScript Library - Distributed Computation Module
 * Provides coherence-preserving distributed computation for neural networks
 */

// Import the Prime object from core
const Prime = require("../core");

// Create the Distributed namespace with proper structure
Prime.Distributed = Prime.Distributed || {};

// Import submodules in a specific order to manage dependencies
// First, import base modules
require("./communication");
require("./partition");

// Then import coherence modules
require("./coherence-violations");
require("./coherence-recovery");
require("./coherence-metrics");
require("./coherence-core");
require("./coherence");

// Finally, import cluster module (which depends on the others)
require("./cluster");

// Ensure backward compatibility
if (!Prime.distributed) {
  Prime.distributed = {};
  
  // Create redirection for backward compatibility
  Object.defineProperty(Prime.distributed, 'coherence', {
    get: function() { return Prime.Distributed.Coherence; },
    enumerable: true,
    configurable: true
  });
  
  Object.defineProperty(Prime.distributed, 'cluster', {
    get: function() { return Prime.Distributed.Cluster; },
    enumerable: true,
    configurable: true
  });
  
  Object.defineProperty(Prime.distributed, 'communication', {
    get: function() { return Prime.Distributed.Communication; },
    enumerable: true,
    configurable: true
  });
  
  Object.defineProperty(Prime.distributed, 'partition', {
    get: function() { return Prime.Distributed.Partition; },
    enumerable: true,
    configurable: true
  });
}

// Export the enhanced Prime object
module.exports = Prime;
