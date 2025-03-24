/**
 * PrimeOS JavaScript Library - Distributed Computation Module
 * Provides coherence-preserving distributed computation for neural networks
 */

// Import the Prime object from core
const Prime = require("../core");

// Ensure mathematics module is loaded first as it's a dependency
require("../mathematics");

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

// Ensure backward compatibility using direct assignment instead of getters
if (!Prime.distributed) {
  Prime.distributed = {};
}

// Define properties for distributed immediately to prevent circular reference issues
Prime.distributed.coherence = Prime.Distributed.Coherence;
Prime.distributed.cluster = Prime.Distributed.Cluster;
Prime.distributed.communication = Prime.Distributed.Communication;
Prime.distributed.partition = Prime.Distributed.Partition;

// Export the enhanced Prime object
module.exports = Prime;
