/**
 * PrimeOS JavaScript Library - Distributed Computation Module
 * Provides coherence-preserving distributed computation for neural networks
 */

// Import the Prime object from core
const Prime = require("../core");

// Ensure mathematics module is loaded first as it's a dependency
try {
  require("../mathematics");
} catch (error) {
  console.warn("Error loading mathematics module:", error.message);
  // Continue anyway as the distributed module can work with fallbacks
}

// Create the Distributed namespace with proper structure
Prime.Distributed = Prime.Distributed || {};

// Import submodules in a specific order to manage dependencies
// Use a function to safely require modules with error handling
function safeRequire(modulePath) {
  try {
    return require(modulePath);
  } catch (error) {
    console.warn(`Error loading module '${modulePath}':`, error.message);
    return {};
  }
}

// Define the loading order with dependencies managed properly
const modules = [
  // First, import base modules with fewer dependencies
  "./communication",
  "./partition",
  
  // Then import coherence modules in specific order to manage dependencies
  "./coherence-violations",
  "./coherence-recovery",
  "./coherence-metrics",
  "./coherence-core",
  "./coherence",
  
  // Finally, import cluster module (which depends on the others)
  "./cluster"
];

// Load all modules in order, handling any circular dependencies
modules.forEach(modulePath => {
  try {
    safeRequire(modulePath);
  } catch (circularError) {
    console.warn(`Possible circular dependency detected in '${modulePath}':`, circularError.message);
    // For circular dependencies, try loading in a setTimeout to break the cycle
    setTimeout(() => {
      try {
        safeRequire(modulePath);
      } catch (error) {
        console.warn(`Failed to load module '${modulePath}' after circular dependency resolution:`, error.message);
      }
    }, 0);
  }
});

// Ensure backward compatibility using direct assignment instead of getters
if (!Prime.distributed) {
  Prime.distributed = {};
}

// Define properties for distributed immediately to prevent circular reference issues
Prime.distributed.coherence = Prime.Distributed.Coherence;
Prime.distributed.cluster = Prime.Distributed.Cluster;
Prime.distributed.communication = Prime.Distributed.Communication;
Prime.distributed.partition = Prime.Distributed.Partition;

// Set up a default Logger if not available
if (!Prime.Logger) {
  Prime.Logger = {
    debug: console.debug.bind(console),
    info: console.info.bind(console),
    warn: console.warn.bind(console),
    error: console.error.bind(console)
  };
}

// Export the enhanced Prime object
module.exports = Prime;
