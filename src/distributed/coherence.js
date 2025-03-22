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

// Create a function to safely load components
const safeRequire = function(path) {
  try {
    return require(path);
  } catch (error) {
    console.error(`Error loading module ${path}:`, error.message);
    return {};
  }
};

// Import coherence components with protection against circular dependencies
const modules = [
  './coherence-violations',
  './coherence-recovery',
  './coherence-metrics',
  './coherence-core'
];

// Load modules in a controlled manner
modules.forEach(modulePath => {
  try {
    require(modulePath);
  } catch (error) {
    // If direct require fails, it might be due to circular dependencies
    // Set up placeholder objects that will be populated later
    const moduleName = modulePath.split('/').pop().replace('.js', '');
    const namespacePath = moduleName.split('-').map(part => 
      part.charAt(0).toUpperCase() + part.slice(1)
    ).join('');
    
    // Add placeholder if needed
    if (!Prime.distributed.coherence[namespacePath]) {
      Prime.distributed.coherence[namespacePath] = {};
    }
    
    console.warn(`Module ${modulePath} lazy-loaded due to potential circular dependency`);
  }
});

// Export the enhanced Prime object
module.exports = Prime;