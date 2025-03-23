/**
 * PrimeOS JavaScript Library - Component System
 * Main entry point for component modules
 * Version 1.0.0
 */

// Import Prime using CommonJS to avoid circular dependency
const Prime = require('../core.js');
// Ensure all modules are loaded in correct order
require('../mathematics.js');
require('../coherence.js');
require('../framework/index.js');

// Import component modules in correct dependency order
require('./base.js');
require('./registry.js');
require('./factory.js');
require('./template.js');
require('./rendering.js');
require('./performance.js');
require('./documentation.js');

(function (Prime) {
  // Ensure Prime.Components namespace exists
  Prime.Components = Prime.Components || {};

  // Add version information for the component system
  Prime.Components.version = '1.0.0';

  // Map of loaded modules
  Prime.Components.modules = [
    'base',
    'registry',
    'factory',
    'template',
    'rendering',
    'performance',
    'documentation',
  ];

  // Publish component system loaded event
  Prime.EventBus.publish('module:loaded', { name: 'component-system' });
})(Prime);

// CommonJS export (no ES module export to avoid circular dependency)
if (typeof module !== 'undefined' && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== 'undefined') {
  window.Prime = Prime;
}
