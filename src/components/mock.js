/**
 * PrimeOS JavaScript Library - Component Mock
 * Simple component implementation for tests
 */

// Import the Prime object from core
const Prime = require('../core');

/**
 * Create a simple component for testing
 * @param {Object} config - Component configuration
 * @returns {Object} Created component
 */
function createComponent(config = {}) {
  const component = {
    name: config.name || 'unnamed_component',
    state: { ...config.state },
    methods: { ...config.methods }
  };
  
  // Set up methods to use 'this' context correctly
  Object.keys(component.methods).forEach(methodName => {
    const originalMethod = component.methods[methodName];
    component.methods[methodName] = function(...args) {
      return originalMethod.apply(component, args);
    };
  });
  
  return component;
}

// Add component creation function to Prime namespace
Prime.createComponent = createComponent;

// Export the enhanced Prime object
module.exports = Prime;