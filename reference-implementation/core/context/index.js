/**
 * PrimeOS Reference Implementation - Context Module
 * 
 * Provides context sharing mechanisms for PrimeOS components and applications.
 * Context sharing enables topological data visualization and context-aware behavior.
 */

const { ContextProvider, ContextConsumer, ContextHub, SchemaValidator } = require('./context-sharing');

/**
 * Initialize the context system
 * @param {Object} options - Configuration options
 * @param {Object} options.eventBus - EventBus instance
 * @param {Object} options.manifoldRegistry - ManifoldRegistry instance
 * @returns {Object} Context system
 */
async function initializeContextSystem(options = {}) {
  // Create context hub
  const contextHub = new ContextHub(options);
  
  // Initialize hub
  await contextHub.initialize();
  
  // Return context system
  return {
    hub: contextHub,
    
    // Factory functions
    createProvider: async (options) => {
      return contextHub.registerProvider(options);
    },
    
    createConsumer: async (options) => {
      return contextHub.registerConsumer(options);
    }
  };
}

// Export module
module.exports = {
  ContextProvider,
  ContextConsumer,
  ContextHub,
  SchemaValidator,
  initializeContextSystem
};