/**
 * PrimeOS App Bundle System
 * 
 * Entry point for the PrimeOS App Bundle system that provides portable application
 * packaging, distribution, and installation capabilities.
 */

const { BundleManager } = require('./bundle-manager');
const { BundleAPI } = require('./bundle-api');
const { BundleCatalogUI } = require('./bundle-ui');

/**
 * Initialize the bundle system with the given dependencies
 * @param {Object} options - Configuration options
 * @param {Object} options.store - PrimeStore instance for bundle data
 * @param {Object} options.eventBus - EventBus for notifications
 * @param {Object} options.identity - Identity service for signatures
 * @returns {Object} Bundle system components
 */
function initBundleSystem(options) {
  // Create bundle manager
  const bundleManager = new BundleManager({
    store: options.store,
    eventBus: options.eventBus,
    identity: options.identity
  });
  
  // Notify system of bundle component initialization
  options.eventBus.publish('system:component-ready', {
    component: 'bundle',
    timestamp: new Date().toISOString()
  });
  
  return {
    bundleManager,
    BundleAPI,
    BundleCatalogUI,
    
    /**
     * Create a new BundleAPI instance for an app
     * @param {string} appId - Application ID
     * @returns {BundleAPI} Bundle API instance
     */
    createBundleAPI(appId) {
      return new BundleAPI({
        bundleManager,
        eventBus: options.eventBus,
        appId
      });
    },
    
    /**
     * Create a bundle catalog UI component
     * @param {HTMLElement} container - Container element
     * @param {string} appId - Application ID
     * @returns {BundleCatalogUI} Bundle catalog UI instance
     */
    createBundleCatalogUI(container, appId) {
      const bundleAPI = this.createBundleAPI(appId);
      
      return new BundleCatalogUI({
        bundleAPI,
        container,
        eventBus: options.eventBus
      });
    },
    
    /**
     * Connect to the official PrimeOS App repository
     * @returns {Promise<Object>} Connection result
     */
    async connectToOfficialRepository() {
      try {
        const remote = await bundleManager.connectToRemote(
          'https://github.com/UOR-Foundation/PrimeOS-Apps',
          { branch: 'main' }
        );
        
        console.log('Connected to official PrimeOS App repository');
        return { success: true, remote };
      } catch (error) {
        console.error('Failed to connect to official repository:', error);
        return { success: false, error: error.message };
      }
    }
  };
}

// Export the bundle system
module.exports = {
  initBundleSystem,
  BundleManager,
  BundleAPI,
  BundleCatalogUI
};

// Expose to browser environment if applicable
if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.Bundle = {
    initBundleSystem,
    BundleManager,
    BundleAPI,
    BundleCatalogUI
  };
}