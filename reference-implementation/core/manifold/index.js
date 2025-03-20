/**
 * PrimeOS Reference Implementation - Manifold Module
 * 
 * Provides functionality for working with manifolds, including import/export,
 * serialization, validation, and remote synchronization.
 */

const { ManifoldImportExport } = require('./manifold-import-export');
const { NetworkAdapter } = require('./network-adapter');

/**
 * Initialize the manifold system
 * @param {Object} options - Configuration options
 * @param {Object} options.manifoldRegistry - ManifoldRegistry instance
 * @param {Object} options.secureVault - SecureVault instance
 * @param {Object} options.eventBus - EventBus instance
 * @returns {Object} Manifold system
 */
async function initializeManifoldSystem(options = {}) {
  // Create network adapter
  const networkAdapter = new NetworkAdapter({
    headers: {
      'X-PrimeOS-Client': 'PrimeOS-Reference-Implementation'
    }
  });
  
  // Create import/export manager
  const importExport = new ManifoldImportExport({
    ...options,
    networkAdapter
  });
  
  // Initialize import/export
  await importExport.initialize();
  
  // Return manifold system
  return {
    importExport,
    networkAdapter
  };
}

// Export module
module.exports = {
  ManifoldImportExport,
  NetworkAdapter,
  initializeManifoldSystem
};