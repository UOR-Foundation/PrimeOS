/**
 * PrimeOS Reference Implementation - Extensions Module
 * 
 * Provides extensibility mechanisms for PrimeOS through plugins and extension points.
 * The extension system allows components, UI elements, and functionality to be added
 * to PrimeOS without modifying the core system.
 */

const { ExtensionManager, Extension, ExtensionPoint, SchemaValidator } = require('./extension-system');

/**
 * Initialize the extension system
 * @param {Object} options - Configuration options
 * @param {Object} options.eventBus - EventBus instance
 * @param {Object} options.manifoldRegistry - ManifoldRegistry instance
 * @param {Object} options.secureVault - SecureVault instance
 * @returns {Object} Extension system
 */
async function initializeExtensionSystem(options = {}) {
  // Create extension manager
  const extensionManager = new ExtensionManager(options);
  
  // Initialize manager
  await extensionManager.initialize();
  
  // Register standard extension points
  await Promise.all([
    // UI extension points
    extensionManager.registerExtensionPoint({
      id: 'ui:toolbar',
      name: 'Toolbar',
      description: 'Add items to the main toolbar',
      schema: {
        type: 'object',
        properties: {
          id: { type: 'string' },
          label: { type: 'string' },
          icon: { type: 'string' },
          position: { type: 'number' }
        },
        required: ['id', 'label']
      }
    }),
    
    extensionManager.registerExtensionPoint({
      id: 'ui:sidebar',
      name: 'Sidebar',
      description: 'Add panels to the sidebar',
      schema: {
        type: 'object',
        properties: {
          id: { type: 'string' },
          label: { type: 'string' },
          icon: { type: 'string' },
          position: { type: 'number' }
        },
        required: ['id', 'label']
      }
    }),
    
    extensionManager.registerExtensionPoint({
      id: 'ui:contextmenu',
      name: 'Context Menu',
      description: 'Add items to context menus',
      schema: {
        type: 'object',
        properties: {
          id: { type: 'string' },
          label: { type: 'string' },
          icon: { type: 'string' },
          context: { type: 'string' }
        },
        required: ['id', 'label', 'context']
      }
    }),
    
    // Functionality extension points
    extensionManager.registerExtensionPoint({
      id: 'context:providers',
      name: 'Context Providers',
      description: 'Provide context to the system',
      schema: {
        type: 'object',
        properties: {
          id: { type: 'string' },
          contextType: { type: 'string' },
          description: { type: 'string' }
        },
        required: ['id', 'contextType']
      }
    }),
    
    extensionManager.registerExtensionPoint({
      id: 'manifold:converters',
      name: 'Manifold Converters',
      description: 'Convert between manifold formats',
      schema: {
        type: 'object',
        properties: {
          id: { type: 'string' },
          sourceType: { type: 'string' },
          targetType: { type: 'string' },
          description: { type: 'string' }
        },
        required: ['id', 'sourceType', 'targetType']
      }
    })
  ]);
  
  // Return extension system
  return {
    manager: extensionManager,
    
    // Factory functions
    registerExtensionPoint: async (options) => {
      return extensionManager.registerExtensionPoint(options);
    },
    
    installExtension: async (manifest) => {
      return extensionManager.installExtension(manifest);
    },
    
    getContentFor: (extensionPointId) => {
      return extensionManager.getExtensionPointContent(extensionPointId);
    },
    
    subscribeToExtensionPoint: (extensionPointId, callback) => {
      return extensionManager.subscribeToExtensionPoint(extensionPointId, callback);
    }
  };
}

// Export module
module.exports = {
  ExtensionManager,
  Extension,
  ExtensionPoint,
  SchemaValidator,
  initializeExtensionSystem
};