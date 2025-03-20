/**
 * PrimeOS Reference Implementation - Extension System Tests
 * 
 * Tests for the extension system that allows PrimeOS to be extended with
 * plugins, additional components, and custom functionality.
 */

// Import test dependencies
const { ManifoldRegistry } = require('./adapters/manifold-bridge');
const { SecureVault } = require('./adapters/secrets-manager-bridge');

// Import the system under test
const { 
  ExtensionManager, 
  Extension, 
  ExtensionPoint 
} = require('../core/extensions/extension-system');

describe('Extension System', () => {
  let extensionManager;
  let mockEventBus;
  let mockManifoldRegistry;
  let mockSecureVault;
  
  beforeEach(() => {
    // Create mock EventBus
    mockEventBus = {
      publish: jest.fn(),
      subscribe: jest.fn().mockImplementation((event, handler) => {
        return () => {}; // Return unsubscribe function
      })
    };
    
    // Create mock ManifoldRegistry
    mockManifoldRegistry = {
      registerApp: jest.fn().mockImplementation(async (spec) => {
        return {
          getId: () => `extension-${spec.name}`,
          getMeta: () => ({ id: `extension-${spec.name}`, type: 'application' }),
          getInvariant: () => ({ name: spec.name, version: spec.version }),
          getVariant: () => ({})
        };
      }),
      getManifold: jest.fn().mockResolvedValue(null),
      createRelation: jest.fn().mockResolvedValue({}),
      updateManifold: jest.fn().mockResolvedValue({})
    };
    
    // Create mock SecureVault
    mockSecureVault = {
      getSecret: jest.fn().mockResolvedValue(null),
      setSecret: jest.fn().mockResolvedValue(true),
      hasSecret: jest.fn().mockResolvedValue(false),
      removeSecret: jest.fn().mockResolvedValue(true)
    };
    
    // Create extension manager
    extensionManager = new ExtensionManager({
      eventBus: mockEventBus,
      manifoldRegistry: mockManifoldRegistry,
      secureVault: mockSecureVault
    });
  });
  
  describe('Initialization', () => {
    it('should initialize correctly', async () => {
      await extensionManager.initialize();
      
      // Should subscribe to events
      expect(mockEventBus.subscribe).toHaveBeenCalledWith(
        'extension:register-extension-point', 
        expect.any(Function)
      );
      
      expect(mockEventBus.subscribe).toHaveBeenCalledWith(
        'extension:install-request', 
        expect.any(Function)
      );
    });
    
    it('should load installed extensions', async () => {
      // Mock existing extensions
      mockSecureVault.hasSecret.mockResolvedValueOnce(true);
      mockSecureVault.getSecret.mockResolvedValueOnce([
        {
          id: 'test-extension',
          name: 'Test Extension',
          version: '1.0.0',
          extensionPoints: ['ui:toolbar'],
          enabled: true
        }
      ]);
      
      await extensionManager.initialize();
      
      // Should have loaded extension
      expect(extensionManager.extensions.size).toBe(1);
      expect(extensionManager.extensions.get('test-extension')).toBeDefined();
    });
  });
  
  describe('Extension Points', () => {
    beforeEach(async () => {
      await extensionManager.initialize();
    });
    
    it('should register an extension point', async () => {
      const result = await extensionManager.registerExtensionPoint({
        id: 'ui:toolbar',
        name: 'Toolbar Extension Point',
        description: 'Add items to the toolbar',
        schema: {
          type: 'object',
          properties: {
            id: { type: 'string' },
            label: { type: 'string' },
            icon: { type: 'string' }
          },
          required: ['id', 'label']
        }
      });
      
      // Should return extension point
      expect(result).toBeDefined();
      expect(result.id).toBe('ui:toolbar');
      
      // Should add to extension points map
      expect(extensionManager.extensionPoints.has('ui:toolbar')).toBe(true);
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'extension:extension-point-registered',
        expect.objectContaining({
          id: 'ui:toolbar'
        })
      );
    });
    
    it('should throw error if extension point already exists', async () => {
      // Register once
      await extensionManager.registerExtensionPoint({
        id: 'ui:toolbar',
        name: 'Toolbar Extension Point'
      });
      
      // Try to register again
      await expect(extensionManager.registerExtensionPoint({
        id: 'ui:toolbar',
        name: 'Duplicate Toolbar'
      })).rejects.toThrow('Extension point already exists');
    });
    
    it('should get extension point by ID', async () => {
      // Register extension point
      await extensionManager.registerExtensionPoint({
        id: 'ui:toolbar',
        name: 'Toolbar Extension Point'
      });
      
      // Get extension point
      const extensionPoint = extensionManager.getExtensionPoint('ui:toolbar');
      
      expect(extensionPoint).toBeDefined();
      expect(extensionPoint.id).toBe('ui:toolbar');
    });
    
    it('should list all extension points', async () => {
      // Register extension points
      await extensionManager.registerExtensionPoint({
        id: 'ui:toolbar',
        name: 'Toolbar Extension Point'
      });
      
      await extensionManager.registerExtensionPoint({
        id: 'ui:sidebar',
        name: 'Sidebar Extension Point'
      });
      
      // Get all extension points
      const points = extensionManager.getAllExtensionPoints();
      
      expect(points.length).toBe(2);
      expect(points[0].id).toBe('ui:toolbar');
      expect(points[1].id).toBe('ui:sidebar');
    });
  });
  
  describe('Extensions', () => {
    beforeEach(async () => {
      await extensionManager.initialize();
      
      // Register extension points
      await extensionManager.registerExtensionPoint({
        id: 'ui:toolbar',
        name: 'Toolbar Extension Point',
        schema: { type: 'object' }
      });
      
      await extensionManager.registerExtensionPoint({
        id: 'ui:sidebar',
        name: 'Sidebar Extension Point',
        schema: { type: 'object' }
      });
    });
    
    it('should install an extension', async () => {
      // Extension manifest
      const manifest = {
        id: 'test-extension',
        name: 'Test Extension',
        version: '1.0.0',
        description: 'Test extension for PrimeOS',
        author: 'Test Author',
        extensionPoints: {
          'ui:toolbar': [
            {
              id: 'test-button',
              label: 'Test Button',
              icon: 'test-icon'
            }
          ]
        }
      };
      
      const result = await extensionManager.installExtension(manifest);
      
      // Should return extension
      expect(result).toBeDefined();
      expect(result.id).toBe('test-extension');
      
      // Should add to extensions map
      expect(extensionManager.extensions.has('test-extension')).toBe(true);
      
      // Should create extension in manifold registry
      expect(mockManifoldRegistry.registerApp).toHaveBeenCalledWith(
        expect.objectContaining({
          name: 'Test Extension',
          version: '1.0.0',
          type: 'extension'
        })
      );
      
      // Should save to secure vault
      expect(mockSecureVault.setSecret).toHaveBeenCalledWith(
        'installed-extensions',
        expect.arrayContaining([
          expect.objectContaining({
            id: 'test-extension'
          })
        ])
      );
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'extension:installed',
        expect.objectContaining({
          id: 'test-extension'
        })
      );
    });
    
    it('should validate extension against extension point schema', async () => {
      // Update extension point with schema
      extensionManager.extensionPoints.get('ui:toolbar').schema = {
        type: 'object',
        properties: {
          id: { type: 'string' },
          label: { type: 'string' }
        },
        required: ['id', 'label']
      };
      
      // Valid extension
      const validManifest = {
        id: 'valid-extension',
        name: 'Valid Extension',
        version: '1.0.0',
        extensionPoints: {
          'ui:toolbar': [
            {
              id: 'test-button',
              label: 'Test Button'
            }
          ]
        }
      };
      
      // Invalid extension (missing required label)
      const invalidManifest = {
        id: 'invalid-extension',
        name: 'Invalid Extension',
        version: '1.0.0',
        extensionPoints: {
          'ui:toolbar': [
            {
              id: 'test-button'
              // missing label
            }
          ]
        }
      };
      
      // Should install valid extension
      await expect(extensionManager.installExtension(validManifest)).resolves.toBeDefined();
      
      // Should reject invalid extension
      await expect(extensionManager.installExtension(invalidManifest)).rejects.toThrow('Schema validation failed');
    });
    
    it('should uninstall an extension', async () => {
      // First install an extension
      await extensionManager.installExtension({
        id: 'test-extension',
        name: 'Test Extension',
        version: '1.0.0',
        extensionPoints: {
          'ui:toolbar': [
            {
              id: 'test-button',
              label: 'Test Button'
            }
          ]
        }
      });
      
      // Then uninstall it
      const result = await extensionManager.uninstallExtension('test-extension');
      
      // Should return success
      expect(result).toBe(true);
      
      // Should remove from extensions map
      expect(extensionManager.extensions.has('test-extension')).toBe(false);
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'extension:uninstalled',
        expect.objectContaining({
          id: 'test-extension'
        })
      );
    });
    
    it('should enable and disable extensions', async () => {
      // Install extension
      await extensionManager.installExtension({
        id: 'test-extension',
        name: 'Test Extension',
        version: '1.0.0',
        extensionPoints: {
          'ui:toolbar': [
            {
              id: 'test-button',
              label: 'Test Button'
            }
          ]
        }
      });
      
      // Disable extension
      await extensionManager.setExtensionEnabled('test-extension', false);
      
      // Check state
      const extension = extensionManager.extensions.get('test-extension');
      expect(extension.enabled).toBe(false);
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'extension:disabled',
        expect.objectContaining({
          id: 'test-extension'
        })
      );
      
      // Re-enable extension
      await extensionManager.setExtensionEnabled('test-extension', true);
      
      // Check state
      expect(extension.enabled).toBe(true);
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'extension:enabled',
        expect.objectContaining({
          id: 'test-extension'
        })
      );
    });
  });
  
  describe('Extension Content', () => {
    beforeEach(async () => {
      await extensionManager.initialize();
      
      // Register extension points
      await extensionManager.registerExtensionPoint({
        id: 'ui:toolbar',
        name: 'Toolbar Extension Point'
      });
      
      await extensionManager.registerExtensionPoint({
        id: 'ui:sidebar',
        name: 'Sidebar Extension Point'
      });
      
      // Install extensions
      await extensionManager.installExtension({
        id: 'extension-1',
        name: 'Extension 1',
        version: '1.0.0',
        extensionPoints: {
          'ui:toolbar': [
            { id: 'button-1', label: 'Button 1' },
            { id: 'button-2', label: 'Button 2' }
          ]
        }
      });
      
      await extensionManager.installExtension({
        id: 'extension-2',
        name: 'Extension 2',
        version: '1.0.0',
        extensionPoints: {
          'ui:toolbar': [
            { id: 'button-3', label: 'Button 3' }
          ],
          'ui:sidebar': [
            { id: 'panel-1', label: 'Panel 1' }
          ]
        }
      });
    });
    
    it('should get all content for an extension point', () => {
      // Get all toolbar content
      const toolbarContent = extensionManager.getExtensionPointContent('ui:toolbar');
      
      // Should return all items
      expect(toolbarContent.length).toBe(3);
      expect(toolbarContent[0].id).toBe('button-1');
      expect(toolbarContent[1].id).toBe('button-2');
      expect(toolbarContent[2].id).toBe('button-3');
      
      // Get all sidebar content
      const sidebarContent = extensionManager.getExtensionPointContent('ui:sidebar');
      
      // Should return all items
      expect(sidebarContent.length).toBe(1);
      expect(sidebarContent[0].id).toBe('panel-1');
    });
    
    it('should filter out content from disabled extensions', async () => {
      // Disable extension-1
      await extensionManager.setExtensionEnabled('extension-1', false);
      
      // Get toolbar content
      const toolbarContent = extensionManager.getExtensionPointContent('ui:toolbar');
      
      // Should only return content from enabled extensions
      expect(toolbarContent.length).toBe(1);
      expect(toolbarContent[0].id).toBe('button-3');
    });
    
    it('should get content by item ID', () => {
      // Get specific item
      const button2 = extensionManager.getContentItemById('ui:toolbar', 'button-2');
      
      // Should return the item
      expect(button2).toBeDefined();
      expect(button2.id).toBe('button-2');
      expect(button2.label).toBe('Button 2');
      
      // Should include metadata
      expect(button2.extensionId).toBe('extension-1');
    });
    
    it('should subscribe to extension point content changes', async () => {
      // Create mock handler
      const handler = jest.fn();
      
      // Subscribe to toolbar changes
      extensionManager.subscribeToExtensionPoint('ui:toolbar', handler);
      
      // Install new extension with toolbar content
      await extensionManager.installExtension({
        id: 'extension-3',
        name: 'Extension 3',
        version: '1.0.0',
        extensionPoints: {
          'ui:toolbar': [
            { id: 'button-4', label: 'Button 4' }
          ]
        }
      });
      
      // Handler should be called
      expect(handler).toHaveBeenCalledWith(
        expect.arrayContaining([
          expect.objectContaining({ id: 'button-4' })
        ])
      );
    });
  });
});