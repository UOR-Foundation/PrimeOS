/**
 * PrimeOS Reference Implementation - Remote Manifold Import/Export Tests
 * 
 * Tests for the functionality to import and export manifolds between PrimeOS instances.
 */

// Import test dependencies
const { ManifoldRegistry } = require('./adapters/manifold-bridge');
const { SecureVault } = require('./adapters/secrets-manager-bridge');

// Import system under test
const { ManifoldImportExport } = require('../core/manifold/manifold-import-export');

describe('Remote Manifold Import/Export', () => {
  let importExport;
  let mockManifoldRegistry;
  let mockSecureVault;
  let mockEventBus;
  let mockNetworkAdapter;
  
  beforeEach(() => {
    // Create mock ManifoldRegistry
    mockManifoldRegistry = {
      getManifold: jest.fn().mockResolvedValue(null),
      getManifolds: jest.fn().mockResolvedValue([]),
      registerApp: jest.fn().mockImplementation(async (spec) => {
        return {
          getId: () => `app-${spec.name}`,
          getMeta: () => ({ id: `app-${spec.name}`, type: 'application' }),
          getInvariant: () => ({ name: spec.name, version: spec.version }),
          getVariant: () => ({})
        };
      }),
      createRelation: jest.fn().mockResolvedValue({}),
      findManifolds: jest.fn().mockResolvedValue([]),
      updateManifold: jest.fn().mockResolvedValue({})
    };
    
    // Create mock SecureVault
    mockSecureVault = {
      getSecret: jest.fn().mockResolvedValue(null),
      setSecret: jest.fn().mockResolvedValue(true),
      hasSecret: jest.fn().mockResolvedValue(false),
      removeSecret: jest.fn().mockResolvedValue(true)
    };
    
    // Create mock EventBus
    mockEventBus = {
      publish: jest.fn(),
      subscribe: jest.fn().mockImplementation((event, handler) => {
        return () => {}; // Return unsubscribe function
      })
    };
    
    // Create mock NetworkAdapter
    mockNetworkAdapter = {
      get: jest.fn().mockResolvedValue({ data: null }),
      post: jest.fn().mockResolvedValue({ data: null }),
      setAuthToken: jest.fn()
    };
    
    // Create system under test
    importExport = new ManifoldImportExport({
      manifoldRegistry: mockManifoldRegistry,
      secureVault: mockSecureVault,
      eventBus: mockEventBus,
      networkAdapter: mockNetworkAdapter
    });
  });
  
  describe('Initialization', () => {
    it('should initialize correctly', async () => {
      await importExport.initialize();
      
      // Should subscribe to events
      expect(mockEventBus.subscribe).toHaveBeenCalledWith(
        'remote-manifold:import-request', 
        expect.any(Function)
      );
      
      expect(mockEventBus.subscribe).toHaveBeenCalledWith(
        'remote-manifold:export-request', 
        expect.any(Function)
      );
    });
    
    it('should load credentials from secure vault', async () => {
      // Mock existing credentials
      mockSecureVault.hasSecret.mockResolvedValueOnce(true);
      mockSecureVault.getSecret.mockResolvedValueOnce({
        endpoints: [
          { name: 'TestEndpoint', url: 'https://test.primeos.org', token: 'test-token' }
        ]
      });
      
      await importExport.initialize();
      
      // Should have loaded credentials
      expect(importExport.remoteEndpoints.length).toBe(1);
      expect(importExport.remoteEndpoints[0].name).toBe('TestEndpoint');
    });
  });
  
  describe('Export Functionality', () => {
    beforeEach(async () => {
      await importExport.initialize();
    });
    
    it('should export a single manifold', async () => {
      // Mock manifold
      const mockManifold = {
        getId: () => 'test-manifold',
        getMeta: () => ({ id: 'test-manifold', type: 'application' }),
        getInvariant: () => ({ name: 'TestApp', version: '1.0.0' }),
        getVariant: () => ({ status: 'active' }),
        getRelatedManifolds: () => [],
        toJSON: () => ({
          meta: { id: 'test-manifold', type: 'application' },
          invariant: { name: 'TestApp', version: '1.0.0' },
          variant: { status: 'active' }
        })
      };
      
      mockManifoldRegistry.getManifold.mockResolvedValueOnce(mockManifold);
      
      // Mock serialized manifold response
      mockNetworkAdapter.post.mockResolvedValueOnce({
        data: {
          success: true,
          manifestId: 'remote-test-manifold'
        }
      });
      
      // Export manifold
      const result = await importExport.exportManifold({
        manifoldId: 'test-manifold',
        endpointUrl: 'https://remote.primeos.org',
        includeRelated: false
      });
      
      // Should send correct request
      expect(mockNetworkAdapter.post).toHaveBeenCalledWith(
        'https://remote.primeos.org/api/manifolds/import',
        expect.objectContaining({
          manifold: expect.objectContaining({
            meta: expect.objectContaining({ id: 'test-manifold' })
          })
        })
      );
      
      // Should return success result
      expect(result.success).toBe(true);
      expect(result.remoteId).toBe('remote-test-manifold');
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'remote-manifold:exported',
        expect.objectContaining({
          sourceId: 'test-manifold',
          remoteId: 'remote-test-manifold'
        })
      );
    });
    
    it('should export a manifold with related manifolds', async () => {
      // Mock main manifold
      const mockManifold = {
        getId: () => 'test-manifold',
        getMeta: () => ({ id: 'test-manifold', type: 'application' }),
        getInvariant: () => ({ name: 'TestApp', version: '1.0.0' }),
        getVariant: () => ({ status: 'active' }),
        getRelatedManifolds: () => [
          {
            type: 'uses',
            manifold: {
              getId: () => 'related-manifold',
              getMeta: () => ({ id: 'related-manifold', type: 'component' }),
              getInvariant: () => ({ name: 'RelatedComponent', version: '1.0.0' }),
              getVariant: () => ({}),
              getRelatedManifolds: () => [],
              toJSON: () => ({
                meta: { id: 'related-manifold', type: 'component' },
                invariant: { name: 'RelatedComponent', version: '1.0.0' },
                variant: {}
              })
            }
          }
        ],
        toJSON: () => ({
          meta: { id: 'test-manifold', type: 'application' },
          invariant: { name: 'TestApp', version: '1.0.0' },
          variant: { status: 'active' }
        })
      };
      
      mockManifoldRegistry.getManifold.mockResolvedValueOnce(mockManifold);
      
      // Mock network response
      mockNetworkAdapter.post.mockResolvedValueOnce({
        data: {
          success: true,
          manifestId: 'remote-test-manifold',
          relatedManifoldIds: {
            'related-manifold': 'remote-related-manifold'
          }
        }
      });
      
      // Export manifold with related
      const result = await importExport.exportManifold({
        manifoldId: 'test-manifold',
        endpointUrl: 'https://remote.primeos.org',
        includeRelated: true
      });
      
      // Should send correct request
      expect(mockNetworkAdapter.post).toHaveBeenCalledWith(
        'https://remote.primeos.org/api/manifolds/import',
        expect.objectContaining({
          manifold: expect.objectContaining({
            meta: expect.objectContaining({ id: 'test-manifold' })
          }),
          relatedManifolds: expect.arrayContaining([
            expect.objectContaining({
              meta: expect.objectContaining({ id: 'related-manifold' })
            })
          ]),
          relationships: expect.arrayContaining([
            expect.objectContaining({
              sourceId: 'test-manifold',
              targetId: 'related-manifold',
              type: 'uses'
            })
          ])
        })
      );
      
      // Should return success result with related info
      expect(result.success).toBe(true);
      expect(result.remoteId).toBe('remote-test-manifold');
      expect(result.relatedRemoteIds['related-manifold']).toBe('remote-related-manifold');
    });
    
    it('should handle export failures gracefully', async () => {
      // Mock manifold
      mockManifoldRegistry.getManifold.mockResolvedValueOnce({
        getId: () => 'test-manifold',
        getMeta: () => ({ id: 'test-manifold', type: 'application' }),
        getInvariant: () => ({ name: 'TestApp', version: '1.0.0' }),
        getVariant: () => ({}),
        getRelatedManifolds: () => [],
        toJSON: () => ({
          meta: { id: 'test-manifold', type: 'application' },
          invariant: { name: 'TestApp', version: '1.0.0' },
          variant: {}
        })
      });
      
      // Mock error response
      mockNetworkAdapter.post.mockRejectedValueOnce(new Error('Network error'));
      
      // Export manifold
      await expect(importExport.exportManifold({
        manifoldId: 'test-manifold',
        endpointUrl: 'https://remote.primeos.org'
      })).rejects.toThrow('Network error');
      
      // Should publish error event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'remote-manifold:export-error',
        expect.objectContaining({
          manifoldId: 'test-manifold',
          error: expect.any(Error)
        })
      );
    });
  });
  
  describe('Import Functionality', () => {
    beforeEach(async () => {
      await importExport.initialize();
    });
    
    it('should import a single manifold', async () => {
      // Mock remote manifold data
      const remoteMorphology = {
        manifold: {
          meta: { id: 'remote-manifold', type: 'application' },
          invariant: { name: 'RemoteApp', version: '1.0.0' },
          variant: { status: 'active' }
        },
        relatedManifolds: [],
        relationships: []
      };
      
      mockNetworkAdapter.get.mockResolvedValueOnce({
        data: remoteMorphology
      });
      
      // Import manifold
      const result = await importExport.importManifold({
        remoteId: 'remote-manifold',
        endpointUrl: 'https://remote.primeos.org'
      });
      
      // Should retrieve remote data
      expect(mockNetworkAdapter.get).toHaveBeenCalledWith(
        'https://remote.primeos.org/api/manifolds/export/remote-manifold'
      );
      
      // Should register manifold locally
      expect(mockManifoldRegistry.registerApp).toHaveBeenCalledWith(
        expect.objectContaining({
          name: 'RemoteApp',
          version: '1.0.0',
          remoteOrigin: 'https://remote.primeos.org',
          originalId: 'remote-manifold'
        })
      );
      
      // Should return success result
      expect(result.success).toBe(true);
      expect(result.localId).toBeDefined();
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'remote-manifold:imported',
        expect.objectContaining({
          remoteId: 'remote-manifold',
          localId: expect.any(String)
        })
      );
    });
    
    it('should import a manifold with related manifolds', async () => {
      // Mock remote morphology data
      const remoteMorphology = {
        manifold: {
          meta: { id: 'remote-app', type: 'application' },
          invariant: { name: 'RemoteApp', version: '1.0.0' },
          variant: { status: 'active' }
        },
        relatedManifolds: [
          {
            meta: { id: 'remote-component', type: 'component' },
            invariant: { name: 'RemoteComponent', version: '1.0.0' },
            variant: {}
          }
        ],
        relationships: [
          {
            sourceId: 'remote-app',
            targetId: 'remote-component',
            type: 'uses',
            metadata: {}
          }
        ]
      };
      
      mockNetworkAdapter.get.mockResolvedValueOnce({
        data: remoteMorphology
      });
      
      // Mock registerApp to return different IDs for different calls
      mockManifoldRegistry.registerApp
        .mockResolvedValueOnce({
          getId: () => 'local-app',
          getMeta: () => ({ id: 'local-app', type: 'application' })
        })
        .mockResolvedValueOnce({
          getId: () => 'local-component',
          getMeta: () => ({ id: 'local-component', type: 'component' })
        });
      
      // Import manifold
      const result = await importExport.importManifold({
        remoteId: 'remote-app',
        endpointUrl: 'https://remote.primeos.org',
        includeRelated: true
      });
      
      // Should register both manifolds
      expect(mockManifoldRegistry.registerApp).toHaveBeenCalledTimes(2);
      
      // Should create relation
      expect(mockManifoldRegistry.createRelation).toHaveBeenCalledWith(
        'local-app',
        'local-component',
        'uses',
        expect.any(Object)
      );
      
      // Should return success with ID mappings
      expect(result.success).toBe(true);
      expect(result.localId).toBe('local-app');
      expect(result.relatedLocalIds['remote-component']).toBe('local-component');
    });
    
    it('should handle import failures gracefully', async () => {
      // Mock network error
      mockNetworkAdapter.get.mockRejectedValueOnce(new Error('Network error'));
      
      // Import manifold
      await expect(importExport.importManifold({
        remoteId: 'remote-manifold',
        endpointUrl: 'https://remote.primeos.org'
      })).rejects.toThrow('Network error');
      
      // Should publish error event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'remote-manifold:import-error',
        expect.objectContaining({
          remoteId: 'remote-manifold',
          error: expect.any(Error)
        })
      );
    });
  });
  
  describe('Remote Endpoint Management', () => {
    beforeEach(async () => {
      await importExport.initialize();
    });
    
    it('should add a remote endpoint', async () => {
      // Add endpoint
      await importExport.addRemoteEndpoint({
        name: 'Test Remote',
        url: 'https://test.primeos.org',
        token: 'test-token'
      });
      
      // Should save to secure vault
      expect(mockSecureVault.setSecret).toHaveBeenCalledWith(
        'remote-manifold-endpoints',
        expect.arrayContaining([
          expect.objectContaining({
            name: 'Test Remote',
            url: 'https://test.primeos.org'
          })
        ])
      );
      
      // Should add to internal list
      expect(importExport.remoteEndpoints.length).toBe(1);
      expect(importExport.remoteEndpoints[0].name).toBe('Test Remote');
    });
    
    it('should remove a remote endpoint', async () => {
      // Add endpoint first
      await importExport.addRemoteEndpoint({
        name: 'Test Remote',
        url: 'https://test.primeos.org',
        token: 'test-token'
      });
      
      // Remove endpoint
      await importExport.removeRemoteEndpoint('Test Remote');
      
      // Should update secure vault
      expect(mockSecureVault.setSecret).toHaveBeenCalledWith(
        'remote-manifold-endpoints',
        []
      );
      
      // Should remove from internal list
      expect(importExport.remoteEndpoints.length).toBe(0);
    });
    
    it('should get all remote endpoints', async () => {
      // Add two endpoints
      await importExport.addRemoteEndpoint({
        name: 'Test Remote 1',
        url: 'https://test1.primeos.org',
        token: 'test-token-1'
      });
      
      await importExport.addRemoteEndpoint({
        name: 'Test Remote 2',
        url: 'https://test2.primeos.org',
        token: 'test-token-2'
      });
      
      // Get endpoints
      const endpoints = await importExport.getRemoteEndpoints();
      
      // Should return all endpoints (without tokens)
      expect(endpoints.length).toBe(2);
      expect(endpoints[0].name).toBe('Test Remote 1');
      expect(endpoints[0].url).toBe('https://test1.primeos.org');
      expect(endpoints[0].token).toBeUndefined();
      
      expect(endpoints[1].name).toBe('Test Remote 2');
    });
  });
  
  describe('Event Handling', () => {
    beforeEach(async () => {
      await importExport.initialize();
    });
    
    it('should handle import-request events', async () => {
      // Get handler
      const handler = mockEventBus.subscribe.mock.calls.find(
        call => call[0] === 'remote-manifold:import-request'
      )[1];
      
      // Mock implementation
      importExport.importManifold = jest.fn().mockResolvedValue({
        success: true,
        localId: 'local-id'
      });
      
      // Call handler
      await handler({
        remoteId: 'remote-id',
        endpointUrl: 'https://remote.primeos.org'
      });
      
      // Should call importManifold
      expect(importExport.importManifold).toHaveBeenCalledWith({
        remoteId: 'remote-id',
        endpointUrl: 'https://remote.primeos.org'
      });
    });
    
    it('should handle export-request events', async () => {
      // Get handler
      const handler = mockEventBus.subscribe.mock.calls.find(
        call => call[0] === 'remote-manifold:export-request'
      )[1];
      
      // Mock implementation
      importExport.exportManifold = jest.fn().mockResolvedValue({
        success: true,
        remoteId: 'remote-id'
      });
      
      // Call handler
      await handler({
        manifoldId: 'local-id',
        endpointUrl: 'https://remote.primeos.org'
      });
      
      // Should call exportManifold
      expect(importExport.exportManifold).toHaveBeenCalledWith({
        manifoldId: 'local-id',
        endpointUrl: 'https://remote.primeos.org'
      });
    });
  });
});