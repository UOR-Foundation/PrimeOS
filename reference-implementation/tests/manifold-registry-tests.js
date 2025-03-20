/**
 * PrimeOS Reference Implementation - ManifoldRegistry Tests
 * 
 * Tests for the manifold-based application and component registration.
 */

// Mock the base0 libraries
jest.mock('../../src/framework/base0/manifold', () => {
  return {
    Manifold: class MockManifold {
      constructor(options = {}) {
        this.meta = options.meta || {};
        this.invariant = options.invariant || {};
        this.variant = options.variant || {};
        this.depth = options.depth || 0;
        this._spaces = new Set(options.spaces || []);
        this._relations = new Map();
      }
      
      updateVariant(updates) {
        this.variant = { ...this.variant, ...updates };
      }
      
      getMeta() { return this.meta; }
      getInvariant() { return this.invariant; }
      getVariant() { return this.variant; }
      getCoherenceScore() { return 0.95; }
      getId() { return this.meta.id || 'mock-id'; }
      getSpaces() { return Array.from(this._spaces); }
      
      addToSpace(space) {
        this._spaces.add(space);
        return this;
      }
      
      removeFromSpace(space) {
        this._spaces.delete(space);
        return this;
      }
      
      existsInSpace(space) {
        return this._spaces.has(space);
      }
      
      relateTo(target, relationType, metadata = {}) {
        this._relations.set(target.getId(), {
          type: relationType,
          manifold: target,
          metadata,
          established: new Date().toISOString()
        });
        return this;
      }
      
      getRelatedManifolds(relationType) {
        if (!relationType) {
          return Array.from(this._relations.values());
        }
        
        return Array.from(this._relations.values())
          .filter(relation => relation.type === relationType);
      }
      
      toJSON() { 
        return { 
          meta: this.meta, 
          invariant: this.invariant, 
          variant: this.variant, 
          depth: this.depth,
          spaces: Array.from(this._spaces)
        }; 
      }
      
      static fromJSON(json) { return new this(json); }
    },
    
    ManifoldSpace: class MockManifoldSpace {
      constructor(options = {}) {
        this.id = options.id || 'mock-space';
        this.name = options.name || 'Mock Space';
        this.dimension = options.dimension || 0;
        this.properties = options.properties || {};
        this._manifolds = new Map();
      }
      
      addManifold(manifold) {
        this._manifolds.set(manifold.getId(), manifold);
        return this;
      }
      
      removeManifold(manifoldOrId) {
        const id = manifoldOrId.getId ? manifoldOrId.getId() : manifoldOrId;
        this._manifolds.delete(id);
        return this;
      }
      
      getManifolds() {
        return Array.from(this._manifolds.values());
      }
      
      findManifolds(property, value) {
        return this.getManifolds().filter(manifold => {
          // Check in meta
          if (manifold.meta && manifold.meta[property] === value) {
            return true;
          }
          
          // Check in invariant
          if (manifold.invariant && manifold.invariant[property] === value) {
            return true;
          }
          
          // Check in variant
          if (manifold.variant && manifold.variant[property] === value) {
            return true;
          }
          
          return false;
        });
      }
      
      hasManifold(manifoldOrId) {
        const id = manifoldOrId.getId ? manifoldOrId.getId() : manifoldOrId;
        return this._manifolds.has(id);
      }
      
      getCoherence() {
        return 0.95;
      }
    }
  };
});

jest.mock('../../src/framework/base0/coherence-validator', () => {
  return class MockCoherenceValidator {
    constructor(options = {}) {
      this.defaultThreshold = options.defaultThreshold || 0.8;
      this.strictValidation = options.strictValidation || false;
      this._validationRules = new Map();
    }
    
    registerRule(name, fn, description = '') {
      this._validationRules.set(name, { name, fn, description });
    }
    
    validateManifold() {
      return { valid: true, coherence: 0.9, errors: [], warnings: [] };
    }
  };
});

// Import the bridge adapter to test
const { ManifoldRegistry, Manifold, ManifoldSpace } = require('./adapters/store-bridge');

describe('ManifoldRegistry', () => {
  let registry;
  let mockEventBus;
  let mockStore;
  let mockCoherenceEngine;
  
  beforeEach(() => {
    // Mock event bus
    mockEventBus = {
      publish: jest.fn(),
      subscribe: jest.fn().mockImplementation((event, handler) => {
        return () => {}; // Return unsubscribe function
      })
    };
    
    // Mock store
    mockStore = {
      query: jest.fn().mockResolvedValue([]),
      get: jest.fn().mockResolvedValue(null),
      put: jest.fn().mockResolvedValue(true),
      remove: jest.fn().mockResolvedValue(true)
    };
    
    // Mock coherence engine
    mockCoherenceEngine = {
      registerManifold: jest.fn().mockReturnValue(true),
      registerSpace: jest.fn().mockReturnValue(true),
      validateManifold: jest.fn().mockResolvedValue({
        valid: true,
        score: 0.9,
        errors: [],
        warnings: []
      }),
      validateOperation: jest.fn().mockResolvedValue({
        valid: true,
        score: 0.9,
        errors: [],
        warnings: []
      }),
      getCoherenceMetrics: jest.fn().mockResolvedValue({
        systemCoherence: 0.95,
        spaces: {
          apps: { coherence: 0.95, manifoldCount: 0 },
          components: { coherence: 0.90, manifoldCount: 0 },
          bundles: { coherence: 0.92, manifoldCount: 0 }
        }
      })
    };
    
    // Create mock validator
    const mockValidator = new (jest.requireMock('../../src/framework/base0/coherence-validator'))();
    
    // Create registry instance
    registry = new ManifoldRegistry({
      eventBus: mockEventBus,
      store: mockStore,
      coherenceEngine: mockCoherenceEngine,
      validator: mockValidator
    });
    
    // Initialize the registry
    return registry.initialize();
  });
  
  describe('Initialization', () => {
    it('should initialize with proper spaces', () => {
      expect(registry.spaces.apps).toBeDefined();
      expect(registry.spaces.components).toBeDefined();
      expect(registry.spaces.bundles).toBeDefined();
    });
    
    it('should load manifolds from storage during initialization', () => {
      expect(mockStore.query).toHaveBeenCalledWith({
        index: 'type',
        value: 'manifold'
      });
    });
    
    it('should register with coherence engine during initialization', () => {
      // Just verify the method was called - we don't need to check the exact argument structure
      expect(mockCoherenceEngine.registerManifold).toHaveBeenCalled();
      
      // Check that register space was called 3 times (for apps, components, bundles)
      expect(mockCoherenceEngine.registerSpace).toHaveBeenCalledTimes(3);
    });
  });
  
  describe('App Registration', () => {
    it('should register an app as a manifold', async () => {
      const appSpec = {
        name: 'TestApp',
        version: '1.0.0',
        entryPoint: 'index.js',
        permissions: ['storage']
      };
      
      const appManifold = await registry.registerApp(appSpec);
      
      // Should create a manifold with correct structure
      expect(appManifold.getMeta().type).toBe('application');
      expect(appManifold.getInvariant().name).toBe('TestApp');
      expect(appManifold.getInvariant().permissions).toEqual(['storage']);
      
      // Should add to app registry space
      expect(registry.spaces.apps.hasManifold(appManifold.getId())).toBe(true);
      
      // Should persist to storage
      expect(mockStore.put).toHaveBeenCalledWith(
        expect.objectContaining({
          id: `manifold:${appManifold.getId()}`,
          type: 'manifold',
          manifoldType: 'application'
        })
      );
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'manifold-registry:app-registered',
        expect.objectContaining({
          id: appManifold.getId(),
          name: 'TestApp'
        })
      );
      
      // Should update registry stats
      expect(registry.registryManifold.getVariant().appCount).toBe(1);
    });
    
    it('should reject invalid app specifications', async () => {
      // Missing name
      const invalidSpec = {
        version: '1.0.0'
      };
      
      await expect(registry.registerApp(invalidSpec)).rejects.toThrow('Invalid app specification');
    });
  });
  
  describe('Component Registration', () => {
    it('should register a component as a manifold', async () => {
      const componentSpec = {
        name: 'TestComponent',
        version: '1.0.0',
        componentType: 'ui',
        dependencies: { 'core-ui': '^1.0.0' }
      };
      
      const componentManifold = await registry.registerComponent(componentSpec);
      
      // Should create a manifold with correct structure
      expect(componentManifold.getMeta().type).toBe('component');
      expect(componentManifold.getInvariant().name).toBe('TestComponent');
      expect(componentManifold.getInvariant().type).toBe('ui');
      
      // Should add to component registry space
      expect(registry.spaces.components.hasManifold(componentManifold.getId())).toBe(true);
      
      // Should persist to storage
      expect(mockStore.put).toHaveBeenCalledWith(
        expect.objectContaining({
          id: `manifold:${componentManifold.getId()}`,
          type: 'manifold',
          manifoldType: 'component'
        })
      );
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'manifold-registry:component-registered',
        expect.objectContaining({
          id: componentManifold.getId(),
          name: 'TestComponent'
        })
      );
      
      // Should update registry stats
      expect(registry.registryManifold.getVariant().componentCount).toBe(1);
    });
  });
  
  describe('Bundle Registration', () => {
    it('should register a bundle as a manifold', async () => {
      const bundleSpec = {
        name: 'TestBundle',
        version: '1.0.0',
        dependencies: { 'core': '^1.0.0' },
        components: ['component1', 'component2'],
        apps: ['testApp']
      };
      
      const bundleManifold = await registry.registerBundle(bundleSpec);
      
      // Should create a manifold with correct structure
      expect(bundleManifold.getMeta().type).toBe('bundle');
      expect(bundleManifold.getInvariant().name).toBe('TestBundle');
      expect(bundleManifold.getVariant().components).toEqual(['component1', 'component2']);
      
      // Should add to bundle registry space
      expect(registry.spaces.bundles.hasManifold(bundleManifold.getId())).toBe(true);
      
      // Should persist to storage
      expect(mockStore.put).toHaveBeenCalledWith(
        expect.objectContaining({
          id: `manifold:${bundleManifold.getId()}`,
          type: 'manifold',
          manifoldType: 'bundle'
        })
      );
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'manifold-registry:bundle-registered',
        expect.objectContaining({
          id: bundleManifold.getId(),
          name: 'TestBundle'
        })
      );
      
      // Should update registry stats
      expect(registry.registryManifold.getVariant().bundleCount).toBe(1);
    });
  });
  
  describe('Manifold Retrieval', () => {
    it('should get a manifold by ID from memory', async () => {
      // First register a manifold
      const appSpec = { name: 'AppToRetrieve', version: '1.0.0' };
      const appManifold = await registry.registerApp(appSpec);
      const id = appManifold.getId();
      
      // Then retrieve it
      const retrieved = await registry.getManifold(id);
      
      expect(retrieved).toBeDefined();
      expect(retrieved.getId()).toBe(id);
      expect(retrieved.getInvariant().name).toBe('AppToRetrieve');
    });
    
    it('should get a manifold by ID from storage if not in memory', async () => {
      // Mock a stored manifold
      const storedManifold = {
        id: 'manifold:stored-id',
        type: 'manifold',
        manifoldType: 'application',
        data: {
          meta: { id: 'stored-id', type: 'application' },
          invariant: { name: 'StoredApp', version: '1.0.0' },
          variant: { status: 'registered' },
          depth: 2
        }
      };
      
      mockStore.get.mockResolvedValueOnce(storedManifold);
      
      // Retrieve the manifold
      const retrieved = await registry.getManifold('stored-id');
      
      expect(retrieved).toBeDefined();
      expect(retrieved.getId()).toBe('stored-id');
      expect(retrieved.getInvariant().name).toBe('StoredApp');
      
      // Should be added to the appropriate space
      expect(registry.spaces.apps.hasManifold('stored-id')).toBe(true);
    });
    
    it('should return null for non-existent manifolds', async () => {
      const retrieved = await registry.getManifold('non-existent-id');
      expect(retrieved).toBeNull();
    });
  });
  
  describe('Manifold Finding', () => {
    beforeEach(async () => {
      // Register some test manifolds
      await registry.registerApp({ 
        name: 'TestApp1', 
        version: '1.0.0',
        author: 'test-author'
      });
      
      await registry.registerApp({ 
        name: 'TestApp2', 
        version: '2.0.0',
        author: 'test-author'
      });
      
      await registry.registerComponent({ 
        name: 'TestComponent',
        componentType: 'ui',
        author: 'test-author'
      });
    });
    
    it('should find manifolds by property', async () => {
      // Find by author
      const authorManifolds = await registry.findManifolds('all', 'author', 'test-author');
      expect(authorManifolds.length).toBe(3);
      
      // Find by version
      const versionManifolds = await registry.findManifolds('apps', 'version', '2.0.0');
      expect(versionManifolds.length).toBe(1);
      expect(versionManifolds[0].getInvariant().name).toBe('TestApp2');
      
      // Find by component type
      const uiComponents = await registry.findManifolds('components', 'type', 'ui');
      expect(uiComponents.length).toBe(1);
    });
    
    it('should throw error for invalid space ID', async () => {
      await expect(registry.findManifolds('invalid-space', 'author', 'test-author'))
        .rejects.toThrow('Invalid space ID');
    });
  });
  
  describe('Manifold Updates', () => {
    it('should update a manifold\'s variant properties', async () => {
      // Register a manifold
      const appManifold = await registry.registerApp({ 
        name: 'AppToUpdate', 
        version: '1.0.0' 
      });
      
      const id = appManifold.getId();
      
      // Update the manifold
      const updates = {
        status: 'active',
        instances: 2,
        lastAccessed: new Date().toISOString()
      };
      
      const updated = await registry.updateManifold(id, updates);
      
      // Check for updates
      expect(updated.getVariant().status).toBe('active');
      expect(updated.getVariant().instances).toBe(2);
      expect(updated.getVariant().lastAccessed).toBeDefined();
      
      // Should persist to storage
      expect(mockStore.put).toHaveBeenCalledWith(
        expect.objectContaining({
          id: `manifold:${id}`,
          type: 'manifold'
        })
      );
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'manifold-registry:manifold-updated',
        expect.objectContaining({
          id: id,
          type: 'application'
        })
      );
    });
    
    it('should throw error for non-existent manifold updates', async () => {
      await expect(registry.updateManifold('non-existent', { status: 'active' }))
        .rejects.toThrow('Manifold not found');
    });
  });
  
  describe('Manifold Relations', () => {
    it('should create relations between manifolds', async () => {
      // Register manifolds
      const appManifold = await registry.registerApp({ name: 'RelatedApp', version: '1.0.0' });
      const bundleManifold = await registry.registerBundle({ name: 'RelatedBundle', version: '1.0.0' });
      
      // Create relation
      const relation = await registry.createRelation(
        appManifold.getId(),
        bundleManifold.getId(),
        'contains',
        { added: new Date().toISOString() }
      );
      
      // Check relation was created
      expect(relation.sourceId).toBe(appManifold.getId());
      expect(relation.targetId).toBe(bundleManifold.getId());
      expect(relation.relationType).toBe('contains');
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'manifold-registry:relation-created',
        expect.objectContaining({
          sourceId: appManifold.getId(),
          targetId: bundleManifold.getId(),
          relationType: 'contains'
        })
      );
      
      // Should persist the source manifold with relation
      expect(mockStore.put).toHaveBeenCalledWith(
        expect.objectContaining({
          id: `manifold:${appManifold.getId()}`
        })
      );
    });
    
    it('should throw error for relations with non-existent manifolds', async () => {
      const appManifold = await registry.registerApp({ name: 'App', version: '1.0.0' });
      
      await expect(registry.createRelation(
        appManifold.getId(),
        'non-existent',
        'contains'
      )).rejects.toThrow('Source or target manifold not found');
      
      await expect(registry.createRelation(
        'non-existent',
        appManifold.getId(),
        'contains'
      )).rejects.toThrow('Source or target manifold not found');
    });
  });
  
  describe('Coherence Metrics', () => {
    it('should provide system coherence metrics', async () => {
      // Register some manifolds
      await registry.registerApp({ name: 'App1', version: '1.0.0' });
      await registry.registerApp({ name: 'App2', version: '1.0.0' });
      await registry.registerComponent({ name: 'Component1' });
      await registry.registerBundle({ name: 'Bundle1', version: '1.0.0' });
      
      // Get metrics
      const metrics = await registry.getCoherenceMetrics();
      
      expect(metrics.systemCoherence).toBeDefined();
      expect(metrics.spaces.apps).toBeDefined();
      expect(metrics.spaces.apps.manifoldCount).toBe(2);
      expect(metrics.spaces.components.manifoldCount).toBe(1);
      expect(metrics.spaces.bundles.manifoldCount).toBe(1);
    });
  });
  
  describe('Event Handling', () => {
    it('should handle app-factory:created events', async () => {
      // Simulate app creation event
      const eventHandler = mockEventBus.subscribe.mock.calls.find(
        call => call[0] === 'app-factory:created'
      )[1];
      
      const appSpec = { name: 'EventApp', version: '1.0.0' };
      await eventHandler({ appSpec });
      
      // Should have registered the app
      const apps = registry.spaces.apps.getManifolds();
      const eventApp = apps.find(app => app.getInvariant().name === 'EventApp');
      
      expect(eventApp).toBeDefined();
    });
    
    it('should handle app-factory:step-completed events for publishing', async () => {
      // Register an app with projectId
      const appManifold = await registry.registerApp({ 
        name: 'PublishedApp', 
        version: '1.0.0' 
      });
      
      // Update with projectId for testing
      await registry.updateManifold(appManifold.getId(), {
        projectId: 'test-project-123'
      });
      
      // Mock findManifolds to return this app when queried by projectId
      registry.findManifolds = jest.fn().mockResolvedValueOnce([appManifold]);
      
      // Simulate publishing event
      const eventHandler = mockEventBus.subscribe.mock.calls.find(
        call => call[0] === 'app-factory:step-completed'
      )[1];
      
      await eventHandler({ 
        step: 'publishing', 
        projectId: 'test-project-123' 
      });
      
      // Should have updated the app status
      expect(registry.findManifolds).toHaveBeenCalledWith(
        'apps', 'projectId', 'test-project-123'
      );
      
      // Get updated app
      const updatedApp = await registry.getManifold(appManifold.getId());
      expect(updatedApp.getVariant().status).toBe('published');
      expect(updatedApp.getVariant().publishedAt).toBeDefined();
    });
  });
});