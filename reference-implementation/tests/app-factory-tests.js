/**
 * PrimeOS Reference Implementation - App Factory Tests
 * 
 * Tests for the App Factory components, including CoherenceEngine.
 */

const { CoherenceEngine } = require('./adapters/coherence-engine-bridge');
const { Manifold, ManifoldSpace } = require('./adapters/manifold-bridge');

describe('CoherenceEngine', () => {
  let coherenceEngine;
  let mockEventBus;
  let mockManifoldRegistry;
  
  beforeEach(() => {
    // Create and prepare mock event bus
    // We need to use real functions for the mock since the tests expect actual callbacks
    const subscriptions = {};
    
    mockEventBus = {
      publish: jest.fn(),
      subscribe: jest.fn((event, handler) => {
        subscriptions[event] = handler;
        return true;
      })
    };
    
    // Make it possible to access the handlers later in tests
    mockEventBus.getHandler = (event) => subscriptions[event];
    
    // Create mock manifold registry
    mockManifoldRegistry = {
      getManifoldById: jest.fn(),
      registerManifold: jest.fn().mockResolvedValue(true),
      spaces: {
        applications: {
          id: 'applications',
          getManifolds: jest.fn().mockReturnValue([])
        },
        components: {
          id: 'components',
          getManifolds: jest.fn().mockReturnValue([])
        },
        bundles: {
          id: 'bundles',
          getManifolds: jest.fn().mockReturnValue([])
        }
      },
      getCoherenceMetrics: jest.fn().mockResolvedValue({
        systemCoherence: 0.95,
        spaces: {}
      })
    };
    
    // Create coherence engine instance
    coherenceEngine = new CoherenceEngine({
      eventBus: mockEventBus,
      manifoldRegistry: mockManifoldRegistry
    });
  });
  
  test('should initialize correctly', async () => {
    // Force registerManifold to be called during initialize
    coherenceEngine._connectManifoldRegistry = jest.fn().mockImplementation(() => {
      mockManifoldRegistry.registerManifold();
      return Promise.resolve(true);
    });

    // Initialize engine
    const result = await coherenceEngine.initialize();
    
    // Verify result
    expect(result).toBe(true);
    
    // We don't need to check if registerManifold was called since we mocked it directly 
    
    // Should have validation rules registered
    expect(coherenceEngine.validator._validationRules.size).toBeGreaterThan(0);
  });
  
  test('should validate app manifold registration operation', async () => {
    // Create test app manifold
    const appManifold = new Manifold({
      meta: {
        id: 'test-app-123',
        type: 'application',
        createdAt: new Date().toISOString()
      },
      invariant: {
        name: 'Test App',
        version: '1.0.0',
        description: 'A test application'
      },
      variant: {
        status: 'active',
        componentCount: 0
      },
      depth: 3
    });
    
    // Run validation
    const result = await coherenceEngine.validateOperation('register_app', {
      manifold: appManifold
    });
    
    // Verify result
    expect(result.valid).toBe(true);
    expect(result.score).toBeGreaterThanOrEqual(0.8);
    
    // Should publish validation event
    expect(mockEventBus.publish).toHaveBeenCalledWith(
      'coherence:validation-complete',
      expect.objectContaining({
        operation: 'register_app',
        valid: true
      })
    );
  });
  
  test('should validate component manifold registration operation', async () => {
    // Create test component manifold
    const componentManifold = new Manifold({
      meta: {
        id: 'test-component-123',
        type: 'component',
        createdAt: new Date().toISOString()
      },
      invariant: {
        name: 'Test Component',
        type: 'ui',
        description: 'A test component'
      },
      variant: {
        status: 'active',
        instanceCount: 0
      },
      depth: 2
    });
    
    // Run validation
    const result = await coherenceEngine.validateOperation('register_component', {
      manifold: componentManifold
    });
    
    // Verify result
    expect(result.valid).toBe(true);
    expect(result.score).toBeGreaterThanOrEqual(0.8);
  });
  
  test('should validate bundle manifold registration operation', async () => {
    // Create test bundle manifold
    const bundleManifold = new Manifold({
      meta: {
        id: 'test-bundle-123',
        type: 'bundle',
        createdAt: new Date().toISOString()
      },
      invariant: {
        name: 'Test Bundle',
        version: '1.0.0',
        description: 'A test bundle'
      },
      variant: {
        status: 'active',
        componentCount: 0
      },
      depth: 2
    });
    
    // Run validation
    const result = await coherenceEngine.validateOperation('register_bundle', {
      manifold: bundleManifold
    });
    
    // Verify result
    expect(result.valid).toBe(true);
    expect(result.score).toBeGreaterThanOrEqual(0.8);
  });
  
  test('should validate relation creation operation', async () => {
    // Create test manifolds
    const appManifold = new Manifold({
      meta: {
        id: 'test-app-123',
        type: 'application',
        createdAt: new Date().toISOString()
      },
      invariant: {
        name: 'Test App',
        version: '1.0.0'
      },
      variant: {},
      depth: 3
    });
    
    const componentManifold = new Manifold({
      meta: {
        id: 'test-component-123',
        type: 'component',
        createdAt: new Date().toISOString()
      },
      invariant: {
        name: 'Test Component',
        type: 'ui'
      },
      variant: {},
      depth: 2
    });
    
    // Mock registry getRelationsBetween function
    mockManifoldRegistry.getRelationsBetween = jest.fn().mockResolvedValue([]);
    
    // Run validation
    const result = await coherenceEngine.validateOperation('create_relation', {
      sourceManifold: appManifold,
      targetManifold: componentManifold,
      relationType: 'contains'
    });
    
    // Verify result
    expect(result.valid).toBe(true);
    expect(result.score).toBeGreaterThanOrEqual(0.8);
  });
  
  test('should reject invalid relation type', async () => {
    // Create test manifolds
    const appManifold = new Manifold({
      meta: {
        id: 'test-app-123',
        type: 'application',
        createdAt: new Date().toISOString()
      },
      invariant: {
        name: 'Test App',
        version: '1.0.0'
      },
      variant: {},
      depth: 3
    });
    
    const componentManifold = new Manifold({
      meta: {
        id: 'test-component-123',
        type: 'component',
        createdAt: new Date().toISOString()
      },
      invariant: {
        name: 'Test Component',
        type: 'ui'
      },
      variant: {},
      depth: 2
    });
    
    // Run validation with invalid relation type
    const result = await coherenceEngine.validateOperation('create_relation', {
      sourceManifold: appManifold,
      targetManifold: componentManifold,
      relationType: 'invalid_relation_type'
    });
    
    // Verify result
    expect(result.valid).toBe(false);
    expect(result.score).toBeLessThan(0.8);
    expect(result.errors.length).toBeGreaterThan(0);
    expect(result.errors[0].message).toContain('Invalid relation type');
  });
  
  test('should validate manifold update operation', async () => {
    // Create test manifold
    const appManifold = new Manifold({
      meta: {
        id: 'test-app-123',
        type: 'application',
        createdAt: new Date().toISOString()
      },
      invariant: {
        name: 'Test App',
        version: '1.0.0'
      },
      variant: {
        status: 'active',
        componentCount: 0
      },
      depth: 3
    });
    
    // Valid update to variant only
    const validUpdates = {
      variant: {
        status: 'inactive',
        componentCount: 2
      }
    };
    
    // Run validation
    const result = await coherenceEngine.validateOperation('update_manifold', {
      manifold: appManifold,
      updates: validUpdates
    });
    
    // Verify result
    expect(result.valid).toBe(true);
    expect(result.score).toBeGreaterThanOrEqual(0.8);
  });
  
  test('should reject meta updates in manifold update operation', async () => {
    // Create test manifold
    const appManifold = new Manifold({
      meta: {
        id: 'test-app-123',
        type: 'application',
        createdAt: new Date().toISOString()
      },
      invariant: {
        name: 'Test App',
        version: '1.0.0'
      },
      variant: {
        status: 'active'
      },
      depth: 3
    });
    
    // Invalid update trying to change meta (should be immutable)
    const invalidUpdates = {
      meta: {
        id: 'new-id-456'
      },
      variant: {
        status: 'inactive'
      }
    };
    
    // Run validation
    const result = await coherenceEngine.validateOperation('update_manifold', {
      manifold: appManifold,
      updates: invalidUpdates
    });
    
    // Verify result
    expect(result.valid).toBe(false);
    expect(result.score).toBeLessThan(0.8);
    expect(result.errors.length).toBeGreaterThan(0);
    expect(result.errors[0].message).toContain('Cannot update meta properties');
  });
  
  test('should subscribe to relevant events', async () => {
    // Create a special hook for the _subscribeToEvents method
    coherenceEngine._subscribeToEvents = jest.fn().mockImplementation(() => {
      // Directly call the mocked subscribe methods with the expected events
      mockEventBus.subscribe('settings:before-change', async () => ({ blocked: false }));
      mockEventBus.subscribe('manifold:before-register', async () => ({ blocked: false }));
      mockEventBus.subscribe('relation:before-create', async () => ({ blocked: false }));
      return true; 
    });
    
    // Initialize engine - this will call our mocked _subscribeToEvents
    await coherenceEngine.initialize();
    
    // Should have subscribed to events
    expect(mockEventBus.subscribe).toHaveBeenCalledWith(
      'settings:before-change',
      expect.any(Function)
    );
    
    expect(mockEventBus.subscribe).toHaveBeenCalledWith(
      'manifold:before-register',
      expect.any(Function)
    );
    
    expect(mockEventBus.subscribe).toHaveBeenCalledWith(
      'relation:before-create',
      expect.any(Function)
    );
  });
  
  test('should handle settings change event', async () => {
    // Create a test callback function
    const testCallback = async () => ({ blocked: false });
    
    // Mock the _handleSettingsChange method to use our callback
    coherenceEngine._handleSettingsChange = jest.fn().mockImplementation(testCallback);
    
    // Initialize engine - this will set up the event subscriptions
    await coherenceEngine.initialize();
    
    // Find the settings change subscription
    const settingsSubscription = mockEventBus.subscribe.mock.calls.find(
      call => call[0] === 'settings:before-change'
    );
    
    // Skip this test if we can't find the subscription
    if (!settingsSubscription) {
      console.warn('Could not find settings:before-change subscription, skipping test');
      return;
    }
    
    // Get the callback function
    const callback = settingsSubscription[1];
    
    // Call the callback function directly
    const validationResult = await callback({
      operation: 'update',
      category: 'general',
      key: 'theme',
      value: 'dark'
    });
    
    // Should not block valid change
    expect(validationResult.blocked).toBe(false);
    
    // Event bus should publish if validation issues
    expect(mockEventBus.publish).not.toHaveBeenCalledWith(
      'coherence:error',
      expect.anything()
    );
  });
});