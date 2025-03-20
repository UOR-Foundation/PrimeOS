/**
 * PrimeOS Reference Implementation - Context Sharing Tests
 * 
 * Tests for the context sharing mechanism that allows components and
 * applications to share context with each other.
 */

// Import test dependencies
const { ManifoldRegistry } = require('./adapters/manifold-bridge');

// Import the system under test
const { ContextProvider, ContextConsumer, ContextHub } = require('../core/context/context-sharing');

describe('Context Sharing Mechanism', () => {
  let contextHub;
  let mockEventBus;
  let mockRegistry;
  
  beforeEach(() => {
    // Create mock EventBus
    mockEventBus = {
      publish: jest.fn(),
      subscribe: jest.fn().mockImplementation((event, handler) => {
        return () => {}; // Return unsubscribe function
      })
    };
    
    // Create mock ManifoldRegistry
    mockRegistry = {
      getManifold: jest.fn().mockResolvedValue(null),
      createRelation: jest.fn().mockResolvedValue({}),
      updateManifold: jest.fn().mockResolvedValue({})
    };
    
    // Create context hub
    contextHub = new ContextHub({
      eventBus: mockEventBus,
      manifoldRegistry: mockRegistry
    });
  });
  
  describe('ContextHub', () => {
    it('should initialize correctly', async () => {
      await contextHub.initialize();
      
      // Should subscribe to events
      expect(mockEventBus.subscribe).toHaveBeenCalledWith(
        'context:register-provider', 
        expect.any(Function)
      );
      
      expect(mockEventBus.subscribe).toHaveBeenCalledWith(
        'context:register-consumer', 
        expect.any(Function)
      );
    });
    
    it('should register a context provider', async () => {
      const providerId = 'test-provider';
      const contextType = 'test-context';
      
      const provider = await contextHub.registerProvider({
        id: providerId,
        contextType,
        description: 'Test Provider',
        schema: { type: 'object' }
      });
      
      // Should return a provider instance
      expect(provider).toBeInstanceOf(ContextProvider);
      expect(provider.id).toBe(providerId);
      
      // Should add to providers map
      expect(contextHub.providers.has(providerId)).toBe(true);
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'context:provider-registered',
        expect.objectContaining({
          id: providerId,
          contextType
        })
      );
    });
    
    it('should register a context consumer', async () => {
      const consumerId = 'test-consumer';
      const contextType = 'test-context';
      
      const consumer = await contextHub.registerConsumer({
        id: consumerId,
        contextTypes: [contextType],
        description: 'Test Consumer'
      });
      
      // Should return a consumer instance
      expect(consumer).toBeInstanceOf(ContextConsumer);
      expect(consumer.id).toBe(consumerId);
      
      // Should add to consumers map
      expect(contextHub.consumers.has(consumerId)).toBe(true);
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'context:consumer-registered',
        expect.objectContaining({
          id: consumerId,
          contextTypes: [contextType]
        })
      );
    });
    
    it('should connect compatible providers and consumers', async () => {
      // Register provider
      const provider = await contextHub.registerProvider({
        id: 'test-provider',
        contextType: 'test-context',
        description: 'Test Provider',
        schema: { type: 'object' }
      });
      
      // Register consumer
      const consumer = await contextHub.registerConsumer({
        id: 'test-consumer',
        contextTypes: ['test-context'],
        description: 'Test Consumer'
      });
      
      // Should create connection
      expect(contextHub.connections.size).toBe(1);
      
      // Connection should have correct references
      const connection = Array.from(contextHub.connections.values())[0];
      expect(connection.providerId).toBe('test-provider');
      expect(connection.consumerId).toBe('test-consumer');
      
      // Provider should know about consumer
      expect(provider.getConsumers().length).toBe(1);
      expect(provider.getConsumers()[0]).toBe('test-consumer');
      
      // Consumer should know about provider
      expect(consumer.getProviders().length).toBe(1);
      expect(consumer.getProviders()[0]).toBe('test-provider');
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'context:connection-created',
        expect.objectContaining({
          providerId: 'test-provider',
          consumerId: 'test-consumer'
        })
      );
    });
    
    it('should not connect incompatible providers and consumers', async () => {
      // Register provider
      await contextHub.registerProvider({
        id: 'test-provider',
        contextType: 'test-context-1',
        description: 'Test Provider',
        schema: { type: 'object' }
      });
      
      // Register consumer with different context type
      await contextHub.registerConsumer({
        id: 'test-consumer',
        contextTypes: ['test-context-2'],
        description: 'Test Consumer'
      });
      
      // Should not create connection
      expect(contextHub.connections.size).toBe(0);
    });
    
    it('should list providers by context type', async () => {
      // Register providers
      await contextHub.registerProvider({
        id: 'provider-1',
        contextType: 'type-a',
        description: 'Provider 1'
      });
      
      await contextHub.registerProvider({
        id: 'provider-2',
        contextType: 'type-a',
        description: 'Provider 2'
      });
      
      await contextHub.registerProvider({
        id: 'provider-3',
        contextType: 'type-b',
        description: 'Provider 3'
      });
      
      // Get providers for type-a
      const typeAProviders = contextHub.getProvidersByType('type-a');
      expect(typeAProviders.length).toBe(2);
      expect(typeAProviders[0].id).toBe('provider-1');
      expect(typeAProviders[1].id).toBe('provider-2');
      
      // Get providers for type-b
      const typeBProviders = contextHub.getProvidersByType('type-b');
      expect(typeBProviders.length).toBe(1);
      expect(typeBProviders[0].id).toBe('provider-3');
    });
    
    it('should list consumers by context type', async () => {
      // Register consumers
      await contextHub.registerConsumer({
        id: 'consumer-1',
        contextTypes: ['type-a'],
        description: 'Consumer 1'
      });
      
      await contextHub.registerConsumer({
        id: 'consumer-2',
        contextTypes: ['type-a', 'type-b'],
        description: 'Consumer 2'
      });
      
      await contextHub.registerConsumer({
        id: 'consumer-3',
        contextTypes: ['type-b'],
        description: 'Consumer 3'
      });
      
      // Get consumers for type-a
      const typeAConsumers = contextHub.getConsumersByType('type-a');
      expect(typeAConsumers.length).toBe(2);
      expect(typeAConsumers[0].id).toBe('consumer-1');
      expect(typeAConsumers[1].id).toBe('consumer-2');
      
      // Get consumers for type-b
      const typeBConsumers = contextHub.getConsumersByType('type-b');
      expect(typeBConsumers.length).toBe(2);
      expect(typeBConsumers[0].id).toBe('consumer-2');
      expect(typeBConsumers[1].id).toBe('consumer-3');
    });
  });
  
  describe('ContextProvider', () => {
    let provider;
    
    beforeEach(async () => {
      await contextHub.initialize();
      
      // Register provider
      provider = await contextHub.registerProvider({
        id: 'test-provider',
        contextType: 'test-context',
        description: 'Test Provider',
        schema: {
          type: 'object',
          properties: {
            value: { type: 'string' }
          }
        }
      });
    });
    
    it('should update context and notify consumers', async () => {
      // Register consumer
      const consumer = await contextHub.registerConsumer({
        id: 'test-consumer',
        contextTypes: ['test-context'],
        description: 'Test Consumer'
      });
      
      // Set up consumer handler
      const contextHandler = jest.fn();
      consumer.onContextUpdate(contextHandler);
      
      // Update context
      const contextData = { value: 'test value' };
      await provider.updateContext(contextData);
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'context:updated',
        expect.objectContaining({
          providerId: 'test-provider',
          contextType: 'test-context',
          data: contextData
        })
      );
      
      // Consumer handler should be called
      expect(contextHandler).toHaveBeenCalledWith(
        expect.objectContaining({
          providerId: 'test-provider',
          contextType: 'test-context',
          data: contextData
        })
      );
    });
    
    it('should validate context data against schema', async () => {
      // Create invalid context data
      const invalidData = { value: 123 }; // Should be string
      
      // Should reject invalid data
      await expect(provider.updateContext(invalidData)).rejects.toThrow('Schema validation failed');
      
      // Publish should not be called for invalid data
      expect(mockEventBus.publish).not.toHaveBeenCalledWith(
        'context:updated',
        expect.anything()
      );
    });
    
    it('should get consumers connected to the provider', async () => {
      // Register consumers
      await contextHub.registerConsumer({
        id: 'consumer-1',
        contextTypes: ['test-context'],
        description: 'Consumer 1'
      });
      
      await contextHub.registerConsumer({
        id: 'consumer-2',
        contextTypes: ['test-context'],
        description: 'Consumer 2'
      });
      
      await contextHub.registerConsumer({
        id: 'consumer-3',
        contextTypes: ['other-context'],
        description: 'Consumer 3'
      });
      
      // Get consumers
      const consumers = provider.getConsumers();
      
      // Should return connected consumers
      expect(consumers.length).toBe(2);
      expect(consumers).toContain('consumer-1');
      expect(consumers).toContain('consumer-2');
      expect(consumers).not.toContain('consumer-3');
    });
  });
  
  describe('ContextConsumer', () => {
    let consumer;
    
    beforeEach(async () => {
      await contextHub.initialize();
      
      // Register consumer
      consumer = await contextHub.registerConsumer({
        id: 'test-consumer',
        contextTypes: ['type-a', 'type-b'],
        description: 'Test Consumer'
      });
    });
    
    it('should receive context updates from providers', async () => {
      // Register providers
      const providerA = await contextHub.registerProvider({
        id: 'provider-a',
        contextType: 'type-a',
        description: 'Provider A'
      });
      
      const providerB = await contextHub.registerProvider({
        id: 'provider-b',
        contextType: 'type-b',
        description: 'Provider B'
      });
      
      // Set up context handlers
      const handlerA = jest.fn();
      const handlerB = jest.fn();
      const handlerAny = jest.fn();
      
      consumer.onContextUpdate('type-a', handlerA);
      consumer.onContextUpdate('type-b', handlerB);
      consumer.onContextUpdate(handlerAny);
      
      // Update contexts
      await providerA.updateContext({ value: 'a' });
      await providerB.updateContext({ value: 'b' });
      
      // Type-specific handlers should be called
      expect(handlerA).toHaveBeenCalledWith(
        expect.objectContaining({
          providerId: 'provider-a',
          contextType: 'type-a',
          data: { value: 'a' }
        })
      );
      
      expect(handlerB).toHaveBeenCalledWith(
        expect.objectContaining({
          providerId: 'provider-b',
          contextType: 'type-b',
          data: { value: 'b' }
        })
      );
      
      // General handler should be called for both
      expect(handlerAny).toHaveBeenCalledTimes(2);
    });
    
    it('should get latest context by type', async () => {
      // Register provider
      const provider = await contextHub.registerProvider({
        id: 'provider-a',
        contextType: 'type-a',
        description: 'Provider A'
      });
      
      // Update context
      const contextData = { value: 'test' };
      await provider.updateContext(contextData);
      
      // Get latest context
      const context = consumer.getLatestContext('type-a');
      
      // Should return correct context
      expect(context).toEqual(
        expect.objectContaining({
          providerId: 'provider-a',
          data: contextData
        })
      );
    });
    
    it('should get providers connected to the consumer', async () => {
      // Register providers
      await contextHub.registerProvider({
        id: 'provider-a',
        contextType: 'type-a',
        description: 'Provider A'
      });
      
      await contextHub.registerProvider({
        id: 'provider-b',
        contextType: 'type-b',
        description: 'Provider B'
      });
      
      await contextHub.registerProvider({
        id: 'provider-c',
        contextType: 'type-c',
        description: 'Provider C'
      });
      
      // Get providers
      const providers = consumer.getProviders();
      
      // Should return connected providers
      expect(providers.length).toBe(2);
      expect(providers).toContain('provider-a');
      expect(providers).toContain('provider-b');
      expect(providers).not.toContain('provider-c');
    });
  });
});