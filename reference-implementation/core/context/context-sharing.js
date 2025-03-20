/**
 * PrimeOS Reference Implementation - Context Sharing
 * 
 * Provides a mechanism for components and applications to share context with
 * each other in a structured, event-driven manner. This enables topological
 * visualization of data relationships and context-aware behavior across
 * the PrimeOS environment.
 */

/**
 * Schema validator for context data
 * Simple implementation for basic validation
 */
class SchemaValidator {
  /**
   * Validate data against schema
   * @param {Object} data - Data to validate
   * @param {Object} schema - JSON Schema to validate against
   * @returns {Object} Validation result
   */
  validate(data, schema) {
    // Handle missing schema
    if (!schema) {
      return { valid: true, errors: [] };
    }
    
    // Perform basic validation
    const errors = [];
    
    // Type validation
    if (schema.type) {
      const dataType = this._getType(data);
      if (dataType !== schema.type) {
        if (!(schema.type === 'object' && dataType === 'array')) {
          errors.push(`Expected type ${schema.type}, got ${dataType}`);
        }
      }
    }
    
    // Property validation for objects
    if (schema.type === 'object' && schema.properties && typeof data === 'object' && data !== null) {
      Object.keys(schema.properties).forEach(prop => {
        if (data[prop] !== undefined) {
          const propSchema = schema.properties[prop];
          const propType = this._getType(data[prop]);
          
          if (propSchema.type && propType !== propSchema.type) {
            errors.push(`Property ${prop}: Expected type ${propSchema.type}, got ${propType}`);
          }
        } else if (schema.required && schema.required.includes(prop)) {
          errors.push(`Required property ${prop} is missing`);
        }
      });
    }
    
    // Array validation
    if (schema.type === 'array' && schema.items && Array.isArray(data)) {
      data.forEach((item, index) => {
        const itemSchema = schema.items;
        const itemType = this._getType(item);
        
        if (itemSchema.type && itemType !== itemSchema.type) {
          errors.push(`Array item ${index}: Expected type ${itemSchema.type}, got ${itemType}`);
        }
      });
    }
    
    return {
      valid: errors.length === 0,
      errors
    };
  }
  
  /**
   * Get JavaScript type
   * @param {*} value - Value to check
   * @returns {string} Type name
   */
  _getType(value) {
    if (value === null) return 'null';
    if (Array.isArray(value)) return 'array';
    return typeof value;
  }
}

/**
 * Context Provider
 * 
 * Represents a component that provides context to other components.
 */
class ContextProvider {
  /**
   * Create a context provider
   * @param {Object} options - Provider options
   * @param {string} options.id - Unique provider ID
   * @param {string} options.contextType - Type of context provided
   * @param {Object} options.schema - JSON Schema for context data
   * @param {string} options.description - Provider description
   * @param {Object} options.hub - Parent context hub
   */
  constructor(options) {
    this.id = options.id;
    this.contextType = options.contextType;
    this.schema = options.schema || null;
    this.description = options.description || '';
    this.hub = options.hub;
    this.validator = new SchemaValidator();
    
    // Last provided context
    this.latestContext = null;
    
    // Metadata
    this.metadata = {
      created: new Date().toISOString(),
      updateCount: 0,
      manifoldId: options.manifoldId || null
    };
  }
  
  /**
   * Update context data
   * @param {Object} data - New context data
   * @returns {Promise<boolean>} Success flag
   */
  async updateContext(data) {
    // Validate data against schema
    if (this.schema) {
      const validation = this.validator.validate(data, this.schema);
      if (!validation.valid) {
        throw new Error(`Schema validation failed: ${validation.errors.join(', ')}`);
      }
    }
    
    // Create context update
    const contextUpdate = {
      providerId: this.id,
      contextType: this.contextType,
      data,
      timestamp: new Date().toISOString()
    };
    
    // Store latest context
    this.latestContext = contextUpdate;
    this.metadata.updateCount++;
    
    // Publish update to the hub
    await this.hub.publishContextUpdate(contextUpdate);
    
    return true;
  }
  
  /**
   * Get consumers connected to this provider
   * @returns {Array<string>} Connected consumer IDs
   */
  getConsumers() {
    return this.hub.getConsumersForProvider(this.id);
  }
  
  /**
   * Get provider information
   * @returns {Object} Provider info
   */
  getInfo() {
    return {
      id: this.id,
      contextType: this.contextType,
      description: this.description,
      schema: this.schema,
      metadata: { ...this.metadata },
      consumerCount: this.getConsumers().length
    };
  }
}

/**
 * Context Consumer
 * 
 * Represents a component that consumes context from providers.
 */
class ContextConsumer {
  /**
   * Create a context consumer
   * @param {Object} options - Consumer options
   * @param {string} options.id - Unique consumer ID
   * @param {Array<string>} options.contextTypes - Types of context to consume
   * @param {string} options.description - Consumer description
   * @param {Object} options.hub - Parent context hub
   */
  constructor(options) {
    this.id = options.id;
    this.contextTypes = options.contextTypes || [];
    this.description = options.description || '';
    this.hub = options.hub;
    
    // Context handlers by type
    this.handlers = new Map();
    
    // General handlers (for any context type)
    this.generalHandlers = [];
    
    // Latest context by type
    this.latestContexts = new Map();
    
    // Metadata
    this.metadata = {
      created: new Date().toISOString(),
      updateCount: 0,
      manifoldId: options.manifoldId || null
    };
  }
  
  /**
   * Register a context update handler
   * @param {string|Function} typeOrHandler - Context type or handler function
   * @param {Function} [handler] - Handler function if type specified
   * @returns {Function} Unsubscribe function
   */
  onContextUpdate(typeOrHandler, handler) {
    if (typeof typeOrHandler === 'function') {
      // General handler for any context type
      const generalHandler = typeOrHandler;
      this.generalHandlers.push(generalHandler);
      
      // Return unsubscribe function
      return () => {
        const index = this.generalHandlers.indexOf(generalHandler);
        if (index !== -1) {
          this.generalHandlers.splice(index, 1);
        }
      };
    } else {
      // Type-specific handler
      const contextType = typeOrHandler;
      
      if (!this.handlers.has(contextType)) {
        this.handlers.set(contextType, []);
      }
      
      this.handlers.get(contextType).push(handler);
      
      // Return unsubscribe function
      return () => {
        const typeHandlers = this.handlers.get(contextType) || [];
        const index = typeHandlers.indexOf(handler);
        if (index !== -1) {
          typeHandlers.splice(index, 1);
        }
      };
    }
  }
  
  /**
   * Handle context update
   * @param {Object} contextUpdate - Context update
   */
  handleContextUpdate(contextUpdate) {
    const { contextType } = contextUpdate;
    
    // Update latest context
    this.latestContexts.set(contextType, contextUpdate);
    this.metadata.updateCount++;
    
    // Call type-specific handlers
    const typeHandlers = this.handlers.get(contextType) || [];
    typeHandlers.forEach(handler => {
      try {
        handler(contextUpdate);
      } catch (error) {
        console.error(`Error in context handler for ${contextType}:`, error);
      }
    });
    
    // Call general handlers
    this.generalHandlers.forEach(handler => {
      try {
        handler(contextUpdate);
      } catch (error) {
        console.error('Error in general context handler:', error);
      }
    });
  }
  
  /**
   * Get latest context by type
   * @param {string} contextType - Context type
   * @returns {Object|null} Latest context or null
   */
  getLatestContext(contextType) {
    return this.latestContexts.get(contextType) || null;
  }
  
  /**
   * Get all latest contexts
   * @returns {Object} Map of context types to latest contexts
   */
  getAllLatestContexts() {
    return Object.fromEntries(this.latestContexts);
  }
  
  /**
   * Get providers connected to this consumer
   * @returns {Array<string>} Connected provider IDs
   */
  getProviders() {
    return this.hub.getProvidersForConsumer(this.id);
  }
  
  /**
   * Get consumer information
   * @returns {Object} Consumer info
   */
  getInfo() {
    return {
      id: this.id,
      contextTypes: [...this.contextTypes],
      description: this.description,
      metadata: { ...this.metadata },
      providerCount: this.getProviders().length
    };
  }
}

/**
 * Context Connection
 * 
 * Represents a connection between a provider and a consumer.
 */
class ContextConnection {
  /**
   * Create a context connection
   * @param {Object} options - Connection options
   * @param {string} options.providerId - Provider ID
   * @param {string} options.consumerId - Consumer ID
   * @param {string} options.contextType - Context type
   */
  constructor(options) {
    this.providerId = options.providerId;
    this.consumerId = options.consumerId;
    this.contextType = options.contextType;
    this.id = `${this.providerId}:${this.contextType}:${this.consumerId}`;
    this.created = new Date().toISOString();
    this.updateCount = 0;
  }
  
  /**
   * Increment update count
   */
  incrementUpdateCount() {
    this.updateCount++;
  }
  
  /**
   * Get connection information
   * @returns {Object} Connection info
   */
  getInfo() {
    return {
      providerId: this.providerId,
      consumerId: this.consumerId,
      contextType: this.contextType,
      id: this.id,
      created: this.created,
      updateCount: this.updateCount
    };
  }
}

/**
 * Context Hub
 * 
 * Central registry for context providers and consumers.
 */
class ContextHub {
  /**
   * Create a context hub
   * @param {Object} options - Hub options
   * @param {Object} options.eventBus - Event bus for pub/sub
   * @param {Object} options.manifoldRegistry - ManifoldRegistry instance
   */
  constructor(options = {}) {
    this.eventBus = options.eventBus || { publish: () => {}, subscribe: () => {} };
    this.manifoldRegistry = options.manifoldRegistry;
    
    // Registry maps
    this.providers = new Map();
    this.consumers = new Map();
    this.connections = new Map();
    
    // Context type indices
    this.providersByType = new Map();
    this.consumersByType = new Map();
    
    // Initialization flag
    this.initialized = false;
  }
  
  /**
   * Initialize the context hub
   * @returns {Promise<boolean>} Success flag
   */
  async initialize() {
    if (this.initialized) {
      return true;
    }
    
    try {
      // Subscribe to events
      this.eventBus.subscribe('context:register-provider', this._handleRegisterProvider.bind(this));
      this.eventBus.subscribe('context:register-consumer', this._handleRegisterConsumer.bind(this));
      this.eventBus.subscribe('context:unregister-provider', this._handleUnregisterProvider.bind(this));
      this.eventBus.subscribe('context:unregister-consumer', this._handleUnregisterConsumer.bind(this));
      
      this.initialized = true;
      return true;
    } catch (error) {
      console.error('Failed to initialize context hub:', error);
      return false;
    }
  }
  
  /**
   * Register a context provider
   * @param {Object} options - Provider options
   * @returns {Promise<ContextProvider>} Provider instance
   */
  async registerProvider(options) {
    // Check if provider already exists
    if (this.providers.has(options.id)) {
      throw new Error(`Provider with ID ${options.id} already exists`);
    }
    
    // Create provider
    const provider = new ContextProvider({
      ...options,
      hub: this
    });
    
    // Add to registry
    this.providers.set(provider.id, provider);
    
    // Add to type index
    if (!this.providersByType.has(provider.contextType)) {
      this.providersByType.set(provider.contextType, []);
    }
    this.providersByType.get(provider.contextType).push(provider);
    
    // Register with manifold registry if available
    if (this.manifoldRegistry && options.manifoldId) {
      try {
        await this.manifoldRegistry.updateManifold(options.manifoldId, {
          contextProviderId: provider.id,
          contextType: provider.contextType
        });
      } catch (error) {
        console.warn('Failed to update manifold with context provider:', error);
      }
    }
    
    // Connect to compatible consumers
    this._connectProvider(provider);
    
    // Publish event
    this.eventBus.publish('context:provider-registered', {
      id: provider.id,
      contextType: provider.contextType,
      description: provider.description
    });
    
    return provider;
  }
  
  /**
   * Register a context consumer
   * @param {Object} options - Consumer options
   * @returns {Promise<ContextConsumer>} Consumer instance
   */
  async registerConsumer(options) {
    // Check if consumer already exists
    if (this.consumers.has(options.id)) {
      throw new Error(`Consumer with ID ${options.id} already exists`);
    }
    
    // Create consumer
    const consumer = new ContextConsumer({
      ...options,
      hub: this
    });
    
    // Add to registry
    this.consumers.set(consumer.id, consumer);
    
    // Add to type indices
    consumer.contextTypes.forEach(type => {
      if (!this.consumersByType.has(type)) {
        this.consumersByType.set(type, []);
      }
      this.consumersByType.get(type).push(consumer);
    });
    
    // Register with manifold registry if available
    if (this.manifoldRegistry && options.manifoldId) {
      try {
        await this.manifoldRegistry.updateManifold(options.manifoldId, {
          contextConsumerId: consumer.id,
          contextTypes: consumer.contextTypes
        });
      } catch (error) {
        console.warn('Failed to update manifold with context consumer:', error);
      }
    }
    
    // Connect to compatible providers
    this._connectConsumer(consumer);
    
    // Publish event
    this.eventBus.publish('context:consumer-registered', {
      id: consumer.id,
      contextTypes: [...consumer.contextTypes],
      description: consumer.description
    });
    
    return consumer;
  }
  
  /**
   * Unregister a provider
   * @param {string} providerId - Provider ID
   * @returns {Promise<boolean>} Success flag
   */
  async unregisterProvider(providerId) {
    const provider = this.providers.get(providerId);
    if (!provider) {
      return false;
    }
    
    // Remove connections
    const connectionIds = [];
    for (const [id, connection] of this.connections.entries()) {
      if (connection.providerId === providerId) {
        connectionIds.push(id);
      }
    }
    
    connectionIds.forEach(id => {
      this.connections.delete(id);
    });
    
    // Remove from type index
    const typeProviders = this.providersByType.get(provider.contextType) || [];
    const index = typeProviders.findIndex(p => p.id === providerId);
    if (index !== -1) {
      typeProviders.splice(index, 1);
    }
    
    // Remove from registry
    this.providers.delete(providerId);
    
    // Publish event
    this.eventBus.publish('context:provider-unregistered', {
      id: providerId,
      contextType: provider.contextType
    });
    
    return true;
  }
  
  /**
   * Unregister a consumer
   * @param {string} consumerId - Consumer ID
   * @returns {Promise<boolean>} Success flag
   */
  async unregisterConsumer(consumerId) {
    const consumer = this.consumers.get(consumerId);
    if (!consumer) {
      return false;
    }
    
    // Remove connections
    const connectionIds = [];
    for (const [id, connection] of this.connections.entries()) {
      if (connection.consumerId === consumerId) {
        connectionIds.push(id);
      }
    }
    
    connectionIds.forEach(id => {
      this.connections.delete(id);
    });
    
    // Remove from type indices
    consumer.contextTypes.forEach(type => {
      const typeConsumers = this.consumersByType.get(type) || [];
      const index = typeConsumers.findIndex(c => c.id === consumerId);
      if (index !== -1) {
        typeConsumers.splice(index, 1);
      }
    });
    
    // Remove from registry
    this.consumers.delete(consumerId);
    
    // Publish event
    this.eventBus.publish('context:consumer-unregistered', {
      id: consumerId,
      contextTypes: consumer.contextTypes
    });
    
    return true;
  }
  
  /**
   * Publish context update
   * @param {Object} contextUpdate - Context update
   */
  async publishContextUpdate(contextUpdate) {
    const { providerId, contextType } = contextUpdate;
    
    // Get consumers for this provider and context type
    const consumers = this.getConsumersForProviderAndType(providerId, contextType);
    
    // Notify each consumer
    for (const consumerId of consumers) {
      const consumer = this.consumers.get(consumerId);
      if (consumer) {
        consumer.handleContextUpdate(contextUpdate);
        
        // Update connection statistics
        const connectionId = `${providerId}:${contextType}:${consumerId}`;
        const connection = this.connections.get(connectionId);
        if (connection) {
          connection.incrementUpdateCount();
        }
      }
    }
    
    // Publish global event
    this.eventBus.publish('context:updated', {
      providerId,
      contextType,
      data: contextUpdate.data,
      consumerCount: consumers.length
    });
    
    return true;
  }
  
  /**
   * Get consumers for a provider
   * @param {string} providerId - Provider ID
   * @returns {Array<string>} Consumer IDs
   */
  getConsumersForProvider(providerId) {
    const consumers = new Set();
    
    for (const connection of this.connections.values()) {
      if (connection.providerId === providerId) {
        consumers.add(connection.consumerId);
      }
    }
    
    return Array.from(consumers);
  }
  
  /**
   * Get consumers for a provider and context type
   * @param {string} providerId - Provider ID
   * @param {string} contextType - Context type
   * @returns {Array<string>} Consumer IDs
   */
  getConsumersForProviderAndType(providerId, contextType) {
    const consumers = [];
    
    for (const connection of this.connections.values()) {
      if (connection.providerId === providerId && connection.contextType === contextType) {
        consumers.push(connection.consumerId);
      }
    }
    
    return consumers;
  }
  
  /**
   * Get providers for a consumer
   * @param {string} consumerId - Consumer ID
   * @returns {Array<string>} Provider IDs
   */
  getProvidersForConsumer(consumerId) {
    const providers = new Set();
    
    for (const connection of this.connections.values()) {
      if (connection.consumerId === consumerId) {
        providers.add(connection.providerId);
      }
    }
    
    return Array.from(providers);
  }
  
  /**
   * Get providers by context type
   * @param {string} contextType - Context type
   * @returns {Array<ContextProvider>} Providers
   */
  getProvidersByType(contextType) {
    return this.providersByType.get(contextType) || [];
  }
  
  /**
   * Get consumers by context type
   * @param {string} contextType - Context type
   * @returns {Array<ContextConsumer>} Consumers
   */
  getConsumersByType(contextType) {
    return this.consumersByType.get(contextType) || [];
  }
  
  /**
   * Get context connection information
   * @returns {Array<Object>} Connection info
   */
  getConnectionInfo() {
    return Array.from(this.connections.values()).map(connection => connection.getInfo());
  }
  
  /**
   * Connect a provider to compatible consumers
   * @param {ContextProvider} provider - Provider to connect
   * @private
   */
  _connectProvider(provider) {
    const { id: providerId, contextType } = provider;
    
    // Find compatible consumers
    const compatibleConsumers = this.consumersByType.get(contextType) || [];
    
    // Create connections
    compatibleConsumers.forEach(consumer => {
      const consumerId = consumer.id;
      
      // Create connection
      const connection = new ContextConnection({
        providerId,
        consumerId,
        contextType
      });
      
      // Add to connections map
      this.connections.set(connection.id, connection);
      
      // Publish event
      this.eventBus.publish('context:connection-created', {
        providerId,
        consumerId,
        contextType
      });
      
      // If provider has latest context, send it to the consumer
      const provider = this.providers.get(providerId);
      if (provider && provider.latestContext) {
        consumer.handleContextUpdate(provider.latestContext);
      }
    });
  }
  
  /**
   * Connect a consumer to compatible providers
   * @param {ContextConsumer} consumer - Consumer to connect
   * @private
   */
  _connectConsumer(consumer) {
    const { id: consumerId, contextTypes } = consumer;
    
    // Find compatible providers for each context type
    contextTypes.forEach(contextType => {
      const compatibleProviders = this.providersByType.get(contextType) || [];
      
      // Create connections
      compatibleProviders.forEach(provider => {
        const providerId = provider.id;
        
        // Create connection
        const connection = new ContextConnection({
          providerId,
          consumerId,
          contextType
        });
        
        // Add to connections map
        this.connections.set(connection.id, connection);
        
        // Publish event
        this.eventBus.publish('context:connection-created', {
          providerId,
          consumerId,
          contextType
        });
        
        // If provider has latest context, send it to the consumer
        if (provider.latestContext) {
          consumer.handleContextUpdate(provider.latestContext);
        }
      });
    });
  }
  
  /**
   * Handle register provider event
   * @param {Object} data - Event data
   * @private
   */
  async _handleRegisterProvider(data) {
    try {
      await this.registerProvider(data);
    } catch (error) {
      console.error('Error handling register provider event:', error);
    }
  }
  
  /**
   * Handle register consumer event
   * @param {Object} data - Event data
   * @private
   */
  async _handleRegisterConsumer(data) {
    try {
      await this.registerConsumer(data);
    } catch (error) {
      console.error('Error handling register consumer event:', error);
    }
  }
  
  /**
   * Handle unregister provider event
   * @param {Object} data - Event data
   * @private
   */
  async _handleUnregisterProvider(data) {
    try {
      await this.unregisterProvider(data.id);
    } catch (error) {
      console.error('Error handling unregister provider event:', error);
    }
  }
  
  /**
   * Handle unregister consumer event
   * @param {Object} data - Event data
   * @private
   */
  async _handleUnregisterConsumer(data) {
    try {
      await this.unregisterConsumer(data.id);
    } catch (error) {
      console.error('Error handling unregister consumer event:', error);
    }
  }
}

// Export module
module.exports = {
  ContextProvider,
  ContextConsumer,
  ContextHub,
  SchemaValidator
};