/**
 * Context Sharing System
 * 
 * Provides a mechanism for components to share context data with schema validation.
 */

class ContextHub {
  constructor(options = {}) {
    this.manifoldRegistry = options.manifoldRegistry;
    this.eventBus = options.eventBus;
    this.providers = new Map();
    this.consumers = new Map();
    this.connections = [];
    this.initialized = false;
  }
  
  async initialize() {
    if (this.initialized) return this;
    
    // Set up event listeners if event bus is provided
    if (this.eventBus) {
      this.eventBus.subscribe('context:provider-registered', (data) => {
        this._connectCompatibleConsumers(data.id, data.contextType);
      });
      
      this.eventBus.subscribe('context:consumer-registered', (data) => {
        this._connectCompatibleProviders(data.id, data.contextTypes);
      });
    }
    
    this.initialized = true;
    return this;
  }
  
  /**
   * Register a context provider
   */
  async registerProvider(options) {
    if (!options.id || !options.contextType) {
      throw new Error('Provider ID and context type are required');
    }
    
    // Create provider
    const provider = new ContextProvider({
      id: options.id,
      contextType: options.contextType, 
      description: options.description,
      schema: options.schema,
      contextHub: this,
      eventBus: this.eventBus
    });
    
    // Store provider
    this.providers.set(options.id, provider);
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('context:provider-registered', {
        id: options.id,
        contextType: options.contextType
      });
    }
    
    return provider;
  }
  
  /**
   * Register a context consumer
   */
  async registerConsumer(options) {
    if (!options.id || !options.contextTypes || !options.contextTypes.length) {
      throw new Error('Consumer ID and context types are required');
    }
    
    // Create consumer
    const consumer = new ContextConsumer({
      id: options.id,
      contextTypes: options.contextTypes,
      description: options.description,
      contextHub: this,
      eventBus: this.eventBus
    });
    
    // Store consumer
    this.consumers.set(options.id, consumer);
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('context:consumer-registered', {
        id: options.id,
        contextTypes: options.contextTypes
      });
    }
    
    return consumer;
  }
  
  /**
   * Create a connection between provider and consumer
   */
  _createConnection(providerId, consumerId, contextType) {
    // Check if connection already exists
    const existingConnection = this.connections.find(
      conn => conn.providerId === providerId && 
              conn.consumerId === consumerId &&
              conn.contextType === contextType
    );
    
    if (existingConnection) {
      return existingConnection;
    }
    
    // Create new connection
    const connection = {
      providerId,
      consumerId,
      contextType,
      created: new Date().toISOString()
    };
    
    this.connections.push(connection);
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('context:connection-created', connection);
    }
    
    return connection;
  }
  
  /**
   * Connect compatible providers to a consumer
   */
  _connectCompatibleProviders(consumerId, contextTypes) {
    const consumer = this.consumers.get(consumerId);
    if (!consumer) return;
    
    // For each provider
    for (const [providerId, provider] of this.providers.entries()) {
      // If provider offers a context type the consumer wants
      if (contextTypes.includes(provider.contextType)) {
        // Create connection
        this._createConnection(providerId, consumerId, provider.contextType);
        
        // If provider has current context data, deliver it to the consumer
        if (provider.currentContext !== undefined) {
          consumer._receiveContext(provider.contextType, provider.currentContext, providerId);
        }
      }
    }
  }
  
  /**
   * Connect compatible consumers to a provider
   */
  _connectCompatibleConsumers(providerId, contextType) {
    const provider = this.providers.get(providerId);
    if (!provider) return;
    
    // For each consumer
    for (const [consumerId, consumer] of this.consumers.entries()) {
      // If consumer wants the context type the provider offers
      if (consumer.contextTypes.includes(contextType)) {
        // Create connection
        this._createConnection(providerId, consumerId, contextType);
        
        // If provider has current context data, deliver it to the consumer
        if (provider.currentContext !== undefined) {
          consumer._receiveContext(contextType, provider.currentContext, providerId);
        }
      }
    }
  }
  
  /**
   * Get all connections
   */
  getConnectionInfo() {
    return [...this.connections];
  }
  
  /**
   * Update context from provider to connected consumers
   */
  _updateContext(providerId, contextType, data) {
    // Find connections for this provider and context type
    const connections = this.connections.filter(
      conn => conn.providerId === providerId && conn.contextType === contextType
    );
    
    // For each connection, update the consumer
    for (const connection of connections) {
      const consumer = this.consumers.get(connection.consumerId);
      if (consumer) {
        consumer._receiveContext(contextType, data, providerId);
      }
    }
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('context:updated', {
        providerId,
        contextType,
        timestamp: new Date().toISOString()
      });
    }
  }
  
  /**
   * Get a provider by ID
   */
  getProvider(id) {
    return this.providers.get(id);
  }
  
  /**
   * Get a consumer by ID
   */
  getConsumer(id) {
    return this.consumers.get(id);
  }
}

class ContextProvider {
  constructor(options) {
    this.id = options.id;
    this.contextType = options.contextType;
    this.description = options.description || '';
    this.schema = options.schema;
    this.contextHub = options.contextHub;
    this.eventBus = options.eventBus;
    this.currentContext = undefined;
  }
  
  /**
   * Update the context data
   */
  async updateContext(data) {
    // Validate data against schema if schema is provided
    if (this.schema) {
      this._validateAgainstSchema(data);
    }
    
    // Store current context
    this.currentContext = data;
    
    // Propagate update to context hub
    if (this.contextHub) {
      this.contextHub._updateContext(this.id, this.contextType, data);
    }
    
    return true;
  }
  
  /**
   * Validate data against schema
   */
  _validateAgainstSchema(data) {
    // Simple schema validation
    if (!data || typeof data !== 'object') {
      throw new Error('Context data must be an object');
    }
    
    if (!this.schema) return true;
    
    // Check required properties
    if (this.schema.required) {
      for (const prop of this.schema.required) {
        if (!(prop in data)) {
          throw new Error(`Required property '${prop}' is missing`);
        }
      }
    }
    
    // Check property types
    if (this.schema.properties) {
      for (const [prop, propSchema] of Object.entries(this.schema.properties)) {
        if (prop in data) {
          if (propSchema.type === 'string' && typeof data[prop] !== 'string') {
            throw new Error(`Property '${prop}' should be a string`);
          } else if (propSchema.type === 'number' && typeof data[prop] !== 'number') {
            throw new Error(`Property '${prop}' should be a number`);
          } else if (propSchema.type === 'boolean' && typeof data[prop] !== 'boolean') {
            throw new Error(`Property '${prop}' should be a boolean`);
          } else if (propSchema.type === 'object' && (typeof data[prop] !== 'object' || data[prop] === null)) {
            throw new Error(`Property '${prop}' should be an object`);
          } else if (propSchema.type === 'array' && !Array.isArray(data[prop])) {
            throw new Error(`Property '${prop}' should be an array`);
          }
        }
      }
    }
    
    return true;
  }
}

class ContextConsumer {
  constructor(options) {
    this.id = options.id;
    this.contextTypes = options.contextTypes;
    this.description = options.description || '';
    this.contextHub = options.contextHub;
    this.eventBus = options.eventBus;
    this.contextHandlers = new Map();
    this.receivedContexts = new Map();
  }
  
  /**
   * Subscribe to context updates for a specific type
   */
  onContext(contextType, handler) {
    if (!this.contextTypes.includes(contextType)) {
      throw new Error(`This consumer does not subscribe to context type '${contextType}'`);
    }
    
    if (!this.contextHandlers.has(contextType)) {
      this.contextHandlers.set(contextType, []);
    }
    
    this.contextHandlers.get(contextType).push(handler);
    
    // If we already have this context type, call the handler immediately
    if (this.receivedContexts.has(contextType)) {
      const contextData = this.receivedContexts.get(contextType);
      handler(contextData.data, contextData.providerId);
    }
    
    // Return unsubscribe function
    return () => {
      const handlers = this.contextHandlers.get(contextType) || [];
      const index = handlers.indexOf(handler);
      if (index !== -1) {
        handlers.splice(index, 1);
      }
    };
  }
  
  /**
   * Receive context update from provider (internal use)
   */
  _receiveContext(contextType, data, providerId) {
    // Store received context
    this.receivedContexts.set(contextType, { data, providerId });
    
    // Call handlers
    const handlers = this.contextHandlers.get(contextType) || [];
    for (const handler of handlers) {
      try {
        handler(data, providerId);
      } catch (error) {
        console.error(`Error in context handler for ${contextType}: ${error.message}`);
      }
    }
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('context:consumer-updated', {
        consumerId: this.id,
        contextType,
        providerId,
        timestamp: new Date().toISOString()
      });
    }
  }
  
  /**
   * Get all received contexts
   */
  getReceivedContexts() {
    return Object.fromEntries(this.receivedContexts);
  }
  
  /**
   * Get specific context type
   */
  getContext(contextType) {
    return this.receivedContexts.has(contextType) 
      ? this.receivedContexts.get(contextType).data 
      : undefined;
  }
}

// CommonJS export
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { ContextHub, ContextProvider, ContextConsumer };
}

// ES module export
export { ContextHub, ContextProvider, ContextConsumer };
