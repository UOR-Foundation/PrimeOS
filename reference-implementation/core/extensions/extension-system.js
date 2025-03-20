/**
 * Extension System
 * 
 * Provides a framework for extending PrimeOS through standardized extension points.
 */

class ExtensionManager {
  constructor(options = {}) {
    this.eventBus = options.eventBus;
    this.manifoldRegistry = options.manifoldRegistry;
    this.secureVault = options.secureVault;
    
    this.extensionPoints = new Map();
    this.extensions = new Map();
    this.subscriptions = new Map();
    this.initialized = false;
  }
  
  async initialize() {
    if (this.initialized) return this;
    
    // Set up event listeners if event bus is provided
    if (this.eventBus) {
      this.eventBus.subscribe('extension:installed', (data) => {
        this._processExtensionPoints(data.extension);
      });
      
      this.eventBus.subscribe('extension:uninstalled', (data) => {
        this._removeExtensionContent(data.extension);
      });
      
      this.eventBus.subscribe('extension:enabled', (data) => {
        this._processExtensionPoints(data.extension);
      });
      
      this.eventBus.subscribe('extension:disabled', (data) => {
        this._removeExtensionContent(data.extension);
      });
    }
    
    this.initialized = true;
    return this;
  }
  
  /**
   * Register a new extension point
   */
  async registerExtensionPoint(options) {
    if (!options.id) {
      throw new Error('Extension point ID is required');
    }
    
    if (this.extensionPoints.has(options.id)) {
      throw new Error(`Extension point with ID '${options.id}' already exists`);
    }
    
    // Create extension point
    const extensionPoint = new ExtensionPoint({
      id: options.id,
      name: options.name || options.id,
      description: options.description || '',
      schema: options.schema
    });
    
    // Store extension point
    this.extensionPoints.set(options.id, extensionPoint);
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('extension-point:registered', {
        id: options.id,
        name: extensionPoint.name
      });
    }
    
    // Process existing extensions for this point
    for (const extension of this.extensions.values()) {
      if (extension.enabled && extension.extensionPoints && extension.extensionPoints[options.id]) {
        this._addExtensionContent(extension, options.id);
      }
    }
    
    return extensionPoint;
  }
  
  /**
   * Install a new extension
   */
  async installExtension(manifest) {
    if (!manifest.id) {
      throw new Error('Extension ID is required');
    }
    
    if (this.extensions.has(manifest.id)) {
      throw new Error(`Extension with ID '${manifest.id}' already exists`);
    }
    
    // Validate manifest
    this._validateExtensionManifest(manifest);
    
    // Create extension
    const extension = new Extension({
      id: manifest.id,
      name: manifest.name || manifest.id,
      version: manifest.version || '1.0.0',
      description: manifest.description || '',
      extensionPoints: manifest.extensionPoints || {},
      enabled: true
    });
    
    // Store extension
    this.extensions.set(manifest.id, extension);
    
    // Store extension data securely if secure vault is available
    if (this.secureVault) {
      await this.secureVault.setSecret(`extension:${manifest.id}`, JSON.stringify(extension));
    }
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('extension:installed', {
        id: extension.id,
        name: extension.name,
        extension
      });
    }
    
    return extension;
  }
  
  /**
   * Uninstall an extension
   */
  async uninstallExtension(id) {
    const extension = this.extensions.get(id);
    if (!extension) {
      throw new Error(`Extension with ID '${id}' not found`);
    }
    
    // Remove extension points content
    this._removeExtensionContent(extension);
    
    // Remove extension
    this.extensions.delete(id);
    
    // Remove from secure vault if available
    if (this.secureVault) {
      await this.secureVault.removeSecret(`extension:${id}`);
    }
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('extension:uninstalled', {
        id,
        extension
      });
    }
    
    return true;
  }
  
  /**
   * Enable or disable an extension
   */
  async setExtensionEnabled(id, enabled) {
    const extension = this.extensions.get(id);
    if (!extension) {
      throw new Error(`Extension with ID '${id}' not found`);
    }
    
    if (extension.enabled === enabled) {
      return extension;
    }
    
    // Update extension
    extension.enabled = enabled;
    
    // Update in secure vault if available
    if (this.secureVault) {
      await this.secureVault.setSecret(`extension:${id}`, JSON.stringify(extension));
    }
    
    // Process extension points
    if (enabled) {
      this._processExtensionPoints(extension);
      
      // Emit event
      if (this.eventBus) {
        this.eventBus.publish('extension:enabled', {
          id,
          extension
        });
      }
    } else {
      this._removeExtensionContent(extension);
      
      // Emit event
      if (this.eventBus) {
        this.eventBus.publish('extension:disabled', {
          id,
          extension
        });
      }
    }
    
    return extension;
  }
  
  /**
   * Get all extension points
   */
  getAllExtensionPoints() {
    return Array.from(this.extensionPoints.values());
  }
  
  /**
   * Get all extensions
   */
  getAllExtensions() {
    return Array.from(this.extensions.values());
  }
  
  /**
   * Get extension point content
   */
  getExtensionPointContent(extensionPointId) {
    const extensionPoint = this.extensionPoints.get(extensionPointId);
    if (!extensionPoint) {
      return [];
    }
    
    return extensionPoint.getContent();
  }
  
  /**
   * Subscribe to extension point changes
   */
  subscribeToExtensionPoint(extensionPointId, handler) {
    const extensionPoint = this.extensionPoints.get(extensionPointId);
    if (!extensionPoint) {
      throw new Error(`Extension point '${extensionPointId}' not found`);
    }
    
    if (!this.subscriptions.has(extensionPointId)) {
      this.subscriptions.set(extensionPointId, []);
    }
    
    this.subscriptions.get(extensionPointId).push(handler);
    
    // Initial call with current content
    handler(extensionPoint.getContent());
    
    // Return unsubscribe function
    return () => {
      const handlers = this.subscriptions.get(extensionPointId) || [];
      const index = handlers.indexOf(handler);
      if (index !== -1) {
        handlers.splice(index, 1);
      }
    };
  }
  
  /**
   * Process extension points for an extension
   */
  _processExtensionPoints(extension) {
    if (!extension.extensionPoints) return;
    
    for (const [pointId, items] of Object.entries(extension.extensionPoints)) {
      this._addExtensionContent(extension, pointId, items);
    }
  }
  
  /**
   * Add extension content to an extension point
   */
  _addExtensionContent(extension, extensionPointId, items) {
    const extensionPoint = this.extensionPoints.get(extensionPointId);
    if (!extensionPoint) return;
    
    // Use provided items or get from extension
    const contentItems = items || extension.extensionPoints[extensionPointId];
    if (!contentItems || !Array.isArray(contentItems)) return;
    
    // Add each item
    for (const item of contentItems) {
      // Add extension metadata
      const enrichedItem = {
        ...item,
        extensionId: extension.id,
        extensionName: extension.name
      };
      
      // Add to extension point
      extensionPoint.addContent(enrichedItem);
    }
    
    // Notify subscribers
    this._notifyExtensionPointSubscribers(extensionPointId);
  }
  
  /**
   * Remove extension content from all extension points
   */
  _removeExtensionContent(extension) {
    if (!extension.extensionPoints) return;
    
    for (const pointId of Object.keys(extension.extensionPoints)) {
      const extensionPoint = this.extensionPoints.get(pointId);
      if (extensionPoint) {
        // Remove all content from this extension
        extensionPoint.removeContentByExtension(extension.id);
        
        // Notify subscribers
        this._notifyExtensionPointSubscribers(pointId);
      }
    }
  }
  
  /**
   * Notify extension point subscribers about changes
   */
  _notifyExtensionPointSubscribers(extensionPointId) {
    const extensionPoint = this.extensionPoints.get(extensionPointId);
    if (!extensionPoint) return;
    
    const handlers = this.subscriptions.get(extensionPointId) || [];
    const content = extensionPoint.getContent();
    
    for (const handler of handlers) {
      try {
        handler(content);
      } catch (error) {
        console.error(`Error in extension point handler: ${error.message}`);
      }
    }
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('extension-point:content-changed', {
        id: extensionPointId,
        name: extensionPoint.name
      });
    }
  }
  
  /**
   * Validate extension manifest
   */
  _validateExtensionManifest(manifest) {
    // Basic validation
    if (!manifest.id) {
      throw new Error('Extension ID is required');
    }
    
    if (!manifest.name) {
      throw new Error('Extension name is required');
    }
    
    if (!manifest.version) {
      throw new Error('Extension version is required');
    }
    
    // Check extension points
    if (manifest.extensionPoints) {
      for (const [pointId, items] of Object.entries(manifest.extensionPoints)) {
        const extensionPoint = this.extensionPoints.get(pointId);
        
        // Warn if extension point doesn't exist
        if (!extensionPoint) {
          console.warn(`Extension point '${pointId}' is not registered`);
          continue;
        }
        
        // Validate schema if available
        if (extensionPoint.schema && Array.isArray(items)) {
          for (const item of items) {
            this._validateItemAgainstSchema(item, extensionPoint.schema, pointId);
          }
        }
      }
    }
    
    return true;
  }
  
  /**
   * Validate an item against schema
   */
  _validateItemAgainstSchema(item, schema, pointId) {
    // Check if item is an object
    if (!item || typeof item !== 'object') {
      throw new Error(`Extension point '${pointId}' items must be objects`);
    }
    
    // Check required properties
    if (schema.required) {
      for (const prop of schema.required) {
        if (!(prop in item)) {
          throw new Error(`Required property '${prop}' is missing in extension point '${pointId}'`);
        }
      }
    }
    
    // Check property types
    if (schema.properties) {
      for (const [prop, propSchema] of Object.entries(schema.properties)) {
        if (prop in item) {
          if (propSchema.type === 'string' && typeof item[prop] !== 'string') {
            throw new Error(`Property '${prop}' should be a string in extension point '${pointId}'`);
          } else if (propSchema.type === 'number' && typeof item[prop] !== 'number') {
            throw new Error(`Property '${prop}' should be a number in extension point '${pointId}'`);
          } else if (propSchema.type === 'boolean' && typeof item[prop] !== 'boolean') {
            throw new Error(`Property '${prop}' should be a boolean in extension point '${pointId}'`);
          } else if (propSchema.type === 'object' && (typeof item[prop] !== 'object' || item[prop] === null)) {
            throw new Error(`Property '${prop}' should be an object in extension point '${pointId}'`);
          } else if (propSchema.type === 'array' && !Array.isArray(item[prop])) {
            throw new Error(`Property '${prop}' should be an array in extension point '${pointId}'`);
          }
        }
      }
    }
    
    return true;
  }
}

class ExtensionPoint {
  constructor(options) {
    this.id = options.id;
    this.name = options.name || options.id;
    this.description = options.description || '';
    this.schema = options.schema;
    this.content = [];
  }
  
  /**
   * Add content to this extension point
   */
  addContent(item) {
    // Check if item already exists
    const existingIndex = this.content.findIndex(i => 
      i.id === item.id && i.extensionId === item.extensionId
    );
    
    if (existingIndex !== -1) {
      // Update existing item
      this.content[existingIndex] = item;
    } else {
      // Add new item
      this.content.push(item);
    }
    
    return true;
  }
  
  /**
   * Remove content by ID
   */
  removeContent(id) {
    this.content = this.content.filter(item => item.id !== id);
    return true;
  }
  
  /**
   * Remove all content from a specific extension
   */
  removeContentByExtension(extensionId) {
    this.content = this.content.filter(item => item.extensionId !== extensionId);
    return true;
  }
  
  /**
   * Get all content
   */
  getContent() {
    return [...this.content];
  }
}

class Extension {
  constructor(options) {
    this.id = options.id;
    this.name = options.name || options.id;
    this.version = options.version || '1.0.0';
    this.description = options.description || '';
    this.extensionPoints = options.extensionPoints || {};
    this.enabled = options.enabled !== false;
  }
  
  /**
   * Convert to JSON
   */
  toJSON() {
    return {
      id: this.id,
      name: this.name,
      version: this.version,
      description: this.description,
      extensionPoints: this.extensionPoints,
      enabled: this.enabled
    };
  }
}

// CommonJS export
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { ExtensionManager, ExtensionPoint, Extension };
}

// ES module export
export { ExtensionManager, ExtensionPoint, Extension };
