/**
 * PrimeOS Reference Implementation - Extension System
 * 
 * Provides a framework for extending PrimeOS functionality through plugins and
 * extension points. This system allows PrimeOS to be customized with additional
 * features, UI components, and integrations without modifying core functionality.
 */

/**
 * Schema validator for extension content
 * Simplified implementation for basic validation
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
      // Check required properties
      if (schema.required) {
        for (const prop of schema.required) {
          if (data[prop] === undefined) {
            errors.push(`Required property ${prop} is missing`);
          }
        }
      }
      
      // Check property types
      Object.keys(schema.properties).forEach(prop => {
        if (data[prop] !== undefined) {
          const propSchema = schema.properties[prop];
          const propType = this._getType(data[prop]);
          
          if (propSchema.type && propType !== propSchema.type) {
            errors.push(`Property ${prop}: Expected type ${propSchema.type}, got ${propType}`);
          }
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
        
        // Validate object items
        if (itemType === 'object' && itemSchema.type === 'object' && itemSchema.properties) {
          const itemResult = this.validate(item, itemSchema);
          if (!itemResult.valid) {
            errors.push(...itemResult.errors.map(err => `Array item ${index}: ${err}`));
          }
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
 * Extension Point
 * 
 * Represents a point in the system where extensions can integrate.
 */
class ExtensionPoint {
  /**
   * Create an extension point
   * @param {Object} options - Extension point options
   * @param {string} options.id - Unique extension point ID
   * @param {string} options.name - Display name
   * @param {string} options.description - Description
   * @param {Object} options.schema - JSON Schema for content validation
   * @param {Object} options.manager - Parent extension manager
   */
  constructor(options) {
    this.id = options.id;
    this.name = options.name || '';
    this.description = options.description || '';
    this.schema = options.schema || null;
    this.manager = options.manager;
    this.validator = new SchemaValidator();
    
    // Subscribe callbacks
    this.subscribers = [];
    
    // Metadata
    this.metadata = {
      created: new Date().toISOString(),
      lastUpdated: new Date().toISOString()
    };
  }
  
  /**
   * Get all content for this extension point
   * @returns {Array<Object>} Content items
   */
  getContent() {
    return this.manager.getExtensionPointContent(this.id);
  }
  
  /**
   * Subscribe to content changes
   * @param {Function} callback - Callback function
   * @returns {Function} Unsubscribe function
   */
  subscribe(callback) {
    this.subscribers.push(callback);
    
    // Immediately call with current content
    callback(this.getContent());
    
    // Return unsubscribe function
    return () => {
      const index = this.subscribers.indexOf(callback);
      if (index !== -1) {
        this.subscribers.splice(index, 1);
      }
    };
  }
  
  /**
   * Notify subscribers of content changes
   */
  notifySubscribers() {
    const content = this.getContent();
    for (const subscriber of this.subscribers) {
      try {
        subscriber(content);
      } catch (error) {
        console.error(`Error in extension point subscriber for ${this.id}:`, error);
      }
    }
  }
  
  /**
   * Validate content against schema
   * @param {Object} content - Content to validate
   * @returns {Object} Validation result
   */
  validateContent(content) {
    return this.validator.validate(content, this.schema);
  }
  
  /**
   * Get extension point information
   * @returns {Object} Extension point info
   */
  getInfo() {
    return {
      id: this.id,
      name: this.name,
      description: this.description,
      schema: this.schema,
      metadata: { ...this.metadata },
      contentCount: this.getContent().length
    };
  }
}

/**
 * Extension
 * 
 * Represents an installed extension.
 */
class Extension {
  /**
   * Create an extension
   * @param {Object} manifest - Extension manifest
   * @param {Object} options - Extension options
   * @param {Object} options.manager - Parent extension manager
   */
  constructor(manifest, options) {
    this.id = manifest.id;
    this.name = manifest.name || '';
    this.version = manifest.version || '1.0.0';
    this.description = manifest.description || '';
    this.author = manifest.author || '';
    this.manifest = manifest;
    this.extensionPoints = manifest.extensionPoints || {};
    this.manager = options.manager;
    
    // Extension state
    this.enabled = manifest.enabled !== false;
    this.installed = new Date().toISOString();
    this.lastUpdated = new Date().toISOString();
    
    // Properties for persistence
    this.manifestId = null;
  }
  
  /**
   * Enable the extension
   * @returns {Promise<boolean>} Success flag
   */
  async enable() {
    if (this.enabled) {
      return true;
    }
    
    this.enabled = true;
    this.lastUpdated = new Date().toISOString();
    
    // Notify extension points
    for (const extensionPointId of Object.keys(this.extensionPoints)) {
      const extensionPoint = this.manager.getExtensionPoint(extensionPointId);
      if (extensionPoint) {
        extensionPoint.notifySubscribers();
      }
    }
    
    return true;
  }
  
  /**
   * Disable the extension
   * @returns {Promise<boolean>} Success flag
   */
  async disable() {
    if (!this.enabled) {
      return true;
    }
    
    this.enabled = false;
    this.lastUpdated = new Date().toISOString();
    
    // Notify extension points
    for (const extensionPointId of Object.keys(this.extensionPoints)) {
      const extensionPoint = this.manager.getExtensionPoint(extensionPointId);
      if (extensionPoint) {
        extensionPoint.notifySubscribers();
      }
    }
    
    return true;
  }
  
  /**
   * Get extension information
   * @returns {Object} Extension info
   */
  getInfo() {
    return {
      id: this.id,
      name: this.name,
      version: this.version,
      description: this.description,
      author: this.author,
      enabled: this.enabled,
      installed: this.installed,
      lastUpdated: this.lastUpdated,
      extensionPoints: Object.keys(this.extensionPoints),
      manifestId: this.manifestId
    };
  }
  
  /**
   * Get content for an extension point
   * @param {string} extensionPointId - Extension point ID
   * @returns {Array<Object>} Content items
   */
  getContentForExtensionPoint(extensionPointId) {
    if (!this.enabled) {
      return [];
    }
    
    const content = this.extensionPoints[extensionPointId];
    if (!content) {
      return [];
    }
    
    // Add metadata to each item
    const contentItems = Array.isArray(content) ? content : [content];
    return contentItems.map(item => ({
      ...item,
      extensionId: this.id,
      extensionName: this.name
    }));
  }
  
  /**
   * Get serializable data for persistence
   * @returns {Object} Serializable data
   */
  toJSON() {
    return {
      id: this.id,
      name: this.name,
      version: this.version,
      description: this.description,
      author: this.author,
      extensionPoints: { ...this.extensionPoints },
      enabled: this.enabled,
      installed: this.installed,
      lastUpdated: this.lastUpdated,
      manifestId: this.manifestId
    };
  }
}

/**
 * Extension Manager
 * 
 * Central registry for extension points and extensions.
 */
class ExtensionManager {
  /**
   * Create an extension manager
   * @param {Object} options - Manager options
   * @param {Object} options.eventBus - Event bus for pub/sub
   * @param {Object} options.manifoldRegistry - ManifoldRegistry instance
   * @param {Object} options.secureVault - SecureVault instance
   */
  constructor(options = {}) {
    this.eventBus = options.eventBus || { publish: () => {}, subscribe: () => {} };
    this.manifoldRegistry = options.manifoldRegistry;
    this.secureVault = options.secureVault;
    
    // Registry maps
    this.extensionPoints = new Map();
    this.extensions = new Map();
    
    // Validator
    this.validator = new SchemaValidator();
    
    // Subscribers by extension point
    this.subscribers = new Map();
    
    // Initialization flag
    this.initialized = false;
  }
  
  /**
   * Initialize the extension manager
   * @returns {Promise<boolean>} Success flag
   */
  async initialize() {
    if (this.initialized) {
      return true;
    }
    
    try {
      // Load installed extensions
      await this._loadInstalledExtensions();
      
      // Subscribe to events
      this.eventBus.subscribe('extension:register-extension-point', this._handleRegisterExtensionPoint.bind(this));
      this.eventBus.subscribe('extension:install-request', this._handleInstallRequest.bind(this));
      this.eventBus.subscribe('extension:uninstall-request', this._handleUninstallRequest.bind(this));
      this.eventBus.subscribe('extension:enable-request', this._handleEnableRequest.bind(this));
      this.eventBus.subscribe('extension:disable-request', this._handleDisableRequest.bind(this));
      
      this.initialized = true;
      return true;
    } catch (error) {
      console.error('Failed to initialize extension manager:', error);
      return false;
    }
  }
  
  /**
   * Register an extension point
   * @param {Object} options - Extension point options
   * @returns {Promise<ExtensionPoint>} Extension point
   */
  async registerExtensionPoint(options) {
    // Check if extension point already exists
    if (this.extensionPoints.has(options.id)) {
      throw new Error(`Extension point already exists: ${options.id}`);
    }
    
    // Create extension point
    const extensionPoint = new ExtensionPoint({
      ...options,
      manager: this
    });
    
    // Add to registry
    this.extensionPoints.set(extensionPoint.id, extensionPoint);
    
    // Publish event
    this.eventBus.publish('extension:extension-point-registered', {
      id: extensionPoint.id,
      name: extensionPoint.name,
      description: extensionPoint.description
    });
    
    return extensionPoint;
  }
  
  /**
   * Install an extension
   * @param {Object} manifest - Extension manifest
   * @returns {Promise<Extension>} Installed extension
   */
  async installExtension(manifest) {
    // Validate manifest
    this._validateManifest(manifest);
    
    // Check if extension already exists
    if (this.extensions.has(manifest.id)) {
      throw new Error(`Extension already exists: ${manifest.id}`);
    }
    
    // Validate extension content against extension points
    this._validateExtensionContent(manifest);
    
    // Create extension
    const extension = new Extension(manifest, {
      manager: this
    });
    
    // Register with manifold registry if available
    if (this.manifoldRegistry) {
      try {
        const manifold = await this.manifoldRegistry.registerApp({
          name: extension.name,
          version: extension.version,
          description: extension.description,
          type: 'extension',
          author: extension.author,
          extensionId: extension.id,
          extensionPoints: Object.keys(extension.extensionPoints)
        });
        
        extension.manifestId = manifold.getId();
      } catch (error) {
        console.warn('Failed to register extension manifold:', error);
      }
    }
    
    // Add to registry
    this.extensions.set(extension.id, extension);
    
    // Save to secure vault
    await this._saveInstalledExtensions();
    
    // Notify extension points
    for (const extensionPointId of Object.keys(extension.extensionPoints)) {
      const extensionPoint = this.getExtensionPoint(extensionPointId);
      if (extensionPoint) {
        extensionPoint.notifySubscribers();
      }
    }
    
    // Publish event
    this.eventBus.publish('extension:installed', {
      id: extension.id,
      name: extension.name,
      version: extension.version
    });
    
    return extension;
  }
  
  /**
   * Uninstall an extension
   * @param {string} extensionId - Extension ID
   * @returns {Promise<boolean>} Success flag
   */
  async uninstallExtension(extensionId) {
    const extension = this.extensions.get(extensionId);
    if (!extension) {
      return false;
    }
    
    // Remove from registry
    this.extensions.delete(extensionId);
    
    // Save to secure vault
    await this._saveInstalledExtensions();
    
    // Notify extension points
    for (const extensionPointId of Object.keys(extension.extensionPoints)) {
      const extensionPoint = this.getExtensionPoint(extensionPointId);
      if (extensionPoint) {
        extensionPoint.notifySubscribers();
      }
    }
    
    // Publish event
    this.eventBus.publish('extension:uninstalled', {
      id: extension.id,
      name: extension.name,
      version: extension.version
    });
    
    return true;
  }
  
  /**
   * Enable or disable an extension
   * @param {string} extensionId - Extension ID
   * @param {boolean} enabled - Enabled state
   * @returns {Promise<boolean>} Success flag
   */
  async setExtensionEnabled(extensionId, enabled) {
    const extension = this.extensions.get(extensionId);
    if (!extension) {
      return false;
    }
    
    if (enabled) {
      await extension.enable();
      
      // Publish event
      this.eventBus.publish('extension:enabled', {
        id: extension.id,
        name: extension.name
      });
    } else {
      await extension.disable();
      
      // Publish event
      this.eventBus.publish('extension:disabled', {
        id: extension.id,
        name: extension.name
      });
    }
    
    // Save to secure vault
    await this._saveInstalledExtensions();
    
    return true;
  }
  
  /**
   * Get an extension point by ID
   * @param {string} extensionPointId - Extension point ID
   * @returns {ExtensionPoint|null} Extension point or null
   */
  getExtensionPoint(extensionPointId) {
    return this.extensionPoints.get(extensionPointId) || null;
  }
  
  /**
   * Get all extension points
   * @returns {Array<ExtensionPoint>} Extension points
   */
  getAllExtensionPoints() {
    return Array.from(this.extensionPoints.values());
  }
  
  /**
   * Get an extension by ID
   * @param {string} extensionId - Extension ID
   * @returns {Extension|null} Extension or null
   */
  getExtension(extensionId) {
    return this.extensions.get(extensionId) || null;
  }
  
  /**
   * Get all extensions
   * @returns {Array<Extension>} Extensions
   */
  getAllExtensions() {
    return Array.from(this.extensions.values());
  }
  
  /**
   * Get all content for an extension point
   * @param {string} extensionPointId - Extension point ID
   * @returns {Array<Object>} Content items
   */
  getExtensionPointContent(extensionPointId) {
    const allContent = [];
    
    // Get content from all enabled extensions
    for (const extension of this.extensions.values()) {
      if (extension.enabled) {
        const content = extension.getContentForExtensionPoint(extensionPointId);
        allContent.push(...content);
      }
    }
    
    return allContent;
  }
  
  /**
   * Get content item by ID
   * @param {string} extensionPointId - Extension point ID
   * @param {string} itemId - Item ID
   * @returns {Object|null} Content item or null
   */
  getContentItemById(extensionPointId, itemId) {
    const content = this.getExtensionPointContent(extensionPointId);
    return content.find(item => item.id === itemId) || null;
  }
  
  /**
   * Subscribe to extension point content changes
   * @param {string} extensionPointId - Extension point ID
   * @param {Function} callback - Callback function
   * @returns {Function} Unsubscribe function
   */
  subscribeToExtensionPoint(extensionPointId, callback) {
    const extensionPoint = this.getExtensionPoint(extensionPointId);
    if (!extensionPoint) {
      throw new Error(`Extension point not found: ${extensionPointId}`);
    }
    
    return extensionPoint.subscribe(callback);
  }
  
  /**
   * Validate extension manifest
   * @param {Object} manifest - Extension manifest
   * @throws {Error} If manifest is invalid
   * @private
   */
  _validateManifest(manifest) {
    // Check required fields
    if (!manifest.id) {
      throw new Error('Extension manifest must have an ID');
    }
    
    if (!manifest.name) {
      throw new Error('Extension manifest must have a name');
    }
    
    if (!manifest.version) {
      throw new Error('Extension manifest must have a version');
    }
    
    // Validate extensionPoints object
    if (manifest.extensionPoints) {
      if (typeof manifest.extensionPoints !== 'object' || Array.isArray(manifest.extensionPoints)) {
        throw new Error('Extension manifest extensionPoints must be an object');
      }
      
      // Check for unknown extension points
      for (const extensionPointId of Object.keys(manifest.extensionPoints)) {
        if (!this.extensionPoints.has(extensionPointId)) {
          throw new Error(`Unknown extension point: ${extensionPointId}`);
        }
      }
    }
  }
  
  /**
   * Validate extension content against extension point schemas
   * @param {Object} manifest - Extension manifest
   * @throws {Error} If content is invalid
   * @private
   */
  _validateExtensionContent(manifest) {
    if (!manifest.extensionPoints) {
      return;
    }
    
    for (const [extensionPointId, content] of Object.entries(manifest.extensionPoints)) {
      const extensionPoint = this.getExtensionPoint(extensionPointId);
      if (!extensionPoint) {
        throw new Error(`Extension point not found: ${extensionPointId}`);
      }
      
      // Skip validation if no schema
      if (!extensionPoint.schema) {
        continue;
      }
      
      // Validate content against schema
      const contentItems = Array.isArray(content) ? content : [content];
      
      for (const item of contentItems) {
        const validation = extensionPoint.validateContent(item);
        if (!validation.valid) {
          throw new Error(`Schema validation failed for extension point ${extensionPointId}: ${validation.errors.join(', ')}`);
        }
      }
    }
  }
  
  /**
   * Load installed extensions from secure vault
   * @returns {Promise<boolean>} Success flag
   * @private
   */
  async _loadInstalledExtensions() {
    try {
      // Check if extensions are stored
      const hasExtensions = await this.secureVault.hasSecret('installed-extensions');
      if (!hasExtensions) {
        return true;
      }
      
      // Load extensions
      const extensionData = await this.secureVault.getSecret('installed-extensions');
      if (!Array.isArray(extensionData)) {
        console.warn('Invalid extension data in secure vault');
        return false;
      }
      
      // Create extensions
      for (const data of extensionData) {
        try {
          const extension = new Extension(data, {
            manager: this
          });
          
          this.extensions.set(extension.id, extension);
        } catch (error) {
          console.warn(`Failed to load extension ${data.id}:`, error);
        }
      }
      
      return true;
    } catch (error) {
      console.error('Failed to load installed extensions:', error);
      return false;
    }
  }
  
  /**
   * Save installed extensions to secure vault
   * @returns {Promise<boolean>} Success flag
   * @private
   */
  async _saveInstalledExtensions() {
    try {
      // Convert extensions to JSON
      const extensionData = Array.from(this.extensions.values()).map(extension => 
        extension.toJSON()
      );
      
      // Save to secure vault
      await this.secureVault.setSecret('installed-extensions', extensionData);
      
      return true;
    } catch (error) {
      console.error('Failed to save installed extensions:', error);
      return false;
    }
  }
  
  /**
   * Handle register extension point event
   * @param {Object} data - Event data
   * @private
   */
  async _handleRegisterExtensionPoint(data) {
    try {
      await this.registerExtensionPoint(data);
    } catch (error) {
      console.error('Error handling register extension point event:', error);
    }
  }
  
  /**
   * Handle install request event
   * @param {Object} data - Event data
   * @private
   */
  async _handleInstallRequest(data) {
    try {
      await this.installExtension(data.manifest);
    } catch (error) {
      console.error('Error handling install request event:', error);
      
      // Publish error event
      this.eventBus.publish('extension:install-error', {
        manifest: data.manifest,
        error: error.message
      });
    }
  }
  
  /**
   * Handle uninstall request event
   * @param {Object} data - Event data
   * @private
   */
  async _handleUninstallRequest(data) {
    try {
      await this.uninstallExtension(data.extensionId);
    } catch (error) {
      console.error('Error handling uninstall request event:', error);
      
      // Publish error event
      this.eventBus.publish('extension:uninstall-error', {
        extensionId: data.extensionId,
        error: error.message
      });
    }
  }
  
  /**
   * Handle enable request event
   * @param {Object} data - Event data
   * @private
   */
  async _handleEnableRequest(data) {
    try {
      await this.setExtensionEnabled(data.extensionId, true);
    } catch (error) {
      console.error('Error handling enable request event:', error);
    }
  }
  
  /**
   * Handle disable request event
   * @param {Object} data - Event data
   * @private
   */
  async _handleDisableRequest(data) {
    try {
      await this.setExtensionEnabled(data.extensionId, false);
    } catch (error) {
      console.error('Error handling disable request event:', error);
    }
  }
}

// Export module
module.exports = {
  ExtensionManager,
  Extension,
  ExtensionPoint,
  SchemaValidator
};