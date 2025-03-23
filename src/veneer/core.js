/**
 * PrimeOS Veneer - Core Framework
 * Provides a high-level API for PrimeOS applications
 */

const Prime = require('../core');
const EventEmitter = require('events');
const { PrimeError } = require('../core/error');
const path = require('path');

// Load coherence systems
const { CoherenceManager } = require('./coherence-manager');
const { CoherenceBoundaryRegistry } = require('./coherence-boundaries');

/**
 * PrimeVeneer Error class
 */
class PrimeVeneerError extends PrimeError {
  constructor(message, details = {}, code = 'VENEER_ERROR') {
    super(message, details, code);
    this.name = 'PrimeVeneerError';
  }
}

/**
 * Core PrimeOS Veneer class
 * Acts as the main integration point between applications and PrimeOS
 */
class PrimeVeneer extends EventEmitter {
  /**
   * Create a new PrimeVeneer instance
   * @param {Object} options - Veneer options
   */
  constructor(options = {}) {
    super();
    
    this.options = {
      debug: false,
      storageProvider: 'auto',
      coherenceThreshold: 0.7,
      maxApps: 100,
      appDirectories: [],
      monitoringInterval: 5000,     // 5 seconds
      strictCoherence: false,       // Strict coherence enforcement
      autoResolveViolations: true,  // Auto-resolve coherence violations
      ...options
    };
    
    // Application registry
    this.applications = new Map();
    
    // Resource managers
    this.resources = {
      storage: null,
      compute: null,
      memory: null,
      network: null
    };
    
    // System state
    this.state = {
      initialized: false,
      systemCoherence: 1.0,
      resourceUtilization: {
        storage: 0,
        compute: 0,
        memory: 0
      }
    };
    
    // Bind methods to maintain context
    this.registerApplication = this.registerApplication.bind(this);
    this.unregisterApplication = this.unregisterApplication.bind(this);
    this.getApplication = this.getApplication.bind(this);
    this.getAllApplications = this.getAllApplications.bind(this);
    
    // Coherence systems
    this.coherenceMonitor = null;
    
    // Initialize coherence manager
    this.coherenceManager = new CoherenceManager({
      monitoringInterval: this.options.monitoringInterval,
      baselineThreshold: this.options.coherenceThreshold,
      strictMode: this.options.strictCoherence,
      autoResolve: this.options.autoResolveViolations
    });
    
    // Initialize coherence boundary registry
    this.boundaryRegistry = new CoherenceBoundaryRegistry({
      enableStrictValidation: this.options.strictCoherence,
      defaultThreshold: this.options.coherenceThreshold
    });
    
    // Set veneer reference in coherence manager
    this.coherenceManager.setVeneer(this);
    
    // App registry and loader
    this.registry = null;
    this.loader = null;
    
    Prime.Logger.info('PrimeVeneer initialized', { options: this.options });
  }
  
  /**
   * Initialize the veneer system
   * @returns {Promise<void>}
   */
  async init() {
    if (this.state.initialized) {
      return;
    }
    
    try {
      Prime.Logger.info('PrimeVeneer initializing');
      
      // Initialize resource managers
      await this._initResourceManagers();
      
      // Initialize registry and loader
      await this._initAppManagement();
      
      // Start coherence monitoring
      await this.coherenceManager.startMonitoring();
      
      // Mark as initialized
      this.state.initialized = true;
      this.emit('initialized');
      
      Prime.Logger.info('PrimeVeneer initialized successfully');
    } catch (error) {
      Prime.Logger.error('Failed to initialize PrimeVeneer', { error });
      throw new PrimeVeneerError('Failed to initialize veneer', { 
        originalError: error 
      }, 'VENEER_INIT_FAILED');
    }
  }
  
  /**
   * Register a new application with the veneer
   * @param {Object} appInstance - Application instance
   * @param {string} appId - Unique application ID
   * @returns {Promise<void>}
   */
  async registerApplication(appInstance, appId) {
    if (!this.state.initialized) {
      throw new PrimeVeneerError('Veneer not initialized', {}, 'VENEER_NOT_INITIALIZED');
    }
    
    if (this.applications.has(appId)) {
      throw new PrimeVeneerError('Application already registered', { appId }, 'APP_ALREADY_REGISTERED');
    }
    
    // Check application limit
    if (this.applications.size >= this.options.maxApps) {
      throw new PrimeVeneerError('Maximum number of applications reached', { 
        current: this.applications.size, 
        max: this.options.maxApps 
      }, 'MAX_APPS_REACHED');
    }
    
    // Validate application instance
    if (!appInstance || typeof appInstance.init !== 'function') {
      throw new PrimeVeneerError('Invalid application instance', { appId }, 'INVALID_APP_INSTANCE');
    }
    
    // Register the application
    this.applications.set(appId, {
      instance: appInstance,
      id: appId,
      state: 'registered',
      resources: {
        allocated: {},
        requested: {}
      },
      metadata: appInstance.metadata || { name: appId },
      coherenceScore: 1.0,
      registeredAt: Date.now()
    });
    
    // Register app coherence boundaries if specified in manifest
    if (appInstance.manifest && appInstance.manifest.coherence && appInstance.manifest.coherence.boundaries) {
      this._registerAppCoherenceBoundaries(appId, appInstance.manifest.coherence.boundaries);
    }
    
    Prime.Logger.info('Application registered', { appId });
    this.emit('application:registered', { appId });
    
    return appInstance;
  }
  
  /**
   * Unregister an application from the veneer
   * @param {string} appId - Application ID to unregister
   * @returns {Promise<boolean>} - True if successfully unregistered
   */
  async unregisterApplication(appId) {
    if (!this.applications.has(appId)) {
      return false;
    }
    
    const app = this.applications.get(appId);
    
    // Stop the application if running
    if (app.state === 'running' && typeof app.instance.stop === 'function') {
      await app.instance.stop();
    }
    
    // Release all resources
    await this._releaseAppResources(appId);
    
    // Remove from registry
    this.applications.delete(appId);
    
    Prime.Logger.info('Application unregistered', { appId });
    this.emit('application:unregistered', { appId });
    
    return true;
  }
  
  /**
   * Get an application by ID
   * @param {string} appId - Application ID
   * @returns {Object|null} - Application instance or null if not found
   */
  getApplication(appId) {
    if (!this.applications.has(appId)) {
      return null;
    }
    
    return this.applications.get(appId).instance;
  }
  
  /**
   * Get all registered applications
   * @returns {Array<Object>} - Array of application metadata
   */
  getAllApplications() {
    return Array.from(this.applications.values()).map(app => ({
      id: app.id,
      state: app.state,
      metadata: app.metadata,
      coherenceScore: app.coherenceScore,
      registeredAt: app.registeredAt
    }));
  }
  
  /**
   * Load a PrimeApp from a directory
   * @param {string} directory - Directory containing the PrimeApp
   * @param {Object} options - Load options
   * @returns {Promise<Object>} - Loaded application instance
   */
  async loadApp(directory, options = {}) {
    if (!this.state.initialized) {
      throw new PrimeVeneerError('Veneer not initialized', {}, 'VENEER_NOT_INITIALIZED');
    }
    
    if (!this.loader) {
      throw new PrimeVeneerError('App loader not initialized', {}, 'LOADER_NOT_INITIALIZED');
    }
    
    return this.loader.loadFromDirectory(directory, options);
  }
  
  /**
   * Load a PrimeApp from a ZIP file
   * @param {string} zipFile - Path to the ZIP file
   * @param {Object} options - Load options
   * @returns {Promise<Object>} - Loaded application instance
   */
  async loadAppFromZip(zipFile, options = {}) {
    if (!this.state.initialized) {
      throw new PrimeVeneerError('Veneer not initialized', {}, 'VENEER_NOT_INITIALIZED');
    }
    
    if (!this.loader) {
      throw new PrimeVeneerError('App loader not initialized', {}, 'LOADER_NOT_INITIALIZED');
    }
    
    return this.loader.loadFromZip(zipFile, options);
  }
  
  /**
   * Load a PrimeApp from an NPM package
   * @param {string} packageName - NPM package name
   * @param {Object} options - Load options
   * @returns {Promise<Object>} - Loaded application instance
   */
  async loadAppFromNpm(packageName, options = {}) {
    if (!this.state.initialized) {
      throw new PrimeVeneerError('Veneer not initialized', {}, 'VENEER_NOT_INITIALIZED');
    }
    
    if (!this.loader) {
      throw new PrimeVeneerError('App loader not initialized', {}, 'LOADER_NOT_INITIALIZED');
    }
    
    return this.loader.loadFromNpm(packageName, options);
  }
  
  /**
   * Unload a PrimeApp
   * @param {string} appId - ID of the app to unload
   * @returns {Promise<boolean>} - True if successfully unloaded
   */
  async unloadApp(appId) {
    if (!this.state.initialized) {
      throw new PrimeVeneerError('Veneer not initialized', {}, 'VENEER_NOT_INITIALIZED');
    }
    
    if (!this.loader) {
      throw new PrimeVeneerError('App loader not initialized', {}, 'LOADER_NOT_INITIALIZED');
    }
    
    return this.loader.unload(appId);
  }
  
  /**
   * Discover available PrimeApps in the configured directories
   * @param {string[]} additionalDirectories - Additional directories to search
   * @returns {Promise<Array<Object>>} - Discovered apps
   */
  async discoverApps(additionalDirectories = []) {
    if (!this.state.initialized) {
      throw new PrimeVeneerError('Veneer not initialized', {}, 'VENEER_NOT_INITIALIZED');
    }
    
    if (!this.registry) {
      throw new PrimeVeneerError('App registry not initialized', {}, 'REGISTRY_NOT_INITIALIZED');
    }
    
    return this.registry.discoverApps(additionalDirectories);
  }
  
  /**
   * Get available apps from the registry
   * @param {Object} options - Filter options
   * @returns {Array<Object>} - List of app manifests
   */
  getAvailableApps(options = {}) {
    if (!this.registry) {
      return [];
    }
    
    return this.registry.getAvailableApps(options);
  }
  
  /**
   * Find apps that provide a specific interface
   * @param {string} interfaceName - Interface name
   * @returns {Array<Object>} - List of app IDs that provide the interface
   */
  findInterfaceProviders(interfaceName) {
    if (!this.registry) {
      return [];
    }
    
    return this.registry.findInterfaceProviders(interfaceName);
  }
  
  /**
   * Allocate a resource for an application
   * @param {string} appId - Application ID
   * @param {string} resourceType - Type of resource (storage, compute, memory, network)
   * @param {Object} requirements - Resource requirements
   * @returns {Promise<Object>} - Resource handle
   */
  async allocateResource(appId, resourceType, requirements) {
    if (!this.applications.has(appId)) {
      throw new PrimeVeneerError('Application not registered', { appId }, 'APP_NOT_REGISTERED');
    }
    
    if (!this.resources[resourceType]) {
      throw new PrimeVeneerError('Resource type not available', { resourceType }, 'RESOURCE_NOT_AVAILABLE');
    }
    
    const app = this.applications.get(appId);
    
    // Update requested resources
    app.resources.requested[resourceType] = requirements;
    
    // Log resources allocation
    Prime.Logger.debug(`Allocating resource: ${resourceType} for app: ${appId}`, requirements);
    
    // Allocate the resource
    const resourceHandle = await this.resources[resourceType].allocate(appId, requirements);
    
    // Update allocated resources
    app.resources.allocated[resourceType] = resourceHandle;
    
    Prime.Logger.info('Resource allocated', { appId, resourceType, requirements });
    this.emit('resource:allocated', { appId, resourceType, requirements });
    
    return resourceHandle;
  }
  
  /**
   * Release a resource for an application
   * @param {string} appId - Application ID
   * @param {string} resourceType - Type of resource to release
   * @returns {Promise<boolean>} - True if successfully released
   */
  async releaseResource(appId, resourceType) {
    if (!this.applications.has(appId)) {
      return false;
    }
    
    const app = this.applications.get(appId);
    
    if (!app.resources.allocated[resourceType]) {
      return false;
    }
    
    // Release the resource
    await this.resources[resourceType].release(appId);
    
    // Update allocated resources
    delete app.resources.allocated[resourceType];
    delete app.resources.requested[resourceType];
    
    Prime.Logger.info('Resource released', { appId, resourceType });
    this.emit('resource:released', { appId, resourceType });
    
    return true;
  }
  
  /**
   * Calculate overall system coherence score
   * @returns {number} - Coherence score between 0 and 1
   */
  calculateSystemCoherence() {
    if (this.applications.size === 0) {
      return 1.0; // Perfect coherence when no apps are running
    }
    
    // Calculate weighted coherence score
    let totalScore = 0;
    let totalWeight = 0;
    
    for (const app of this.applications.values()) {
      // Get app's coherence score, either from directly calculated or from the instance
      let appCoherence = app.coherenceScore;
      
      // If no coherence score is set yet, try to get it from the instance
      if (appCoherence === undefined || appCoherence === null) {
        if (app.instance && typeof app.instance.calculateCoherence === 'function') {
          try {
            appCoherence = app.instance.calculateCoherence();
          } catch (error) {
            Prime.Logger.warn(`Error getting coherence from app ${app.id}`, { error });
            appCoherence = 1.0; // Default to perfect coherence if calculation fails
          }
        } else {
          appCoherence = 1.0; // Default to perfect coherence
        }
      }
      
      // Calculate weight based on resource utilization
      // The more resources an app uses, the more it affects system coherence
      const allocatedResources = app.resources && app.resources.allocated 
        ? Object.keys(app.resources.allocated)
        : [];
      
      // Each resource type adds weight
      const weight = 1 + allocatedResources.length * 2;
      
      totalWeight += weight;
      totalScore += appCoherence * weight;
    }
    
    const overallScore = totalWeight > 0 ? totalScore / totalWeight : 1.0;
    
    // Update system state
    this.state.systemCoherence = overallScore;
    
    return overallScore;
  }
  
  /**
   * Register application coherence boundaries
   * @private
   * @param {string} appId - Application ID
   * @param {Object} boundaries - Coherence boundaries from manifest
   */
  _registerAppCoherenceBoundaries(appId, boundaries) {
    if (!boundaries || typeof boundaries !== 'object') {
      return;
    }
    
    // Process each domain in the boundaries
    for (const [domain, domainBoundaries] of Object.entries(boundaries)) {
      if (!domainBoundaries || typeof domainBoundaries !== 'object') {
        continue;
      }
      
      // Process each boundary in the domain
      for (const [name, boundaryConfig] of Object.entries(domainBoundaries)) {
        // Create validator function based on the domain and name
        const validator = (value, context) => {
          // The validator will be called by the boundary registry
          // We need to implement a default validation logic for each boundary type
          
          // For resource boundaries, check resource utilization
          if (domain === 'resource') {
            return this._validateResourceBoundary(name, value, context, boundaryConfig);
          }
          
          // For numerical boundaries, check numerical properties
          if (domain === 'numerical') {
            return this._validateNumericalBoundary(name, value, context, boundaryConfig);
          }
          
          // For logical boundaries, check consistency
          if (domain === 'logical') {
            return this._validateLogicalBoundary(name, value, context, boundaryConfig);
          }
          
          // Default to true for unknown domains
          return true;
        };
        
        // Register the boundary with app-specific prefix
        this.boundaryRegistry.registerBoundary(
          domain,
          `${appId}_${name}`,
          validator,
          {
            appId,
            type: boundaryConfig.type || 'soft',
            threshold: boundaryConfig.threshold || this.options.coherenceThreshold,
            description: boundaryConfig.description || `${domain} boundary for ${appId}`,
            priority: boundaryConfig.priority || 5
          }
        );
      }
    }
    
    Prime.Logger.debug(`Registered coherence boundaries for ${appId}`, { boundaries });
  }
  
  /**
   * Validate a resource boundary
   * @private
   */
  _validateResourceBoundary(resourceType, value, context, config) {
    // Implementation depends on resource type
    if (resourceType === 'memory') {
      // Support multiple context formats for memory - handle both the direct test case format
      // and the format that would be used in real monitoring
      const memoryLimit = context.memoryLimit || context.max || 'Infinity';
      const memoryUsage = context.memory || context.usage || 0;
      
      const maxBytes = typeof memoryLimit === 'string' ? this._parseMemorySize(memoryLimit) : memoryLimit;
      
      if (maxBytes === Infinity) return 1.0;
      const remainingPercentage = (maxBytes - memoryUsage) / maxBytes;
      return Math.max(0, Math.min(1, remainingPercentage));
    }
    
    if (resourceType === 'storage') {
      const quota = context.quota || context.max || 'Infinity';
      const used = context.used || context.usage || 0;
      
      const maxBytes = typeof quota === 'string' ? this._parseMemorySize(quota) : quota;
      
      if (maxBytes === Infinity) return 1.0;
      return Math.max(0, Math.min(1, 1 - (used / maxBytes)));
    }
    
    if (resourceType === 'compute') {
      const concurrency = context.concurrency || context.maxConcurrency || Infinity;
      const tasks = context.tasks || context.currentTasks || 0;
      
      if (concurrency === Infinity) return 1.0;
      return Math.max(0, Math.min(1, 1 - (tasks / concurrency)));
    }
    
    return 1.0; // Default to full coherence for unknown resources
  }
  
  /**
   * Validate a numerical boundary
   * @private
   */
  _validateNumericalBoundary(name, value, context, config) {
    if (name === 'finiteness') {
      // Check if value is finite
      if (typeof value === 'number') {
        return Number.isFinite(value);
      }
      
      // For arrays, check proportion of finite values
      if (Array.isArray(value)) {
        const finiteCount = value.filter(item => 
          typeof item === 'number' && Number.isFinite(item)
        ).length;
        
        return value.length > 0 ? finiteCount / value.length : 1.0;
      }
      
      return true;
    }
    
    if (name === 'precision') {
      // Check numerical precision
      const tolerance = context.tolerance || 1e-10;
      
      if (typeof value === 'number') {
        return Number.isFinite(value);
      }
      
      if (Array.isArray(value)) {
        const finiteCount = value.filter(item => 
          typeof item === 'number' && Number.isFinite(item)
        ).length;
        
        return value.length > 0 ? finiteCount / value.length : 1.0;
      }
      
      return true;
    }
    
    return true; // Default to valid for unknown boundaries
  }
  
  /**
   * Validate a logical boundary
   * @private
   */
  _validateLogicalBoundary(name, value, context, config) {
    if (name === 'consistency') {
      // Check logical consistency
      return context.valid !== false;
    }
    
    return true; // Default to valid for unknown boundaries
  }
  
  /**
   * Parse memory size string to bytes
   * @private
   */
  _parseMemorySize(sizeStr) {
    if (typeof sizeStr === 'number') {
      return sizeStr;
    }
    
    if (sizeStr === 'Infinity' || sizeStr === 'infinity') {
      return Infinity;
    }
    
    const units = {
      B: 1,
      KB: 1024,
      MB: 1024 * 1024,
      GB: 1024 * 1024 * 1024,
      TB: 1024 * 1024 * 1024 * 1024
    };
    
    const match = /^(\d+(?:\.\d+)?)\s*([KMGT]?B)$/i.exec(sizeStr);
    
    if (!match) {
      return 10 * 1024 * 1024; // Default to 10MB
    }
    
    const size = parseFloat(match[1]);
    const unit = match[2].toUpperCase();
    
    return size * (units[unit] || units.B);
  }

  /**
   * Initialize resource managers
   * @private
   */
  async _initResourceManagers() {
    // Import storage directly
    const Storage = require('../storage');
    
    // Import resources
    const { ResourceManager } = require('./resources');
    
    // Initialize storage resource manager
    this.resources.storage = new VeneerResourceManager('storage');
    await this.resources.storage.init();
    
    // Initialize compute resource manager
    this.resources.compute = new VeneerResourceManager('compute');
    await this.resources.compute.init();
    
    // Initialize memory resource manager
    this.resources.memory = new VeneerResourceManager('memory');
    await this.resources.memory.init();
    
    // Initialize network resource manager
    this.resources.network = new VeneerResourceManager('network');
    await this.resources.network.init();
  }
  
  /**
   * Initialize app management (registry and loader)
   * @private
   */
  async _initAppManagement() {
    // Import registry and loader
    const { PrimeAppRegistry } = require('./registry');
    const { PrimeAppLoader } = require('./loader');
    
    // Create registry
    this.registry = new PrimeAppRegistry({
      appDirectories: this.options.appDirectories
    });
    
    // Create loader
    this.loader = new PrimeAppLoader({
      validateManifest: true,
      autoRegisterDependencies: true,
      allowUnsignedApps: this.options.debug || process.env.NODE_ENV === 'development'
    });
    
    // Connect loader to veneer and registry
    this.loader.setVeneer(this);
    this.loader.setRegistry(this.registry);
    
    // Connect registry to veneer
    this.registry.setVeneer(this);
    
    // Discover apps in configured directories
    if (this.options.appDirectories.length > 0) {
      await this.registry.discoverApps();
      
      Prime.Logger.info('Discovered PrimeApps', {
        count: this.registry.apps.size
      });
    }
  }
  
  /**
   * Check system coherence
   * @returns {Promise<Object>} Coherence check results
   */
  async checkCoherence() {
    if (!this.state.initialized) {
      return {
        systemCoherence: 1.0,
        violations: []
      };
    }
    
    // Use the coherence manager to check
    const results = await this.coherenceManager.checkCoherence();
    
    // Update state
    this.state.systemCoherence = results.systemCoherence;
    
    // Emit event if coherence is below threshold
    if (this.state.systemCoherence < this.options.coherenceThreshold) {
      this.emit('coherence:violated', {
        score: this.state.systemCoherence,
        threshold: this.options.coherenceThreshold,
        violations: results.violations.length
      });
    }
    
    return results;
  }
  
  /**
   * Release all resources for an application
   * @private
   * @param {string} appId - Application ID
   */
  async _releaseAppResources(appId) {
    const app = this.applications.get(appId);
    if (!app) return;
    
    // Release each allocated resource
    for (const resourceType of Object.keys(app.resources.allocated)) {
      await this.releaseResource(appId, resourceType);
    }
  }
  
  /**
   * Shutdown the veneer system
   * @returns {Promise<void>}
   */
  async shutdown() {
    if (!this.state.initialized) {
      return;
    }
    
    Prime.Logger.info('PrimeVeneer shutting down');
    
    // Stop coherence monitoring
    if (this.coherenceManager) {
      this.coherenceManager.stopMonitoring();
    }
    
    // Unregister all applications
    for (const appId of this.applications.keys()) {
      await this.unregisterApplication(appId);
    }
    
    // Clean up loader if available
    if (this.loader) {
      await this.loader.cleanup();
    }
    
    // Clear application registry
    this.applications.clear();
    
    // Mark as not initialized
    this.state.initialized = false;
    this.emit('shutdown');
    
    Prime.Logger.info('PrimeVeneer shutdown complete');
  }
}

/**
 * Resource Manager wrapper class for the Veneer
 * Manages creating and allocating resource instances for apps
 */
class VeneerResourceManager {
  constructor(type) {
    this.type = type;
    this.allocations = new Map();
    this.resources = {};
  }
  
  /**
   * Initialize the resource manager
   * @returns {Promise<void>}
   */
  async init() {
    Prime.Logger.info(`Initializing ${this.type} resource manager`);
    return true;
  }
  
  /**
   * Allocate a resource for an app
   * @param {string} appId - Application ID
   * @param {Object} requirements - Resource requirements
   * @returns {Promise<Object>} - Resource handle
   */
  async allocate(appId, requirements) {
    // Create a new resource instance using the ResourceManager factory
    const { ResourceManager } = require('./resources');
    const resource = ResourceManager.createResource(this.type, appId, requirements);
    
    // Initialize the resource
    await resource.init();
    
    // Store allocation
    this.allocations.set(appId, {
      resource,
      requirements,
      allocatedAt: Date.now()
    });
    
    Prime.Logger.info(`Resource allocated: ${this.type} for ${appId}`, requirements);
    
    return resource;
  }
  
  /**
   * Release a resource for an app
   * @param {string} appId - Application ID
   * @returns {Promise<boolean>} - True if successfully released
   */
  async release(appId) {
    if (!this.allocations.has(appId)) {
      return false;
    }
    
    const allocation = this.allocations.get(appId);
    
    // Release the resource
    await allocation.resource.release();
    
    // Remove allocation
    this.allocations.delete(appId);
    
    Prime.Logger.info(`Resource released: ${this.type} for ${appId}`);
    
    return true;
  }
}

// Add to Prime namespace
Prime.Veneer = {
  PrimeVeneer,
  PrimeVeneerError,
  VeneerResourceManager,
  
  // Add coherence systems
  CoherenceManager,
  CoherenceBoundaryRegistry
};

module.exports = Prime.Veneer;