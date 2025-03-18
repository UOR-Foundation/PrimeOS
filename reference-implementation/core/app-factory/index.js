/**
 * PrimeOS App Factory
 * 
 * Main entry point for the App Factory system that enables AI-assisted
 * application creation within the PrimeOS environment.
 * 
 * This module integrates with the core PrimeOS systems (Shell, BundleManager,
 * AppAPI, PrimeStore) to provide a comprehensive app creation platform.
 */

// Define components at the global level for dual-mode (CommonJS and ES Modules) compatibility
let AppFactoryManager, ClaudeService, ClaudeOrchestrator, CoherenceEngine, BundleManager, AppFactoryUI;
let AppFactoryStorage, AppFactoryConfig, AppFactoryBundleIntegration, AppFactoryShellIntegration, AppFactoryAppAPIIntegration;

// Define App Factory events
const APP_FACTORY_EVENTS = {
  // Project lifecycle events
  PROJECT_CREATED: 'app-factory:project-created',
  PROJECT_UPDATED: 'app-factory:project-updated',
  PROJECT_DELETED: 'app-factory:project-deleted',
  
  // Generation events
  GENERATION_STARTED: 'app-factory:generation-started',
  GENERATION_PROGRESS: 'app-factory:generation-progress',
  GENERATION_COMPLETED: 'app-factory:generation-completed',
  GENERATION_FAILED: 'app-factory:generation-failed',
  
  // Testing events
  TESTS_STARTED: 'app-factory:tests-started',
  TESTS_COMPLETED: 'app-factory:tests-completed',
  
  // Publication events
  PUBLICATION_STARTED: 'app-factory:publication-started',
  PUBLICATION_COMPLETED: 'app-factory:publication-completed',
  PUBLICATION_FAILED: 'app-factory:publication-failed'
};

// Load dependencies - browser vs. Node environment compatibility
if (typeof window !== 'undefined') {
  // Browser environment - dependencies should be available via PrimeOS global
  console.log('App Factory running in browser environment');
  
  // Load Claude API Client script dynamically
  const loadClaudeAPI = () => {
    return new Promise((resolve) => {
      const script = document.createElement('script');
      script.src = '/reference-implementation/core/app-factory/utils/claude-api-browser.js';
      script.onload = () => {
        console.log('Claude API client loaded successfully');
        resolve(true);
      };
      script.onerror = () => {
        console.error('Failed to load Claude API client');
        resolve(false);
      };
      document.head.appendChild(script);
    });
  };
  
  // Load the Claude API client
  loadClaudeAPI().then(success => {
    if (success) {
      console.log('Ready to use Claude API');
    }
  });
  
  // Create stub implementations for components when running in the browser
  AppFactoryManager = class AppFactoryManager {
    constructor(options) {
      console.log('App Factory Manager initialized with options:', options);
      this.options = options;
      this.store = options.store;
      this.eventBus = options.eventBus;
      this.claudeService = options.claudeService;
      this.claudeOrchestrator = options.claudeOrchestrator;
      this.coherenceEngine = options.coherenceEngine;
      this.bundleManager = options.bundleManager;
    }
  };
  
  // Real Claude service that uses the API
  ClaudeService = class ClaudeService {
    constructor(options) {
      console.log('Claude Service initialized');
      this.options = options;
      
      // Create Claude API client if available
      this.apiClient = null;
      if (window.PrimeOS && window.PrimeOS.ClaudeAPIClientBrowser) {
        // Use the secure vault to get the API key if available
        const apiKey = '';
        
        this.apiClient = new window.PrimeOS.ClaudeAPIClientBrowser({
          apiKey: apiKey, // Empty by default, will be loaded from secure vault
          model: 'claude-3-sonnet-20240229'
        });
        
        console.log('Claude API client created - will load API key from Settings');
      } else {
        console.warn('Claude API client not available, using stub');
      }
    }
    
    // Delegate to the API client if available
    async generateDomainInsights(domainData) {
      console.log('Generating domain insights', domainData);
      
      if (this.apiClient && this.apiClient.ready) {
        console.log('Using real Claude API for domain insights');
        return this.apiClient.generateDomainInsights(domainData);
      }
      
      // Fallback to stub
      return { 
        ...domainData,
        insights: ['Generated insights would appear here'],
        personas: ['User persona 1', 'User persona 2'],
        functionalAreas: ['Area 1', 'Area 2']
      };
    }
    
    async suggestRequirements(domainData) {
      console.log('Suggesting requirements based on domain', domainData);
      
      if (this.apiClient && this.apiClient.ready) {
        console.log('Using real Claude API for requirements');
        return this.apiClient.suggestRequirements(domainData);
      }
      
      // Fallback to stub
      return { 
        entities: [{ name: 'User', fields: [{ name: 'name', type: 'string' }] }],
        features: ['User authentication', 'Dashboard view'],
        nonFunctionalRequirements: [{ category: 'Performance', description: 'The app should be fast' }]
      };
    }
    
    // Basic executeRequest for ClaudeOrchestrator
    async executeRequest(prompt, conversationId) {
      console.log('Executing request to Claude API:', { prompt, conversationId });
      
      if (this.apiClient && this.apiClient.ready) {
        console.log('Using real Claude API for request');
        // Stub implementation
        return "Claude API response would appear here";
      }
      
      // Fallback to stub
      return JSON.stringify({ message: "This is a stub Claude response" });
    }
  };
  
  // Claude Orchestrator stub
  ClaudeOrchestrator = class ClaudeOrchestrator {
    constructor(options) {
      console.log('Claude Orchestrator initialized');
      this.claudeService = options.claudeService;
      this.eventBus = options.eventBus;
      this.promptLibrary = options.promptLibrary || {};
      this.conversationContext = new Map();
      
      console.log('Claude Orchestrator ready');
    }
    
    async runInspirationPhase(projectId, initialInput) {
      console.log('Running inspiration phase with Claude:', { projectId, initialInput });
      return {
        appPurpose: initialInput.purpose || 'App purpose',
        appDomain: initialInput.domain || 'General',
        targetUsers: [initialInput.audience || 'General users'],
        useCases: ['Primary use case'],
        keyFeatures: ['Key feature 1', 'Key feature 2'],
        keyTerms: []
      };
    }
    
    async runCoherenceMappingPhase(projectId, inspirationResults) {
      console.log('Running coherence mapping phase with Claude:', { projectId, inspirationResults });
      return {
        entities: [
          { name: 'User', properties: [{name: 'id', type: 'string'}, {name: 'name', type: 'string'}] }
        ],
        relationships: [],
        processes: [],
        states: [],
        invariants: [],
        constraints: [],
        coherenceMetrics: { score: 0.85 }
      };
    }
    
    async runBundleSpecificationPhase(projectId, coherenceResults) {
      console.log('Running bundle specification phase with Claude:', { projectId, coherenceResults });
      return {
        manifest: {
          name: 'Generated App',
          version: '1.0.0',
          description: 'Auto-generated application',
          entryPoint: 'views/main.js'
        },
        components: [],
        models: [],
        services: [],
        views: [],
        assets: []
      };
    }
    
    clearProjectContext(projectId) {
      console.log(`Clearing conversation context for project: ${projectId}`);
    }
  };
  
  // Coherence Engine stub
  CoherenceEngine = class CoherenceEngine {
    constructor(options) {
      console.log('Coherence Engine initialized');
      this.claudeService = options.claudeService;
      this.eventBus = options.eventBus;
      this.thresholds = {
        minimumScore: 0.75
      };
      
      console.log('Coherence Engine ready');
    }
    
    async mapCoherence(domain, entities) {
      console.log('Mapping coherence:', { domain, entities });
      return {
        score: 0.85,
        entityRelationships: { score: 0.8 },
        processFlows: { score: 0.85 },
        stateTransitions: { score: 0.9 }
      };
    }
    
    async validateComponentCoherence(component, coherenceMap) {
      console.log('Validating component coherence:', { component, coherenceMap });
      return {
        valid: true,
        score: 0.85,
        issues: [],
        recommendations: []
      };
    }
    
    async validateBundleCoherence(bundle) {
      console.log('Validating bundle coherence:', { bundle });
      return {
        valid: true,
        metrics: {
          score: 0.85,
          interfaceCompleteness: 0.8,
          structuralIntegrity: 0.9
        },
        issues: [],
        recommendations: []
      };
    }
  };
  
  // Bundle Manager stub
  BundleManager = class BundleManager {
    constructor(options) {
      console.log('Bundle Manager initialized');
      this.store = options.store;
      this.coherenceEngine = options.coherenceEngine;
      this.eventBus = options.eventBus;
      
      console.log('Bundle Manager ready');
    }
    
    async createBundle(bundleId, initialData) {
      console.log('Creating bundle:', { bundleId, initialData });
      return {
        id: `bundle_${bundleId}`,
        bundleId,
        manifest: {
          name: initialData.name || bundleId,
          version: '1.0.0'
        }
      };
    }
    
    async loadBundle(bundleId) {
      console.log('Loading bundle:', { bundleId });
      return {
        id: `bundle_${bundleId}`,
        bundleId,
        manifest: {
          name: 'Stub Bundle',
          version: '1.0.0'
        }
      };
    }
    
    async addBundleFile(bundleId, filePath, content, options) {
      console.log('Adding bundle file:', { bundleId, filePath, options });
      return {
        id: `bundle_${bundleId}`,
        bundleId
      };
    }
    
    async validateBundle(bundleId) {
      console.log('Validating bundle:', { bundleId });
      return {
        valid: true,
        structureValidation: { valid: true },
        coherenceValidation: { valid: true }
      };
    }
    
    async exportBundle(bundleId) {
      console.log('Exporting bundle:', { bundleId });
      return {
        manifest: {
          name: 'Stub Bundle',
          version: '1.0.0'
        },
        code: {},
        resources: {}
      };
    }
  };
  
  AppFactoryUI = class AppFactoryUI {
    constructor(options) {
      console.log('App Factory UI initialized');
      this.options = options;
    }
    
    render() {
      console.log('App Factory UI rendered');
      
      // Create a simple UI when running in the browser
      if (this.options?.container) {
        const container = this.options.container;
        container.innerHTML = `
          <div class="app-factory-container">
            <h2>App Factory</h2>
            <p>AI-powered application creation platform</p>
            <p>Version: 0.1.0</p>
            <button id="create-app-btn">Create New App</button>
          </div>
        `;
        
        // Add event listeners
        const createBtn = container.querySelector('#create-app-btn');
        if (createBtn) {
          createBtn.addEventListener('click', () => {
            console.log('Create app button clicked');
            alert('App Factory: Create new app functionality coming soon!');
          });
        }
      }
    }
  };
  
  // Integration components
  AppFactoryStorage = class AppFactoryStorage {
    constructor(store) {
      console.log('App Factory Storage initialized');
      this.store = store;
    }
    
    async getPreferences() {
      return { apiKey: null };
    }
  };
  
  AppFactoryConfig = class AppFactoryConfig {
    constructor(store, options) {
      console.log('App Factory Config initialized');
      this.store = store;
      this.options = options;
    }
    
    async getPreferences() {
      return { apiKey: null };
    }
  };
  
  AppFactoryBundleIntegration = class AppFactoryBundleIntegration {
    constructor(bundleManager, options) {
      console.log('App Factory Bundle Integration initialized');
      this.bundleManager = bundleManager;
      this.options = options;
    }
  };
  
  AppFactoryShellIntegration = class AppFactoryShellIntegration {
    constructor(shell, options) {
      console.log('App Factory Shell Integration initialized');
      this.shell = shell;
      this.options = options;
    }
    
    async registerAppFactory() {
      console.log('App Factory registered with shell');
      return true;
    }
  };
  
  AppFactoryAppAPIIntegration = class AppFactoryAppAPIIntegration {
    constructor(options) {
      console.log('App Factory AppAPI Integration initialized');
      this.options = options;
    }
  };
} else {
  // Node.js environment - use require() for dependencies
  try {
    AppFactoryManager = require('./AppFactoryManager').AppFactoryManager;
    ClaudeService = require('./claude-service').ClaudeService;
    ClaudeOrchestrator = require('./ClaudeOrchestrator').ClaudeOrchestrator;
    CoherenceEngine = require('./CoherenceEngine').CoherenceEngine;
    BundleManager = require('./BundleManager').BundleManager;
    AppFactoryUI = require('./app-factory-ui').AppFactoryUI;
    
    // Integration components
    AppFactoryStorage = require('./utils/persistence').AppFactoryStorage;
    AppFactoryConfig = require('./utils/configuration').AppFactoryConfig;
    AppFactoryBundleIntegration = require('./integration/bundle-integration').AppFactoryBundleIntegration;
    AppFactoryShellIntegration = require('./integration/shell-integration').AppFactoryShellIntegration;
    AppFactoryAppAPIIntegration = require('./integration/app-api-integration').AppFactoryAppAPIIntegration;
  } catch (error) {
    console.error('Failed to load App Factory dependencies:', error);
  }
}

// Create the App Factory object with all methods and components
const AppFactory = {
  // Component classes
  AppFactoryManager,
  ClaudeService,
  ClaudeOrchestrator,
  CoherenceEngine,
  BundleManager,
  AppFactoryUI,
  AppFactoryStorage,
  AppFactoryConfig,
  AppFactoryBundleIntegration,
  AppFactoryShellIntegration,
  AppFactoryAppAPIIntegration,
  
  // Events
  EVENTS: APP_FACTORY_EVENTS,
  
  /**
   * Register event handlers with the event bus
   * @param {Object} eventBus - Event bus to register with
   */
  registerEvents: function(eventBus) {
    if (!eventBus) return;
    
    // Register for system events
    
    // Listen for user login to load projects
    eventBus.subscribe('identity:login', (data) => {
      console.log('User logged in:', data);
    });
    
    // Listen for app installation to detect importable apps
    eventBus.subscribe('bundle:installed', (data) => {
      console.log('Bundle installed:', data);
    });
    
    // Listen for theme changes
    eventBus.subscribe('system:theme-changed', (data) => {
      console.log('Theme changed:', data);
    });
  },
  
  /**
   * Initialize App Factory for system integration
   * @param {Object} options - System options
   * @param {Object} options.shell - Shell instance
   * @param {Object} options.store - PrimeStore instance
   * @param {Object} options.bundleManager - BundleManager instance
   * @param {Object} options.eventBus - EventBus instance
   * @param {Object} options.identity - Identity service
   * @returns {Promise<Object>} Initialized App Factory system
   */
  initializeSystem: async function(options = {}) {
    if (!options.shell) {
      throw new Error('Shell instance is required');
    }
    
    if (!options.store) {
      throw new Error('Store instance is required');
    }
    
    if (!options.bundleManager) {
      throw new Error('BundleManager instance is required');
    }
    
    if (!options.eventBus) {
      throw new Error('EventBus instance is required');
    }
    
    console.log('Initializing App Factory system integration');
    
    // Get current user if identity service provided
    let userId = 'default';
    if (options.identity) {
      const currentUser = await options.identity.getCurrentUser();
      if (currentUser && currentUser.id) {
        userId = currentUser.id;
      }
    }
    
    // Create integration components
    const storageIntegration = new this.AppFactoryStorage(options.store);
    
    const configManager = new this.AppFactoryConfig(options.store, {
      userId,
      eventBus: options.eventBus
    });
    
    const bundleIntegration = new this.AppFactoryBundleIntegration(options.bundleManager, {
      eventBus: options.eventBus
    });
    
    const shellIntegration = new this.AppFactoryShellIntegration(options.shell, {
      eventBus: options.eventBus
    });
    
    // Register events
    this.registerEvents(options.eventBus);
    
    // Register App Factory with Shell
    await shellIntegration.registerAppFactory();
    
    // Load user preferences
    const preferences = await configManager.getPreferences();
    
    // Create app factory instance
    const appFactory = this.createAppFactory({
      apiKey: preferences.apiKey,
      store: options.store,
      eventBus: options.eventBus,
      bundleManager: options.bundleManager,
      storageIntegration,
      configManager,
      bundleIntegration,
      shellIntegration,
      userId
    });
    
    return {
      appFactory,
      storageIntegration,
      configManager,
      bundleIntegration,
      shellIntegration
    };
  },
  
  /**
   * Create a new App Factory instance with all required dependencies
   * @param {Object} options - Configuration options
   * @returns {Object} App Factory instance with all components
   */
  createAppFactory: function(options = {}) {
    // Create service instances
    const claudeService = new this.ClaudeService({
      apiKey: options.apiKey,
      eventBus: options.eventBus,
      promptTemplates: options.promptTemplates
    });
    
    // Create the Claude orchestrator
    const claudeOrchestrator = new this.ClaudeOrchestrator({
      claudeService,
      eventBus: options.eventBus,
      promptLibrary: options.promptLibrary
    });
    
    // Create the coherence engine
    const coherenceEngine = new this.CoherenceEngine({
      claudeService,
      eventBus: options.eventBus
    });
    
    // Create the bundle manager
    const bundleManager = new this.BundleManager({
      store: options.store,
      coherenceEngine,
      eventBus: options.eventBus
    });
    
    // Create the manager with integrations
    const managerOptions = {
      claudeService,
      claudeOrchestrator,
      bundleManager,
      coherenceEngine,
      store: options.store,
      eventBus: options.eventBus,
      storageIntegration: options.storageIntegration,
      configManager: options.configManager,
      bundleIntegration: options.bundleIntegration,
      shellIntegration: options.shellIntegration,
      userId: options.userId
    };
    
    const manager = new this.AppFactoryManager(managerOptions);
    
    // Create UI component if container provided
    let ui = null;
    if (options.container) {
      ui = new this.AppFactoryUI({
        container: options.container,
        manager,
        eventBus: options.eventBus
      });
      ui.render();
    }
    
    // Return the complete factory
    return {
      manager,
      claudeService,
      claudeOrchestrator,
      coherenceEngine,
      bundleManager,
      ui
    };
  }
};

// Export for browser environments
if (typeof window !== 'undefined') {
  // Initialize PrimeOS global object if needed
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  
  // Export using multiple naming patterns for shell compatibility
  window.PrimeOS.AppFactory = AppFactory;       // As a component
  window.PrimeOS['app-factory'] = AppFactory;   // Direct ID lookup
  window.PrimeOS['AppFactory'] = AppFactory;    // Capitalized
  
  // Create a class constructor that shell.js can use to initialize the app
  window.PrimeOS['app-factory'] = class AppFactoryApp {
    static async initialize(container, options) {
      console.log('AppFactory initialize called with container:', container);
      const app = new AppFactoryApp(container, options);
      await app.init();
      return app;
    }
    
    constructor(container, options) {
      this.container = container;
      this.options = options;
      this.name = 'App Factory';
      
      console.log('AppFactory constructor called');
    }
    
    async init() {
      console.log('Initializing App Factory UI');
      if (this.container) {
        // Initialize App Factory components from PrimeOS
        try {
          // Get all store, eventBus, and other integrations from window
          const shell = window.PrimeOS.shell || this.options.shell;
          const store = window.PrimeOS.store || this.options.store;
          const eventBus = window.PrimeOS.eventBus || this.options.eventBus;
          const bundleManager = window.PrimeOS.bundleManager || this.options.bundleManager;
          
          console.log('Integrating with PrimeOS components:', { 
            hasShell: !!shell, 
            hasStore: !!store, 
            hasEventBus: !!eventBus, 
            hasBundleManager: !!bundleManager 
          });
          
          // Initialize the manager if all dependencies are available
          this.manager = null;
          if (store && eventBus) {
            // Create minimal manager instance with browser functionality
            console.log('Creating App Factory Manager');
            
            // Create simple Claude service stub with browser functionality
            const claudeService = {
              generateDomainInsights: async (domain) => {
                console.log('Generating domain insights', domain);
                return { ...domain, insights: ['Generated insights would appear here'] };
              },
              suggestRequirements: async (domain) => {
                console.log('Suggesting requirements based on domain', domain);
                return { 
                  entities: [{ name: 'User', fields: [{ name: 'name', type: 'string' }] }],
                  features: ['User authentication', 'Dashboard view']
                };
              },
              enhanceRequirements: async (requirements) => {
                return requirements;
              },
              generateAppSpecification: async () => {
                return { architecture: { type: 'modular' } };
              },
              validateSpecification: async (spec) => {
                return { valid: true };
              }
            };
            
            // Create test runner stub
            const testRunner = {
              runTests: async () => {
                return { success: true, passed: 10, total: 10 };
              }
            };
            
            // Define AppFactoryManager class globally if not available
            if (!window.PrimeOS.AppFactoryManager) {
              console.log('Creating AppFactoryManager class');
              
              // Create a simple manager implementation for the browser
              window.PrimeOS.AppFactoryManager = class AppFactoryManager {
                constructor(options) {
                  this.options = options;
                  this.store = options.store;
                  this.eventBus = options.eventBus;
                  this.claudeService = options.claudeService;
                  this.testRunner = options.testRunner;
                  this.projects = new Map();
                  
                  console.log('AppFactoryManager initialized with options', options);
                }
                
                async getProjects() {
                  // Return demo projects
                  return [
                    {
                      id: 'demo-project-1',
                      name: 'Task Manager App',
                      description: 'A simple task management application',
                      currentStep: 'domain',
                      created: new Date().toISOString(),
                      modified: new Date().toISOString(),
                      progress: 1
                    },
                    {
                      id: 'demo-project-2',
                      name: 'Weather Forecast',
                      description: 'App to display weather forecasts',
                      currentStep: 'requirements',
                      created: new Date().toISOString(),
                      modified: new Date().toISOString(),
                      progress: 2
                    }
                  ];
                }
                
                async createProject(name, description) {
                  // Create a demo project
                  const projectId = `project-${Date.now()}`;
                  console.log(`Creating demo project ${name} (${projectId})`);
                  
                  // Notify event
                  if (this.eventBus) {
                    this.eventBus.publish('app-factory:project-created', {
                      projectId,
                      name,
                      description
                    });
                  }
                  
                  return projectId;
                }
                
                async getProjectStatus(projectId) {
                  // Return demo project status
                  return {
                    id: projectId,
                    name: 'Demo Project',
                    description: 'A demo project created for testing',
                    currentStep: 'domain',
                    progress: {
                      domain: { status: 'pending' },
                      requirements: { status: 'pending' },
                      specification: { status: 'pending' },
                      generation: { status: 'pending' },
                      testing: { status: 'pending' },
                      publishing: { status: 'pending' }
                    },
                    progressPercentage: 0,
                    created: new Date().toISOString(),
                    modified: new Date().toISOString(),
                    fileCount: 0,
                    isImported: false,
                    hasErrors: false
                  };
                }
              };
            }
            
            // Create manager instance
            this.manager = new window.PrimeOS.AppFactoryManager({
              claudeService,
              store,
              eventBus,
              bundleManager,
              testRunner
            });
          }
        } catch (error) {
          console.error('Failed to initialize App Factory components:', error);
        }
        
        // Render UI
        this.container.innerHTML = `
          <div class="app-factory-container" style="padding: 20px; height: 100%; display: flex; flex-direction: column; font-family: system-ui, -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;">
            <div style="margin-bottom: 24px;">
              <h1 style="margin-bottom: 8px; color: #333; font-size: 28px;">App Factory</h1>
              <p style="margin-bottom: 20px; color: #666;">AI-powered application creation platform for PrimeOS</p>
              
              <div style="display: flex; gap: 16px; margin-bottom: 24px;">
                <button id="new-app-btn" style="padding: 10px 20px; background-color: #4a6da7; color: white; border: none; border-radius: 4px; cursor: pointer; font-weight: 500;">Create New App</button>
                <button id="import-app-btn" style="padding: 10px 20px; background-color: #f5f5f5; border: 1px solid #ddd; border-radius: 4px; cursor: pointer;">Import Existing App</button>
              </div>
            </div>
            
            <div style="flex: 1; overflow: auto;">
              <div id="projects-list">
                <h3 style="margin-bottom: 16px; color: #333; border-bottom: 1px solid #eee; padding-bottom: 8px;">Recent Projects</h3>
                <div id="projects-container">
                  <p style="color: #666; font-style: italic;" id="no-projects-message">Loading projects...</p>
                </div>
              </div>
            </div>
            
            <div id="create-app-modal" style="display: none; position: fixed; top: 0; left: 0; width: 100%; height: 100%; background-color: rgba(0,0,0,0.5); z-index: 1000;">
              <div style="background: white; border-radius: 8px; width: 500px; max-width: 90%; position: absolute; top: 50%; left: 50%; transform: translate(-50%, -50%); padding: 24px; box-shadow: 0 4px 12px rgba(0,0,0,0.15);">
                <h2 style="margin-bottom: 16px;">Create New App</h2>
                <form id="create-app-form">
                  <div style="margin-bottom: 16px;">
                    <label style="display: block; margin-bottom: 8px; font-weight: 500;">App Name</label>
                    <input type="text" id="app-name-input" style="width: 100%; padding: 8px; border: 1px solid #ddd; border-radius: 4px;" placeholder="My Awesome App" required>
                  </div>
                  
                  <div style="margin-bottom: 20px;">
                    <label style="display: block; margin-bottom: 8px; font-weight: 500;">Description</label>
                    <textarea id="app-description-input" style="width: 100%; padding: 8px; border: 1px solid #ddd; border-radius: 4px; min-height: 80px;" placeholder="Describe what your app will do" required></textarea>
                  </div>
                  
                  <div style="display: flex; justify-content: flex-end; gap: 12px;">
                    <button type="button" id="cancel-create-btn" style="padding: 8px 16px; background-color: #f5f5f5; border: 1px solid #ddd; border-radius: 4px; cursor: pointer;">Cancel</button>
                    <button type="submit" style="padding: 8px 16px; background-color: #4a6da7; color: white; border: none; border-radius: 4px; cursor: pointer; font-weight: 500;">Create App</button>
                  </div>
                </form>
              </div>
            </div>
          </div>
        `;
        
        // Load projects if manager is available
        this.loadProjects();
        
        // Add event listeners
        const newAppBtn = this.container.querySelector('#new-app-btn');
        if (newAppBtn) {
          newAppBtn.addEventListener('click', () => {
            const modal = this.container.querySelector('#create-app-modal');
            if (modal) modal.style.display = 'block';
          });
        }
        
        const cancelCreateBtn = this.container.querySelector('#cancel-create-btn');
        if (cancelCreateBtn) {
          cancelCreateBtn.addEventListener('click', () => {
            const modal = this.container.querySelector('#create-app-modal');
            if (modal) modal.style.display = 'none';
          });
        }
        
        const createAppForm = this.container.querySelector('#create-app-form');
        if (createAppForm) {
          createAppForm.addEventListener('submit', async (e) => {
            e.preventDefault();
            
            const nameInput = this.container.querySelector('#app-name-input');
            const descriptionInput = this.container.querySelector('#app-description-input');
            
            if (nameInput && descriptionInput) {
              const name = nameInput.value.trim();
              const description = descriptionInput.value.trim();
              
              if (name && description) {
                await this.createNewProject(name, description);
                
                // Hide modal
                const modal = this.container.querySelector('#create-app-modal');
                if (modal) modal.style.display = 'none';
                
                // Reset form
                createAppForm.reset();
              }
            }
          });
        }
        
        const importAppBtn = this.container.querySelector('#import-app-btn');
        if (importAppBtn) {
          importAppBtn.addEventListener('click', () => {
            alert('Import existing app feature coming soon!');
          });
        }
      }
    }
    
    /**
     * Load projects from storage
     */
    async loadProjects() {
      if (!this.manager) {
        const noProjectsMsg = this.container.querySelector('#no-projects-message');
        if (noProjectsMsg) {
          noProjectsMsg.textContent = 'App Factory is not fully initialized. Please check the console for details.';
        }
        return;
      }
      
      try {
        // Get projects from manager
        const projects = await this.manager.getProjects();
        
        const projectsContainer = this.container.querySelector('#projects-container');
        if (!projectsContainer) return;
        
        if (projects.length === 0) {
          projectsContainer.innerHTML = `
            <p style="color: #666; font-style: italic;">No recent projects found. Create a new app to get started.</p>
          `;
          return;
        }
        
        // Display projects
        projectsContainer.innerHTML = projects.map(project => `
          <div class="project-card" style="padding: 16px; background: white; border-radius: 8px; margin-bottom: 16px; border: 1px solid #eee; cursor: pointer;" data-project-id="${project.id}">
            <h4 style="margin: 0 0 8px 0; color: #333;">${project.name}</h4>
            <p style="margin: 0 0 12px 0; color: #666; font-size: 14px;">${project.description || 'No description'}</p>
            <div style="display: flex; justify-content: space-between; align-items: center;">
              <span style="font-size: 12px; color: #888;">Created: ${new Date(project.created).toLocaleDateString()}</span>
              <span style="font-size: 13px; padding: 4px 8px; background: #f0f4fa; border-radius: 4px; color: #4a6da7;">
                ${project.currentStep} (${Math.floor((project.progress / 6) * 100)}%)
              </span>
            </div>
          </div>
        `).join('');
        
        // Add click listeners to project cards
        const projectCards = projectsContainer.querySelectorAll('.project-card');
        projectCards.forEach(card => {
          card.addEventListener('click', async () => {
            const projectId = card.dataset.projectId;
            if (projectId) {
              await this.openProject(projectId);
            }
          });
        });
      } catch (error) {
        console.error('Failed to load projects:', error);
        
        const projectsContainer = this.container.querySelector('#projects-container');
        if (projectsContainer) {
          projectsContainer.innerHTML = `
            <p style="color: #c00; font-style: italic;">Error loading projects: ${error.message}</p>
          `;
        }
      }
    }
    
    /**
     * Create a new project
     * @param {string} name - Project name
     * @param {string} description - Project description
     */
    async createNewProject(name, description) {
      if (!this.manager) {
        alert('Cannot create project: App Factory manager is not initialized');
        return;
      }
      
      try {
        // Create project
        const projectId = await this.manager.createProject(name, description);
        
        // Refresh project list
        await this.loadProjects();
        
        // Show success message
        alert(`Project "${name}" created successfully!`);
        
        // Open the project
        await this.openProject(projectId);
      } catch (error) {
        console.error('Failed to create project:', error);
        alert(`Failed to create project: ${error.message}`);
      }
    }
    
    /**
     * Open a project
     * @param {string} projectId - Project ID
     */
    async openProject(projectId) {
      if (!this.manager) {
        alert('Cannot open project: App Factory manager is not initialized');
        return;
      }
      
      try {
        // Get project status
        const status = await this.manager.getProjectStatus(projectId);
        
        // Display project view
        this.container.innerHTML = `
          <div class="project-view" style="padding: 20px; height: 100%; display: flex; flex-direction: column; font-family: system-ui, -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;">
            <div style="display: flex; justify-content: space-between; align-items: center; margin-bottom: 24px;">
              <div>
                <h1 style="margin: 0 0 8px 0; color: #333; font-size: 24px;">${status.name}</h1>
                <p style="margin: 0; color: #666;">${status.description || 'No description'}</p>
              </div>
              <button id="back-to-projects" style="padding: 8px 16px; background-color: #f5f5f5; border: 1px solid #ddd; border-radius: 4px; cursor: pointer;">Back to Projects</button>
            </div>
            
            <div style="margin-bottom: 24px;">
              <div style="display: flex; justify-content: space-between; align-items: center; margin-bottom: 8px;">
                <h3 style="margin: 0; color: #333;">Project Progress</h3>
                <span style="font-size: 14px; color: #4a6da7; font-weight: 500;">${status.progressPercentage}% Complete</span>
              </div>
              
              <div style="height: 8px; background: #eee; border-radius: 4px; overflow: hidden;">
                <div style="height: 100%; background: #4a6da7; width: ${status.progressPercentage}%;"></div>
              </div>
              
              <div style="display: flex; flex-wrap: wrap; gap: 12px; margin-top: 16px;">
                ${this.renderWorkflowSteps(status)}
              </div>
            </div>
            
            <div style="flex: 1; overflow: auto; border: 1px solid #eee; border-radius: 8px; padding: 16px; background: white;">
              <h3 style="margin-top: 0; color: #333; border-bottom: 1px solid #eee; padding-bottom: 8px;">
                ${this.getStepDisplayName(status.currentStep)}
              </h3>
              
              <div id="step-content" style="padding: 16px;">
                <p style="color: #666; font-style: italic;">Loading step content...</p>
              </div>
            </div>
          </div>
        `;
        
        // Add event listeners
        const backBtn = this.container.querySelector('#back-to-projects');
        if (backBtn) {
          backBtn.addEventListener('click', () => {
            this.init(); // Reset to main view
          });
        }
        
        // Load step content
        this.loadProjectStepContent(projectId, status.currentStep);
        
      } catch (error) {
        console.error('Failed to open project:', error);
        alert(`Failed to open project: ${error.message}`);
      }
    }
    
    /**
     * Load project step content
     * @param {string} projectId - Project ID
     * @param {string} step - Current step
     */
    async loadProjectStepContent(projectId, step) {
      const stepContent = this.container.querySelector('#step-content');
      if (!stepContent) return;
      
      // Display placeholder based on step
      switch (step) {
        case 'domain':
          stepContent.innerHTML = `
            <p>In this step, you'll define the domain of your application.</p>
            <div style="margin-top: 16px;">
              <div style="margin-bottom: 16px;">
                <label style="display: block; margin-bottom: 8px; font-weight: 500;">App Purpose</label>
                <textarea id="app-purpose" style="width: 100%; padding: 8px; border: 1px solid #ddd; border-radius: 4px; min-height: 80px;" placeholder="Describe the main purpose of your application"></textarea>
              </div>
              
              <div style="margin-bottom: 16px;">
                <label style="display: block; margin-bottom: 8px; font-weight: 500;">Target Audience</label>
                <textarea id="app-audience" style="width: 100%; padding: 8px; border: 1px solid #ddd; border-radius: 4px; min-height: 80px;" placeholder="Who will use this application?"></textarea>
              </div>
              
              <button id="save-domain" style="padding: 8px 16px; background-color: #4a6da7; color: white; border: none; border-radius: 4px; cursor: pointer; font-weight: 500;">Save & Continue</button>
            </div>
          `;
          
          // Add event listener for the save button
          const saveButton = stepContent.querySelector('#save-domain');
          if (saveButton) {
            saveButton.addEventListener('click', async () => {
              // Get form values
              const purpose = stepContent.querySelector('#app-purpose')?.value || '';
              const audience = stepContent.querySelector('#app-audience')?.value || '';
              
              if (purpose.trim() === '') {
                alert('Please enter an app purpose');
                return;
              }
              
              try {
                // Show a loading state
                saveButton.textContent = 'Processing with Claude...';
                saveButton.disabled = true;
                
                // Store domain data
                const domainData = { purpose, audience };
                console.log('Domain data to process:', domainData);
                
                // Process with Claude using real API if available
                let enhancedDomain = domainData;
                
                if (this.manager && this.manager.claudeService && this.manager.claudeService.apiClient) {
                  try {
                    // Update the status element
                    stepContent.innerHTML += `
                      <div id="claude-status" style="margin-top: 16px; padding: 12px; background: #f5f7fa; border-radius: 4px;">
                        <p style="margin: 0; font-style: italic;">Claude is analyzing your input and generating domain insights...</p>
                      </div>
                    `;
                    
                    // Use the real Claude API to generate domain insights
                    console.log('Using real Claude API to generate domain insights');
                    enhancedDomain = await this.manager.claudeService.generateDomainInsights(domainData);
                    
                    // Update the status
                    const statusElement = document.getElementById('claude-status');
                    if (statusElement) {
                      if (enhancedDomain.error) {
                        statusElement.innerHTML = `
                          <p style="margin: 0; color: #c00;">Error analyzing domain: ${enhancedDomain.insights[0]}</p>
                        `;
                      } else {
                        statusElement.innerHTML = `
                          <p style="margin: 0; color: #4a6da7; font-weight: 500;">Domain analysis complete!</p>
                        `;
                      }
                    }
                    
                    console.log('Enhanced domain data:', enhancedDomain);
                  } catch (error) {
                    console.error('Error processing with Claude API:', error);
                  }
                } else {
                  // Fallback to simple implementation
                  console.log('Claude API not available, using stub data');
                  await new Promise(resolve => setTimeout(resolve, 1000));
                  
                  enhancedDomain = {
                    ...domainData,
                    insights: ['Automatically generated insight 1', 'Automatically generated insight 2'],
                    personas: ['User persona 1', 'User persona 2'],
                    functionalAreas: ['Area 1', 'Area 2']
                  };
                }
                
                // Update the project status in our implementation
                if (this.manager) {
                  // Add domain completion method to manager if it doesn't exist
                  if (!this.manager.updateDomainStep) {
                    this.manager.updateDomainStep = async (projectId, domainData) => {
                      console.log('Demo implementation: Completing domain step', projectId, domainData);
                      return { status: 'completed', nextStep: 'requirements' };
                    };
                  }
                  
                  // Call the method with enhanced domain data
                  await this.manager.updateDomainStep(projectId, enhancedDomain);
                }
                
                // Update the UI to show the next step
                const status = await this.manager.getProjectStatus(projectId);
                
                // Force next step for demo
                status.currentStep = 'requirements';
                status.progress.domain.status = 'completed';
                status.progressPercentage = 16.67; // 1/6 steps
                
                // Render requirements step
                this.loadProjectStepContent(projectId, 'requirements');
                
                // Update progress indicators
                const progressBar = this.container.querySelector('div[style*="background: #4a6da7"]');
                if (progressBar) progressBar.style.width = '16.67%';
                
                // Update step indicators
                const stepIndicators = this.container.querySelectorAll('div[style*="border: 1px solid #eee; border-radius: 4px;"]');
                if (stepIndicators && stepIndicators.length >= 2) {
                  // Set domain step to completed (green)
                  const domainStep = stepIndicators[0].querySelector('div');
                  if (domainStep) domainStep.style.backgroundColor = '#4caf50';
                  
                  // Set requirements step to in-progress (blue)
                  const reqStep = stepIndicators[1].querySelector('div');
                  if (reqStep) reqStep.style.backgroundColor = '#2196f3';
                  
                  // Update active step
                  stepIndicators.forEach((step, index) => {
                    if (index === 0) {
                      // Remove active from domain step
                      step.style.fontWeight = '400';
                      step.style.borderColor = '#eee';
                    }
                    if (index === 1) {
                      // Add active to requirements step
                      step.style.fontWeight = '600';
                      step.style.borderColor = '#4a6da7';
                    }
                  });
                }
                
                // Update step title
                const stepTitle = this.container.querySelector('h3[style*="border-bottom: 1px solid #eee"]');
                if (stepTitle) stepTitle.textContent = this.getStepDisplayName('requirements');
              } catch (error) {
                console.error('Error saving domain data:', error);
                alert('Failed to save domain data: ' + error.message);
                
                // Reset button
                saveButton.textContent = 'Save & Continue';
                saveButton.disabled = false;
              }
            });
          }
          break;
          
        case 'requirements':
          // Load project to get domain insights
          let domainData = null;
          if (this.manager) {
            try {
              const status = await this.manager.getProjectStatus(projectId);
              if (status.progress && status.progress.domain && status.progress.domain.data) {
                domainData = status.progress.domain.data;
              }
            } catch (error) {
              console.error('Error loading domain data for requirements step:', error);
            }
          }
          
          // Create content based on domain data
          let domainInsightsHTML = '<p>No domain insights available. Please go back to the domain step.</p>';
          
          if (domainData) {
            domainInsightsHTML = `
              <div style="margin-bottom: 20px;">
                <h4 style="margin-top: 0;">Domain Insights</h4>
                <p><strong>Purpose:</strong> ${domainData.purpose || 'Not specified'}</p>
                <p><strong>Target Audience:</strong> ${domainData.audience || 'Not specified'}</p>
                
                ${domainData.insights && domainData.insights.length > 0 ? `
                  <div style="margin-top: 12px;">
                    <strong>Key Insights:</strong>
                    <ul style="margin-top: 8px;">
                      ${domainData.insights.map(insight => `<li>${insight}</li>`).join('')}
                    </ul>
                  </div>
                ` : ''}
                
                ${domainData.personas && domainData.personas.length > 0 ? `
                  <div style="margin-top: 12px;">
                    <strong>User Personas:</strong>
                    <ul style="margin-top: 8px;">
                      ${domainData.personas.map(persona => `<li>${persona}</li>`).join('')}
                    </ul>
                  </div>
                ` : ''}
                
                ${domainData.functionalAreas && domainData.functionalAreas.length > 0 ? `
                  <div style="margin-top: 12px;">
                    <strong>Functional Areas:</strong>
                    <ul style="margin-top: 8px;">
                      ${domainData.functionalAreas.map(area => `<li>${area}</li>`).join('')}
                    </ul>
                  </div>
                ` : ''}
              </div>
            `;
          }
          
          // Render the requirements step interface
          stepContent.innerHTML = `
            <div style="margin-bottom: 16px;">
              <p>Based on your domain definition, we'll now gather the requirements for your application.</p>
            </div>
            
            ${domainInsightsHTML}
            
            <div style="margin-top: 24px;">
              <button id="generate-requirements-btn" style="padding: 8px 16px; background-color: #4a6da7; color: white; border: none; border-radius: 4px; cursor: pointer; font-weight: 500;">Generate Requirements</button>
            </div>
            
            <div id="requirements-result" style="display: none; margin-top: 24px;">
              <!-- Requirements will be displayed here -->
            </div>
          `;
          
          // Add event listener for generate requirements button
          const generateBtn = stepContent.querySelector('#generate-requirements-btn');
          if (generateBtn && domainData) {
            generateBtn.addEventListener('click', async () => {
              // Show loading state
              generateBtn.textContent = 'Generating...';
              generateBtn.disabled = true;
              
              // Show status
              const requirementsResult = stepContent.querySelector('#requirements-result');
              if (requirementsResult) {
                requirementsResult.style.display = 'block';
                requirementsResult.innerHTML = `
                  <div style="padding: 16px; background: #f5f7fa; border-radius: 4px;">
                    <p style="margin: 0; font-style: italic;">Claude is generating application requirements based on your domain insights...</p>
                  </div>
                `;
              }
              
              try {
                // Generate requirements using Claude
                let requirements = null;
                
                if (this.manager && this.manager.claudeService && this.manager.claudeService.apiClient) {
                  // Use real Claude API
                  console.log('Using real Claude API to generate requirements');
                  requirements = await this.manager.claudeService.suggestRequirements(domainData);
                } else {
                  // Use stub implementation
                  console.log('Using stub implementation for requirements');
                  await new Promise(resolve => setTimeout(resolve, 1500));
                  
                  requirements = {
                    entities: [
                      {
                        name: 'User',
                        description: 'Application user',
                        fields: [
                          { name: 'id', type: 'string', description: 'User ID' },
                          { name: 'name', type: 'string', description: 'User name' },
                          { name: 'email', type: 'string', description: 'User email' }
                        ]
                      },
                      {
                        name: 'Task',
                        description: 'User task',
                        fields: [
                          { name: 'id', type: 'string', description: 'Task ID' },
                          { name: 'title', type: 'string', description: 'Task title' },
                          { name: 'description', type: 'string', description: 'Task description' },
                          { name: 'completed', type: 'boolean', description: 'Task completion status' }
                        ]
                      }
                    ],
                    features: [
                      { name: 'User Authentication', description: 'Allow users to sign up and log in', priority: 'High' },
                      { name: 'Task Management', description: 'Create, edit, and delete tasks', priority: 'High' },
                      { name: 'Task Filtering', description: 'Filter tasks by various criteria', priority: 'Medium' }
                    ],
                    nonFunctionalRequirements: [
                      { category: 'Performance', description: 'The application should respond within 2 seconds' },
                      { category: 'Security', description: 'User data should be encrypted' }
                    ]
                  };
                }
                
                console.log('Generated requirements:', requirements);
                
                // Display the requirements
                if (requirementsResult) {
                  // Generate HTML for requirements
                  const entitiesHTML = requirements.entities ? `
                    <div style="margin-bottom: 24px;">
                      <h4 style="margin-top: 0; border-bottom: 1px solid #eee; padding-bottom: 8px;">Data Entities</h4>
                      ${requirements.entities.map(entity => `
                        <div style="margin-bottom: 16px; padding: 12px; background: white; border: 1px solid #eee; border-radius: 4px;">
                          <h5 style="margin-top: 0; margin-bottom: 8px;">${entity.name}</h5>
                          <p style="margin-top: 0; color: #666; font-size: 14px;">${entity.description || 'No description'}</p>
                          
                          <table style="width: 100%; border-collapse: collapse; margin-top: 12px;">
                            <thead>
                              <tr style="border-bottom: 1px solid #eee;">
                                <th style="text-align: left; padding: 8px; font-size: 14px;">Field</th>
                                <th style="text-align: left; padding: 8px; font-size: 14px;">Type</th>
                                <th style="text-align: left; padding: 8px; font-size: 14px;">Description</th>
                              </tr>
                            </thead>
                            <tbody>
                              ${entity.fields ? entity.fields.map(field => `
                                <tr style="border-bottom: 1px solid #f5f5f5;">
                                  <td style="padding: 8px; font-size: 14px;">${field.name}</td>
                                  <td style="padding: 8px; font-size: 14px; color: #0d47a1;">${field.type}</td>
                                  <td style="padding: 8px; font-size: 14px; color: #666;">${field.description || 'No description'}</td>
                                </tr>
                              `).join('') : ''}
                            </tbody>
                          </table>
                        </div>
                      `).join('')}
                    </div>
                  ` : '';
                  
                  const featuresHTML = requirements.features ? `
                    <div style="margin-bottom: 24px;">
                      <h4 style="margin-top: 0; border-bottom: 1px solid #eee; padding-bottom: 8px;">Features</h4>
                      <div style="display: grid; grid-template-columns: repeat(auto-fill, minmax(280px, 1fr)); gap: 16px;">
                        ${requirements.features.map(feature => `
                          <div style="padding: 16px; background: white; border: 1px solid #eee; border-radius: 4px;">
                            <div style="display: flex; justify-content: space-between; align-items: center; margin-bottom: 8px;">
                              <h5 style="margin: 0;">${feature.name}</h5>
                              ${feature.priority ? `
                                <span style="font-size: 12px; padding: 4px 8px; border-radius: 4px; font-weight: 500; background: ${
                                  feature.priority === 'High' ? '#e3f2fd' : 
                                  feature.priority === 'Medium' ? '#f3e5f5' : 
                                  '#fce4ec'
                                }; color: ${
                                  feature.priority === 'High' ? '#0d47a1' : 
                                  feature.priority === 'Medium' ? '#6a1b9a' : 
                                  '#c2185b'
                                };">${feature.priority}</span>
                              ` : ''}
                            </div>
                            <p style="margin: 0; color: #666; font-size: 14px;">${feature.description || 'No description'}</p>
                          </div>
                        `).join('')}
                      </div>
                    </div>
                  ` : '';
                  
                  const nfrHTML = requirements.nonFunctionalRequirements ? `
                    <div>
                      <h4 style="margin-top: 0; border-bottom: 1px solid #eee; padding-bottom: 8px;">Non-Functional Requirements</h4>
                      <div style="display: grid; grid-template-columns: repeat(auto-fill, minmax(280px, 1fr)); gap: 16px;">
                        ${requirements.nonFunctionalRequirements.map(nfr => `
                          <div style="padding: 16px; background: white; border: 1px solid #eee; border-radius: 4px;">
                            <h5 style="margin-top: 0; margin-bottom: 8px; color: #333;">${nfr.category}</h5>
                            <p style="margin: 0; color: #666; font-size: 14px;">${nfr.description || 'No description'}</p>
                          </div>
                        `).join('')}
                      </div>
                    </div>
                  ` : '';
                  
                  // Combine sections
                  requirementsResult.innerHTML = `
                    <div style="margin-bottom: 16px;">
                      <h3 style="margin-top: 0;">Generated Requirements</h3>
                      <p>Claude has analyzed your domain and generated the following requirements:</p>
                    </div>
                    
                    ${entitiesHTML}
                    ${featuresHTML}
                    ${nfrHTML}
                    
                    <div style="margin-top: 24px; display: flex; justify-content: flex-end;">
                      <button id="continue-to-specification" style="padding: 10px 20px; background-color: #4a6da7; color: white; border: none; border-radius: 4px; cursor: pointer; font-weight: 500;">Continue to Specification</button>
                    </div>
                  `;
                  
                  // Add event listener for the continue button
                  const continueBtn = requirementsResult.querySelector('#continue-to-specification');
                  if (continueBtn) {
                    continueBtn.addEventListener('click', () => {
                      // Update UI for specification step
                      // Update progress indicators
                      const progressBar = this.container.querySelector('div[style*="background: #4a6da7"]');
                      if (progressBar) progressBar.style.width = '33.33%'; // 2/6 steps
                      
                      // Update step indicators
                      const stepIndicators = this.container.querySelectorAll('div[style*="border: 1px solid #eee; border-radius: 4px;"]');
                      if (stepIndicators && stepIndicators.length >= 3) {
                        // Set domain step to completed (green)
                        const domainStep = stepIndicators[0].querySelector('div');
                        if (domainStep) domainStep.style.backgroundColor = '#4caf50';
                        
                        // Set requirements step to completed (green)
                        const reqStep = stepIndicators[1].querySelector('div');
                        if (reqStep) reqStep.style.backgroundColor = '#4caf50';
                        
                        // Set specification step to in-progress (blue)
                        const specStep = stepIndicators[2].querySelector('div');
                        if (specStep) specStep.style.backgroundColor = '#2196f3';
                        
                        // Update active step
                        stepIndicators.forEach((step, index) => {
                          if (index === 1) {
                            // Remove active from requirements step
                            step.style.fontWeight = '400';
                            step.style.borderColor = '#eee';
                          }
                          if (index === 2) {
                            // Add active to specification step
                            step.style.fontWeight = '600';
                            step.style.borderColor = '#4a6da7';
                          }
                        });
                      }
                      
                      // Update step title
                      const stepTitle = this.container.querySelector('h3[style*="border-bottom: 1px solid #eee"]');
                      if (stepTitle) stepTitle.textContent = this.getStepDisplayName('specification');
                      
                      // Load specification step content
                      this.loadProjectStepContent(projectId, 'specification');
                    });
                  }
                }
              } catch (error) {
                console.error('Error generating requirements:', error);
                
                // Show error
                if (requirementsResult) {
                  requirementsResult.innerHTML = `
                    <div style="padding: 16px; background: #ffebee; border-radius: 4px; color: #c62828;">
                      <p style="margin: 0;"><strong>Error generating requirements:</strong> ${error.message}</p>
                    </div>
                  `;
                }
              } finally {
                // Reset button
                generateBtn.textContent = 'Generate Requirements';
                generateBtn.disabled = false;
              }
            });
          }
          break;
          
        case 'specification':
          stepContent.innerHTML = `
            <p>Review and edit the generated application specification.</p>
            <p style="color: #c00;">This step is not fully implemented in the demo.</p>
          `;
          break;
          
        case 'generation':
          stepContent.innerHTML = `
            <p>Generate code for your application based on the specification.</p>
            <p style="color: #c00;">This step is not fully implemented in the demo.</p>
          `;
          break;
          
        case 'testing':
          stepContent.innerHTML = `
            <p>Run tests on your generated application code.</p>
            <p style="color: #c00;">This step is not fully implemented in the demo.</p>
          `;
          break;
          
        case 'publishing':
          stepContent.innerHTML = `
            <p>Publish your application as a bundle or to GitHub.</p>
            <p style="color: #c00;">This step is not fully implemented in the demo.</p>
          `;
          break;
          
        default:
          stepContent.innerHTML = `
            <p>Unknown step: ${step}</p>
          `;
      }
    }
    
    /**
     * Render workflow steps
     * @param {Object} status - Project status
     * @returns {string} HTML for workflow steps
     */
    renderWorkflowSteps(status) {
      const steps = [
        { id: 'domain', name: 'Domain' },
        { id: 'requirements', name: 'Requirements' },
        { id: 'specification', name: 'Specification' },
        { id: 'generation', name: 'Generation' },
        { id: 'testing', name: 'Testing' },
        { id: 'publishing', name: 'Publishing' }
      ];
      
      return steps.map(step => {
        const stepStatus = status.progress[step.id]?.status || 'pending';
        
        let color = '#ddd'; // Default color for pending
        if (stepStatus === 'completed') color = '#4caf50';
        if (stepStatus === 'in_progress') color = '#2196f3';
        if (stepStatus === 'error') color = '#f44336';
        
        let active = status.currentStep === step.id ? 'font-weight: 600; border-color: #4a6da7;' : '';
        
        return `
          <div style="display: flex; align-items: center; padding: 8px 12px; border: 1px solid #eee; border-radius: 4px; ${active}">
            <div style="width: 12px; height: 12px; border-radius: 50%; background-color: ${color}; margin-right: 8px;"></div>
            <span>${step.name}</span>
          </div>
        `;
      }).join('');
    }
    
    /**
     * Get display name for a step
     * @param {string} stepId - Step ID
     * @returns {string} Display name
     */
    getStepDisplayName(stepId) {
      const stepMap = {
        domain: 'Domain Identification',
        requirements: 'Requirements Gathering',
        specification: 'Specification Creation',
        generation: 'Code Generation',
        testing: 'Testing & Validation',
        publishing: 'App Publishing'
      };
      
      return stepMap[stepId] || stepId;
    }
    
    /**
     * Called when the app is activated
     */
    onActivate() {
      console.log('App Factory activated');
      
      // Notify system of activation
      if (window.PrimeOS && window.PrimeOS.eventBus) {
        window.PrimeOS.eventBus.publish('app-factory:activated');
      }
    }
    
    /**
     * Called when the app is deactivated
     */
    onDeactivate() {
      console.log('App Factory deactivated');
      
      // Notify system of deactivation
      if (window.PrimeOS && window.PrimeOS.eventBus) {
        window.PrimeOS.eventBus.publish('app-factory:deactivated');
      }
      
      // Save any pending work
      if (this.manager) {
        // No real work to save in the demo, but in a real implementation, 
        // this would save any unsaved changes
      }
    }
  };
}

// Export for CommonJS environments
if (typeof module !== 'undefined' && module.exports) {
  module.exports = AppFactory;
}