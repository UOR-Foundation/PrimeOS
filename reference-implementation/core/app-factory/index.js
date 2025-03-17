/**
 * PrimeOS App Factory
 * 
 * Main entry point for the App Factory system that enables AI-assisted
 * application creation within the PrimeOS environment.
 */

// Import core components
const { AppFactoryManager } = require('./app-factory-manager');
const { ClaudeService } = require('./claude-service');
const { AppSpecGenerator } = require('./app-spec-generator');
const { CodeGenerator } = require('./code-generator');
const { TestRunner } = require('./test-runner');
const { AppPublisher } = require('./app-publisher');
const { AppFactoryUI } = require('./app-factory-ui');

// Export all components
module.exports = {
  AppFactoryManager,
  ClaudeService,
  AppSpecGenerator,
  CodeGenerator,
  TestRunner,
  AppPublisher,
  AppFactoryUI,
  
  /**
   * Create a new App Factory instance with all required dependencies
   * @param {Object} options - Configuration options
   * @returns {Object} App Factory instance with all components
   */
  createAppFactory: function(options = {}) {
    // Create service instances
    const claudeService = new ClaudeService({
      apiKey: options.apiKey,
      eventBus: options.eventBus,
      promptTemplates: options.promptTemplates
    });
    
    const specGenerator = new AppSpecGenerator({
      claudeService,
      eventBus: options.eventBus
    });
    
    const codeGenerator = new CodeGenerator({
      claudeService,
      eventBus: options.eventBus,
      templates: options.templates
    });
    
    const testRunner = new TestRunner({
      eventBus: options.eventBus,
      includeJest: options.includeJest,
      includeLint: options.includeLint
    });
    
    const appPublisher = new AppPublisher({
      store: options.store,
      eventBus: options.eventBus,
      bundleManager: options.bundleManager
    });
    
    // Create the manager
    const manager = new AppFactoryManager({
      claudeService,
      store: options.store,
      eventBus: options.eventBus,
      bundleManager: options.bundleManager,
      testRunner
    });
    
    // Create UI component if container provided
    let ui = null;
    if (options.container) {
      ui = new AppFactoryUI({
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
      specGenerator,
      codeGenerator,
      testRunner,
      appPublisher,
      ui
    };
  }
};

// Export for browser environments
if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.AppFactory = module.exports;
}