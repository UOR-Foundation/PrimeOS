/**
 * PrimeOS Settings Application
 * 
 * A system application for managing PrimeOS settings, API keys, and 
 * system configuration.
 */

// Import dependencies - use different variable names to avoid conflicts
let SettingsAppAPI;
let SettingsStore;
let SecureVault;
let SettingsPanel;
let SecretsManager;

try {
  // Import core modules based on environment
  if (typeof window !== 'undefined' && window.PrimeOS) {
    console.log('Using PrimeOS from global window object');
    SettingsAppAPI = window.PrimeOS.AppAPI;
    SettingsStore = window.PrimeOS.SettingsStore;
    SecureVault = window.PrimeOS.SecureVault;
    SettingsPanel = window.PrimeOS.SettingsPanel;
    SecretsManager = window.PrimeOS.SecretsManager;
  } else {
    // For Node.js or when not available in window
    console.log('Attempting to require modules');
    const appApiModule = require('../../core/apps/app-api');
    const settingsStoreModule = require('./models/settings-store');
    const secureVaultModule = require('../../core/identity/secure-vault');
    const settingsPanelModule = require('./components/settings-panel');
    const secretsManagerModule = require('./components/secrets-manager');
    
    SettingsAppAPI = appApiModule.AppAPI;
    SettingsStore = settingsStoreModule.SettingsStore;
    SecureVault = secureVaultModule.SecureVault;
    SettingsPanel = settingsPanelModule.SettingsPanel;
    SecretsManager = secretsManagerModule.SecretsManager;
  }
} catch (error) {
  console.error('Failed to import required modules:', error);
  
  // Mock implementations for testing
  SettingsAppAPI = class {
    constructor(options) {
      this.appId = options.appId;
      this.container = options.containerElement;
      this.eventBus = options.eventBus || { publish: () => {}, subscribe: () => () => {} };
      this.store = options.store || null;
      this.windowId = options.windowId || null;
      this.state = { preferences: {} };
    }
    
    showNotification(notification) {
      console.log('NOTIFICATION:', notification);
    }
    
    async loadPreferences() {
      return this.state.preferences;
    }
    
    async savePreferences(preferences) {
      this.state.preferences = { ...this.state.preferences, ...preferences };
    }
  };
}

/**
 * Settings Application
 */
class Settings {
  /**
   * Initialize the settings app
   * @param {HTMLElement} container - Container element
   * @param {Object} options - Initialization options
   */
  static async initialize(container, options) {
    const settings = new Settings(container, options);
    await settings.init();
    return settings;
  }
  
  /**
   * Constructor
   * @param {HTMLElement} container - Container element
   * @param {Object} options - Initialization options
   */
  constructor(container, options) {
    this.container = container;
    this.options = options;
    this.appId = 'settings';
    
    // Initialize AppAPI
    this.api = new SettingsAppAPI({
      appId: this.appId,
      containerElement: container,
      eventBus: options.eventBus,
      store: options.store,
      identity: options.identity,
      windowId: options.windowId
    });
    
    // Create event bus if not provided
    this.eventBus = options.eventBus || {
      publish: (event, data) => console.log(`Event: ${event}`, data),
      subscribe: (event, callback) => {
        console.log(`Subscribed to: ${event}`);
        return () => {}; // Unsubscribe function
      }
    };
    
    // Create a secure vault for API keys
    this.secureVault = new SecureVault({ 
      eventBus: this.eventBus 
    });
    
    // Create settings store
    this.settingsStore = new SettingsStore({
      eventBus: this.eventBus,
      secureVault: this.secureVault
    });
    
    // Initialize UI components
    this.settingsPanel = null;
    this.secretsManager = null;
    
    // Bind methods
    this.saveSettings = this.saveSettings.bind(this);
    this.loadSettings = this.loadSettings.bind(this);
    this.handleSettingsEvents = this.handleSettingsEvents.bind(this);
  }
  
  /**
   * Initialize the application
   */
  async init() {
    // Initialize the settings store
    await this.settingsStore.loadAll();
    
    // Initialize the secure vault
    await this.secureVault.initialize && await this.secureVault.initialize();
    
    // Create UI components and render
    this.renderUI();
    
    // Set up event handlers for settings events
    this.handleSettingsEvents();
    
    // Apply theme if available
    const preferences = await this.api.loadPreferences();
    if (preferences.theme) {
      await this.settingsStore.updateSetting('appearance', 'theme', preferences.theme);
      this.applyTheme(preferences.theme);
    }
    
    // Notify shell that we're ready
    this.api.showNotification({
      title: 'Settings',
      message: 'Settings application initialized',
      type: 'success',
      timeout: 2000
    });
    
    return this;
  }
  
  /**
   * Render the main UI
   */
  renderUI() {
    // Create a container for the settings components
    this.container.innerHTML = `
      <div class="settings-app">
        <div id="settings-container" class="settings-container">
          <!-- Settings panel will be inserted here -->
        </div>
      </div>
    `;
    
    // Add styles
    const style = document.createElement('style');
    style.textContent = `
      .settings-app {
        display: flex;
        height: 100%;
        font-family: Arial, sans-serif;
        overflow: hidden;
        color: #333;
      }
      
      .settings-container {
        display: flex;
        flex: 1;
        overflow: hidden;
      }
    `;
    
    this.container.appendChild(style);
    
    // Create and initialize the Settings Panel component
    this.settingsPanel = new SettingsPanel({
      store: this.settingsStore,
      eventBus: this.eventBus
    });
    
    // Create and initialize the Secrets Manager component
    this.secretsManager = new SecretsManager({
      secureVault: this.secureVault,
      eventBus: this.eventBus,
      store: this.settingsStore
    });
    
    // Initialize components
    Promise.all([
      this.settingsPanel.initialize(),
      this.secretsManager.initialize()
    ]).then(() => {
      // Render the settings panel in the container
      const settingsContainer = this.container.querySelector('#settings-container');
      if (settingsContainer) {
        settingsContainer.appendChild(this.settingsPanel.render());
      }
      
      console.log('Settings UI components initialized');
    }).catch(error => {
      console.error('Failed to initialize settings components:', error);
    });
  }
  
  /**
   * Set up event handlers for settings events
   */
  handleSettingsEvents() {
    if (!this.eventBus) return;
    
    // Listen for settings:save-requested
    this.eventBus.subscribe('settings:save-requested', async () => {
      await this.saveSettings();
    });
    
    // Listen for settings:reset-requested
    this.eventBus.subscribe('settings:reset-requested', async () => {
      await this.settingsStore.resetToDefaults();
    });
    
    // Listen for settings:api-key-changed
    this.eventBus.subscribe('settings:api-key-changed', async (data) => {
      // Notify other components that might need the API key
      // This is handled by the event bus broadcast to all subscribers
      console.log(`API key changed: ${data.key}`);
      
      // Save preferences if needed
      if (data.key === 'claudeApiKey') {
        const apiUrlInput = document.querySelector('[data-category="apiKeys"][data-setting="claudeApiUrl"]');
        const apiModelInput = document.querySelector('[data-category="apiKeys"][data-setting="claudeModel"]');
        
        if (apiUrlInput) {
          await this.settingsStore.updateSetting('apiKeys', 'claudeApiUrl', apiUrlInput.value);
        }
        
        if (apiModelInput) {
          await this.settingsStore.updateSetting('apiKeys', 'claudeModel', apiModelInput.value);
        }
      }
    });
    
    // Listen for appearance changes
    this.eventBus.subscribe('settings:changed', async (data) => {
      if (data.category === 'appearance' && data.key === 'theme') {
        this.applyTheme(data.value);
        await this.api.savePreferences({ theme: data.value });
      }
    });
    
    // Listen for view-documentation request
    this.eventBus.subscribe('settings:view-documentation', () => {
      this.api.showNotification({
        title: 'Documentation',
        message: 'Documentation feature coming soon',
        type: 'info',
        timeout: 3000
      });
    });
    
    // Listen for check-updates request
    this.eventBus.subscribe('settings:check-updates', () => {
      this.api.showNotification({
        title: 'Updates',
        message: 'No updates available',
        type: 'info',
        timeout: 3000
      });
    });
  }
  
  /**
   * Apply theme to settings app
   * @param {string} theme - Theme name (light or dark)
   */
  applyTheme(theme) {
    const settingsApp = this.container.querySelector('.settings-app');
    
    if (theme === 'dark') {
      settingsApp.classList.add('theme-dark');
      document.documentElement.classList.add('theme-dark');
    } else {
      settingsApp.classList.remove('theme-dark');
      document.documentElement.classList.remove('theme-dark');
    }
  }
  
  /**
   * Save settings to store
   */
  async saveSettings() {
    try {
      // Save all settings in the store
      await this.settingsStore.saveAll();
      
      // Get appearance settings for preferences
      const appearance = this.settingsStore.getSettings('appearance') || {};
      
      // Save to preferences
      await this.api.savePreferences({
        theme: appearance.theme || 'light',
        fontSize: appearance.fontSize || 'medium',
        fontFamily: appearance.fontFamily || 'system-ui'
      });
      
      // Show success notification
      this.api.showNotification({
        title: 'Settings Saved',
        message: 'Your settings have been saved successfully',
        type: 'success',
        timeout: 3000
      });
      
      return true;
    } catch (error) {
      console.error('Failed to save settings:', error);
      
      // Show error notification
      this.api.showNotification({
        title: 'Error Saving Settings',
        message: error.message,
        type: 'error',
        timeout: 3000
      });
      
      return false;
    }
  }
  
  /**
   * Load settings from store
   */
  async loadSettings() {
    try {
      // Load all settings from store
      await this.settingsStore.loadAll();
      
      // Get theme preference
      const preferences = await this.api.loadPreferences();
      if (preferences.theme) {
        await this.settingsStore.updateSetting('appearance', 'theme', preferences.theme);
      }
      
      return true;
    } catch (error) {
      console.error('Failed to load settings:', error);
      return false;
    }
  }
  
  /**
   * Get window title for shell
   * @returns {string} Window title
   */
  getTitle() {
    return 'Settings';
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { default: Settings };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.Settings = Settings;
}