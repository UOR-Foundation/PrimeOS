/**
 * PrimeOS Settings Store
 * 
 * A manifold-based settings storage system that provides secure and
 * persistent settings management with proper domain decomposition.
 */

// Import dependencies
const { Manifold } = require('../../../../src/framework/base0/manifold.js');
const { SecureVault } = require('../../../core/identity/secure-vault.js');

/**
 * SettingsStore - Manages application and system settings
 * Implements manifold-based settings model with meta/invariant/variant decomposition
 */
class SettingsStore {
  /**
   * Create a new SettingsStore instance
   * @param {Object} options - Configuration options
   * @param {Object} options.storage - Storage provider (optional)
   * @param {Object} options.eventBus - Event bus for communication
   * @param {Object} options.secureVault - Secure vault for API keys (optional)
   * @param {Object} options.defaults - Default settings values
   */
  constructor(options = {}) {
    this.storage = options.storage || this._createDefaultStorage();
    this.eventBus = options.eventBus;
    
    // Create or use secure vault for sensitive data
    this.secureVault = options.secureVault || this._createSecureVault();
    
    // Default settings if none provided
    this.defaults = options.defaults || {
      general: {
        language: 'en',
        theme: 'system',
        notifications: true,
        startupApp: ''
      },
      appearance: {
        accentColor: '#007bff',
        fontSize: 'medium',
        fontFamily: 'system-ui',
        darkMode: false
      },
      security: {
        enablePasswordLock: false,
        autoLockTimeout: 5,
        saveLoginSession: true,
        sessionTimeout: 60,
        enableAnalytics: false
      },
      apiKeys: {
        claudeApiKey: '',
        claudeApiUrl: 'https://api.anthropic.com/v1/messages',
        claudeModel: 'claude-3-sonnet-20240229'
      },
      developer: {
        enableDevTools: false,
        enableDebugLogging: false,
        logLevel: 'error',
        debugMode: false,
        coherenceThreshold: 0.8,
        manifestDepth: 'moderate'
      },
      notifications: {
        enabled: true,
        sound: true,
        desktop: true,
        criticalOnly: false
      },
      about: {
        version: '1.0.0',
        buildDate: new Date().toISOString().slice(0, 10),
        license: 'MIT'
      }
    };
    
    // Track initialization state
    this.initialized = false;
    
    // Settings data structure using Maps for each category
    this.categories = new Map();

    // Settings manifest that stores metadata about all settings
    this.settingsManifold = new Manifold({
      meta: {
        id: `settings_manifold_${Date.now()}`,
        type: 'settings',
        createdAt: new Date().toISOString(),
        description: 'PrimeOS settings store manifest'
      },
      invariant: {
        categories: Object.keys(this.defaults),
        requiredCategories: ['general', 'security', 'apiKeys'],
        persistenceRequired: true,
        validationRequired: true,
        version: '1.0.0'
      },
      variant: {
        lastAccessed: Date.now(),
        lastUpdated: Date.now(),
        changeCount: 0,
        lastCategory: null
      },
      depth: 3 // System level
    });
    
    // Initialize settings maps with default values
    this._initializeSettingsManifolds();
    
    // Bind methods
    this.initialize = this.initialize.bind(this);
    this.getCategory = this.getCategory.bind(this);
    this.getSetting = this.getSetting.bind(this);
    this.updateSetting = this.updateSetting.bind(this);
    this.save = this.save.bind(this);
    this.getApiKey = this.getApiKey.bind(this);
    this.updateApiKey = this.updateApiKey.bind(this);
    this.getApiKeys = this.getApiKeys.bind(this);
    this.resetToDefaults = this.resetToDefaults.bind(this);
  }
  
  /**
   * Initialize settings with values from storage
   * @returns {Promise<boolean>} Success indicator
   */
  async initialize() {
    try {
      // Get stored settings from storage
      const storedSettings = await this.storage.getItem('settings');
      
      if (storedSettings) {
        // Parse stored settings
        const parsed = JSON.parse(storedSettings);
        
        // Update each category with stored values, preserving defaults for missing values
        for (const [category, values] of Object.entries(parsed)) {
          if (this.categories.has(category)) {
            const categoryMap = this.categories.get(category);
            
            // Update each setting value from storage
            for (const [key, value] of Object.entries(values)) {
              categoryMap.set(key, value);
            }
          } else if (category !== 'apiKeys') {
            // Create new category if it doesn't exist and isn't sensitive
            this.categories.set(category, new Map(Object.entries(values)));
          }
        }
      }
      
      // Load API keys from SecureVault
      if (this.secureVault) {
        try {
          const claudeApiKey = await this.secureVault.getSecret('claudeApiKey');
          
          // Update API key in settings
          if (claudeApiKey) {
            const apiKeys = this.getCategory('apiKeys');
            apiKeys.set('claudeApiKey', claudeApiKey);
          }
        } catch (error) {
          console.error('Failed to load API keys from SecureVault:', error);
        }
      }
      
      // Mark as initialized
      this.initialized = true;
      
      // Update manifold accessed timestamp
      this.settingsManifold.updateVariant({
        lastAccessed: Date.now()
      });
      
      return true;
    } catch (error) {
      console.error('Failed to initialize settings:', error);
      return false;
    }
  }
  
  /**
   * Initialize manifolds for each settings category
   * @private
   */
  _initializeSettingsManifolds() {
    // Create a settings map for each category
    this.settings = {};
    
    Object.keys(this.defaults).forEach(category => {
      this.categories.set(category, new Map(Object.entries(this.defaults[category])));
      
      // Create manifold for this category (for coherence tracking)
      this.settings[category] = new Manifold({
        meta: {
          id: `settings_${category}_${Date.now()}`,
          type: 'settings_category',
          createdAt: new Date().toISOString(),
          category
        },
        invariant: {
          settingKeys: Object.keys(this.defaults[category]),
          category,
          schemaVersion: '1.0.0'
        },
        variant: {
          values: { ...this.defaults[category] },
          lastUpdated: Date.now(),
          changeCount: 0
        },
        depth: 3 // System level
      });
    });
  }
  
  /**
   * Get settings for a category
   * @param {string} category - Settings category
   * @returns {Map} Map of settings for the category
   */
  getCategory(category) {
    // Update access timestamp
    this.settingsManifold.updateVariant({
      lastAccessed: Date.now()
    });
    
    // Get the settings map for this category
    if (this.categories.has(category)) {
      return this.categories.get(category);
    }
    
    // Return empty map if category not found
    return new Map();
  }
  
  /**
   * Get a specific setting value
   * @param {string} category - Settings category
   * @param {string} key - Setting key
   * @param {*} defaultValue - Default value if setting not found
   * @returns {*} Setting value or default
   */
  getSetting(category, key, defaultValue = null) {
    const categoryMap = this.getCategory(category);
    
    if (categoryMap.has(key)) {
      return categoryMap.get(key);
    }
    
    return defaultValue;
  }
  
  /**
   * Update a setting value
   * @param {string} category - Settings category
   * @param {string} key - Setting key
   * @param {*} value - New value
   * @returns {Promise<boolean>} Success indicator
   */
  async updateSetting(category, key, value) {
    try {
      // Create category if it doesn't exist
      if (!this.categories.has(category)) {
        this.categories.set(category, new Map());
      }
      
      const categoryMap = this.categories.get(category);
      
      // Handle special case for API keys
      if (category === 'apiKeys' && key === 'claudeApiKey') {
        if (value && value.trim()) {
          // Store API key in secure vault
          await this.updateApiKey(key, value);
        } else {
          // Remove API key from secure vault
          if (this.secureVault) {
            await this.secureVault.removeSecret(key);
          }
        }
      }
      
      // Update the value
      categoryMap.set(key, value);
      
      // Update manifold for tracking
      if (this.settings[category]) {
        this.settings[category].updateVariant({
          values: { ...Object.fromEntries(categoryMap.entries()) },
          lastUpdated: Date.now(),
          changeCount: (this.settings[category].getVariant().changeCount || 0) + 1
        });
      }
      
      // Update global settings manifold
      this.settingsManifold.updateVariant({
        lastUpdated: Date.now(),
        changeCount: (this.settingsManifold.getVariant().changeCount || 0) + 1,
        lastCategory: category
      });
      
      // Save to storage
      await this.save();
      
      // Notify about changes
      if (this.eventBus) {
        // Specific setting change
        this.eventBus.publish('settings:changed', {
          category,
          key,
          value,
          timestamp: new Date().toISOString()
        });
        
        // API key changes get special notification
        if (category === 'apiKeys') {
          this.eventBus.publish('settings:api-key-changed', {
            key,
            value,
            timestamp: new Date().toISOString()
          });
        }
      }
      
      return true;
    } catch (error) {
      console.error(`Failed to update setting ${category}.${key}:`, error);
      return false;
    }
  }
  
  /**
   * Save all settings to storage
   * @returns {Promise<boolean>} Success indicator
   */
  async save() {
    try {
      // Convert settings to plain object for storage
      const settingsObject = {};
      
      for (const [category, values] of this.categories.entries()) {
        // Skip storing sensitive categories directly
        if (category === 'apiKeys') {
          continue;
        }
        
        settingsObject[category] = Object.fromEntries(values.entries());
      }
      
      // Save to storage
      await this.storage.setItem('settings', JSON.stringify(settingsObject));
      
      // Notify about save
      if (this.eventBus) {
        this.eventBus.publish('settings:saved', {
          timestamp: new Date().toISOString()
        });
      }
      
      return true;
    } catch (error) {
      console.error('Failed to save settings:', error);
      
      // Notify about error
      if (this.eventBus) {
        this.eventBus.publish('settings:save-error', {
          error: error.message,
          timestamp: new Date().toISOString()
        });
      }
      
      return false;
    }
  }
  
  /**
   * Update an API key in secure storage
   * @param {string} keyName - Key name
   * @param {string} value - API key value
   * @returns {Promise<boolean>} Success indicator
   */
  async updateApiKey(keyName, value) {
    if (!this.secureVault) {
      return false;
    }
    
    try {
      // Save to secure vault
      await this.secureVault.setSecret(keyName, value, {
        type: 'api_key',
        created: new Date().toISOString(),
        source: 'settings_store'
      });
      
      // Update in-memory settings
      const apiKeys = this.getCategory('apiKeys');
      apiKeys.set(keyName, value);
      
      return true;
    } catch (error) {
      console.error(`Failed to update API key ${keyName}:`, error);
      return false;
    }
  }
  
  /**
   * Get a specific API key from secure storage
   * @param {string} keyName - Key name
   * @returns {Promise<string|null>} API key value
   */
  async getApiKey(keyName) {
    if (!this.secureVault) {
      return null;
    }
    
    try {
      return await this.secureVault.getSecret(keyName);
    } catch (error) {
      console.error(`Failed to get API key ${keyName}:`, error);
      return null;
    }
  }
  
  /**
   * Get all API keys
   * @returns {Object} Map of API keys and values
   */
  getApiKeys() {
    // Convert Map to plain object
    return Object.fromEntries(this.getCategory('apiKeys').entries());
  }
  
  /**
   * Reset all settings to defaults
   * @param {string} [category] - Optional category to reset (if omitted, resets all)
   * @returns {Promise<boolean>} Success indicator
   */
  async resetToDefaults(category) {
    try {
      if (category) {
        // Reset specific category
        if (this.defaults[category]) {
          this.categories.set(category, new Map(Object.entries(this.defaults[category])));
          
          // Handle special case for API keys
          if (category === 'apiKeys' && this.secureVault) {
            await this.secureVault.removeSecret('claudeApiKey');
          }
          
          // Update manifold for tracking
          if (this.settings[category]) {
            this.settings[category].updateVariant({
              values: { ...this.defaults[category] },
              lastUpdated: Date.now(),
              changeCount: (this.settings[category].getVariant().changeCount || 0) + 1
            });
          }
          
          // Notify about reset
          if (this.eventBus) {
            this.eventBus.publish('settings:category-reset', {
              category,
              timestamp: new Date().toISOString()
            });
          }
        }
      } else {
        // Reset all categories
        for (const categoryName of Object.keys(this.defaults)) {
          this.categories.set(categoryName, new Map(Object.entries(this.defaults[categoryName])));
          
          // Update manifold for tracking
          if (this.settings[categoryName]) {
            this.settings[categoryName].updateVariant({
              values: { ...this.defaults[categoryName] },
              lastUpdated: Date.now(),
              changeCount: (this.settings[categoryName].getVariant().changeCount || 0) + 1
            });
          }
        }
        
        // Handle special case for API keys
        if (this.secureVault) {
          await this.secureVault.removeSecret('claudeApiKey');
        }
        
        // Notify about reset
        if (this.eventBus) {
          this.eventBus.publish('settings:reset', {
            timestamp: new Date().toISOString()
          });
        }
      }
      
      // Update global settings manifold
      this.settingsManifold.updateVariant({
        lastUpdated: Date.now(),
        changeCount: (this.settingsManifold.getVariant().changeCount || 0) + 1
      });
      
      // Save changes
      await this.save();
      
      return true;
    } catch (error) {
      console.error('Failed to reset settings:', error);
      return false;
    }
  }
  
  /**
   * Get default settings
   * @returns {Object} Default settings
   */
  getDefaultSettings() {
    return this.defaults;
  }
  
  /**
   * Get settings for a category
   * @param {string} category - Settings category
   * @returns {Object} Settings for the category
   */
  getSettings(category) {
    if (!category || !this.settings[category]) {
      return null;
    }
    
    // Return a copy of the variant values
    return { ...this.settings[category].getVariant().values };
  }
  
  /**
   * Get all settings
   * @returns {Object} All settings values
   */
  getAllSettings() {
    const allSettings = {};
    
    Object.keys(this.settings).forEach(category => {
      allSettings[category] = this.getSettings(category);
    });
    
    return allSettings;
  }

  /**
   * Create default storage provider
   * @private
   * @returns {Object} Storage provider
   */
  _createDefaultStorage() {
    // Simple storage using localStorage in browser or in-memory in Node.js
    if (typeof localStorage !== 'undefined') {
      return {
        getItem: async (key) => localStorage.getItem(key),
        setItem: async (key, value) => localStorage.setItem(key, value),
        removeItem: async (key) => localStorage.removeItem(key)
      };
    } else {
      // In-memory fallback for Node.js
      const storage = new Map();
      return {
        getItem: async (key) => storage.get(key) || null,
        setItem: async (key, value) => storage.set(key, value),
        removeItem: async (key) => storage.delete(key)
      };
    }
  }
  
  /**
   * Create a secure vault instance
   * @private
   * @returns {Object} SecureVault instance
   */
  _createSecureVault() {
    // Check if SecureVault is available
    try {
      // Create a new SecureVault with event bus
      return new SecureVault({
        eventBus: this.eventBus
      });
    } catch (error) {
      console.error('Failed to create SecureVault:', error);
      
      // Return minimal compatible interface
      return {
        getSecret: async () => null,
        setSecret: async () => false,
        removeSecret: async () => false,
        getAllKeys: async () => []
      };
    }
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { SettingsStore };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.SettingsStore = SettingsStore;
}