/**
 * PrimeOS Configuration Manager
 * 
 * System-wide configuration management for PrimeOS that provides
 * coherence-validated settings storage and retrieval.
 */

/**
 * Configuration Manager for system and application settings
 */
class ConfigurationManager {
  /**
   * Create a new Configuration Manager
   * @param {Object} options - Configuration options
   * @param {Object} options.store - PrimeStore instance for persistence
   * @param {Object} options.eventBus - Event bus for notifications
   * @param {Object} options.secureVault - Secure vault for sensitive settings
   * @param {Object} options.coherence - Coherence validator
   */
  constructor(options = {}) {
    // Store dependencies
    this.store = options.store;
    this.eventBus = options.eventBus;
    this.secureVault = options.secureVault;
    this.coherence = options.coherence;
    
    // Initialize state
    this.systemConfigKey = 'system_configuration';
    this.configCache = null;
    this.defaultConfig = {
      system: {
        language: 'English',
        notifications: true,
        startupApp: null,
        lastBootTime: null
      },
      appearance: {
        theme: 'light',
        accentColor: '#007bff',
        fontSize: 'medium',
        animations: true
      },
      security: {
        enablePasswordLock: false,
        autoLockTimeout: 5, // minutes
        saveLoginSession: true,
        sessionTimeout: 60 // minutes
      },
      apiEndpoints: {
        claudeApiUrl: 'https://api.anthropic.com/v1/messages'
      }
    };
    
    // Bind methods
    this._loadConfigFromStore = this._loadConfigFromStore.bind(this);
    this._saveConfigToStore = this._saveConfigToStore.bind(this);
    this._validateCoherence = this._validateCoherence.bind(this);
    
    // Initialize by loading config
    this._loadConfigFromStore()
      .then(() => console.log('Configuration loaded'))
      .catch(err => console.error('Failed to load configuration', err));
    
    // Listen for config update events
    if (this.eventBus) {
      this.eventBus.subscribe('settings:updated', this.handleSettingsUpdate.bind(this));
    }
  }
  
  /**
   * Get a configuration value
   * @param {string} path - Configuration path (e.g., 'system.language')
   * @param {*} defaultValue - Default value if not found
   * @returns {Promise<*>} Configuration value
   */
  async getConfig(path, defaultValue) {
    if (!this.configCache) {
      await this._loadConfigFromStore();
    }
    
    try {
      // Parse the path to navigate the config object
      const parts = path.split('.');
      let current = this.configCache;
      
      for (let i = 0; i < parts.length; i++) {
        const part = parts[i];
        if (current === undefined || current === null) {
          return defaultValue;
        }
        
        current = current[part];
      }
      
      return current !== undefined ? current : defaultValue;
    } catch (error) {
      console.error(`Error getting config ${path}:`, error);
      return defaultValue;
    }
  }
  
  /**
   * Set a configuration value
   * @param {string} path - Configuration path (e.g., 'system.language')
   * @param {*} value - Value to set
   * @returns {Promise<boolean>} Success indicator
   */
  async setConfig(path, value) {
    if (!this.configCache) {
      await this._loadConfigFromStore();
    }
    
    try {
      // Parse the path to navigate the config object
      const parts = path.split('.');
      let current = this.configCache;
      
      // Navigate to the parent object of the property we want to set
      for (let i = 0; i < parts.length - 1; i++) {
        const part = parts[i];
        
        // Create the path if it doesn't exist
        if (!current[part]) {
          current[part] = {};
        }
        
        current = current[part];
      }
      
      // Set the property
      const lastPart = parts[parts.length - 1];
      const oldValue = current[lastPart];
      current[lastPart] = value;
      
      // Validate coherence of updated config
      if (this.coherence && !this._validateCoherence(this.configCache)) {
        // Revert change if coherence check fails
        current[lastPart] = oldValue;
        throw new Error('Coherence check failed for configuration update');
      }
      
      // Save to store
      await this._saveConfigToStore();
      
      // Notify about the change
      if (this.eventBus) {
        this.eventBus.publish('config:changed', {
          path,
          oldValue,
          newValue: value,
          timestamp: new Date().toISOString()
        });
      }
      
      return true;
    } catch (error) {
      console.error(`Error setting config ${path}:`, error);
      return false;
    }
  }
  
  /**
   * Reset configuration to defaults
   * @param {string} [section] - Optional section to reset (resets all if not specified)
   * @returns {Promise<boolean>} Success indicator
   */
  async resetConfig(section) {
    try {
      if (section) {
        // Reset only the specified section
        if (this.defaultConfig[section]) {
          this.configCache[section] = JSON.parse(JSON.stringify(this.defaultConfig[section]));
        } else {
          throw new Error(`Unknown configuration section: ${section}`);
        }
      } else {
        // Reset all configuration
        this.configCache = JSON.parse(JSON.stringify(this.defaultConfig));
      }
      
      // Save to store
      await this._saveConfigToStore();
      
      // Notify about the reset
      if (this.eventBus) {
        this.eventBus.publish('config:reset', {
          section,
          timestamp: new Date().toISOString()
        });
      }
      
      return true;
    } catch (error) {
      console.error(`Error resetting config:`, error);
      return false;
    }
  }
  
  /**
   * Get all configuration
   * @returns {Promise<Object>} Complete configuration
   */
  async getAllConfig() {
    if (!this.configCache) {
      await this._loadConfigFromStore();
    }
    
    return JSON.parse(JSON.stringify(this.configCache));
  }
  
  /**
   * Handle settings update event
   * @param {Object} event - Settings update event
   */
  async handleSettingsUpdate(event) {
    try {
      console.log('Received settings update event:', event);
      
      // If the categories array is present, update corresponding config sections
      if (Array.isArray(event.categories)) {
        const needsSave = event.categories.some(category => this._updateFromSettings(category));
        
        if (needsSave) {
          await this._saveConfigToStore();
        }
      }
    } catch (error) {
      console.error('Error handling settings update:', error);
    }
  }
  
  /**
   * Update configuration from settings for a specific category
   * @private
   * @param {string} category - Settings category
   * @returns {boolean} True if changes were made
   */
  _updateFromSettings(category) {
    if (!this.configCache || !category) return false;
    
    try {
      // Get settings from localStorage for now
      // In a production implementation, this would come from the settings service
      const settingsJson = localStorage.getItem('primeosSettings');
      if (!settingsJson) return false;
      
      const settings = JSON.parse(settingsJson);
      let changed = false;
      
      if (settings[category] && this.configCache[category]) {
        // Update matching properties
        Object.keys(settings[category]).forEach(key => {
          if (this.configCache[category][key] !== settings[category][key]) {
            this.configCache[category][key] = settings[category][key];
            changed = true;
          }
        });
      }
      
      return changed;
    } catch (error) {
      console.error(`Error updating from settings for ${category}:`, error);
      return false;
    }
  }
  
  /**
   * Get a sensitive configuration value from the secure vault
   * @param {string} key - Configuration key
   * @returns {Promise<string|null>} Configuration value or null if not found
   */
  async getSecureConfig(key) {
    if (!this.secureVault) {
      console.warn('Secure vault not available');
      return null;
    }
    
    try {
      return await this.secureVault.getSecret(key);
    } catch (error) {
      console.error(`Error getting secure config ${key}:`, error);
      return null;
    }
  }
  
  /**
   * Set a sensitive configuration value in the secure vault
   * @param {string} key - Configuration key
   * @param {string} value - Value to set
   * @param {Object} [metadata={}] - Additional metadata
   * @returns {Promise<boolean>} Success indicator
   */
  async setSecureConfig(key, value, metadata = {}) {
    if (!this.secureVault) {
      console.warn('Secure vault not available');
      return false;
    }
    
    try {
      return await this.secureVault.setSecret(key, value, metadata);
    } catch (error) {
      console.error(`Error setting secure config ${key}:`, error);
      return false;
    }
  }
  
  /**
   * Load configuration from store
   * @private
   * @returns {Promise<void>}
   */
  async _loadConfigFromStore() {
    try {
      // Skip if no store is available
      if (!this.store) {
        this.configCache = JSON.parse(JSON.stringify(this.defaultConfig));
        return;
      }
      
      // Load config from store
      const config = await this.store.get(this.systemConfigKey);
      
      if (!config) {
        // Initialize with defaults
        this.configCache = JSON.parse(JSON.stringify(this.defaultConfig));
        await this._saveConfigToStore();
        return;
      }
      
      // Merge with defaults to ensure all properties exist
      const mergedConfig = JSON.parse(JSON.stringify(this.defaultConfig));
      
      // Recursively merge stored config into defaults
      const mergeObjects = (target, source) => {
        for (const key in source) {
          if (source[key] && typeof source[key] === 'object' && !Array.isArray(source[key])) {
            if (!target[key]) target[key] = {};
            mergeObjects(target[key], source[key]);
          } else {
            target[key] = source[key];
          }
        }
      };
      
      mergeObjects(mergedConfig, config.data);
      this.configCache = mergedConfig;
      
      // Validate coherence
      if (this.coherence && !this._validateCoherence(this.configCache)) {
        console.warn('Coherence check failed when loading configuration');
        // In a real implementation, this would trigger a recovery process
      }
    } catch (error) {
      console.error('Failed to load configuration from store:', error);
      this.configCache = JSON.parse(JSON.stringify(this.defaultConfig));
    }
  }
  
  /**
   * Save configuration to store
   * @private
   * @returns {Promise<void>}
   */
  async _saveConfigToStore() {
    try {
      // Skip if no store is available
      if (!this.store) {
        return;
      }
      
      // Create config data object
      const configData = {
        id: this.systemConfigKey,
        type: 'system_configuration',
        data: this.configCache,
        modified: new Date().toISOString()
      };
      
      // Save to store
      await this.store.put(configData);
    } catch (error) {
      console.error('Failed to save configuration to store:', error);
      throw error;
    }
  }
  
  /**
   * Validate coherence of configuration data
   * @private
   * @param {Object} config - Configuration to validate
   * @returns {boolean} Coherence validation result
   */
  _validateCoherence(config) {
    if (!this.coherence) {
      return true; // Skip validation if coherence not available
    }
    
    try {
      // In a full implementation, this would use the Coherence system
      // to validate the mathematical coherence of the configuration structure
      
      // For now, just perform basic structural validation
      if (!config || typeof config !== 'object') {
        return false;
      }
      
      // Check required sections exist
      const requiredSections = ['system', 'appearance', 'security'];
      for (const section of requiredSections) {
        if (!config[section] || typeof config[section] !== 'object') {
          return false;
        }
      }
      
      return true;
    } catch (error) {
      console.error('Coherence validation error:', error);
      return false;
    }
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { ConfigurationManager };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.ConfigurationManager = ConfigurationManager;
}