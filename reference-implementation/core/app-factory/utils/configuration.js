/**
 * PrimeOS App Factory - Configuration Management
 * 
 * Handles App Factory configuration, user preferences, and API key management.
 * Integrates with PrimeOS user preference system.
 */

class AppFactoryConfig {
  /**
   * Create a new configuration manager
   * @param {Object} store - PrimeStore instance
   * @param {Object} options - Configuration options
   * @param {string} options.userId - Current user ID
   * @param {Object} options.eventBus - Event bus for notifications
   */
  constructor(store, options = {}) {
    if (!store) {
      throw new Error('AppFactoryConfig requires a store instance');
    }
    
    this.store = store;
    this.userId = options.userId || 'default';
    this.eventBus = options.eventBus || null;
    this.preferencesKey = `user_preferences_${this.userId}`;
    
    console.log('AppFactoryConfig initialized');
  }
  
  /**
   * Set user ID
   * @param {string} userId - User ID
   */
  setUserId(userId) {
    if (!userId) {
      throw new Error('User ID is required');
    }
    
    this.userId = userId;
    this.preferencesKey = `user_preferences_${userId}`;
  }
  
  /**
   * Get App Factory preferences
   * @returns {Promise<Object>} App Factory preferences
   */
  async getPreferences() {
    try {
      const userPrefs = await this.store.get('system', this.preferencesKey) || {};
      
      // Return App Factory specific preferences with defaults
      return {
        apiKey: userPrefs.appFactory?.apiKey || '',
        templates: userPrefs.appFactory?.templates || 'default',
        defaultPublishTarget: userPrefs.appFactory?.defaultPublishTarget || 'local',
        githubUsername: userPrefs.appFactory?.githubUsername || '',
        githubToken: userPrefs.appFactory?.githubToken || '',
        apiKeyRotation: userPrefs.appFactory?.apiKeyRotation || false,
        apiUsageQuota: userPrefs.appFactory?.apiUsageQuota || 100,
        showPromptReview: userPrefs.appFactory?.showPromptReview || false,
        localOnlyMode: userPrefs.appFactory?.localOnlyMode || false,
        ...userPrefs.appFactory
      };
    } catch (error) {
      console.error('Failed to get App Factory preferences:', error);
      
      // Return defaults on error
      return {
        apiKey: '',
        templates: 'default',
        defaultPublishTarget: 'local',
        githubUsername: '',
        githubToken: '',
        apiKeyRotation: false,
        apiUsageQuota: 100,
        showPromptReview: false,
        localOnlyMode: false
      };
    }
  }
  
  /**
   * Save App Factory preferences
   * @param {Object} appFactoryPrefs - App Factory preferences to save
   * @returns {Promise<Object>} Updated preferences
   */
  async savePreferences(appFactoryPrefs) {
    if (!appFactoryPrefs) {
      throw new Error('Preferences are required');
    }
    
    try {
      // Get existing user preferences
      const userPrefs = await this.store.get('system', this.preferencesKey) || {};
      
      // Update only App Factory section
      userPrefs.appFactory = {
        ...userPrefs.appFactory,
        ...appFactoryPrefs
      };
      
      // Save updated preferences
      await this.store.put('system', this.preferencesKey, userPrefs);
      
      // Notify of preferences update
      if (this.eventBus) {
        this.eventBus.publish('app-factory:preferences-updated', {
          userId: this.userId,
          preferences: userPrefs.appFactory
        });
      }
      
      return userPrefs.appFactory;
    } catch (error) {
      console.error('Failed to save App Factory preferences:', error);
      throw error;
    }
  }
  
  /**
   * Get Claude API key
   * @returns {Promise<string>} API key
   */
  async getApiKey() {
    const prefs = await this.getPreferences();
    return prefs.apiKey || '';
  }
  
  /**
   * Save Claude API key
   * @param {string} apiKey - API key
   * @returns {Promise<Object>} Updated preferences
   */
  async saveApiKey(apiKey) {
    if (!apiKey) {
      throw new Error('API key is required');
    }
    
    return this.savePreferences({ apiKey });
  }
  
  /**
   * Get GitHub credentials
   * @returns {Promise<Object>} GitHub credentials
   */
  async getGitHubCredentials() {
    const prefs = await this.getPreferences();
    
    return {
      username: prefs.githubUsername || '',
      token: prefs.githubToken || ''
    };
  }
  
  /**
   * Save GitHub credentials
   * @param {Object} credentials - GitHub credentials
   * @param {string} credentials.username - GitHub username
   * @param {string} credentials.token - GitHub token
   * @returns {Promise<Object>} Updated preferences
   */
  async saveGitHubCredentials(credentials) {
    if (!credentials) {
      throw new Error('Credentials are required');
    }
    
    return this.savePreferences({
      githubUsername: credentials.username,
      githubToken: credentials.token
    });
  }
  
  /**
   * Get template preference
   * @returns {Promise<string>} Template preference
   */
  async getTemplatePreference() {
    const prefs = await this.getPreferences();
    return prefs.templates || 'default';
  }
  
  /**
   * Save template preference
   * @param {string} template - Template preference
   * @returns {Promise<Object>} Updated preferences
   */
  async saveTemplatePreference(template) {
    if (!template) {
      throw new Error('Template preference is required');
    }
    
    return this.savePreferences({ templates: template });
  }
  
  /**
   * Track API usage
   * @param {string} operation - Operation performed
   * @param {number} tokens - Tokens used
   * @returns {Promise<Object>} Updated usage data
   */
  async trackApiUsage(operation, tokens) {
    try {
      // Get current usage data
      const usageKey = `app_factory_api_usage_${this.userId}`;
      const currentUsage = await this.store.get('system', usageKey) || {
        total: 0,
        operations: {},
        history: []
      };
      
      // Update usage data
      const timestamp = new Date();
      currentUsage.total += tokens;
      
      // Update operation-specific usage
      if (!currentUsage.operations[operation]) {
        currentUsage.operations[operation] = 0;
      }
      currentUsage.operations[operation] += tokens;
      
      // Add to usage history
      currentUsage.history.push({
        timestamp,
        operation,
        tokens
      });
      
      // Trim history if getting too large (keep last 100 entries)
      if (currentUsage.history.length > 100) {
        currentUsage.history = currentUsage.history.slice(-100);
      }
      
      // Save updated usage data
      await this.store.put('system', usageKey, currentUsage);
      
      // Get usage quota
      const prefs = await this.getPreferences();
      const quotaPercent = (currentUsage.total / prefs.apiUsageQuota) * 100;
      
      // Notify of approaching quota if over 80%
      if (quotaPercent > 80 && this.eventBus) {
        this.eventBus.publish('app-factory:api-quota-warning', {
          userId: this.userId,
          percentUsed: quotaPercent,
          total: currentUsage.total,
          quota: prefs.apiUsageQuota
        });
      }
      
      return currentUsage;
    } catch (error) {
      console.error('Failed to track API usage:', error);
      return null;
    }
  }
  
  /**
   * Get API usage data
   * @returns {Promise<Object>} API usage data
   */
  async getApiUsage() {
    try {
      const usageKey = `app_factory_api_usage_${this.userId}`;
      return await this.store.get('system', usageKey) || { total: 0, operations: {}, history: [] };
    } catch (error) {
      console.error('Failed to get API usage data:', error);
      return { total: 0, operations: {}, history: [] };
    }
  }
  
  /**
   * Reset API usage data
   * @returns {Promise<boolean>} Success indicator
   */
  async resetApiUsage() {
    try {
      const usageKey = `app_factory_api_usage_${this.userId}`;
      await this.store.delete('system', usageKey);
      return true;
    } catch (error) {
      console.error('Failed to reset API usage data:', error);
      return false;
    }
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { AppFactoryConfig };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.AppFactoryConfig = AppFactoryConfig;
}