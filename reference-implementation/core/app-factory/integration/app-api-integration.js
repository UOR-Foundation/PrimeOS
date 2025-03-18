/**
 * PrimeOS App Factory - AppAPI Integration
 * 
 * Integrates the App Factory with the PrimeOS AppAPI for
 * application lifecycle management and system services.
 */

class AppFactoryAppAPIIntegration {
  /**
   * Create a new AppAPI integration instance
   * @param {Object} appAPI - AppAPI instance
   * @param {Object} options - Configuration options
   * @param {Object} options.eventBus - Event bus for notifications
   */
  constructor(appAPI, options = {}) {
    if (!appAPI) {
      throw new Error('AppFactoryAppAPIIntegration requires an appAPI instance');
    }
    
    this.appAPI = appAPI;
    this.eventBus = options.eventBus || null;
    
    // Register lifecycle hooks
    this._registerLifecycleHooks();
    
    console.log('AppFactoryAppAPIIntegration initialized');
  }
  
  /**
   * Register App Factory lifecycle hooks
   * @private
   */
  _registerLifecycleHooks() {
    // Register onFocus hook
    this.appAPI.onFocus(() => {
      console.log('App Factory focused');
      if (this.eventBus) {
        this.eventBus.publish('app-factory:focused');
      }
    });
    
    // Register onBlur hook
    this.appAPI.onBlur(() => {
      console.log('App Factory blurred');
      if (this.eventBus) {
        this.eventBus.publish('app-factory:blurred');
      }
    });
    
    // Register onResize hook
    this.appAPI.onResize((dimensions) => {
      console.log('App Factory resized:', dimensions);
      if (this.eventBus) {
        this.eventBus.publish('app-factory:resized', dimensions);
      }
    });
    
    // Register onSuspend hook
    this.appAPI.onSuspend(() => {
      console.log('App Factory suspended');
      if (this.eventBus) {
        this.eventBus.publish('app-factory:suspended');
      }
      
      // Save any pending work
      this._savePendingWork();
    });
    
    // Register onResume hook
    this.appAPI.onResume(() => {
      console.log('App Factory resumed');
      if (this.eventBus) {
        this.eventBus.publish('app-factory:resumed');
      }
      
      // Restore application state
      this._restoreState();
    });
    
    // Register onBeforeClose hook
    this.appAPI.onBeforeClose(async () => {
      console.log('App Factory before close');
      
      // Check for unsaved work
      const hasUnsavedWork = await this._checkUnsavedWork();
      
      if (hasUnsavedWork) {
        // Prompt user to save
        const shouldSave = await this.appAPI.showDialog({
          type: 'confirm',
          title: 'Unsaved Changes',
          message: 'You have unsaved changes. Would you like to save before closing?',
          buttons: ['Save', 'Discard', 'Cancel']
        });
        
        if (shouldSave === 'Save') {
          // Save changes
          await this._savePendingWork();
          return true; // Allow close
        } else if (shouldSave === 'Discard') {
          return true; // Allow close without saving
        } else {
          return false; // Prevent close
        }
      }
      
      return true; // Allow close
    });
    
    // Register onClose hook
    this.appAPI.onClose(() => {
      console.log('App Factory closed');
      if (this.eventBus) {
        this.eventBus.publish('app-factory:closed');
      }
    });
  }
  
  /**
   * Get current user
   * @returns {Promise<Object>} User information
   */
  async getCurrentUser() {
    try {
      return await this.appAPI.getCurrentUser();
    } catch (error) {
      console.error('Failed to get current user:', error);
      return null;
    }
  }
  
  /**
   * Show dialog
   * @param {Object} options - Dialog options
   * @returns {Promise<string>} User selection
   */
  async showDialog(options) {
    try {
      return await this.appAPI.showDialog(options);
    } catch (error) {
      console.error('Failed to show dialog:', error);
      throw error;
    }
  }
  
  /**
   * Show notification
   * @param {Object} options - Notification options
   * @returns {Promise<string>} Notification ID
   */
  async showNotification(options) {
    try {
      return await this.appAPI.showNotification(options);
    } catch (error) {
      console.error('Failed to show notification:', error);
      throw error;
    }
  }
  
  /**
   * Save App Factory preferences
   * @param {Object} preferences - Preferences to save
   * @returns {Promise<boolean>} Success indicator
   */
  async savePreferences(preferences) {
    try {
      await this.appAPI.savePreferences(preferences);
      return true;
    } catch (error) {
      console.error('Failed to save preferences:', error);
      return false;
    }
  }
  
  /**
   * Load App Factory preferences
   * @returns {Promise<Object>} Loaded preferences
   */
  async loadPreferences() {
    try {
      return await this.appAPI.loadPreferences();
    } catch (error) {
      console.error('Failed to load preferences:', error);
      return {};
    }
  }
  
  /**
   * Check for unsaved work
   * @private
   * @returns {Promise<boolean>} Whether there is unsaved work
   */
  async _checkUnsavedWork() {
    // Publish event to check for unsaved work
    if (this.eventBus) {
      const result = await new Promise(resolve => {
        const eventId = `app-factory:check-unsaved-work-${Date.now()}`;
        
        // Set up one-time listener for response
        const unsubscribe = this.eventBus.subscribe('app-factory:unsaved-work-result', (data) => {
          if (data.eventId === eventId) {
            unsubscribe();
            resolve(data.hasUnsavedWork);
          }
        });
        
        // Ask components to check for unsaved work
        this.eventBus.publish('app-factory:check-unsaved-work', { eventId });
        
        // Set timeout to resolve after 500ms if no response
        setTimeout(() => {
          unsubscribe();
          resolve(false);
        }, 500);
      });
      
      return result;
    }
    
    return false;
  }
  
  /**
   * Save pending work
   * @private
   * @returns {Promise<boolean>} Success indicator
   */
  async _savePendingWork() {
    // Publish event to save pending work
    if (this.eventBus) {
      const result = await new Promise(resolve => {
        const eventId = `app-factory:save-pending-work-${Date.now()}`;
        
        // Set up one-time listener for response
        const unsubscribe = this.eventBus.subscribe('app-factory:save-work-result', (data) => {
          if (data.eventId === eventId) {
            unsubscribe();
            resolve(data.success);
          }
        });
        
        // Ask components to save pending work
        this.eventBus.publish('app-factory:save-pending-work', { eventId });
        
        // Set timeout to resolve after 1000ms if no response
        setTimeout(() => {
          unsubscribe();
          resolve(true);
        }, 1000);
      });
      
      return result;
    }
    
    return true;
  }
  
  /**
   * Restore application state
   * @private
   * @returns {Promise<boolean>} Success indicator
   */
  async _restoreState() {
    // Publish event to restore state
    if (this.eventBus) {
      this.eventBus.publish('app-factory:restore-state');
    }
    
    return true;
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { AppFactoryAppAPIIntegration };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.AppFactoryAppAPIIntegration = AppFactoryAppAPIIntegration;
}