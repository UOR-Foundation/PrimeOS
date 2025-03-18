/**
 * PrimeOS App Factory - Shell Integration
 * 
 * Integrates the App Factory with the PrimeOS Shell for
 * UI, window management, and app launching.
 */

class AppFactoryShellIntegration {
  /**
   * Create a new shell integration instance
   * @param {Object} shell - Shell instance
   * @param {Object} options - Configuration options
   * @param {Object} options.eventBus - Event bus for notifications
   */
  constructor(shell, options = {}) {
    if (!shell) {
      throw new Error('AppFactoryShellIntegration requires a shell instance');
    }
    
    this.shell = shell;
    this.eventBus = options.eventBus || null;
    this.appFactoryId = 'app-factory';
    this.appFactoryRegistered = false;
    
    // Bind methods
    this._handleAppLaunch = this._handleAppLaunch.bind(this);
    this._handleAppClose = this._handleAppClose.bind(this);
    
    // Register event handlers
    if (this.eventBus) {
      this.eventBus.subscribe('shell:app-launched', this._handleAppLaunch);
      this.eventBus.subscribe('shell:app-closed', this._handleAppClose);
    }
    
    console.log('AppFactoryShellIntegration initialized');
  }
  
  /**
   * Register App Factory with Shell
   * @param {Object} appInfo - App Factory info
   * @returns {Promise<boolean>} Registration success
   */
  async registerAppFactory(appInfo = {}) {
    try {
      // Default app info
      const defaultInfo = {
        id: this.appFactoryId,
        name: 'App Factory',
        description: 'AI-powered application creation',
        icon: '🏭', // Factory emoji
        path: '/reference-implementation/core/app-factory/index.js',
        isSystem: true,
        category: 'development'
      };
      
      // Merge with provided info
      const mergedInfo = { ...defaultInfo, ...appInfo };
      
      // Register with Shell
      await this.shell.registerApp(mergedInfo);
      
      this.appFactoryRegistered = true;
      
      // Notify of successful registration
      if (this.eventBus) {
        this.eventBus.publish('app-factory:registered', {
          appId: this.appFactoryId
        });
      }
      
      return true;
    } catch (error) {
      console.error('Failed to register App Factory with Shell:', error);
      
      // Notify of registration failure
      if (this.eventBus) {
        this.eventBus.publish('app-factory:registration-failed', {
          error: error.message
        });
      }
      
      return false;
    }
  }
  
  /**
   * Launch App Factory
   * @param {Object} options - Launch options
   * @returns {Promise<Object>} Launch result
   */
  async launchAppFactory(options = {}) {
    try {
      // Ensure App Factory is registered
      if (!this.appFactoryRegistered) {
        await this.registerAppFactory();
      }
      
      // Launch App Factory
      const windowId = await this.shell.launchApp(this.appFactoryId, options);
      
      return { windowId };
    } catch (error) {
      console.error('Failed to launch App Factory:', error);
      throw error;
    }
  }
  
  /**
   * Create a new App Factory window for project
   * @param {string} projectId - Project ID
   * @param {string} projectName - Project name
   * @returns {Promise<Object>} Window creation result
   */
  async createProjectWindow(projectId, projectName) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    try {
      // Create window title
      const title = projectName 
        ? `App Factory - ${projectName}`
        : 'App Factory - Project';
      
      // Create window
      const windowId = await this.shell.createWindow({
        title,
        app: this.appFactoryId,
        params: {
          projectId,
          mode: 'project'
        },
        width: 1000,
        height: 800,
        resizable: true,
        maximizable: true,
        minimizable: true,
        centered: true
      });
      
      return { windowId };
    } catch (error) {
      console.error('Failed to create project window:', error);
      throw error;
    }
  }
  
  /**
   * Create a code preview window
   * @param {Object} file - File to preview
   * @param {string} projectId - Project ID
   * @returns {Promise<Object>} Window creation result
   */
  async createCodePreviewWindow(file, projectId) {
    if (!file) {
      throw new Error('File is required');
    }
    
    try {
      // Create window title
      const title = `Preview - ${file.path}`;
      
      // Create window
      const windowId = await this.shell.createWindow({
        title,
        app: this.appFactoryId,
        params: {
          projectId,
          mode: 'preview',
          filePath: file.path
        },
        width: 800,
        height: 600,
        resizable: true,
        maximizable: true,
        minimizable: true
      });
      
      return { windowId };
    } catch (error) {
      console.error('Failed to create code preview window:', error);
      throw error;
    }
  }
  
  /**
   * Update App Factory app list
   * @returns {Promise<boolean>} Success indicator
   */
  async refreshAppList() {
    try {
      // Notify Shell to refresh app list
      this.eventBus.publish('apps:refresh', { source: 'appFactory' });
      
      return true;
    } catch (error) {
      console.error('Failed to refresh app list:', error);
      return false;
    }
  }
  
  /**
   * Handle app launch event
   * @private
   * @param {Object} data - Event data
   */
  _handleAppLaunch(data) {
    // Check if it's the App Factory
    if (data.appId === this.appFactoryId) {
      console.log('App Factory launched:', data);
    }
  }
  
  /**
   * Handle app close event
   * @private
   * @param {Object} data - Event data
   */
  _handleAppClose(data) {
    // Check if it's the App Factory
    if (data.appId === this.appFactoryId) {
      console.log('App Factory closed:', data);
    }
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { AppFactoryShellIntegration };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.AppFactoryShellIntegration = AppFactoryShellIntegration;
}