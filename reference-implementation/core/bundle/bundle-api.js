/**
 * PrimeOS App Bundle API
 * 
 * Provides a standardized interface for applications to interact with
 * the PrimeOS bundling system. This API enables applications to:
 * 
 * 1. List available bundles
 * 2. Install/uninstall bundles
 * 3. Import/export bundles
 * 4. Create bundles from applications
 */

/**
 * BundleAPI class for application bundle management
 */
class BundleAPI {
  /**
   * Create a new Bundle API instance
   * @param {Object} options - Configuration options
   * @param {BundleManager} options.bundleManager - BundleManager instance
   * @param {Object} options.eventBus - Event bus for inter-component communication
   * @param {Object} options.appId - ID of the app using this API
   */
  constructor(options) {
    // Validate required parameters
    if (!options.bundleManager) {
      throw new Error('BundleAPI requires a bundleManager instance');
    }
    
    if (!options.eventBus) {
      throw new Error('BundleAPI requires an eventBus instance');
    }
    
    if (!options.appId) {
      throw new Error('BundleAPI requires an appId');
    }
    
    // Store dependencies
    this.bundleManager = options.bundleManager;
    this.eventBus = options.eventBus;
    this.appId = options.appId;
    
    // Bind methods
    this._handleBundleEvents = this._handleBundleEvents.bind(this);
    
    // Subscribe to bundle events
    this.eventBus.subscribe('bundle:imported', this._handleBundleEvents);
    this.eventBus.subscribe('bundle:uninstalled', this._handleBundleEvents);
    
    console.log(`BundleAPI initialized for app: ${this.appId}`);
  }
  
  /**
   * Handle bundle-related events
   * @private
   * @param {Object} eventData - Event data
   */
  _handleBundleEvents(eventData) {
    // Process bundle events as needed
    console.log(`Bundle event received by ${this.appId}:`, eventData);
  }
  
  /**
   * Get a list of all available bundles from connected remotes
   * @param {Object} filter - Filter criteria
   * @returns {Promise<Array>} List of available bundles
   */
  async getAvailableBundles(filter = {}) {
    try {
      return await this.bundleManager.queryAvailableBundles(filter);
    } catch (error) {
      console.error('Failed to get available bundles:', error);
      return [];
    }
  }
  
  /**
   * Get a list of all locally installed bundles
   * @returns {Promise<Array>} List of installed bundles
   */
  async getLocallyInstalledBundles() {
    try {
      return await this.bundleManager.getInstalledBundles();
    } catch (error) {
      console.error('Failed to get installed bundles:', error);
      return [];
    }
  }
  
  /**
   * Install a bundle from a specified remote
   * @param {string} bundleId - Bundle ID to install
   * @param {string} remoteUrl - Remote source URL (optional, uses default if not provided)
   * @returns {Promise<Object>} Installation result
   */
  async installBundle(bundleId, remoteUrl) {
    try {
      // If remote URL is provided, use it
      if (remoteUrl) {
        return await this.bundleManager.installBundleFromRemote(bundleId, remoteUrl);
      }
      
      // Otherwise, find the bundle in available remotes
      const availableBundles = await this.getAvailableBundles();
      const bundleInfo = availableBundles.find(bundle => bundle.id === bundleId);
      
      if (!bundleInfo || !bundleInfo.remoteUrl) {
        throw new Error(`Bundle ${bundleId} not found in available bundles`);
      }
      
      return await this.bundleManager.installBundleFromRemote(bundleId, bundleInfo.remoteUrl);
    } catch (error) {
      console.error(`Failed to install bundle ${bundleId}:`, error);
      return {
        success: false,
        error: error.message
      };
    }
  }
  
  /**
   * Uninstall a bundle
   * @param {string} bundleId - Bundle ID to uninstall
   * @returns {Promise<Object>} Uninstallation result
   */
  async uninstallBundle(bundleId) {
    try {
      const success = await this.bundleManager.uninstallBundle(bundleId);
      
      return {
        success,
        bundleId
      };
    } catch (error) {
      console.error(`Failed to uninstall bundle ${bundleId}:`, error);
      return {
        success: false,
        error: error.message
      };
    }
  }
  
  /**
   * Import a bundle from local data
   * @param {Object} bundleData - Bundle data to import
   * @param {Object} options - Import options
   * @returns {Promise<Object>} Import result
   */
  async importBundle(bundleData, options = {}) {
    try {
      return await this.bundleManager.importBundle(bundleData, options);
    } catch (error) {
      console.error('Failed to import bundle:', error);
      return {
        success: false,
        error: error.message
      };
    }
  }
  
  /**
   * Import a bundle from a File object
   * @param {File} file - File object containing the bundle
   * @param {Object} options - Import options
   * @returns {Promise<Object>} Import result
   */
  async importBundleFromFile(file, options = {}) {
    try {
      // Read the file contents
      const bundleData = await this._readBundleFile(file);
      
      // Import the bundle
      return await this.importBundle(bundleData, options);
    } catch (error) {
      console.error('Failed to import bundle from file:', error);
      return {
        success: false,
        error: error.message
      };
    }
  }
  
  /**
   * Read a bundle file and parse its contents
   * @private
   * @param {File} file - Bundle file
   * @returns {Promise<Object>} Parsed bundle data
   */
  async _readBundleFile(file) {
    return new Promise((resolve, reject) => {
      const reader = new FileReader();
      
      reader.onload = function(event) {
        try {
          const bundleData = JSON.parse(event.target.result);
          resolve(bundleData);
        } catch (error) {
          reject(new Error('Invalid bundle format: ' + error.message));
        }
      };
      
      reader.onerror = function() {
        reject(new Error('Failed to read bundle file'));
      };
      
      reader.readAsText(file);
    });
  }
  
  /**
   * Export a bundle for the specified app
   * @param {string} appId - App ID to export
   * @param {Object} options - Export options
   * @returns {Promise<Object>} Export result with bundle data
   */
  async exportBundle(appId, options = {}) {
    try {
      const format = options.format || 'json';
      const bundle = await this.bundleManager.exportBundle(appId, format);
      
      return {
        success: true,
        bundle,
        format
      };
    } catch (error) {
      console.error(`Failed to export bundle for ${appId}:`, error);
      return {
        success: false,
        error: error.message
      };
    }
  }
  
  /**
   * Save a bundle to a file
   * @param {Object} bundle - Bundle data
   * @param {string} filename - Filename to save as
   */
  saveBundleToFile(bundle, filename) {
    try {
      // Convert bundle to JSON string
      const bundleStr = JSON.stringify(bundle, null, 2);
      
      // Create blob and download link
      const blob = new Blob([bundleStr], { type: 'application/json' });
      const url = URL.createObjectURL(blob);
      
      // Create and trigger download
      const a = document.createElement('a');
      a.href = url;
      a.download = filename || `${bundle.manifest.id}.bundle.json`;
      a.style.display = 'none';
      document.body.appendChild(a);
      a.click();
      
      // Clean up
      setTimeout(() => {
        document.body.removeChild(a);
        URL.revokeObjectURL(url);
      }, 100);
      
      return true;
    } catch (error) {
      console.error('Failed to save bundle to file:', error);
      return false;
    }
  }
  
  /**
   * Create a bundle for the specified app
   * @param {string} appId - App ID to bundle
   * @param {Object} options - Bundling options
   * @returns {Promise<Object>} Creation result with bundle data
   */
  async createBundle(appId, options = {}) {
    try {
      const bundle = await this.bundleManager.createBundle(appId, options);
      
      return {
        success: true,
        bundle
      };
    } catch (error) {
      console.error(`Failed to create bundle for ${appId}:`, error);
      return {
        success: false,
        error: error.message
      };
    }
  }
  
  /**
   * Get detailed information about a specific bundle
   * @param {string} bundleId - Bundle ID
   * @returns {Promise<Object>} Bundle information
   */
  async getBundleInfo(bundleId) {
    try {
      const bundleInfo = await this.bundleManager.getBundleMetadata(bundleId);
      
      if (!bundleInfo) {
        return {
          success: false,
          error: `Bundle ${bundleId} not found`
        };
      }
      
      return {
        success: true,
        bundle: bundleInfo
      };
    } catch (error) {
      console.error(`Failed to get info for bundle ${bundleId}:`, error);
      return {
        success: false,
        error: error.message
      };
    }
  }
  
  /**
   * Connect to a remote bundle repository
   * @param {string} remoteUrl - Remote URL
   * @param {Object} options - Connection options
   * @returns {Promise<Object>} Connection result
   */
  async connectToRemote(remoteUrl, options = {}) {
    try {
      const remote = await this.bundleManager.connectToRemote(remoteUrl, options);
      
      return {
        success: true,
        remote: {
          url: remoteUrl,
          type: remote.constructor.name
        }
      };
    } catch (error) {
      console.error(`Failed to connect to remote ${remoteUrl}:`, error);
      return {
        success: false,
        error: error.message
      };
    }
  }
  
  /**
   * Register an app to make it available for bundling
   * @param {Object} appInfo - App information
   * @param {Object} options - Registration options
   * @returns {Promise<Object>} Registration result
   */
  async registerApp(appInfo, options = {}) {
    try {
      // Validate app info
      if (!appInfo.id || !appInfo.name || !appInfo.version) {
        throw new Error('App registration requires id, name, and version');
      }
      
      // Create app record with metadata
      const appRecord = {
        id: appInfo.id,
        type: 'app',
        name: appInfo.name,
        version: appInfo.version,
        author: appInfo.author || 'Unknown',
        description: appInfo.description || '',
        entryPoint: appInfo.entryPoint || 'index.js',
        permissions: options.permissions || [],
        tags: options.tags || [],
        registered: new Date().toISOString(),
        bundleable: true
      };
      
      // Add to store
      await this.bundleManager.store.put(appRecord);
      
      return {
        success: true,
        appId: appInfo.id
      };
    } catch (error) {
      console.error(`Failed to register app ${appInfo.id}:`, error);
      return {
        success: false,
        error: error.message
      };
    }
  }
  
  /**
   * Cleanup resources when API is no longer needed
   */
  dispose() {
    // Unsubscribe from bundle events
    this.eventBus.unsubscribe('bundle:imported', this._handleBundleEvents);
    this.eventBus.unsubscribe('bundle:uninstalled', this._handleBundleEvents);
    
    console.log(`BundleAPI disposed for app: ${this.appId}`);
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { BundleAPI };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.BundleAPI = BundleAPI;
}