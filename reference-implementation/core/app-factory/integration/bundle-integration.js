/**
 * PrimeOS App Factory - Bundle System Integration
 * 
 * Integrates the App Factory with the PrimeOS Bundle System for
 * app packaging, importing, exporting, and installation.
 */

class AppFactoryBundleIntegration {
  /**
   * Create a new bundle integration instance
   * @param {Object} bundleManager - BundleManager instance
   * @param {Object} options - Configuration options
   * @param {Object} options.eventBus - Event bus for notifications
   */
  constructor(bundleManager, options = {}) {
    if (!bundleManager) {
      throw new Error('AppFactoryBundleIntegration requires a bundleManager instance');
    }
    
    this.bundleManager = bundleManager;
    this.eventBus = options.eventBus || null;
    
    console.log('AppFactoryBundleIntegration initialized');
  }
  
  /**
   * Import an existing app bundle into App Factory
   * @param {string} bundleId - Bundle ID
   * @returns {Promise<Object>} Import result with files and metadata
   */
  async importBundle(bundleId) {
    if (!bundleId) {
      throw new Error('Bundle ID is required');
    }
    
    try {
      // Get bundle metadata
      const bundle = await this.bundleManager.getBundle(bundleId);
      
      if (!bundle) {
        throw new Error(`Bundle with ID ${bundleId} not found`);
      }
      
      // Extract bundle files
      const files = await this.bundleManager.extractBundleFiles(bundleId);
      
      // Create result object
      const result = {
        bundleId,
        metadata: {
          name: bundle.name,
          description: bundle.description,
          version: bundle.version || '1.0.0',
          manifest: bundle.manifest || {}
        },
        files: files.map(file => ({
          path: file.path,
          content: file.content
        }))
      };
      
      // Notify of successful import
      if (this.eventBus) {
        this.eventBus.publish('app-factory:bundle-imported', {
          bundleId,
          metadata: result.metadata
        });
      }
      
      return result;
    } catch (error) {
      console.error(`Failed to import bundle ${bundleId}:`, error);
      
      // Notify of import failure
      if (this.eventBus) {
        this.eventBus.publish('app-factory:bundle-import-failed', {
          bundleId,
          error: error.message
        });
      }
      
      throw error;
    }
  }
  
  /**
   * Create app bundle from App Factory project
   * @param {Object} project - Project data
   * @param {Array} files - Project files
   * @returns {Promise<string>} Created bundle ID
   */
  async createAppBundle(project, files) {
    if (!project) {
      throw new Error('Project data is required');
    }
    
    if (!Array.isArray(files)) {
      throw new Error('Files array is required');
    }
    
    try {
      // Create manifest
      const manifest = this._generateBundleManifest(project);
      
      // Create bundle
      const bundleId = await this.bundleManager.createBundle({
        name: project.name,
        description: project.description,
        type: 'app',
        files: files,
        manifest: manifest
      });
      
      // Notify of bundle creation
      if (this.eventBus) {
        this.eventBus.publish('app-factory:bundle-created', {
          bundleId,
          projectId: project.id,
          metadata: {
            name: project.name,
            description: project.description
          }
        });
      }
      
      return bundleId;
    } catch (error) {
      console.error('Failed to create app bundle:', error);
      
      // Notify of bundle creation failure
      if (this.eventBus) {
        this.eventBus.publish('app-factory:bundle-creation-failed', {
          projectId: project.id,
          error: error.message
        });
      }
      
      throw error;
    }
  }
  
  /**
   * Install app bundle to local system
   * @param {string} bundleId - Bundle ID
   * @returns {Promise<Object>} Installation result
   */
  async installBundle(bundleId) {
    if (!bundleId) {
      throw new Error('Bundle ID is required');
    }
    
    try {
      // Install bundle
      const result = await this.bundleManager.installBundle(bundleId);
      
      // Notify of successful installation
      if (this.eventBus) {
        this.eventBus.publish('app-factory:bundle-installed', {
          bundleId,
          appId: result.appId
        });
      }
      
      return result;
    } catch (error) {
      console.error(`Failed to install bundle ${bundleId}:`, error);
      
      // Notify of installation failure
      if (this.eventBus) {
        this.eventBus.publish('app-factory:bundle-installation-failed', {
          bundleId,
          error: error.message
        });
      }
      
      throw error;
    }
  }
  
  /**
   * Uninstall app bundle from local system
   * @param {string} bundleId - Bundle ID
   * @returns {Promise<boolean>} Uninstallation success
   */
  async uninstallBundle(bundleId) {
    if (!bundleId) {
      throw new Error('Bundle ID is required');
    }
    
    try {
      // Uninstall bundle
      await this.bundleManager.uninstallBundle(bundleId);
      
      // Notify of successful uninstallation
      if (this.eventBus) {
        this.eventBus.publish('app-factory:bundle-uninstalled', {
          bundleId
        });
      }
      
      return true;
    } catch (error) {
      console.error(`Failed to uninstall bundle ${bundleId}:`, error);
      
      // Notify of uninstallation failure
      if (this.eventBus) {
        this.eventBus.publish('app-factory:bundle-uninstallation-failed', {
          bundleId,
          error: error.message
        });
      }
      
      throw error;
    }
  }
  
  /**
   * Export app bundle
   * @param {string} bundleId - Bundle ID
   * @param {string} format - Export format ('json' or 'binary')
   * @returns {Promise<Object>} Export result
   */
  async exportBundle(bundleId, format = 'json') {
    if (!bundleId) {
      throw new Error('Bundle ID is required');
    }
    
    try {
      // Export bundle
      const result = await this.bundleManager.exportBundle(bundleId, format);
      
      // Notify of successful export
      if (this.eventBus) {
        this.eventBus.publish('app-factory:bundle-exported', {
          bundleId,
          format
        });
      }
      
      return result;
    } catch (error) {
      console.error(`Failed to export bundle ${bundleId}:`, error);
      
      // Notify of export failure
      if (this.eventBus) {
        this.eventBus.publish('app-factory:bundle-export-failed', {
          bundleId,
          error: error.message
        });
      }
      
      throw error;
    }
  }
  
  /**
   * Generate bundle manifest from project data
   * @private
   * @param {Object} project - Project data
   * @returns {Object} Bundle manifest
   */
  _generateBundleManifest(project) {
    // Base manifest
    const manifest = {
      name: project.name,
      description: project.description,
      version: project.version || '1.0.0',
      type: 'primeOS-app',
      createdBy: 'AppFactory',
      createdAt: new Date().toISOString()
    };
    
    // Add App Factory metadata
    manifest.appFactory = {
      projectId: project.id,
      manifestStructure: project.specification?.manifestStructure || {
        meta: { requiredFields: ['name', 'version', 'description'] },
        invariant: { assets: true, staticCode: true },
        variant: { stateModel: 'immutable', persistence: true }
      }
    };
    
    // Add manifold structure if available
    if (project.specification && project.specification.architecture && project.specification.architecture.bases) {
      manifest.bases = project.specification.architecture.bases;
    }
    
    // Add entry point
    manifest.main = 'index.js';
    
    // Add required permissions
    manifest.permissions = [];
    
    // Add app interfaces if available
    if (project.specification && project.specification.appInterfaces) {
      manifest.interfaces = project.specification.appInterfaces;
    }
    
    // Add coherence information if available
    if (project.specification && project.specification.coherence) {
      manifest.coherence = project.specification.coherence;
    }
    
    return manifest;
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { AppFactoryBundleIntegration };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.AppFactoryBundleIntegration = AppFactoryBundleIntegration;
}