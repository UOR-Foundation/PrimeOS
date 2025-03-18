/**
 * PrimeOS BundleManager
 * 
 * Manages the lifecycle of Prime Bundles including creation, validation,
 * storage, and deployment. Handles the bundle structure and integrity.
 */

class BundleManager {
  /**
   * Creates a new BundleManager instance
   * @param {Object} options - Configuration options
   * @param {Object} options.store - PrimeStore instance for bundle persistence
   * @param {Object} options.coherenceEngine - CoherenceEngine for validation
   * @param {Object} options.eventBus - Event bus for notifications
   */
  constructor(options = {}) {
    if (!options.store) {
      throw new Error('BundleManager requires a store instance');
    }
    
    this.store = options.store;
    this.coherenceEngine = options.coherenceEngine;
    this.eventBus = options.eventBus;
    
    // Initialize bundle templates
    this.bundleTemplate = {
      manifest: {
        version: '1.0.0',
        coherenceScore: 0,
        permissions: [],
        dependencies: {},
        primeIntegrations: []
      },
      assets: {},
      components: {},
      models: {},
      services: {},
      views: {},
      tests: {},
      docs: {}
    };
    
    console.log('BundleManager initialized');
  }
  
  /**
   * Create a new empty bundle with basic structure
   * @param {string} bundleId - Unique identifier for the bundle
   * @param {Object} initialData - Initial bundle data
   * @returns {Promise<Object>} The created bundle
   */
  async createBundle(bundleId, initialData = {}) {
    if (!bundleId) {
      throw new Error('Bundle ID is required');
    }
    
    console.log(`Creating new bundle: ${bundleId}`);
    
    try {
      // Generate a unique record ID for storage
      const recordId = `bundle_${bundleId}_${Date.now()}`;
      
      // Create initial bundle structure
      const bundle = {
        id: recordId,
        bundleId,
        type: 'prime_bundle',
        created: new Date().toISOString(),
        modified: new Date().toISOString(),
        ...this._createBundleStructure(bundleId, initialData)
      };
      
      // Save to storage
      await this.store.put(bundle);
      
      // Notify creation
      this._notifyBundleEvent('created', bundleId);
      
      return bundle;
    } catch (error) {
      console.error(`Failed to create bundle ${bundleId}:`, error);
      throw error;
    }
  }
  
  /**
   * Load a bundle from storage
   * @param {string} bundleId - Bundle identifier
   * @returns {Promise<Object>} The loaded bundle
   */
  async loadBundle(bundleId) {
    if (!bundleId) {
      throw new Error('Bundle ID is required');
    }
    
    console.log(`Loading bundle: ${bundleId}`);
    
    try {
      // Query for the bundle by bundleId
      const bundles = await this.store.query({
        index: 'bundleId',
        value: bundleId,
        type: 'prime_bundle'
      });
      
      if (!bundles || bundles.length === 0) {
        throw new Error(`Bundle not found: ${bundleId}`);
      }
      
      // Get the most recent version if multiple exist
      const bundle = bundles.sort((a, b) => {
        return new Date(b.modified) - new Date(a.modified);
      })[0];
      
      // Notify load
      this._notifyBundleEvent('loaded', bundleId);
      
      return bundle;
    } catch (error) {
      console.error(`Failed to load bundle ${bundleId}:`, error);
      throw error;
    }
  }
  
  /**
   * Update a bundle with new data
   * @param {string} bundleId - Bundle identifier
   * @param {Object} bundleData - Updated bundle data
   * @returns {Promise<Object>} The updated bundle
   */
  async updateBundle(bundleId, bundleData) {
    if (!bundleId) {
      throw new Error('Bundle ID is required');
    }
    
    if (!bundleData) {
      throw new Error('Bundle data is required');
    }
    
    console.log(`Updating bundle: ${bundleId}`);
    
    try {
      // Load the current bundle
      const currentBundle = await this.loadBundle(bundleId);
      
      // Update bundle with new data
      const updatedBundle = {
        ...currentBundle,
        ...bundleData,
        modified: new Date().toISOString()
      };
      
      // Ensure bundle ID remains constant
      updatedBundle.bundleId = bundleId;
      
      // Save to storage
      await this.store.put(updatedBundle);
      
      // Notify update
      this._notifyBundleEvent('updated', bundleId);
      
      return updatedBundle;
    } catch (error) {
      console.error(`Failed to update bundle ${bundleId}:`, error);
      throw error;
    }
  }
  
  /**
   * Add or update a file in the bundle
   * @param {string} bundleId - Bundle identifier
   * @param {string} filePath - Path within the bundle
   * @param {string} content - File content
   * @param {Object} options - Additional file options
   * @returns {Promise<Object>} Updated bundle
   */
  async addBundleFile(bundleId, filePath, content, options = {}) {
    if (!bundleId || !filePath) {
      throw new Error('Bundle ID and file path are required');
    }
    
    console.log(`Adding file ${filePath} to bundle: ${bundleId}`);
    
    try {
      // Load the current bundle
      const bundle = await this.loadBundle(bundleId);
      
      // Determine file category from path
      const category = this._determineFileCategory(filePath);
      
      // Ensure category exists in bundle
      if (!bundle[category]) {
        bundle[category] = {};
      }
      
      // Add file to appropriate category
      const fileName = filePath.split('/').pop();
      bundle[category][fileName] = {
        path: filePath,
        content: typeof content === 'string' ? content : JSON.stringify(content),
        type: options.type || this._determineFileType(filePath),
        generated: options.generated || false,
        modified: new Date().toISOString()
      };
      
      // Update bundle modified timestamp
      bundle.modified = new Date().toISOString();
      
      // Save updated bundle
      await this.store.put(bundle);
      
      // Notify file addition
      this._notifyBundleEvent('file-added', bundleId, { filePath });
      
      return bundle;
    } catch (error) {
      console.error(`Failed to add file ${filePath} to bundle ${bundleId}:`, error);
      throw error;
    }
  }
  
  /**
   * Remove a file from the bundle
   * @param {string} bundleId - Bundle identifier
   * @param {string} filePath - Path within the bundle
   * @returns {Promise<Object>} Updated bundle
   */
  async removeBundleFile(bundleId, filePath) {
    if (!bundleId || !filePath) {
      throw new Error('Bundle ID and file path are required');
    }
    
    console.log(`Removing file ${filePath} from bundle: ${bundleId}`);
    
    try {
      // Load the current bundle
      const bundle = await this.loadBundle(bundleId);
      
      // Determine file category from path
      const category = this._determineFileCategory(filePath);
      
      // Ensure category exists in bundle
      if (!bundle[category]) {
        throw new Error(`Category ${category} not found in bundle`);
      }
      
      // Get the file name from path
      const fileName = filePath.split('/').pop();
      
      // Check if file exists
      if (!bundle[category][fileName]) {
        throw new Error(`File ${fileName} not found in bundle category ${category}`);
      }
      
      // Remove the file
      delete bundle[category][fileName];
      
      // Update bundle modified timestamp
      bundle.modified = new Date().toISOString();
      
      // Save updated bundle
      await this.store.put(bundle);
      
      // Notify file removal
      this._notifyBundleEvent('file-removed', bundleId, { filePath });
      
      return bundle;
    } catch (error) {
      console.error(`Failed to remove file ${filePath} from bundle ${bundleId}:`, error);
      throw error;
    }
  }
  
  /**
   * Validate bundle structure and coherence
   * @param {string} bundleId - Bundle identifier
   * @returns {Promise<Object>} Validation results
   */
  async validateBundle(bundleId) {
    if (!bundleId) {
      throw new Error('Bundle ID is required');
    }
    
    console.log(`Validating bundle: ${bundleId}`);
    
    try {
      // Load the bundle
      const bundle = await this.loadBundle(bundleId);
      
      // Perform basic structure validation
      const structureValidation = this._validateBundleStructure(bundle);
      
      // Check if coherence engine is available for deeper validation
      let coherenceValidation = { valid: true, score: 0.8 };
      if (this.coherenceEngine) {
        coherenceValidation = await this.coherenceEngine.validateBundleCoherence(bundle);
      }
      
      // Combine validation results
      const validationResult = {
        valid: structureValidation.valid && coherenceValidation.valid,
        structureValidation,
        coherenceValidation
      };
      
      // If valid, update coherence score in manifest
      if (validationResult.valid && bundle.manifest) {
        bundle.manifest.coherenceScore = coherenceValidation.metrics?.score || 0.8;
        bundle.modified = new Date().toISOString();
        await this.store.put(bundle);
      }
      
      // Notify validation
      this._notifyBundleEvent('validated', bundleId, {
        valid: validationResult.valid
      });
      
      return validationResult;
    } catch (error) {
      console.error(`Failed to validate bundle ${bundleId}:`, error);
      throw error;
    }
  }
  
  /**
   * Export bundle for deployment
   * @param {string} bundleId - Bundle identifier
   * @returns {Promise<Object>} Deployable bundle package
   */
  async exportBundle(bundleId) {
    if (!bundleId) {
      throw new Error('Bundle ID is required');
    }
    
    console.log(`Exporting bundle: ${bundleId}`);
    
    try {
      // Load the bundle
      const bundle = await this.loadBundle(bundleId);
      
      // Validate before export
      const validation = await this.validateBundle(bundleId);
      if (!validation.valid) {
        throw new Error(`Cannot export invalid bundle: ${bundleId}`);
      }
      
      // Prepare export structure
      const exportBundle = {
        manifest: bundle.manifest,
        code: {},
        resources: {}
      };
      
      // Export manifest
      if (!exportBundle.manifest.id) {
        exportBundle.manifest.id = bundleId;
      }
      
      // Process code files
      const codeCategories = ['components', 'models', 'services', 'views'];
      for (const category of codeCategories) {
        if (bundle[category]) {
          for (const [fileName, file] of Object.entries(bundle[category])) {
            exportBundle.code[file.path] = this._encodeFileContent(file.content);
          }
        }
      }
      
      // Process resource files
      if (bundle.assets) {
        for (const [fileName, file] of Object.entries(bundle.assets)) {
          exportBundle.resources[file.path] = this._encodeFileContent(file.content);
        }
      }
      
      // Generate coherence.json
      if (this.coherenceEngine) {
        const coherenceDoc = this.coherenceEngine.generateCoherenceDoc(bundle, validation.coherenceValidation);
        exportBundle.code['coherence.json'] = this._encodeFileContent(JSON.stringify(coherenceDoc, null, 2));
      }
      
      // Notify export
      this._notifyBundleEvent('exported', bundleId);
      
      return exportBundle;
    } catch (error) {
      console.error(`Failed to export bundle ${bundleId}:`, error);
      throw error;
    }
  }
  
  /**
   * Validate the structure of a bundle
   * @private
   * @param {Object} bundle - Bundle to validate
   * @returns {Object} Validation result
   */
  _validateBundleStructure(bundle) {
    // Check required fields
    const requiredCategories = ['manifest', 'components', 'models', 'services', 'views'];
    const missingCategories = requiredCategories.filter(category => !bundle[category]);
    
    // Check manifest required fields
    const manifestFields = ['id', 'version', 'name', 'entryPoint'];
    const missingManifestFields = bundle.manifest ?
      manifestFields.filter(field => !bundle.manifest[field]) : manifestFields;
    
    // Check for entry point existence
    let entryPointExists = false;
    if (bundle.manifest && bundle.manifest.entryPoint) {
      const category = this._determineFileCategory(bundle.manifest.entryPoint);
      const fileName = bundle.manifest.entryPoint.split('/').pop();
      entryPointExists = bundle[category] && bundle[category][fileName];
    }
    
    // Compile issues
    const issues = [];
    if (missingCategories.length > 0) {
      issues.push(`Missing required bundle categories: ${missingCategories.join(', ')}`);
    }
    
    if (missingManifestFields.length > 0) {
      issues.push(`Missing required manifest fields: ${missingManifestFields.join(', ')}`);
    }
    
    if (!entryPointExists && bundle.manifest && bundle.manifest.entryPoint) {
      issues.push(`Entry point file not found: ${bundle.manifest.entryPoint}`);
    }
    
    return {
      valid: issues.length === 0,
      issues
    };
  }
  
  /**
   * Create the initial bundle structure
   * @private
   * @param {string} bundleId - Bundle identifier
   * @param {Object} initialData - Initial bundle data
   * @returns {Object} Bundle structure
   */
  _createBundleStructure(bundleId, initialData = {}) {
    // Start with template
    const structure = JSON.parse(JSON.stringify(this.bundleTemplate));
    
    // Add manifest data
    structure.manifest = {
      ...structure.manifest,
      id: bundleId,
      name: initialData.name || bundleId,
      description: initialData.description || '',
      author: initialData.author || '',
      entryPoint: initialData.entryPoint || 'views/main.js',
      created: new Date().toISOString()
    };
    
    // Add initial data to structure if provided
    if (initialData.components) structure.components = initialData.components;
    if (initialData.models) structure.models = initialData.models;
    if (initialData.services) structure.services = initialData.services;
    if (initialData.views) structure.views = initialData.views;
    if (initialData.assets) structure.assets = initialData.assets;
    
    return structure;
  }
  
  /**
   * Determine file category from path
   * @private
   * @param {string} filePath - File path
   * @returns {string} Category name
   */
  _determineFileCategory(filePath) {
    const path = filePath.toLowerCase();
    
    if (path.includes('/assets/') || path.startsWith('assets/')) {
      return 'assets';
    } else if (path.includes('/components/') || path.startsWith('components/')) {
      return 'components';
    } else if (path.includes('/models/') || path.startsWith('models/')) {
      return 'models';
    } else if (path.includes('/services/') || path.startsWith('services/')) {
      return 'services';
    } else if (path.includes('/views/') || path.startsWith('views/')) {
      return 'views';
    } else if (path.includes('/tests/') || path.startsWith('tests/')) {
      return 'tests';
    } else if (path.includes('/docs/') || path.startsWith('docs/')) {
      return 'docs';
    }
    
    // Default to components if can't determine
    return 'components';
  }
  
  /**
   * Determine file type from path
   * @private
   * @param {string} filePath - File path
   * @returns {string} File type
   */
  _determineFileType(filePath) {
    const extension = filePath.split('.').pop().toLowerCase();
    
    switch (extension) {
      case 'js':
        return 'javascript';
      case 'json':
        return 'json';
      case 'css':
        return 'css';
      case 'html':
        return 'html';
      case 'md':
        return 'markdown';
      case 'png':
      case 'jpg':
      case 'jpeg':
      case 'gif':
      case 'svg':
        return 'image';
      default:
        return 'text';
    }
  }
  
  /**
   * Encode file content for storage
   * @private
   * @param {string} content - File content
   * @returns {string} Encoded content
   */
  _encodeFileContent(content) {
    // For text content, use base64 encoding
    try {
      return btoa(content);
    } catch (error) {
      // If btoa fails (e.g., binary data), use a different approach
      console.warn('Failed to encode content with btoa, returning as-is');
      return content;
    }
  }
  
  /**
   * Send a bundle event notification
   * @private
   * @param {string} event - Event name
   * @param {string} bundleId - Bundle ID
   * @param {Object} data - Event data
   */
  _notifyBundleEvent(event, bundleId, data = {}) {
    if (this.eventBus) {
      this.eventBus.publish(`bundle:${event}`, {
        bundleId,
        timestamp: new Date().toISOString(),
        ...data
      });
    }
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { BundleManager };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.BundleManager = BundleManager;
}