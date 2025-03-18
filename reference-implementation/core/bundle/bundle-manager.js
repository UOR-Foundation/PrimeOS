/**
 * PrimeOS App Bundle Manager
 * 
 * Provides functionality for creating, importing, validating, and managing
 * portable PrimeOS application bundles.
 */

/**
 * BundleManager class handles app bundling, import/export, and installation
 */
class BundleManager {
  /**
   * Creates a new BundleManager instance
   * @param {Object} options - Configuration options
   * @param {Object} options.store - PrimeStore instance for bundle data
   * @param {Object} options.eventBus - EventBus for notifications
   * @param {Object} options.identity - Identity service for signatures
   * @param {Object} options.appFactory - Optional App Factory integration
   */
  constructor(options = {}) {
    // Validate required dependencies
    if (!options.store) {
      throw new Error('BundleManager requires a store instance');
    }
    
    if (!options.eventBus) {
      throw new Error('BundleManager requires an eventBus instance');
    }
    
    // Store dependencies
    this.store = options.store;
    this.eventBus = options.eventBus;
    this.identity = options.identity || null;
    this.appFactory = options.appFactory || null;
    
    // Initialize internal state
    this.connectedRemotes = [];
    this.installedBundles = new Map();
    
    // Bind methods
    this._loadInstalledBundles = this._loadInstalledBundles.bind(this);
    this._validateBundleManifest = this._validateBundleManifest.bind(this);
    this._notifyBundleEvent = this._notifyBundleEvent.bind(this);
    
    // Register event handlers
    this.eventBus.subscribe('system:ready', this._loadInstalledBundles);
    
    // Register App Factory events if available
    if (this.appFactory) {
      this.eventBus.subscribe('app-factory:bundle-created', (data) => {
        console.log('App Factory created bundle:', data.bundleId);
      });
    }
    
    console.log('BundleManager initialized');
  }
  
  /**
   * Load metadata for all installed bundles
   * @private
   */
  async _loadInstalledBundles() {
    try {
      // Query all installed bundles from the store
      const bundleRecords = await this.store.query({
        index: 'type',
        value: 'bundle'
      });
      
      // Reset the installed bundles map
      this.installedBundles.clear();
      
      // Populate the map with bundle data
      bundleRecords.forEach(record => {
        this.installedBundles.set(record.id, {
          manifest: record.manifest,
          installed: record.installed,
          enabled: record.enabled !== false
        });
      });
      
      console.log(`Loaded ${this.installedBundles.size} installed bundles`);
    } catch (error) {
      console.error('Failed to load installed bundles:', error);
    }
  }
  
  /**
   * Create a bundle from an installed application
   * @param {string} appId - ID of the application to bundle
   * @param {Object} options - Bundling options
   * @returns {Promise<Object>} The created bundle
   */
  async createBundle(appId, options = {}) {
    if (!appId) {
      throw new Error('App ID is required to create a bundle');
    }
    
    console.log(`Creating bundle for app: ${appId}`);
    
    try {
      // Get app information from the apps store
      const appRecord = await this.store.get(appId);
      
      if (!appRecord) {
        throw new Error(`App not found: ${appId}`);
      }
      
      // Create the bundle manifest
      const manifest = {
        id: appRecord.id,
        name: appRecord.name,
        version: appRecord.version,
        author: appRecord.author || 'Unknown',
        description: appRecord.description || '',
        license: appRecord.license || 'Proprietary',
        entryPoint: appRecord.entryPoint || 'index.js',
        icon: appRecord.icon || null,
        tags: appRecord.tags || [],
        permissions: appRecord.permissions || [],
        dependencies: appRecord.dependencies || {},
        compatibilityVersion: '1.0.0',
        created: new Date().toISOString()
      };
      
      // Collect app code
      const code = await this._collectAppCode(appId);
      
      // Collect app resources
      const resources = await this._collectAppResources(appId);
      
      // Sign the bundle if identity service is available
      if (this.identity && this.identity.isAuthenticated()) {
        manifest.signature = await this._signBundle({
          manifest: { ...manifest, signature: null },
          code,
          resources
        });
      }
      
      // Create the final bundle
      const bundle = {
        manifest,
        code,
        resources
      };
      
      // Notify bundle creation event
      this._notifyBundleEvent('created', bundle.manifest);
      
      return bundle;
    } catch (error) {
      console.error(`Failed to create bundle for ${appId}:`, error);
      throw error;
    }
  }
  
  /**
   * Collect all code files for the specified app
   * @private
   * @param {string} appId - ID of the application
   * @returns {Promise<Object>} Map of file paths to encoded file contents
   */
  async _collectAppCode(appId) {
    try {
      // Get app files from the files store
      const appFiles = await this.store.query({
        index: 'type',
        value: 'file',
        filter: file => file.appId === appId && file.isCode
      });
      
      // Create a map of file paths to encoded content
      const code = {};
      
      for (const file of appFiles) {
        // Base64 encode the file content
        const encodedContent = this._encodeFileContent(file.content, file.encoding);
        code[file.path] = encodedContent;
      }
      
      return code;
    } catch (error) {
      console.error(`Failed to collect code for ${appId}:`, error);
      throw error;
    }
  }
  
  /**
   * Collect all resource files for the specified app
   * @private
   * @param {string} appId - ID of the application
   * @returns {Promise<Object>} Map of resource paths to encoded content
   */
  async _collectAppResources(appId) {
    try {
      // Get app resource files from the files store
      const resourceFiles = await this.store.query({
        index: 'type',
        value: 'file',
        filter: file => file.appId === appId && !file.isCode
      });
      
      // Create a map of resource paths to encoded content
      const resources = {};
      
      for (const file of resourceFiles) {
        // Base64 encode the resource content
        const encodedContent = this._encodeFileContent(file.content, file.encoding);
        resources[file.path] = encodedContent;
      }
      
      return resources;
    } catch (error) {
      console.error(`Failed to collect resources for ${appId}:`, error);
      throw error;
    }
  }
  
  /**
   * Encode file content based on its type
   * @private
   * @param {string|Uint8Array} content - File content
   * @param {string} encoding - Content encoding type
   * @returns {string} Base64-encoded content
   */
  _encodeFileContent(content, encoding) {
    if (encoding === 'base64') {
      // Already base64 encoded
      return content;
    } else if (encoding === 'binary' && content instanceof Uint8Array) {
      // Convert binary data to base64
      const binary = Array.from(content)
        .map(byte => String.fromCharCode(byte))
        .join('');
      return btoa(binary);
    } else {
      // Text content
      return btoa(content);
    }
  }
  
  /**
   * Decode bundle file content based on filename
   * @private
   * @param {string} content - Base64-encoded content
   * @param {string} path - File path
   * @returns {string|Uint8Array} Decoded content
   */
  _decodeFileContent(content, path) {
    // Base64 decode the content
    const decoded = atob(content);
    
    // Check file extension to determine how to handle the content
    const extension = path.split('.').pop().toLowerCase();
    
    // Handle binary files
    const binaryExtensions = ['png', 'jpg', 'jpeg', 'gif', 'webp', 'ico', 'pdf', 'zip'];
    if (binaryExtensions.includes(extension)) {
      // Convert to Uint8Array
      const bytes = new Uint8Array(decoded.length);
      for (let i = 0; i < decoded.length; i++) {
        bytes[i] = decoded.charCodeAt(i);
      }
      return bytes;
    }
    
    // Return as text for all other files
    return decoded;
  }
  
  /**
   * Sign a bundle with the current user's identity
   * @private
   * @param {Object} bundle - Bundle to sign
   * @returns {Promise<string>} Signature
   */
  async _signBundle(bundle) {
    if (!this.identity || !this.identity.isAuthenticated()) {
      throw new Error('Identity service required for signing bundles');
    }
    
    try {
      // Create a string representation of the bundle for signing
      const bundleStr = JSON.stringify(bundle);
      
      // Sign the bundle
      const signature = await this.identity.sign(bundleStr);
      
      return signature;
    } catch (error) {
      console.error('Failed to sign bundle:', error);
      throw error;
    }
  }
  
  /**
   * Validate a bundle's integrity and signature
   * @param {Object} bundle - Bundle to validate
   * @returns {Promise<Object>} Validation result
   */
  async validateBundle(bundle) {
    if (!bundle || !bundle.manifest) {
      throw new Error('Invalid bundle format');
    }
    
    console.log(`Validating bundle: ${bundle.manifest.id}`);
    
    try {
      // Validate manifest structure
      const manifestResult = this._validateBundleManifest(bundle.manifest);
      
      // Validate bundle contents
      const contentResult = this._validateBundleContents(bundle);
      
      // Validate bundle signature if present
      let signatureResult = { valid: false, reason: 'No signature present' };
      if (bundle.manifest.signature) {
        signatureResult = await this._validateBundleSignature(bundle);
      }
      
      // Check for version conflicts with installed apps
      const versionResult = await this._checkVersionConflicts(bundle.manifest);
      
      // Combine all validation results
      const validationResult = {
        valid: manifestResult.valid && contentResult.valid && 
               (signatureResult.valid || !bundle.manifest.signature) &&
               versionResult.valid,
        manifest: manifestResult,
        content: contentResult,
        signature: signatureResult,
        version: versionResult
      };
      
      return validationResult;
    } catch (error) {
      console.error(`Bundle validation failed:`, error);
      return {
        valid: false,
        error: error.message
      };
    }
  }
  
  /**
   * Validate bundle manifest structure and required fields
   * @private
   * @param {Object} manifest - Bundle manifest
   * @returns {Object} Validation result
   */
  _validateBundleManifest(manifest) {
    // Required fields
    const requiredFields = ['id', 'name', 'version', 'entryPoint'];
    const missingFields = requiredFields.filter(field => !manifest[field]);
    
    if (missingFields.length > 0) {
      return {
        valid: false,
        reason: `Missing required fields: ${missingFields.join(', ')}`
      };
    }
    
    // Validate ID format
    const validIdPattern = /^[a-z0-9][a-z0-9-_.]+[a-z0-9]$/i;
    if (!validIdPattern.test(manifest.id)) {
      return {
        valid: false,
        reason: 'Invalid bundle ID format'
      };
    }
    
    // Validate version format
    const validVersionPattern = /^\d+\.\d+\.\d+$/;
    if (!validVersionPattern.test(manifest.version)) {
      return {
        valid: false,
        reason: 'Invalid version format (should be x.y.z)'
      };
    }
    
    // Check permissions format
    if (manifest.permissions && !Array.isArray(manifest.permissions)) {
      return {
        valid: false,
        reason: 'Permissions must be an array'
      };
    }
    
    // Check dependencies format
    if (manifest.dependencies && typeof manifest.dependencies !== 'object') {
      return {
        valid: false,
        reason: 'Dependencies must be an object'
      };
    }
    
    return {
      valid: true
    };
  }
  
  /**
   * Validate bundle contents
   * @private
   * @param {Object} bundle - Bundle to validate
   * @returns {Object} Validation result
   */
  _validateBundleContents(bundle) {
    // Check if code section exists
    if (!bundle.code || typeof bundle.code !== 'object') {
      return {
        valid: false,
        reason: 'Bundle must contain a code section'
      };
    }
    
    // Check if entry point exists in code
    if (!bundle.code[bundle.manifest.entryPoint]) {
      return {
        valid: false,
        reason: `Entry point ${bundle.manifest.entryPoint} not found in code`
      };
    }
    
    // Resources section is optional, but if present must be an object
    if (bundle.resources && typeof bundle.resources !== 'object') {
      return {
        valid: false,
        reason: 'Resources must be an object if present'
      };
    }
    
    return {
      valid: true
    };
  }
  
  /**
   * Validate bundle signature
   * @private
   * @param {Object} bundle - Bundle to validate
   * @returns {Promise<Object>} Signature validation result
   */
  async _validateBundleSignature(bundle) {
    if (!this.identity) {
      return {
        valid: false,
        reason: 'Identity service not available for signature verification'
      };
    }
    
    try {
      // Extract signature
      const signature = bundle.manifest.signature;
      
      // Create bundle copy without signature for verification
      const bundleForVerification = {
        manifest: { ...bundle.manifest, signature: null },
        code: bundle.code,
        resources: bundle.resources
      };
      
      // Create string representation
      const bundleStr = JSON.stringify(bundleForVerification);
      
      // Verify signature
      const isValid = await this.identity.verify(bundleStr, signature, null);
      
      return {
        valid: isValid,
        reason: isValid ? null : 'Invalid signature'
      };
    } catch (error) {
      console.error('Signature validation failed:', error);
      return {
        valid: false,
        reason: `Signature validation error: ${error.message}`
      };
    }
  }
  
  /**
   * Check for version conflicts with installed apps
   * @private
   * @param {Object} manifest - Bundle manifest
   * @returns {Promise<Object>} Version check result
   */
  async _checkVersionConflicts(manifest) {
    // Check if this app is already installed
    const installedBundle = this.installedBundles.get(manifest.id);
    
    if (installedBundle) {
      // Compare versions
      const installedVersion = installedBundle.manifest.version;
      const bundleVersion = manifest.version;
      
      // Parse versions for comparison
      const parseVersion = (ver) => {
        const parts = ver.split('.').map(Number);
        return (parts[0] * 1000000) + (parts[1] * 1000) + parts[2];
      };
      
      const installedValue = parseVersion(installedVersion);
      const bundleValue = parseVersion(bundleVersion);
      
      if (bundleValue < installedValue) {
        return {
          valid: false,
          reason: `Bundle version (${bundleVersion}) is older than installed version (${installedVersion})`
        };
      }
    }
    
    // Check dependencies
    if (manifest.dependencies) {
      for (const [depId, versionReq] of Object.entries(manifest.dependencies)) {
        // Check if dependency is installed
        const depBundle = this.installedBundles.get(depId);
        
        if (!depBundle) {
          return {
            valid: false,
            reason: `Required dependency ${depId} is not installed`
          };
        }
        
        // TODO: Implement version requirement checking
      }
    }
    
    return {
      valid: true
    };
  }
  
  /**
   * Import a bundle from provided bundle data
   * @param {Object} bundleData - Bundle data
   * @param {Object} options - Import options
   * @param {boolean} options.skipValidation - Skip validation
   * @param {boolean} options.overwrite - Overwrite existing bundle
   * @returns {Promise<Object>} Import result
   */
  async importBundle(bundleData, options = {}) {
    console.log(`Importing bundle: ${bundleData.manifest?.id || 'unknown'}`);
    
    try {
      // Validate the bundle unless skipped
      if (!options.skipValidation) {
        const validationResult = await this.validateBundle(bundleData);
        
        if (!validationResult.valid) {
          throw new Error(`Bundle validation failed: ${JSON.stringify(validationResult)}`);
        }
      }
      
      // Check if bundle is already installed
      const bundleId = bundleData.manifest.id;
      const existingBundle = this.installedBundles.get(bundleId);
      
      if (existingBundle && !options.overwrite) {
        throw new Error(`Bundle ${bundleId} is already installed`);
      }
      
      // Store the bundle metadata
      const bundleRecord = {
        id: bundleId,
        type: 'bundle',
        manifest: bundleData.manifest,
        installed: new Date().toISOString(),
        enabled: true
      };
      
      await this.store.put(bundleRecord);
      
      // Store app code files
      await this._storeAppFiles(bundleId, bundleData);
      
      // Add to installed bundles map
      this.installedBundles.set(bundleId, {
        manifest: bundleData.manifest,
        installed: bundleRecord.installed,
        enabled: true
      });
      
      // Notify about the imported bundle
      this._notifyBundleEvent('imported', bundleData.manifest);
      
      return {
        success: true,
        bundleId
      };
    } catch (error) {
      console.error('Bundle import failed:', error);
      return {
        success: false,
        error: error.message
      };
    }
  }
  
  /**
   * Store bundle files in the files store
   * @private
   * @param {string} bundleId - Bundle ID
   * @param {Object} bundleData - Bundle data
   * @returns {Promise<void>}
   */
  async _storeAppFiles(bundleId, bundleData) {
    // Prepare file records for batch save
    const fileRecords = [];
    
    // Process code files
    for (const [path, encodedContent] of Object.entries(bundleData.code)) {
      const content = this._decodeFileContent(encodedContent, path);
      
      fileRecords.push({
        id: `${bundleId}:${path}`,
        path,
        appId: bundleId,
        name: path.split('/').pop(),
        type: 'file',
        isCode: true,
        content,
        encoding: content instanceof Uint8Array ? 'binary' : 'text',
        created: new Date(),
        modified: new Date()
      });
    }
    
    // Process resource files
    if (bundleData.resources) {
      for (const [path, encodedContent] of Object.entries(bundleData.resources)) {
        const content = this._decodeFileContent(encodedContent, path);
        
        fileRecords.push({
          id: `${bundleId}:${path}`,
          path,
          appId: bundleId,
          name: path.split('/').pop(),
          type: 'file',
          isCode: false,
          content,
          encoding: content instanceof Uint8Array ? 'binary' : 'text',
          created: new Date(),
          modified: new Date()
        });
      }
    }
    
    // Save all file records
    if (fileRecords.length > 0) {
      await this.store.saveAll(null, fileRecords);
    }
  }
  
  /**
   * Export a bundle for the specified app
   * @param {string} appId - App ID to export
   * @param {string} format - Export format ('json' or 'binary')
   * @returns {Promise<Object|Uint8Array>} Exported bundle
   */
  async exportBundle(appId, format = 'json') {
    console.log(`Exporting bundle for app: ${appId}`);
    
    try {
      // Check if app is installed
      if (!this.installedBundles.has(appId)) {
        // App not in installedBundles, try to create a new bundle
        const bundle = await this.createBundle(appId);
        
        // Export in the requested format
        if (format === 'json') {
          return bundle;
        } else if (format === 'binary') {
          // Convert to binary format
          const bundleStr = JSON.stringify(bundle);
          const bytes = new TextEncoder().encode(bundleStr);
          return bytes;
        } else {
          throw new Error(`Unsupported export format: ${format}`);
        }
      }
      
      // Get the installed bundle
      const bundleInfo = this.installedBundles.get(appId);
      
      // Reconstruct the full bundle
      const bundle = {
        manifest: bundleInfo.manifest,
        code: await this._collectAppCode(appId),
        resources: await this._collectAppResources(appId)
      };
      
      // Export in the requested format
      if (format === 'json') {
        return bundle;
      } else if (format === 'binary') {
        // Convert to binary format
        const bundleStr = JSON.stringify(bundle);
        const bytes = new TextEncoder().encode(bundleStr);
        return bytes;
      } else {
        throw new Error(`Unsupported export format: ${format}`);
      }
    } catch (error) {
      console.error(`Failed to export bundle for ${appId}:`, error);
      throw error;
    }
  }
  
  /**
   * Install a bundle from a remote source
   * @param {string} bundleId - Bundle ID to install
   * @param {string} remoteUrl - Remote source URL
   * @returns {Promise<Object>} Installation result
   */
  async installBundleFromRemote(bundleId, remoteUrl) {
    console.log(`Installing bundle ${bundleId} from remote: ${remoteUrl}`);
    
    try {
      // Connect to the remote
      const remote = await this.connectToRemote(remoteUrl);
      
      // Fetch the bundle from the remote
      const bundleData = await remote.fetchBundle(bundleId);
      
      // Import the bundle
      return this.importBundle(bundleData, { overwrite: true });
    } catch (error) {
      console.error(`Failed to install bundle from remote:`, error);
      return {
        success: false,
        error: error.message
      };
    }
  }
  
  /**
   * Connect to a remote bundle source
   * @param {string} remoteUrl - Remote source URL
   * @param {Object} options - Connection options
   * @returns {Promise<Object>} Remote provider instance
   */
  async connectToRemote(remoteUrl, options = {}) {
    console.log(`Connecting to remote: ${remoteUrl}`);
    
    try {
      // Check if we're already connected to this remote
      const existing = this.connectedRemotes.find(r => r.url === remoteUrl);
      if (existing) {
        return existing.provider;
      }
      
      // Create a new remote provider
      const provider = await this._createRemoteProvider(remoteUrl, options);
      
      // Add to connected remotes
      this.connectedRemotes.push({
        url: remoteUrl,
        provider,
        connected: new Date()
      });
      
      return provider;
    } catch (error) {
      console.error(`Failed to connect to remote ${remoteUrl}:`, error);
      throw error;
    }
  }
  
  /**
   * Create a remote provider for the specified URL
   * @private
   * @param {string} remoteUrl - Remote URL
   * @param {Object} options - Provider options
   * @returns {Promise<Object>} Remote provider instance
   */
  async _createRemoteProvider(remoteUrl, options) {
    // Default to GitHub provider for the official repo
    if (remoteUrl.includes('github.com/UOR-Foundation/PrimeOS-Apps')) {
      return new GithubRemoteProvider(remoteUrl, options);
    }
    
    // Determine provider type from URL
    if (remoteUrl.includes('github.com')) {
      return new GithubRemoteProvider(remoteUrl, options);
    } else if (remoteUrl.includes('ipfs') || remoteUrl.includes('ipns')) {
      throw new Error('IPFS provider not yet implemented');
    } else {
      // Default to generic HTTP provider
      return new HttpRemoteProvider(remoteUrl, options);
    }
  }
  
  /**
   * Get bundle metadata for the specified bundle
   * @param {string} bundleId - Bundle ID
   * @returns {Promise<Object>} Bundle metadata
   */
  async getBundleMetadata(bundleId) {
    // Check in-memory cache first
    if (this.installedBundles.has(bundleId)) {
      return this.installedBundles.get(bundleId);
    }
    
    // Try to get from store
    try {
      const record = await this.store.get(bundleId);
      if (record && record.type === 'bundle') {
        return {
          manifest: record.manifest,
          installed: record.installed,
          enabled: record.enabled !== false
        };
      }
    } catch (error) {
      console.error(`Failed to get bundle metadata for ${bundleId}:`, error);
    }
    
    return null;
  }
  
  /**
   * Uninstall the specified bundle
   * @param {string} bundleId - Bundle ID to uninstall
   * @returns {Promise<boolean>} Success indicator
   */
  async uninstallBundle(bundleId) {
    console.log(`Uninstalling bundle: ${bundleId}`);
    
    try {
      // Check if bundle is installed
      if (!this.installedBundles.has(bundleId)) {
        throw new Error(`Bundle ${bundleId} is not installed`);
      }
      
      // Notify before uninstall
      this._notifyBundleEvent('uninstalling', { id: bundleId });
      
      // Remove bundle files
      const fileRecords = await this.store.query({
        index: 'type',
        value: 'file',
        filter: file => file.appId === bundleId
      });
      
      for (const file of fileRecords) {
        await this.store.remove(file.id);
      }
      
      // Remove bundle record
      await this.store.remove(bundleId);
      
      // Remove from installed bundles map
      this.installedBundles.delete(bundleId);
      
      // Notify after uninstall
      this._notifyBundleEvent('uninstalled', { id: bundleId });
      
      return true;
    } catch (error) {
      console.error(`Failed to uninstall bundle ${bundleId}:`, error);
      return false;
    }
  }
  
  /**
   * Get a list of all installed bundles
   * @returns {Promise<Array>} List of bundle metadata
   */
  async getInstalledBundles() {
    return Array.from(this.installedBundles.entries()).map(([id, data]) => {
      return {
        id,
        name: data.manifest.name,
        version: data.manifest.version,
        author: data.manifest.author,
        description: data.manifest.description,
        installed: data.installed,
        enabled: data.enabled
      };
    });
  }
  
  /**
   * Query available bundles from connected remotes
   * @param {Object} filter - Query filter
   * @returns {Promise<Array>} List of available bundles
   */
  async queryAvailableBundles(filter = {}) {
    console.log('Querying available bundles from remotes');
    
    // Collect bundles from all connected remotes
    const allBundles = [];
    
    for (const remote of this.connectedRemotes) {
      try {
        const bundles = await remote.provider.fetchBundleCatalog();
        allBundles.push(...bundles);
      } catch (error) {
        console.warn(`Failed to fetch bundles from ${remote.url}:`, error);
      }
    }
    
    // Apply filters if provided
    let filteredBundles = allBundles;
    
    if (filter.query) {
      const query = filter.query.toLowerCase();
      filteredBundles = filteredBundles.filter(bundle => 
        bundle.name.toLowerCase().includes(query) ||
        bundle.description.toLowerCase().includes(query)
      );
    }
    
    if (filter.tags && filter.tags.length > 0) {
      filteredBundles = filteredBundles.filter(bundle => {
        if (!bundle.tags || !Array.isArray(bundle.tags)) return false;
        return filter.tags.some(tag => bundle.tags.includes(tag));
      });
    }
    
    return filteredBundles;
  }
  
  /**
   * Send a bundle event notification
   * @private
   * @param {string} event - Event name
   * @param {Object} bundleInfo - Bundle information
   */
  _notifyBundleEvent(event, bundleInfo) {
    this.eventBus.publish(`bundle:${event}`, {
      bundleId: bundleInfo.id,
      bundleName: bundleInfo.name,
      timestamp: new Date().toISOString(),
      details: bundleInfo
    });
  }
}

/**
 * Base class for remote bundle providers
 */
class RemoteProvider {
  /**
   * Create a new remote provider instance
   * @param {string} url - Remote URL
   * @param {Object} options - Provider options
   */
  constructor(url, options = {}) {
    this.url = url;
    this.options = options;
  }
  
  /**
   * Fetch the bundle catalog from the remote
   * @returns {Promise<Array>} List of available bundles
   */
  async fetchBundleCatalog() {
    throw new Error('Not implemented in base class');
  }
  
  /**
   * Fetch a specific bundle from the remote
   * @param {string} bundleId - Bundle ID to fetch
   * @returns {Promise<Object>} Bundle data
   */
  async fetchBundle(bundleId) {
    throw new Error('Not implemented in base class');
  }
  
  /**
   * Publish a bundle to the remote
   * @param {Object} bundleData - Bundle to publish
   * @returns {Promise<Object>} Publish result
   */
  async publishBundle(bundleData) {
    throw new Error('Not implemented in base class');
  }
}

/**
 * HTTP-based remote provider for bundles
 */
class HttpRemoteProvider extends RemoteProvider {
  /**
   * Fetch the bundle catalog from the remote
   * @returns {Promise<Array>} List of available bundles
   */
  async fetchBundleCatalog() {
    try {
      // Fetch catalog from the remote endpoint
      const response = await fetch(`${this.url}/catalog.json`);
      
      if (!response.ok) {
        throw new Error(`HTTP error: ${response.status} ${response.statusText}`);
      }
      
      const catalog = await response.json();
      return catalog.bundles || [];
    } catch (error) {
      console.error(`Failed to fetch bundle catalog:`, error);
      throw error;
    }
  }
  
  /**
   * Fetch a specific bundle from the remote
   * @param {string} bundleId - Bundle ID to fetch
   * @returns {Promise<Object>} Bundle data
   */
  async fetchBundle(bundleId) {
    try {
      // Fetch bundle from the remote endpoint
      const response = await fetch(`${this.url}/bundles/${bundleId}.json`);
      
      if (!response.ok) {
        throw new Error(`HTTP error: ${response.status} ${response.statusText}`);
      }
      
      return await response.json();
    } catch (error) {
      console.error(`Failed to fetch bundle ${bundleId}:`, error);
      throw error;
    }
  }
  
  /**
   * Publish a bundle to the remote (if supported)
   * @param {Object} bundleData - Bundle to publish
   * @returns {Promise<Object>} Publish result
   */
  async publishBundle(bundleData) {
    // Publishing not supported for basic HTTP provider
    throw new Error('Publishing not supported for this remote type');
  }
}

/**
 * GitHub-based remote provider for bundles
 */
class GithubRemoteProvider extends RemoteProvider {
  /**
   * Create a new GitHub remote provider
   * @param {string} url - GitHub repository URL
   * @param {Object} options - Provider options
   */
  constructor(url, options = {}) {
    super(url, options);
    
    // Extract repo info from URL
    const repoMatch = url.match(/github\.com\/([^\/]+)\/([^\/]+)/);
    if (!repoMatch) {
      throw new Error('Invalid GitHub repository URL');
    }
    
    this.owner = repoMatch[1];
    this.repo = repoMatch[2];
    this.branch = options.branch || 'main';
    
    // API base URL
    this.apiBaseUrl = `https://api.github.com/repos/${this.owner}/${this.repo}/contents`;
  }
  
  /**
   * Fetch the bundle catalog from the GitHub repository
   * @returns {Promise<Array>} List of available bundles
   */
  async fetchBundleCatalog() {
    try {
      // Fetch catalog file from GitHub
      const response = await fetch(`${this.apiBaseUrl}/catalog.json?ref=${this.branch}`);
      
      if (!response.ok) {
        if (response.status === 404) {
          // Try to list all bundles in the bundles directory
          return this._listBundlesDirectory();
        }
        throw new Error(`GitHub API error: ${response.status} ${response.statusText}`);
      }
      
      const data = await response.json();
      
      // Content is base64 encoded
      const content = atob(data.content);
      const catalog = JSON.parse(content);
      
      return catalog.bundles || [];
    } catch (error) {
      console.error(`Failed to fetch bundle catalog from GitHub:`, error);
      throw error;
    }
  }
  
  /**
   * List bundles directory when catalog.json is not available
   * @private
   * @returns {Promise<Array>} List of available bundles
   */
  async _listBundlesDirectory() {
    try {
      // Fetch contents of the bundles directory
      const response = await fetch(`${this.apiBaseUrl}/bundles?ref=${this.branch}`);
      
      if (!response.ok) {
        throw new Error(`GitHub API error: ${response.status} ${response.statusText}`);
      }
      
      const entries = await response.json();
      
      // Extract bundle information from directory entries
      const bundles = [];
      
      for (const entry of entries) {
        if (entry.type === 'dir') {
          try {
            // Try to fetch manifest.json from each bundle directory
            const manifestResponse = await fetch(`${this.apiBaseUrl}/bundles/${entry.name}/manifest.json?ref=${this.branch}`);
            
            if (manifestResponse.ok) {
              const manifestData = await manifestResponse.json();
              const manifestContent = atob(manifestData.content);
              const manifest = JSON.parse(manifestContent);
              
              bundles.push(manifest);
            }
          } catch (error) {
            console.warn(`Failed to fetch manifest for ${entry.name}:`, error);
          }
        }
      }
      
      return bundles;
    } catch (error) {
      console.error(`Failed to list bundles directory:`, error);
      return [];
    }
  }
  
  /**
   * Fetch a specific bundle from the GitHub repository
   * @param {string} bundleId - Bundle ID to fetch
   * @returns {Promise<Object>} Bundle data
   */
  async fetchBundle(bundleId) {
    try {
      // Fetch bundle file from GitHub
      const response = await fetch(`${this.apiBaseUrl}/bundles/${bundleId}/bundle.json?ref=${this.branch}`);
      
      if (!response.ok) {
        throw new Error(`GitHub API error: ${response.status} ${response.statusText}`);
      }
      
      const data = await response.json();
      
      // Content is base64 encoded
      const content = atob(data.content);
      return JSON.parse(content);
    } catch (error) {
      console.error(`Failed to fetch bundle ${bundleId} from GitHub:`, error);
      throw error;
    }
  }
  
  /**
   * Publish a bundle to the GitHub repository (requires token)
   * @param {Object} bundleData - Bundle to publish
   * @returns {Promise<Object>} Publish result
   */
  async publishBundle(bundleData) {
    // Check for GitHub token
    if (!this.options.token) {
      throw new Error('GitHub token required for publishing bundles');
    }
    
    try {
      const bundleId = bundleData.manifest.id;
      const bundlePath = `bundles/${bundleId}/bundle.json`;
      
      // Convert bundle to JSON string
      const bundleContent = JSON.stringify(bundleData, null, 2);
      
      // Encode content as base64
      const encodedContent = btoa(bundleContent);
      
      // Create or update file on GitHub
      const response = await fetch(`https://api.github.com/repos/${this.owner}/${this.repo}/contents/${bundlePath}`, {
        method: 'PUT',
        headers: {
          'Authorization': `token ${this.options.token}`,
          'Content-Type': 'application/json'
        },
        body: JSON.stringify({
          message: `Update bundle: ${bundleId}`,
          content: encodedContent,
          branch: this.branch
        })
      });
      
      if (!response.ok) {
        const error = await response.json();
        throw new Error(`GitHub API error: ${error.message}`);
      }
      
      const result = await response.json();
      
      return {
        success: true,
        url: result.content.html_url
      };
    } catch (error) {
      console.error(`Failed to publish bundle to GitHub:`, error);
      throw error;
    }
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = {
    BundleManager,
    RemoteProvider,
    HttpRemoteProvider,
    GithubRemoteProvider
  };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.BundleManager = BundleManager;
  window.PrimeOS.RemoteProvider = RemoteProvider;
  window.PrimeOS.HttpRemoteProvider = HttpRemoteProvider;
  window.PrimeOS.GithubRemoteProvider = GithubRemoteProvider;
}