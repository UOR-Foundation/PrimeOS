/**
 * PrimeOS Reference Implementation - Remote Manifold Import/Export
 * 
 * Provides functionality to import and export manifolds between PrimeOS instances.
 * This system allows for manifold distribution, sharing, and synchronization
 * across the distributed PrimeOS ecosystem.
 */

/**
 * ManifoldImportExport
 * 
 * Responsible for importing and exporting manifolds to/from remote endpoints.
 */
class ManifoldImportExport {
  /**
   * Create a new ManifoldImportExport instance
   * @param {Object} options - Configuration options
   * @param {Object} options.manifoldRegistry - ManifoldRegistry instance
   * @param {Object} options.secureVault - SecureVault instance for credential storage
   * @param {Object} options.eventBus - EventBus instance
   * @param {Object} options.networkAdapter - Network adapter for HTTP requests
   */
  constructor(options = {}) {
    this.manifoldRegistry = options.manifoldRegistry;
    this.secureVault = options.secureVault;
    this.eventBus = options.eventBus || { publish: () => {}, subscribe: () => {} };
    this.networkAdapter = options.networkAdapter;
    
    // Remote endpoint configuration
    this.remoteEndpoints = [];
    
    // Track import/export operations
    this.operations = new Map();
    
    // Migration options
    this.migrationOptions = {
      preserveIds: false,
      importAsReadOnly: false,
      trackRemoteOrigin: true
    };
    
    // Initialization flag
    this.initialized = false;
  }
  
  /**
   * Initialize the import/export system
   * @returns {Promise<boolean>} Success flag
   */
  async initialize() {
    if (this.initialized) {
      return true;
    }
    
    try {
      // Load remote endpoints from secure vault
      await this._loadRemoteEndpoints();
      
      // Subscribe to events
      this._subscribeToEvents();
      
      this.initialized = true;
      return true;
    } catch (error) {
      console.error('Failed to initialize ManifoldImportExport:', error);
      return false;
    }
  }
  
  /**
   * Export a manifold to a remote endpoint
   * @param {Object} options - Export options
   * @param {string} options.manifoldId - ID of the manifold to export
   * @param {string} options.endpointUrl - URL of the remote endpoint
   * @param {boolean} [options.includeRelated=false] - Whether to include related manifolds
   * @param {Array<string>} [options.relationTypes] - Specific relation types to include
   * @param {number} [options.maxDepth=1] - Maximum depth for related manifolds
   * @returns {Promise<Object>} Export result with remote IDs
   */
  async exportManifold(options) {
    try {
      const { 
        manifoldId, 
        endpointUrl, 
        includeRelated = false, 
        relationTypes = null,
        maxDepth = 1
      } = options;
      
      // Get manifold
      const manifold = await this.manifoldRegistry.getManifold(manifoldId);
      if (!manifold) {
        throw new Error(`Manifold not found: ${manifoldId}`);
      }
      
      // Start building export package (morphology)
      const morphology = {
        manifold: manifold.toJSON(),
        relatedManifolds: [],
        relationships: []
      };
      
      // Add related manifolds if requested
      if (includeRelated) {
        const collectedData = await this._collectRelatedManifolds(
          manifold, 
          relationTypes, 
          maxDepth
        );
        
        morphology.relatedManifolds = collectedData.relatedManifolds;
        morphology.relationships = collectedData.relationships;
      }
      
      // Find endpoint and get auth token
      const endpoint = this._findEndpoint(endpointUrl);
      if (endpoint && endpoint.token) {
        this.networkAdapter.setAuthToken(endpoint.token);
      }
      
      // Send export request
      const response = await this.networkAdapter.post(
        `${endpointUrl}/api/manifolds/import`,
        morphology
      );
      
      // Process response
      const result = {
        success: true,
        sourceId: manifoldId,
        remoteId: response.data.manifestId,
        relatedRemoteIds: response.data.relatedManifoldIds || {},
        endpointUrl
      };
      
      // Track operation
      const operationId = `export-${manifoldId}-${Date.now()}`;
      this.operations.set(operationId, {
        type: 'export',
        sourceId: manifoldId,
        remoteId: response.data.manifestId,
        endpointUrl,
        timestamp: new Date().toISOString(),
        status: 'completed'
      });
      
      // Publish event
      this.eventBus.publish('remote-manifold:exported', {
        sourceId: manifoldId,
        remoteId: response.data.manifestId,
        endpointUrl,
        relatedCount: morphology.relatedManifolds.length,
        operationId
      });
      
      return result;
    } catch (error) {
      // Publish error event
      this.eventBus.publish('remote-manifold:export-error', {
        manifoldId: options.manifoldId,
        error,
        endpointUrl: options.endpointUrl
      });
      
      throw error;
    }
  }
  
  /**
   * Import a manifold from a remote endpoint
   * @param {Object} options - Import options
   * @param {string} options.remoteId - ID of the remote manifold
   * @param {string} options.endpointUrl - URL of the remote endpoint
   * @param {boolean} [options.includeRelated=true] - Whether to include related manifolds
   * @returns {Promise<Object>} Import result with local IDs
   */
  async importManifold(options) {
    try {
      const { 
        remoteId, 
        endpointUrl, 
        includeRelated = true 
      } = options;
      
      // Find endpoint and get auth token
      const endpoint = this._findEndpoint(endpointUrl);
      if (endpoint && endpoint.token) {
        this.networkAdapter.setAuthToken(endpoint.token);
      }
      
      // Fetch remote morphology
      const response = await this.networkAdapter.get(
        `${endpointUrl}/api/manifolds/export/${remoteId}`
      );
      
      const remoteMorphology = response.data;
      
      // Check if this manifold was already imported
      const existingManifolds = await this.manifoldRegistry.findManifolds(
        'all', 'originalId', remoteId
      );
      
      let localManifold;
      const idMap = new Map();
      
      // Either update existing or create new
      if (existingManifolds.length > 0) {
        localManifold = existingManifolds[0];
        
        // Update existing
        await this.manifoldRegistry.updateManifold(
          localManifold.getId(),
          {
            ...remoteMorphology.manifold.variant,
            lastSynced: new Date().toISOString()
          }
        );
        
        idMap.set(remoteId, localManifold.getId());
      } else {
        // Create new manifold based on type
        const manifoldSpec = this._convertToLocalSpec(
          remoteMorphology.manifold,
          endpointUrl
        );
        
        // Register with appropriate type
        switch (remoteMorphology.manifold.meta.type) {
          case 'application':
            localManifold = await this.manifoldRegistry.registerApp(manifoldSpec);
            break;
          case 'component':
            localManifold = await this.manifoldRegistry.registerComponent(manifoldSpec);
            break;
          case 'bundle':
            localManifold = await this.manifoldRegistry.registerBundle(manifoldSpec);
            break;
          default:
            // Default to app registration
            localManifold = await this.manifoldRegistry.registerApp(manifoldSpec);
        }
        
        idMap.set(remoteId, localManifold.getId());
      }
      
      // Import related manifolds if requested
      if (includeRelated && remoteMorphology.relatedManifolds) {
        for (const relatedManifold of remoteMorphology.relatedManifolds) {
          const remoteRelatedId = relatedManifold.meta.id;
          
          // Check if already imported
          const existingRelated = await this.manifoldRegistry.findManifolds(
            'all', 'originalId', remoteRelatedId
          );
          
          let localRelatedManifold;
          
          if (existingRelated.length > 0) {
            localRelatedManifold = existingRelated[0];
            
            // Update existing
            await this.manifoldRegistry.updateManifold(
              localRelatedManifold.getId(),
              {
                ...relatedManifold.variant,
                lastSynced: new Date().toISOString()
              }
            );
            
            idMap.set(remoteRelatedId, localRelatedManifold.getId());
          } else {
            // Create new related manifold
            const relatedSpec = this._convertToLocalSpec(
              relatedManifold,
              endpointUrl
            );
            
            // Register with appropriate type
            switch (relatedManifold.meta.type) {
              case 'application':
                localRelatedManifold = await this.manifoldRegistry.registerApp(relatedSpec);
                break;
              case 'component':
                localRelatedManifold = await this.manifoldRegistry.registerComponent(relatedSpec);
                break;
              case 'bundle':
                localRelatedManifold = await this.manifoldRegistry.registerBundle(relatedSpec);
                break;
              default:
                // Default to component registration
                localRelatedManifold = await this.manifoldRegistry.registerComponent(relatedSpec);
            }
            
            idMap.set(remoteRelatedId, localRelatedManifold.getId());
          }
        }
        
        // Create relationships
        if (remoteMorphology.relationships) {
          for (const relationship of remoteMorphology.relationships) {
            const localSourceId = idMap.get(relationship.sourceId);
            const localTargetId = idMap.get(relationship.targetId);
            
            if (localSourceId && localTargetId) {
              await this.manifoldRegistry.createRelation(
                localSourceId,
                localTargetId,
                relationship.type,
                {
                  ...relationship.metadata,
                  importedFrom: endpointUrl,
                  originalSourceId: relationship.sourceId,
                  originalTargetId: relationship.targetId,
                  importedAt: new Date().toISOString()
                }
              );
            }
          }
        }
      }
      
      // Build result with ID mappings
      const result = {
        success: true,
        localId: localManifold.getId(),
        remoteId,
        relatedLocalIds: {}
      };
      
      // Add related ID mappings
      for (const [remoteId, localId] of idMap.entries()) {
        if (remoteId !== options.remoteId) {
          result.relatedLocalIds[remoteId] = localId;
        }
      }
      
      // Track operation
      const operationId = `import-${remoteId}-${Date.now()}`;
      this.operations.set(operationId, {
        type: 'import',
        remoteId,
        localId: localManifold.getId(),
        endpointUrl,
        timestamp: new Date().toISOString(),
        status: 'completed',
        relatedCount: Object.keys(result.relatedLocalIds).length
      });
      
      // Publish event
      this.eventBus.publish('remote-manifold:imported', {
        remoteId,
        localId: localManifold.getId(),
        endpointUrl,
        relatedCount: Object.keys(result.relatedLocalIds).length,
        operationId
      });
      
      return result;
    } catch (error) {
      // Publish error event
      this.eventBus.publish('remote-manifold:import-error', {
        remoteId: options.remoteId,
        error,
        endpointUrl: options.endpointUrl
      });
      
      throw error;
    }
  }
  
  /**
   * Add a remote endpoint configuration
   * @param {Object} endpoint - Endpoint configuration
   * @param {string} endpoint.name - Friendly name for the endpoint
   * @param {string} endpoint.url - URL of the endpoint
   * @param {string} endpoint.token - Authentication token
   * @returns {Promise<boolean>} Success flag
   */
  async addRemoteEndpoint(endpoint) {
    try {
      // Validate endpoint
      if (!endpoint.name || !endpoint.url) {
        throw new Error('Endpoint requires name and URL');
      }
      
      // Check if already exists
      const existing = this.remoteEndpoints.findIndex(e => e.name === endpoint.name);
      if (existing !== -1) {
        // Update existing
        this.remoteEndpoints[existing] = {
          ...this.remoteEndpoints[existing],
          ...endpoint
        };
      } else {
        // Add new
        this.remoteEndpoints.push(endpoint);
      }
      
      // Save to secure storage
      await this._saveRemoteEndpoints();
      
      // Publish event
      this.eventBus.publish('remote-manifold:endpoint-added', {
        name: endpoint.name,
        url: endpoint.url
      });
      
      return true;
    } catch (error) {
      console.error('Failed to add remote endpoint:', error);
      return false;
    }
  }
  
  /**
   * Remove a remote endpoint configuration
   * @param {string} endpointName - Name of the endpoint to remove
   * @returns {Promise<boolean>} Success flag
   */
  async removeRemoteEndpoint(endpointName) {
    try {
      // Find endpoint
      const index = this.remoteEndpoints.findIndex(e => e.name === endpointName);
      if (index === -1) {
        return false;
      }
      
      // Remove endpoint
      const removed = this.remoteEndpoints.splice(index, 1)[0];
      
      // Save to secure storage
      await this._saveRemoteEndpoints();
      
      // Publish event
      this.eventBus.publish('remote-manifold:endpoint-removed', {
        name: removed.name,
        url: removed.url
      });
      
      return true;
    } catch (error) {
      console.error('Failed to remove remote endpoint:', error);
      return false;
    }
  }
  
  /**
   * Get all configured remote endpoints (without tokens)
   * @returns {Promise<Array>} List of endpoints
   */
  async getRemoteEndpoints() {
    return this.remoteEndpoints.map(endpoint => ({
      name: endpoint.name,
      url: endpoint.url,
      // Don't expose tokens
      lastSync: endpoint.lastSync
    }));
  }
  
  /**
   * Get recent import/export operations
   * @param {number} [limit=20] - Maximum number of operations to return
   * @returns {Array} Recent operations
   */
  getRecentOperations(limit = 20) {
    const operations = Array.from(this.operations.values())
      .sort((a, b) => new Date(b.timestamp) - new Date(a.timestamp));
    
    return operations.slice(0, limit);
  }
  
  /**
   * Set migration options
   * @param {Object} options - Migration options
   * @param {boolean} [options.preserveIds] - Whether to preserve original IDs
   * @param {boolean} [options.importAsReadOnly] - Whether to import as read-only
   * @param {boolean} [options.trackRemoteOrigin] - Whether to track remote origin
   */
  setMigrationOptions(options = {}) {
    this.migrationOptions = {
      ...this.migrationOptions,
      ...options
    };
  }
  
  /**
   * Load remote endpoints from secure storage
   * @private
   */
  async _loadRemoteEndpoints() {
    // Check if endpoints are stored
    const hasEndpoints = await this.secureVault.hasSecret('remote-manifold-endpoints');
    if (!hasEndpoints) {
      this.remoteEndpoints = [];
      return;
    }
    
    // Load endpoints
    const endpoints = await this.secureVault.getSecret('remote-manifold-endpoints');
    this.remoteEndpoints = Array.isArray(endpoints) ? endpoints : [];
  }
  
  /**
   * Save remote endpoints to secure storage
   * @private
   */
  async _saveRemoteEndpoints() {
    await this.secureVault.setSecret('remote-manifold-endpoints', this.remoteEndpoints);
  }
  
  /**
   * Find endpoint configuration by URL
   * @param {string} url - Endpoint URL
   * @returns {Object|null} Endpoint configuration or null
   * @private
   */
  _findEndpoint(url) {
    return this.remoteEndpoints.find(endpoint => endpoint.url === url) || null;
  }
  
  /**
   * Subscribe to events
   * @private
   */
  _subscribeToEvents() {
    // Handle import requests
    this.eventBus.subscribe('remote-manifold:import-request', async (data) => {
      try {
        const result = await this.importManifold(data);
        // Result is already published in importManifold
      } catch (error) {
        console.error('Error handling import request:', error);
      }
    });
    
    // Handle export requests
    this.eventBus.subscribe('remote-manifold:export-request', async (data) => {
      try {
        const result = await this.exportManifold(data);
        // Result is already published in exportManifold
      } catch (error) {
        console.error('Error handling export request:', error);
      }
    });
  }
  
  /**
   * Collect related manifolds for export
   * @param {Object} rootManifold - Root manifold to export
   * @param {Array<string>} relationTypes - Types of relations to include
   * @param {number} maxDepth - Maximum depth to traverse
   * @returns {Promise<Object>} Collected manifolds and relationships
   * @private
   */
  async _collectRelatedManifolds(rootManifold, relationTypes = null, maxDepth = 1) {
    const collectedManifolds = new Map();
    const collectedRelationships = [];
    const processedIds = new Set();
    
    // Process manifold and its relations recursively
    const processManifold = async (manifold, currentDepth = 0) => {
      if (currentDepth > maxDepth) {
        return;
      }
      
      const manifoldId = manifold.getId();
      processedIds.add(manifoldId);
      
      // Get all related manifolds
      let relatedManifolds = manifold.getRelatedManifolds();
      
      // Filter by relation type if specified
      if (relationTypes && relationTypes.length > 0) {
        relatedManifolds = relatedManifolds.filter(relation => 
          relationTypes.includes(relation.type)
        );
      }
      
      // Process each related manifold
      for (const relation of relatedManifolds) {
        const relatedManifold = relation.manifold;
        const relatedId = relatedManifold.getId();
        
        // Add relationship
        collectedRelationships.push({
          sourceId: manifoldId,
          targetId: relatedId,
          type: relation.type,
          metadata: relation.metadata || {}
        });
        
        // Add manifold if not already collected
        if (!collectedManifolds.has(relatedId)) {
          collectedManifolds.set(relatedId, relatedManifold.toJSON());
          
          // Process related manifold recursively if not already processed
          if (!processedIds.has(relatedId)) {
            await processManifold(relatedManifold, currentDepth + 1);
          }
        }
      }
    };
    
    // Start recursive collection
    await processManifold(rootManifold, 0);
    
    return {
      relatedManifolds: Array.from(collectedManifolds.values()),
      relationships: collectedRelationships
    };
  }
  
  /**
   * Convert remote manifold specification to local format
   * @param {Object} remoteManifold - Remote manifold data
   * @param {string} remoteEndpoint - Remote endpoint URL
   * @returns {Object} Local manifold specification
   * @private
   */
  _convertToLocalSpec(remoteManifold, remoteEndpoint) {
    // Extract basic properties from invariant
    const spec = {
      ...remoteManifold.invariant,
      
      // Add import metadata
      remoteOrigin: remoteEndpoint,
      originalId: remoteManifold.meta.id,
      importedAt: new Date().toISOString()
    };
    
    // Add variant properties
    if (remoteManifold.variant) {
      Object.keys(remoteManifold.variant).forEach(key => {
        // Don't override invariant properties
        if (!spec[key]) {
          spec[key] = remoteManifold.variant[key];
        }
      });
    }
    
    // Apply migration options
    if (this.migrationOptions.preserveIds) {
      spec.id = remoteManifold.meta.id;
    }
    
    if (this.migrationOptions.importAsReadOnly) {
      spec.readOnly = true;
    }
    
    return spec;
  }
}

// Export module
module.exports = { ManifoldImportExport };