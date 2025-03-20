/**
 * Manifold Import/Export
 * 
 * Provides functionality for importing and exporting manifolds between PrimeOS instances.
 */

import { NetworkAdapter } from './network-adapter.js';

class ManifoldImportExport {
  constructor(options = {}) {
    this.manifoldRegistry = options.manifoldRegistry;
    this.secureVault = options.secureVault;
    this.eventBus = options.eventBus;
    this.networkAdapter = options.networkAdapter || new NetworkAdapter();
    this.endpoints = new Map();
    this.initialized = false;
  }
  
  async initialize() {
    if (this.initialized) return this;
    
    // Load endpoints from secure vault if available
    if (this.secureVault) {
      const endpointsJson = await this.secureVault.getSecret('manifold:endpoints');
      if (endpointsJson) {
        try {
          const endpoints = JSON.parse(endpointsJson);
          endpoints.forEach(endpoint => {
            this.endpoints.set(endpoint.name, endpoint);
          });
        } catch (error) {
          console.error('Error loading endpoints from secure vault:', error);
        }
      }
    }
    
    this.initialized = true;
    return this;
  }
  
  /**
   * Add a remote endpoint
   */
  async addRemoteEndpoint(endpoint) {
    if (!endpoint.name || !endpoint.url) {
      throw new Error('Endpoint name and URL are required');
    }
    
    if (this.endpoints.has(endpoint.name)) {
      throw new Error(`Endpoint with name "${endpoint.name}" already exists`);
    }
    
    // Store endpoint
    this.endpoints.set(endpoint.name, {
      name: endpoint.name,
      url: endpoint.url,
      token: endpoint.token || null,
      added: new Date().toISOString()
    });
    
    // Store endpoints in secure vault if available
    await this._saveEndpoints();
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('remote-endpoint:added', {
        name: endpoint.name,
        url: endpoint.url
      });
    }
    
    return endpoint;
  }
  
  /**
   * Remove a remote endpoint
   */
  async removeRemoteEndpoint(name) {
    if (!this.endpoints.has(name)) {
      throw new Error(`Endpoint with name "${name}" not found`);
    }
    
    // Remove endpoint
    this.endpoints.delete(name);
    
    // Store endpoints in secure vault if available
    await this._saveEndpoints();
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('remote-endpoint:removed', {
        name
      });
    }
    
    return true;
  }
  
  /**
   * Get all remote endpoints
   */
  async getRemoteEndpoints() {
    return Array.from(this.endpoints.values());
  }
  
  /**
   * Export a manifold to a remote endpoint
   */
  async exportManifold(options) {
    if (!options.manifoldId) {
      throw new Error('Manifold ID is required');
    }
    
    if (!options.endpointUrl) {
      throw new Error('Endpoint URL is required');
    }
    
    // Find endpoint by URL
    const endpoint = Array.from(this.endpoints.values()).find(e => e.url === options.endpointUrl);
    if (!endpoint) {
      throw new Error(`Endpoint with URL "${options.endpointUrl}" not found`);
    }
    
    try {
      // Get manifold
      const manifold = await this.manifoldRegistry.getManifold(options.manifoldId);
      if (!manifold) {
        throw new Error(`Manifold with ID "${options.manifoldId}" not found`);
      }
      
      // Create export morphology
      const morphology = {
        manifold: manifold.toJSON(),
        relatedManifolds: [],
        relationships: []
      };
      
      // Include related manifolds if requested
      if (options.includeRelated) {
        const related = manifold.getRelatedManifolds();
        
        for (const relatedManifold of related) {
          // Get related manifold
          const relatedId = relatedManifold.manifold.getId();
          const fullManifold = await this.manifoldRegistry.getManifold(relatedId);
          
          if (fullManifold) {
            // Add to morphology
            morphology.relatedManifolds.push(fullManifold.toJSON());
            
            // Add relationship
            morphology.relationships.push({
              sourceId: options.manifoldId,
              targetId: relatedId,
              type: relatedManifold.type,
              metadata: relatedManifold.metadata || {}
            });
          }
        }
      }
      
      // Set auth token if available
      if (endpoint.token) {
        this.networkAdapter.setAuthToken(endpoint.token);
      }
      
      // Export to remote endpoint
      const result = await this.networkAdapter.post(
        `${endpoint.url}/api/manifolds/import`,
        morphology
      );
      
      if (!result.data || !result.data.success) {
        throw new Error(`Export failed: ${result.data?.error || 'Unknown error'}`);
      }
      
      // Emit event
      if (this.eventBus) {
        this.eventBus.publish('remote-manifold:exported', {
          sourceId: options.manifoldId,
          remoteId: result.data.manifestId,
          endpoint: endpoint.name
        });
      }
      
      return {
        success: true,
        remoteId: result.data.manifestId,
        relatedIds: result.data.relatedManifoldIds || {}
      };
    } catch (error) {
      // Emit error event
      if (this.eventBus) {
        this.eventBus.publish('remote-manifold:export-error', {
          manifoldId: options.manifoldId,
          endpoint: endpoint.name,
          error
        });
      }
      
      throw error;
    }
  }
  
  /**
   * Import a manifold from a remote endpoint
   */
  async importManifold(options) {
    if (!options.remoteId) {
      throw new Error('Remote manifold ID is required');
    }
    
    if (!options.endpointUrl) {
      throw new Error('Endpoint URL is required');
    }
    
    // Find endpoint by URL
    const endpoint = Array.from(this.endpoints.values()).find(e => e.url === options.endpointUrl);
    if (!endpoint) {
      throw new Error(`Endpoint with URL "${options.endpointUrl}" not found`);
    }
    
    try {
      // Set auth token if available
      if (endpoint.token) {
        this.networkAdapter.setAuthToken(endpoint.token);
      }
      
      // Get manifold from remote endpoint
      const result = await this.networkAdapter.get(
        `${endpoint.url}/api/manifolds/export/${options.remoteId}`
      );
      
      if (!result.data || !result.data.manifold) {
        throw new Error(`Import failed: ${result.data?.error || 'Unknown error'}`);
      }
      
      // Extract morphology
      const morphology = result.data;
      
      // Register manifold
      const manifoldData = morphology.manifold;
      
      // Ensure the manifold has an invariant with a name
      if (!manifoldData.invariant) {
        manifoldData.invariant = {};
      }
      
      if (!manifoldData.invariant.name) {
        manifoldData.invariant.name = `Imported ${manifoldData.meta?.type || 'Manifold'}`;
      }
      
      // Add source information
      manifoldData.invariant.importedFrom = options.endpointUrl;
      manifoldData.invariant.originalId = options.remoteId;
      manifoldData.invariant.importedAt = new Date().toISOString();
      
      // Register main manifold
      let localId;
      
      // Try to find existing manifold with the same original ID
      const existingManifolds = await this.manifoldRegistry.findManifolds(
        'invariant',
        'originalId',
        options.remoteId
      );
      
      if (existingManifolds && existingManifolds.length > 0) {
        // Update existing manifold
        localId = existingManifolds[0].getId();
        await this.manifoldRegistry.updateManifold(localId, {
          updateSource: 'import',
          lastImportedAt: new Date().toISOString()
        });
      } else {
        // Register new manifold
        const manifold = await this.manifoldRegistry.registerApp(manifoldData.invariant);
        localId = manifold.getId();
      }
      
      // Import related manifolds and relationships if requested
      if (options.includeRelated && morphology.relatedManifolds) {
        const relatedIds = {};
        
        // Register related manifolds
        for (const relatedManifold of morphology.relatedManifolds) {
          // Ensure the manifold has an invariant with a name
          if (!relatedManifold.invariant) {
            relatedManifold.invariant = {};
          }
          
          if (!relatedManifold.invariant.name) {
            relatedManifold.invariant.name = `Imported ${relatedManifold.meta?.type || 'Manifold'}`;
          }
          
          // Add source information
          relatedManifold.invariant.importedFrom = options.endpointUrl;
          relatedManifold.invariant.originalId = relatedManifold.meta.id;
          relatedManifold.invariant.importedAt = new Date().toISOString();
          
          // Try to find existing manifold with the same original ID
          const existingRelated = await this.manifoldRegistry.findManifolds(
            'invariant',
            'originalId',
            relatedManifold.meta.id
          );
          
          if (existingRelated && existingRelated.length > 0) {
            // Use existing related manifold
            relatedIds[relatedManifold.meta.id] = existingRelated[0].getId();
            
            // Update it
            await this.manifoldRegistry.updateManifold(relatedIds[relatedManifold.meta.id], {
              updateSource: 'import',
              lastImportedAt: new Date().toISOString()
            });
          } else {
            // Register new related manifold
            const related = await this.manifoldRegistry.registerApp(relatedManifold.invariant);
            relatedIds[relatedManifold.meta.id] = related.getId();
          }
        }
        
        // Create relationships
        if (morphology.relationships) {
          for (const relationship of morphology.relationships) {
            // Map remote IDs to local IDs
            const sourceId = relationship.sourceId === options.remoteId
              ? localId
              : relatedIds[relationship.sourceId];
              
            const targetId = relationship.targetId === options.remoteId
              ? localId
              : relatedIds[relationship.targetId];
            
            if (sourceId && targetId) {
              // Create relationship
              await this.manifoldRegistry.createRelation(
                sourceId,
                targetId,
                relationship.type,
                relationship.metadata
              );
            }
          }
        }
      }
      
      // Emit event
      if (this.eventBus) {
        this.eventBus.publish('remote-manifold:imported', {
          remoteId: options.remoteId,
          localId,
          endpoint: endpoint.name
        });
      }
      
      return {
        success: true,
        localId
      };
    } catch (error) {
      // Emit error event
      if (this.eventBus) {
        this.eventBus.publish('remote-manifold:import-error', {
          remoteId: options.remoteId,
          endpoint: endpoint.name,
          error
        });
      }
      
      throw error;
    }
  }
  
  /**
   * Save endpoints to secure vault
   */
  async _saveEndpoints() {
    if (this.secureVault) {
      await this.secureVault.setSecret(
        'manifold:endpoints',
        JSON.stringify(Array.from(this.endpoints.values()))
      );
    }
  }
}

// CommonJS export
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { ManifoldImportExport };
}

// ES module export
export { ManifoldImportExport };
