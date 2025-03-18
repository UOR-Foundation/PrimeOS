/**
 * PrimeOS App Factory - Storage Integration
 * 
 * Provides integration between the App Factory and PrimeStore for project persistence,
 * file storage, and version management.
 */

class AppFactoryStorage {
  /**
   * Create a new storage integration instance
   * @param {Object} store - PrimeStore instance
   * @param {Object} options - Configuration options
   */
  constructor(store, options = {}) {
    if (!store) {
      throw new Error('AppFactoryStorage requires a store instance');
    }
    
    this.store = store;
    this.projectCollection = options.projectCollection || 'app_factory_projects';
    this.fileCollection = options.fileCollection || 'files';
    
    // Initialize storage if needed
    this._initializeStorage();
    
    console.log('AppFactoryStorage initialized');
  }
  
  /**
   * Initialize necessary storage structures
   * @private
   */
  async _initializeStorage() {
    try {
      // Check if project collection exists, create if not
      const collections = await this.store.getCollections();
      
      if (!collections.includes(this.projectCollection)) {
        await this.store.createCollection(this.projectCollection, {
          indices: [
            { name: 'status', keyPath: 'status' },
            { name: 'createdAt', keyPath: 'createdAt' },
            { name: 'userId', keyPath: 'userId' }
          ],
          schema: {
            id: { type: 'string', required: true },
            name: { type: 'string', required: true },
            description: { type: 'string' },
            status: { type: 'string', required: true },
            createdAt: { type: 'date', required: true },
            updatedAt: { type: 'date', required: true },
            userId: { type: 'string', required: true }
          }
        });
        
        console.log(`Created collection ${this.projectCollection}`);
      }
      
      // Ensure file collection has projectId index
      await this.store.ensureIndex(this.fileCollection, 'projectId');
      
    } catch (error) {
      console.error('Failed to initialize App Factory storage:', error);
    }
  }
  
  /**
   * Save a project to storage
   * @param {Object} project - Project data
   * @returns {Promise<Object>} Saved project
   */
  async saveProject(project) {
    if (!project || !project.id) {
      throw new Error('Project with valid ID is required');
    }
    
    // Update timestamps
    project.updatedAt = new Date();
    
    if (!project.createdAt) {
      project.createdAt = new Date();
    }
    
    try {
      await this.store.put(this.projectCollection, project);
      return project;
    } catch (error) {
      console.error(`Failed to save project ${project.id}:`, error);
      throw error;
    }
  }
  
  /**
   * Get a project by ID
   * @param {string} projectId - Project ID
   * @returns {Promise<Object|null>} Project data or null if not found
   */
  async getProject(projectId) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    try {
      return await this.store.get(this.projectCollection, projectId);
    } catch (error) {
      console.error(`Failed to get project ${projectId}:`, error);
      return null;
    }
  }
  
  /**
   * Get projects by user ID
   * @param {string} userId - User ID
   * @returns {Promise<Array>} Array of user projects
   */
  async getUserProjects(userId) {
    if (!userId) {
      throw new Error('User ID is required');
    }
    
    try {
      return await this.store.query({
        collection: this.projectCollection,
        index: 'userId',
        value: userId
      });
    } catch (error) {
      console.error(`Failed to get projects for user ${userId}:`, error);
      return [];
    }
  }
  
  /**
   * Delete a project and all its files
   * @param {string} projectId - Project ID
   * @returns {Promise<boolean>} Success indicator
   */
  async deleteProject(projectId) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    try {
      // Delete the project files first
      const files = await this.getProjectFiles(projectId);
      
      for (const file of files) {
        await this.store.delete(this.fileCollection, file.id);
      }
      
      // Then delete the project
      await this.store.delete(this.projectCollection, projectId);
      
      return true;
    } catch (error) {
      console.error(`Failed to delete project ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Save project files
   * @param {string} projectId - Project ID
   * @param {Array} files - Array of file objects with path and content
   * @returns {Promise<Array>} Saved file IDs
   */
  async saveProjectFiles(projectId, files) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    if (!Array.isArray(files)) {
      throw new Error('Files must be an array');
    }
    
    try {
      const fileEntries = files.map(file => ({
        id: `${projectId}_${file.path.replace(/\//g, '_')}`,
        projectId: projectId,
        path: file.path,
        content: file.content,
        type: 'app_factory_file',
        createdAt: new Date(),
        updatedAt: new Date()
      }));
      
      await this.store.saveAll(this.fileCollection, fileEntries);
      
      return fileEntries.map(file => file.id);
    } catch (error) {
      console.error(`Failed to save files for project ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Get files for a project
   * @param {string} projectId - Project ID
   * @returns {Promise<Array>} Array of project files
   */
  async getProjectFiles(projectId) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    try {
      return await this.store.query({
        collection: this.fileCollection,
        index: 'projectId',
        value: projectId
      });
    } catch (error) {
      console.error(`Failed to get files for project ${projectId}:`, error);
      return [];
    }
  }
  
  /**
   * Get a specific project file
   * @param {string} projectId - Project ID
   * @param {string} filePath - File path
   * @returns {Promise<Object|null>} File object or null if not found
   */
  async getProjectFile(projectId, filePath) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    if (!filePath) {
      throw new Error('File path is required');
    }
    
    const fileId = `${projectId}_${filePath.replace(/\//g, '_')}`;
    
    try {
      return await this.store.get(this.fileCollection, fileId);
    } catch (error) {
      console.error(`Failed to get file ${filePath} for project ${projectId}:`, error);
      return null;
    }
  }
  
  /**
   * Save a specific project file
   * @param {string} projectId - Project ID
   * @param {string} filePath - File path
   * @param {string} content - File content
   * @returns {Promise<Object>} Saved file
   */
  async saveProjectFile(projectId, filePath, content) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    if (!filePath) {
      throw new Error('File path is required');
    }
    
    const fileId = `${projectId}_${filePath.replace(/\//g, '_')}`;
    
    try {
      const file = {
        id: fileId,
        projectId: projectId,
        path: filePath,
        content: content,
        type: 'app_factory_file',
        updatedAt: new Date()
      };
      
      // Check if file exists
      const existingFile = await this.store.get(this.fileCollection, fileId);
      
      if (existingFile) {
        file.createdAt = existingFile.createdAt;
      } else {
        file.createdAt = new Date();
      }
      
      await this.store.put(this.fileCollection, file);
      
      return file;
    } catch (error) {
      console.error(`Failed to save file ${filePath} for project ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Delete a specific project file
   * @param {string} projectId - Project ID
   * @param {string} filePath - File path
   * @returns {Promise<boolean>} Success indicator
   */
  async deleteProjectFile(projectId, filePath) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    if (!filePath) {
      throw new Error('File path is required');
    }
    
    const fileId = `${projectId}_${filePath.replace(/\//g, '_')}`;
    
    try {
      await this.store.delete(this.fileCollection, fileId);
      return true;
    } catch (error) {
      console.error(`Failed to delete file ${filePath} for project ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Create a project version snapshot
   * @param {string} projectId - Project ID
   * @param {string} versionName - Version name
   * @returns {Promise<Object>} Version data
   */
  async createProjectVersion(projectId, versionName) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    if (!versionName) {
      throw new Error('Version name is required');
    }
    
    try {
      // Get project and files
      const project = await this.getProject(projectId);
      
      if (!project) {
        throw new Error(`Project ${projectId} not found`);
      }
      
      const files = await this.getProjectFiles(projectId);
      
      // Create version object
      const version = {
        id: `${projectId}_version_${Date.now()}`,
        projectId: projectId,
        name: versionName,
        timestamp: new Date(),
        specification: project.specification,
        generatedCode: project.generatedCode,
        testResults: project.testResults,
        status: project.status
      };
      
      // Save version metadata
      await this.store.put(this.projectCollection, version);
      
      // Save version files
      for (const file of files) {
        const versionFile = {
          id: `${version.id}_${file.path.replace(/\//g, '_')}`,
          versionId: version.id,
          projectId: projectId,
          path: file.path,
          content: file.content,
          type: 'app_factory_version_file'
        };
        
        await this.store.put(this.fileCollection, versionFile);
      }
      
      return version;
    } catch (error) {
      console.error(`Failed to create version for project ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Get project versions
   * @param {string} projectId - Project ID
   * @returns {Promise<Array>} Array of version objects
   */
  async getProjectVersions(projectId) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    try {
      return await this.store.query({
        collection: this.projectCollection,
        index: 'projectId',
        value: projectId,
        filter: (item) => item.id.includes('_version_')
      });
    } catch (error) {
      console.error(`Failed to get versions for project ${projectId}:`, error);
      return [];
    }
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { AppFactoryStorage };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.AppFactoryStorage = AppFactoryStorage;
}