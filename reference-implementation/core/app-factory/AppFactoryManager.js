/**
 * PrimeOS AppFactoryManager
 * 
 * Central orchestrator for the App Factory system that coordinates all 
 * components and guides users through the collaborative app creation process.
 */

class AppFactoryManager {
  /**
   * Creates a new AppFactoryManager instance
   * @param {Object} options - Configuration options
   * @param {Object} options.store - PrimeStore instance for persistence
   * @param {Object} options.eventBus - Event bus for notifications
   * @param {Object} options.claudeOrchestrator - ClaudeOrchestrator for AI interactions
   * @param {Object} options.bundleManager - BundleManager for bundle handling
   * @param {Object} options.coherenceEngine - CoherenceEngine for mathematical validation
   */
  constructor(options = {}) {
    // Validate required dependencies
    if (!options.store) {
      throw new Error('AppFactoryManager requires a store instance');
    }
    
    if (!options.eventBus) {
      throw new Error('AppFactoryManager requires an eventBus instance');
    }
    
    // Store core dependencies
    this.store = options.store;
    this.eventBus = options.eventBus;
    this.claudeOrchestrator = options.claudeOrchestrator;
    this.bundleManager = options.bundleManager;
    this.coherenceEngine = options.coherenceEngine;
    this.templateSystem = options.templateSystem;
    
    // Initialize active projects state
    this.activeProjects = new Map();
    
    // Project creation workflow phases
    this.workflowPhases = [
      { id: 'inspiration', name: 'Inspiration', required: true },
      { id: 'coherenceMapping', name: 'Coherence Mapping', required: true },
      { id: 'bundleSpecification', name: 'Bundle Specification', required: true },
      { id: 'componentGeneration', name: 'Component Generation', required: true },
      { id: 'bundleAssembly', name: 'Bundle Assembly', required: true },
      { id: 'libraryIntegration', name: 'Library Integration', required: false }
    ];
    
    // Register event handlers
    this._registerEventHandlers();
    
    console.log('AppFactoryManager initialized');
  }
  
  /**
   * Register event handlers for system events
   * @private
   */
  _registerEventHandlers() {
    // System ready event - load active projects
    this.eventBus.subscribe('system:ready', () => this._loadActiveProjects());
    
    // Component generation events - track progress
    this.eventBus.subscribe('app-factory:component-generated', (data) => {
      this._updateProjectProgress(data.projectId, 'componentGeneration', {
        progress: data.progress
      });
    });
    
    // Bundle validation events
    this.eventBus.subscribe('bundle:validated', (data) => {
      // Find project using this bundle
      this._findProjectByBundleId(data.bundleId)
        .then(projectId => {
          if (projectId) {
            this._updateProjectProgress(projectId, 'bundleAssembly', {
              validated: true,
              coherenceScore: data.coherenceScore
            });
          }
        })
        .catch(error => console.error('Error updating project after bundle validation:', error));
    });
  }
  
  /**
   * Load active projects from storage
   * @private
   */
  async _loadActiveProjects() {
    try {
      // Query all app factory projects from the store
      const projectRecords = await this.store.query({
        index: 'type',
        value: 'app_factory_project'
      });
      
      // Reset the active projects map
      this.activeProjects.clear();
      
      // Populate the map with project data
      projectRecords.forEach(record => {
        this.activeProjects.set(record.id, {
          ...record,
          lastAccessed: new Date()
        });
      });
      
      console.log(`Loaded ${this.activeProjects.size} active app factory projects`);
    } catch (error) {
      console.error('Failed to load active projects:', error);
    }
  }
  
  /**
   * Find project by associated bundle ID
   * @private
   * @param {string} bundleId - Bundle identifier
   * @returns {Promise<string|null>} Project ID or null if not found
   */
  async _findProjectByBundleId(bundleId) {
    try {
      for (const [projectId, project] of this.activeProjects.entries()) {
        if (project.bundleId === bundleId) {
          return projectId;
        }
      }
      
      // If not found in active projects, query the store
      const projects = await this.store.query({
        index: 'bundleId',
        value: bundleId,
        type: 'app_factory_project'
      });
      
      if (projects.length > 0) {
        return projects[0].id;
      }
      
      return null;
    } catch (error) {
      console.error(`Error finding project for bundle ${bundleId}:`, error);
      return null;
    }
  }
  
  /**
   * Create a new project in the App Factory
   * @param {string} name - Project name
   * @param {string} description - Project description
   * @param {Object} options - Additional options
   * @returns {Promise<string>} Created project ID
   */
  async createProject(name, description, options = {}) {
    if (!name) {
      throw new Error('Project name is required');
    }
    
    console.log(`Creating new project: ${name}`);
    
    try {
      // Generate a unique project ID
      const projectId = `app_factory_${Date.now()}_${Math.floor(Math.random() * 10000)}`;
      
      // Create initial project state
      const project = {
        id: projectId,
        type: 'app_factory_project',
        name,
        description: description || '',
        created: new Date().toISOString(),
        modified: new Date().toISOString(),
        currentPhase: 'inspiration',
        progress: {
          inspiration: { status: 'pending', data: null },
          coherenceMapping: { status: 'pending', data: null },
          bundleSpecification: { status: 'pending', data: null },
          componentGeneration: { status: 'pending', data: null },
          bundleAssembly: { status: 'pending', data: null },
          libraryIntegration: { status: 'pending', data: null }
        },
        settings: options.settings || {},
        bundleId: null
      };
      
      // Save to storage
      await this.store.put(project);
      
      // Add to active projects
      this.activeProjects.set(projectId, {
        ...project,
        lastAccessed: new Date()
      });
      
      // Notify project creation
      this._notifyProjectEvent('created', projectId, { name });
      
      return projectId;
    } catch (error) {
      console.error(`Failed to create project ${name}:`, error);
      throw error;
    }
  }
  
  /**
   * Get all active projects
   * @returns {Promise<Array>} Array of project summaries
   */
  async getProjects() {
    try {
      // Ensure active projects are loaded
      if (this.activeProjects.size === 0) {
        await this._loadActiveProjects();
      }
      
      // Convert map to array and format for response
      return Array.from(this.activeProjects.values()).map(project => ({
        id: project.id,
        name: project.name,
        description: project.description,
        created: project.created,
        modified: project.modified,
        currentPhase: project.currentPhase,
        progress: this._calculateProgressPercentage(project),
        bundleId: project.bundleId
      }));
    } catch (error) {
      console.error('Failed to get projects:', error);
      throw error;
    }
  }
  
  /**
   * Get details for a specific project
   * @param {string} projectId - Project ID
   * @returns {Promise<Object>} Project details
   */
  async getProject(projectId) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    try {
      // Check if project is in active projects
      if (this.activeProjects.has(projectId)) {
        const project = this.activeProjects.get(projectId);
        project.lastAccessed = new Date();
        
        return {
          id: project.id,
          name: project.name,
          description: project.description,
          created: project.created,
          modified: project.modified,
          currentPhase: project.currentPhase,
          progress: project.progress,
          progressPercentage: this._calculateProgressPercentage(project),
          bundleId: project.bundleId,
          settings: project.settings
        };
      }
      
      // If not in active projects, load from store
      const project = await this.store.get(projectId);
      
      if (!project || project.type !== 'app_factory_project') {
        throw new Error(`Project not found: ${projectId}`);
      }
      
      // Add to active projects
      this.activeProjects.set(projectId, {
        ...project,
        lastAccessed: new Date()
      });
      
      return {
        id: project.id,
        name: project.name,
        description: project.description,
        created: project.created,
        modified: project.modified,
        currentPhase: project.currentPhase,
        progress: project.progress,
        progressPercentage: this._calculateProgressPercentage(project),
        bundleId: project.bundleId,
        settings: project.settings
      };
    } catch (error) {
      console.error(`Failed to get project ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Delete a project
   * @param {string} projectId - Project ID
   * @returns {Promise<boolean>} Success status
   */
  async deleteProject(projectId) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    console.log(`Deleting project: ${projectId}`);
    
    try {
      // Get project to check if it has a bundle
      const project = await this.getProject(projectId);
      
      // Delete bundle if one exists
      if (project.bundleId && this.bundleManager) {
        try {
          // TODO: Implement bundle deletion in BundleManager
          // await this.bundleManager.deleteBundle(project.bundleId);
          console.log(`Associated bundle ${project.bundleId} would be deleted here`);
        } catch (bundleError) {
          console.error(`Failed to delete bundle for project ${projectId}:`, bundleError);
          // Continue with project deletion even if bundle deletion fails
        }
      }
      
      // Remove from active projects
      this.activeProjects.delete(projectId);
      
      // Remove from store
      await this.store.remove(projectId);
      
      // Clear Claude conversation context
      if (this.claudeOrchestrator) {
        this.claudeOrchestrator.clearProjectContext(projectId);
      }
      
      // Notify project deletion
      this._notifyProjectEvent('deleted', projectId);
      
      return true;
    } catch (error) {
      console.error(`Failed to delete project ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Start or continue the inspiration phase
   * @param {string} projectId - Project ID
   * @param {Object} input - User input for this phase
   * @returns {Promise<Object>} Phase results
   */
  async startInspirationPhase(projectId, input) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    if (!input || Object.keys(input).length === 0) {
      throw new Error('Inspiration input is required');
    }
    
    console.log(`Starting inspiration phase for project: ${projectId}`);
    
    try {
      // Get project
      const project = await this.getProject(projectId);
      
      // Update phase status
      await this._updateProjectProgress(projectId, 'inspiration', {
        status: 'in_progress'
      });
      
      // If Claude orchestrator is available, use it
      if (this.claudeOrchestrator) {
        // Run inspiration phase with input
        const result = await this.claudeOrchestrator.runInspirationPhase(projectId, input);
        
        // Update project with results
        await this._updateProjectProgress(projectId, 'inspiration', {
          status: 'completed',
          data: result
        });
        
        // Update current phase
        await this._updateProjectPhase(projectId, 'coherenceMapping');
        
        return result;
      } else {
        // Generate a simple result without Claude
        const result = {
          appPurpose: input.purpose || input.appPurpose || 'General purpose application',
          appDomain: input.domain || input.appDomain || 'General',
          targetUsers: input.audience ? [input.audience] : ['General users'],
          useCases: input.useCases || ['Basic functionality'],
          keyFeatures: input.features ? input.features.split(',').map(f => f.trim()) : ['Core functionality'],
          keyTerms: []
        };
        
        // Update project with results
        await this._updateProjectProgress(projectId, 'inspiration', {
          status: 'completed',
          data: result
        });
        
        // Update current phase
        await this._updateProjectPhase(projectId, 'coherenceMapping');
        
        return result;
      }
    } catch (error) {
      console.error(`Failed to complete inspiration phase for ${projectId}:`, error);
      
      // Update project to show error
      await this._updateProjectProgress(projectId, 'inspiration', {
        status: 'error',
        error: error.message
      });
      
      throw error;
    }
  }
  
  /**
   * Start or continue the coherence mapping phase
   * @param {string} projectId - Project ID
   * @returns {Promise<Object>} Phase results
   */
  async startCoherenceMappingPhase(projectId) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    console.log(`Starting coherence mapping phase for project: ${projectId}`);
    
    try {
      // Get project
      const project = await this.getProject(projectId);
      
      // Ensure inspiration phase is completed
      if (project.progress.inspiration.status !== 'completed') {
        throw new Error('Inspiration phase must be completed before coherence mapping');
      }
      
      // Get inspiration results
      const inspirationResults = project.progress.inspiration.data;
      
      // Update phase status
      await this._updateProjectProgress(projectId, 'coherenceMapping', {
        status: 'in_progress'
      });
      
      // If Claude orchestrator is available, use it
      if (this.claudeOrchestrator) {
        // Run coherence mapping phase with inspiration results
        const result = await this.claudeOrchestrator.runCoherenceMappingPhase(
          projectId, 
          inspirationResults
        );
        
        // Update project with results
        await this._updateProjectProgress(projectId, 'coherenceMapping', {
          status: 'completed',
          data: result
        });
        
        // Update current phase
        await this._updateProjectPhase(projectId, 'bundleSpecification');
        
        return result;
      } else {
        // Generate a simple result without Claude
        const result = {
          entities: this._generateBasicEntities(inspirationResults),
          relationships: [],
          processes: [],
          states: [],
          invariants: [],
          constraints: [],
          coherenceMetrics: {
            score: 0.8,
            interfaceCompleteness: 0.85,
            structuralIntegrity: 0.9
          }
        };
        
        // Use coherence engine if available
        if (this.coherenceEngine) {
          try {
            const coherenceMap = await this.coherenceEngine.mapCoherence(
              inspirationResults,
              result.entities
            );
            
            // Merge coherence engine results
            Object.assign(result, coherenceMap);
          } catch (coherenceError) {
            console.error('Coherence engine mapping failed:', coherenceError);
            // Continue with basic result
          }
        }
        
        // Update project with results
        await this._updateProjectProgress(projectId, 'coherenceMapping', {
          status: 'completed',
          data: result
        });
        
        // Update current phase
        await this._updateProjectPhase(projectId, 'bundleSpecification');
        
        return result;
      }
    } catch (error) {
      console.error(`Failed to complete coherence mapping phase for ${projectId}:`, error);
      
      // Update project to show error
      await this._updateProjectProgress(projectId, 'coherenceMapping', {
        status: 'error',
        error: error.message
      });
      
      throw error;
    }
  }
  
  /**
   * Start or continue the bundle specification phase
   * @param {string} projectId - Project ID
   * @returns {Promise<Object>} Phase results
   */
  async startBundleSpecificationPhase(projectId) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    console.log(`Starting bundle specification phase for project: ${projectId}`);
    
    try {
      // Get project
      const project = await this.getProject(projectId);
      
      // Ensure coherence mapping phase is completed
      if (project.progress.coherenceMapping.status !== 'completed') {
        throw new Error('Coherence mapping phase must be completed before bundle specification');
      }
      
      // Get coherence mapping results
      const coherenceResults = project.progress.coherenceMapping.data;
      
      // Update phase status
      await this._updateProjectProgress(projectId, 'bundleSpecification', {
        status: 'in_progress'
      });
      
      // If Claude orchestrator is available, use it
      if (this.claudeOrchestrator) {
        // Run bundle specification phase with coherence results
        const result = await this.claudeOrchestrator.runBundleSpecificationPhase(
          projectId, 
          coherenceResults
        );
        
        // Update project with results
        await this._updateProjectProgress(projectId, 'bundleSpecification', {
          status: 'completed',
          data: result
        });
        
        // Update current phase
        await this._updateProjectPhase(projectId, 'componentGeneration');
        
        return result;
      } else {
        // Generate a simple result without Claude
        const result = this._generateBasicSpecification(coherenceResults);
        
        // Update project with results
        await this._updateProjectProgress(projectId, 'bundleSpecification', {
          status: 'completed',
          data: result
        });
        
        // Update current phase
        await this._updateProjectPhase(projectId, 'componentGeneration');
        
        return result;
      }
    } catch (error) {
      console.error(`Failed to complete bundle specification phase for ${projectId}:`, error);
      
      // Update project to show error
      await this._updateProjectProgress(projectId, 'bundleSpecification', {
        status: 'error',
        error: error.message
      });
      
      throw error;
    }
  }
  
  /**
   * Start or continue the component generation phase
   * @param {string} projectId - Project ID
   * @param {Object} options - Generation options
   * @returns {Promise<Object>} Phase results
   */
  async startComponentGenerationPhase(projectId, options = {}) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    console.log(`Starting component generation phase for project: ${projectId}`);
    
    try {
      // Get project
      const project = await this.getProject(projectId);
      
      // Ensure bundle specification phase is completed
      if (project.progress.bundleSpecification.status !== 'completed') {
        throw new Error('Bundle specification phase must be completed before component generation');
      }
      
      // Get specification results
      const specificationResults = project.progress.bundleSpecification.data;
      
      // Update phase status
      await this._updateProjectProgress(projectId, 'componentGeneration', {
        status: 'in_progress'
      });
      
      // If Claude orchestrator is available, use it
      if (this.claudeOrchestrator) {
        // Run component generation phase with specification results
        const result = await this.claudeOrchestrator.runComponentGenerationPhase(
          projectId, 
          specificationResults, 
          options
        );
        
        // Update project with results
        await this._updateProjectProgress(projectId, 'componentGeneration', {
          status: 'completed',
          data: result
        });
        
        // Update current phase
        await this._updateProjectPhase(projectId, 'bundleAssembly');
        
        return result;
      } else {
        // Generate a simple result without Claude
        const result = {
          components: this._generateStubComponents(specificationResults),
          count: 1
        };
        
        // Update project with results
        await this._updateProjectProgress(projectId, 'componentGeneration', {
          status: 'completed',
          data: result
        });
        
        // Update current phase
        await this._updateProjectPhase(projectId, 'bundleAssembly');
        
        return result;
      }
    } catch (error) {
      console.error(`Failed to complete component generation phase for ${projectId}:`, error);
      
      // Update project to show error
      await this._updateProjectProgress(projectId, 'componentGeneration', {
        status: 'error',
        error: error.message
      });
      
      throw error;
    }
  }
  
  /**
   * Start or continue the bundle assembly phase
   * @param {string} projectId - Project ID
   * @returns {Promise<Object>} Phase results
   */
  async startBundleAssemblyPhase(projectId) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    console.log(`Starting bundle assembly phase for project: ${projectId}`);
    
    try {
      // Get project
      const project = await this.getProject(projectId);
      
      // Ensure component generation phase is completed
      if (project.progress.componentGeneration.status !== 'completed') {
        throw new Error('Component generation phase must be completed before bundle assembly');
      }
      
      // Get component generation results
      const componentResults = project.progress.componentGeneration.data;
      const specificationResults = project.progress.bundleSpecification.data;
      
      // Update phase status
      await this._updateProjectProgress(projectId, 'bundleAssembly', {
        status: 'in_progress'
      });
      
      // Create a real bundle using BundleManager or Claude
      let bundleId;
      let assemblyResult;
      
      if (this.claudeOrchestrator) {
        // Use Claude to assemble the bundle
        assemblyResult = await this.claudeOrchestrator.runBundleAssemblyPhase(
          projectId,
          componentResults.components,
          specificationResults
        );
        
        // Create actual bundle using BundleManager if available
        if (this.bundleManager) {
          try {
            // Generate bundle ID from project name
            const bundleId = project.name.toLowerCase().replace(/\s+/g, '-');
            
            // Create initial bundle
            const bundle = await this.bundleManager.createBundle(bundleId, {
              name: project.name,
              description: project.description,
              author: project.settings?.author || 'PrimeOS App Factory'
            });
            
            // Add components to bundle
            for (const [componentName, component] of Object.entries(componentResults.components)) {
              for (const [filePath, file] of Object.entries(component.files)) {
                await this.bundleManager.addBundleFile(bundleId, filePath, file.content, {
                  generated: true
                });
              }
            }
            
            // Validate bundle
            const validation = await this.bundleManager.validateBundle(bundleId);
            
            // Add validation results to assembly result
            assemblyResult.validation = validation;
            assemblyResult.bundleId = bundleId;
            
            // Save bundleId to project
            await this._updateProject(projectId, { bundleId });
          } catch (bundleError) {
            console.error('Failed to create bundle using BundleManager:', bundleError);
            // Continue with Claude's assembly result
          }
        }
      } else if (this.bundleManager) {
        // Use just BundleManager without Claude
        
        // Generate bundle ID from project name
        bundleId = project.name.toLowerCase().replace(/\s+/g, '-');
        
        // Create initial bundle
        const bundle = await this.bundleManager.createBundle(bundleId, {
          name: project.name,
          description: project.description,
          author: project.settings?.author || 'PrimeOS App Factory'
        });
        
        // Add a basic component if none generated
        if (!componentResults.components || Object.keys(componentResults.components).length === 0) {
          const stubComponent = this._generateStubComponents(specificationResults);
          
          for (const [componentName, component] of Object.entries(stubComponent)) {
            for (const [filePath, file] of Object.entries(component.files)) {
              await this.bundleManager.addBundleFile(bundleId, filePath, file.content, {
                generated: true
              });
            }
          }
        } else {
          // Add generated components to bundle
          for (const [componentName, component] of Object.entries(componentResults.components)) {
            for (const [filePath, file] of Object.entries(component.files)) {
              await this.bundleManager.addBundleFile(bundleId, filePath, file.content, {
                generated: true
              });
            }
          }
        }
        
        // Validate bundle
        const validation = await this.bundleManager.validateBundle(bundleId);
        
        // Create assembly result
        assemblyResult = {
          bundleId,
          validation,
          manifest: bundle.manifest,
          components: componentResults.components || stubComponent
        };
        
        // Save bundleId to project
        await this._updateProject(projectId, { bundleId });
      } else {
        // No Claude or BundleManager - create stub result
        assemblyResult = {
          manifest: {
            name: project.name,
            version: '1.0.0',
            description: project.description,
            entryPoint: 'views/main.js'
          },
          components: componentResults.components || this._generateStubComponents(specificationResults),
          coherenceScore: 0.85
        };
      }
      
      // Update project with results
      await this._updateProjectProgress(projectId, 'bundleAssembly', {
        status: 'completed',
        data: assemblyResult
      });
      
      // Update current phase
      await this._updateProjectPhase(projectId, 'libraryIntegration');
      
      return assemblyResult;
    } catch (error) {
      console.error(`Failed to complete bundle assembly phase for ${projectId}:`, error);
      
      // Update project to show error
      await this._updateProjectProgress(projectId, 'bundleAssembly', {
        status: 'error',
        error: error.message
      });
      
      throw error;
    }
  }
  
  /**
   * Start or continue the library integration phase
   * @param {string} projectId - Project ID
   * @param {Object} options - Integration options
   * @returns {Promise<Object>} Phase results
   */
  async startLibraryIntegrationPhase(projectId, options = {}) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    console.log(`Starting library integration phase for project: ${projectId}`);
    
    try {
      // Get project
      const project = await this.getProject(projectId);
      
      // Ensure bundle assembly phase is completed
      if (project.progress.bundleAssembly.status !== 'completed') {
        throw new Error('Bundle assembly phase must be completed before library integration');
      }
      
      // Get bundle assembly results
      const assemblyResults = project.progress.bundleAssembly.data;
      
      // Update phase status
      await this._updateProjectProgress(projectId, 'libraryIntegration', {
        status: 'in_progress'
      });
      
      // Export bundle if we have a bundle manager
      let libraryResult = {
        integrated: false,
        message: 'Library integration is not available'
      };
      
      if (this.bundleManager && project.bundleId) {
        try {
          // Export the bundle
          const exportedBundle = await this.bundleManager.exportBundle(project.bundleId);
          
          // Add to library result
          libraryResult = {
            integrated: true,
            bundleId: project.bundleId,
            exportedBundle,
            localLibraryPath: `/library/${project.bundleId}`
          };
          
          // Generate documentation if Claude is available
          if (this.claudeOrchestrator) {
            try {
              const documentation = await this.claudeOrchestrator.generateDocumentation(
                projectId,
                exportedBundle
              );
              
              // Add documentation files to bundle
              if (documentation.files) {
                for (const [path, file] of Object.entries(documentation.files)) {
                  await this.bundleManager.addBundleFile(project.bundleId, path, file.content, {
                    generated: true
                  });
                }
              }
              
              // Add to library result
              libraryResult.documentation = documentation;
            } catch (docError) {
              console.error('Documentation generation failed:', docError);
              // Continue without documentation
            }
          }
        } catch (bundleError) {
          console.error('Bundle export failed:', bundleError);
          libraryResult.error = bundleError.message;
        }
      }
      
      // Update project with results
      await this._updateProjectProgress(projectId, 'libraryIntegration', {
        status: 'completed',
        data: libraryResult
      });
      
      // Project workflow complete!
      return libraryResult;
    } catch (error) {
      console.error(`Failed to complete library integration phase for ${projectId}:`, error);
      
      // Update project to show error
      await this._updateProjectProgress(projectId, 'libraryIntegration', {
        status: 'error',
        error: error.message
      });
      
      throw error;
    }
  }
  
  /**
   * Continue the workflow to the next phase
   * @param {string} projectId - Project ID
   * @returns {Promise<Object>} Next phase result
   */
  async continueWorkflow(projectId) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    // Get project
    const project = await this.getProject(projectId);
    
    // Determine current phase and next action
    const currentPhase = project.currentPhase;
    
    switch (currentPhase) {
      case 'inspiration':
        // Inspiration requires user input, so can't automatically continue
        return { phase: 'inspiration', status: 'awaiting_input' };
        
      case 'coherenceMapping':
        return await this.startCoherenceMappingPhase(projectId);
        
      case 'bundleSpecification':
        return await this.startBundleSpecificationPhase(projectId);
        
      case 'componentGeneration':
        return await this.startComponentGenerationPhase(projectId);
        
      case 'bundleAssembly':
        return await this.startBundleAssemblyPhase(projectId);
        
      case 'libraryIntegration':
        return await this.startLibraryIntegrationPhase(projectId);
        
      default:
        throw new Error(`Unknown phase: ${currentPhase}`);
    }
  }
  
  /**
   * Export a project's bundle
   * @param {string} projectId - Project ID
   * @returns {Promise<Object>} Exported bundle
   */
  async exportProject(projectId) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    // Get project
    const project = await this.getProject(projectId);
    
    // Check if bundle exists
    if (!project.bundleId) {
      throw new Error('Project does not have an associated bundle');
    }
    
    // Check if bundle manager is available
    if (!this.bundleManager) {
      throw new Error('Bundle manager is not available for export');
    }
    
    try {
      // Export the bundle
      const exportedBundle = await this.bundleManager.exportBundle(project.bundleId);
      
      return exportedBundle;
    } catch (error) {
      console.error(`Failed to export project ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Generate basic entities from inspiration results
   * @private
   * @param {Object} inspirationResults - Inspiration phase results
   * @returns {Array} Basic entity definitions
   */
  _generateBasicEntities(inspirationResults) {
    const entities = [];
    
    // Extract potential entities from key terms and features
    const terms = inspirationResults.keyTerms || [];
    const features = inspirationResults.keyFeatures || [];
    
    // Add a User entity by default
    entities.push({
      name: 'User',
      properties: [
        { name: 'id', type: 'string', required: true },
        { name: 'name', type: 'string', required: true },
        { name: 'email', type: 'string', required: false }
      ]
    });
    
    // Try to derive entities from key terms and features
    const potentialEntities = new Set();
    
    // Add capitalized terms as potential entities
    terms.forEach(term => {
      if (term && term.charAt(0) === term.charAt(0).toUpperCase()) {
        potentialEntities.add(term);
      }
    });
    
    // Extract nouns from features as potential entities
    features.forEach(feature => {
      const words = feature.split(' ');
      words.forEach(word => {
        // Simple heuristic: capitalized words or words longer than 5 chars might be entities
        if ((word.charAt(0) === word.charAt(0).toUpperCase() || word.length > 5) &&
            !['and', 'the', 'for', 'with'].includes(word.toLowerCase())) {
          potentialEntities.add(word);
        }
      });
    });
    
    // Create basic entity definitions
    potentialEntities.forEach(entityName => {
      entities.push({
        name: entityName,
        properties: [
          { name: 'id', type: 'string', required: true },
          { name: 'name', type: 'string', required: true },
          { name: 'description', type: 'string', required: false }
        ]
      });
    });
    
    return entities;
  }
  
  /**
   * Generate a basic bundle specification
   * @private
   * @param {Object} coherenceResults - Coherence mapping results
   * @returns {Object} Basic specification
   */
  _generateBasicSpecification(coherenceResults) {
    // Extract entity information
    const entities = coherenceResults.entities || [];
    const relationships = coherenceResults.relationships || [];
    
    // Create manifest
    const manifest = {
      name: 'Generated App',
      version: '1.0.0',
      description: 'Auto-generated PrimeOS application',
      entryPoint: 'views/main.js',
      coherenceScore: coherenceResults.coherenceMetrics?.score || 0.8,
      permissions: [],
      dependencies: {},
      primeIntegrations: ['eventBus', 'shellAPI', 'storeAPI']
    };
    
    // Generate model components from entities
    const models = entities.map(entity => ({
      name: `${entity.name}Model`,
      type: 'model',
      entity: entity.name,
      properties: entity.properties || [],
      methods: [
        { name: 'create', params: [`${entity.name.toLowerCase()}`] },
        { name: 'get', params: ['id'] },
        { name: 'update', params: ['id', `${entity.name.toLowerCase()}`] },
        { name: 'delete', params: ['id'] }
      ]
    }));
    
    // Generate view components
    const views = [
      { name: 'MainView', type: 'view', path: 'views/main.js' },
      { name: 'HeaderComponent', type: 'component', path: 'components/header.js' },
      { name: 'FooterComponent', type: 'component', path: 'components/footer.js' }
    ];
    
    // Add entity-specific views
    entities.forEach(entity => {
      views.push({ 
        name: `${entity.name}ListView`, 
        type: 'view',
        path: `views/${entity.name.toLowerCase()}-list.js`,
        entity: entity.name
      });
      
      views.push({ 
        name: `${entity.name}DetailView`, 
        type: 'view',
        path: `views/${entity.name.toLowerCase()}-detail.js`,
        entity: entity.name
      });
      
      views.push({ 
        name: `${entity.name}Component`, 
        type: 'component',
        path: `components/${entity.name.toLowerCase()}.js`,
        entity: entity.name
      });
    });
    
    // Generate service components
    const services = [
      { name: 'ApiService', type: 'service', path: 'services/api-service.js' },
      { name: 'StorageService', type: 'service', path: 'services/storage-service.js' }
    ];
    
    // Add entity-specific services
    entities.forEach(entity => {
      services.push({
        name: `${entity.name}Service`,
        type: 'service',
        path: `services/${entity.name.toLowerCase()}-service.js`,
        entity: entity.name,
        dependencies: ['ApiService', 'StorageService']
      });
    });
    
    // Combine into specification
    return {
      manifest,
      components: views.filter(v => v.type === 'component'),
      models,
      services,
      views: views.filter(v => v.type === 'view'),
      assets: [],
      apiSurface: [],
      shellIntegration: {
        menuItems: [{ label: 'Home', view: 'MainView' }],
        appIcon: '📱',
        appName: manifest.name
      },
      permissions: []
    };
  }
  
  /**
   * Generate stub components for testing
   * @private
   * @param {Object} specification - Bundle specification
   * @returns {Object} Stub components
   */
  _generateStubComponents(specification) {
    const components = {};
    
    // Generate a main view component
    components['MainView'] = {
      name: 'MainView',
      type: 'view',
      files: {
        'views/main.js': {
          content: `/**
 * MainView for ${specification.manifest.name}
 * Auto-generated by PrimeOS App Factory
 */

class MainView {
  constructor() {
    console.log('MainView initialized');
  }
  
  render(container) {
    container.innerHTML = \`
      <div class="main-view">
        <h1>${specification.manifest.name}</h1>
        <p>${specification.manifest.description}</p>
        
        <div class="content">
          <p>This is a PrimeOS application.</p>
        </div>
      </div>
    \`;
  }
}

// Export for PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { MainView };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.MainView = MainView;
}`,
          language: 'javascript'
        }
      },
      dependencies: []
    };
    
    return components;
  }
  
  /**
   * Update project's current phase
   * @private
   * @param {string} projectId - Project ID
   * @param {string} phase - New phase
   * @returns {Promise<Object>} Updated project
   */
  async _updateProjectPhase(projectId, phase) {
    // Make sure phase is valid
    if (!this.workflowPhases.some(p => p.id === phase)) {
      throw new Error(`Invalid phase: ${phase}`);
    }
    
    // Update project
    return this._updateProject(projectId, { currentPhase: phase });
  }
  
  /**
   * Update progress for a specific phase
   * @private
   * @param {string} projectId - Project ID
   * @param {string} phase - Phase to update
   * @param {Object} progress - Updated progress data
   * @returns {Promise<Object>} Updated project
   */
  async _updateProjectProgress(projectId, phase, progress) {
    // Get current project
    const project = await this.getProject(projectId);
    
    // Create updated progress object
    const updatedProgress = {
      ...project.progress,
      [phase]: {
        ...project.progress[phase],
        ...progress
      }
    };
    
    // Update project
    return this._updateProject(projectId, { progress: updatedProgress });
  }
  
  /**
   * Update project data
   * @private
   * @param {string} projectId - Project ID
   * @param {Object} updates - Fields to update
   * @returns {Promise<Object>} Updated project
   */
  async _updateProject(projectId, updates) {
    try {
      // Get current project (from active projects or store)
      let project;
      
      if (this.activeProjects.has(projectId)) {
        project = this.activeProjects.get(projectId);
      } else {
        project = await this.store.get(projectId);
        
        if (!project || project.type !== 'app_factory_project') {
          throw new Error(`Project not found: ${projectId}`);
        }
      }
      
      // Create updated project
      const updatedProject = {
        ...project,
        ...updates,
        modified: new Date().toISOString()
      };
      
      // Save to storage
      await this.store.put(updatedProject);
      
      // Update active projects map
      this.activeProjects.set(projectId, {
        ...updatedProject,
        lastAccessed: new Date()
      });
      
      return updatedProject;
    } catch (error) {
      console.error(`Failed to update project ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Calculate progress percentage for a project
   * @private
   * @param {Object} project - Project object
   * @returns {number} Progress percentage (0-100)
   */
  _calculateProgressPercentage(project) {
    // Count completed phases
    let completedCount = 0;
    let totalRequired = 0;
    
    // Loop through workflow phases
    this.workflowPhases.forEach(phase => {
      // Only count required phases for percentage
      if (phase.required) {
        totalRequired++;
        
        // Check if this phase is completed
        if (project.progress[phase.id]?.status === 'completed') {
          completedCount++;
        }
      }
    });
    
    // Calculate percentage
    return Math.floor((completedCount / totalRequired) * 100);
  }
  
  /**
   * Send a project event notification
   * @private
   * @param {string} event - Event name
   * @param {string} projectId - Project ID
   * @param {Object} data - Additional event data
   */
  _notifyProjectEvent(event, projectId, data = {}) {
    if (this.eventBus) {
      this.eventBus.publish(`app-factory:project-${event}`, {
        projectId,
        timestamp: new Date().toISOString(),
        ...data
      });
    }
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { AppFactoryManager };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.AppFactoryManager = AppFactoryManager;
}