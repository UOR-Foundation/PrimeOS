/**
 * PrimeOS App Factory Manager
 * 
 * Main orchestration service for the App Factory system that guides users
 * through the process of creating and modifying PrimeOS applications using
 * the Claude AI assistant.
 */

class AppFactoryManager {
  /**
   * Creates a new App Factory Manager instance
   * @param {Object} options - Configuration options
   * @param {Object} options.claudeService - ClaudeService instance for AI assistance
   * @param {Object} options.store - PrimeStore instance for project persistence
   * @param {Object} options.eventBus - Event bus for notifications
   * @param {Object} options.bundleManager - BundleManager for app packaging
   * @param {Object} options.testRunner - TestRunner for validation
   */
  constructor(options) {
    // Validate required dependencies
    if (!options.claudeService) {
      throw new Error('AppFactoryManager requires a claudeService instance');
    }
    
    if (!options.store) {
      throw new Error('AppFactoryManager requires a store instance');
    }
    
    if (!options.eventBus) {
      throw new Error('AppFactoryManager requires an eventBus instance');
    }
    
    // Store dependencies
    this.claudeService = options.claudeService;
    this.store = options.store;
    this.eventBus = options.eventBus;
    this.bundleManager = options.bundleManager || null;
    this.testRunner = options.testRunner || null;
    
    // Initialize state
    this.activeProjects = new Map();
    
    // Workflow steps definition
    this.workflowSteps = [
      { id: 'domain', name: 'Domain Identification', required: true },
      { id: 'requirements', name: 'Requirements Gathering', required: true },
      { id: 'specification', name: 'Specification Creation', required: true },
      { id: 'generation', name: 'Code Generation', required: true },
      { id: 'testing', name: 'Testing and Validation', required: true },
      { id: 'publishing', name: 'App Publishing', required: false }
    ];
    
    // Bind methods
    this._loadActiveProjects = this._loadActiveProjects.bind(this);
    
    // Register event handlers
    this.eventBus.subscribe('system:ready', this._loadActiveProjects);
    
    console.log('AppFactoryManager initialized');
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
   * Create a new app project
   * @param {string} projectName - The name of the project
   * @param {string} description - Brief description of the app
   * @param {Object} options - Additional options
   * @returns {Promise<string>} The project ID
   */
  async createProject(projectName, description, options = {}) {
    if (!projectName) {
      throw new Error('Project name is required');
    }
    
    console.log(`Creating new app project: ${projectName}`);
    
    try {
      // Generate a unique project ID
      const projectId = `app_factory_${Date.now()}_${Math.floor(Math.random() * 10000)}`;
      
      // Create initial project state
      const project = {
        id: projectId,
        type: 'app_factory_project',
        name: projectName,
        description: description || '',
        created: new Date().toISOString(),
        modified: new Date().toISOString(),
        currentStep: 'domain',
        progress: {
          domain: { status: 'pending', data: null },
          requirements: { status: 'pending', data: null },
          specification: { status: 'pending', data: null },
          generation: { status: 'pending', data: null },
          testing: { status: 'pending', data: null },
          publishing: { status: 'pending', data: null }
        },
        options: options || {},
        files: [],
        testResults: null,
        publishingInfo: null,
        conversationContext: []
      };
      
      // Save the project to storage
      await this.store.put(project);
      
      // Add to active projects map
      this.activeProjects.set(projectId, {
        ...project,
        lastAccessed: new Date()
      });
      
      // Notify project creation
      this._notifyProjectEvent('created', projectId, { name: projectName });
      
      return projectId;
    } catch (error) {
      console.error(`Failed to create project ${projectName}:`, error);
      throw error;
    }
  }
  
  /**
   * Load an existing project
   * @param {string} projectId - The project ID to load
   * @returns {Promise<Object>} The project data
   */
  async loadProject(projectId) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    console.log(`Loading app project: ${projectId}`);
    
    try {
      // Check if project is already in memory
      if (this.activeProjects.has(projectId)) {
        const project = this.activeProjects.get(projectId);
        project.lastAccessed = new Date();
        return project;
      }
      
      // Load project from storage
      const project = await this.store.get(projectId);
      
      if (!project) {
        throw new Error(`Project not found: ${projectId}`);
      }
      
      if (project.type !== 'app_factory_project') {
        throw new Error(`Invalid project type for ${projectId}`);
      }
      
      // Add to active projects map
      this.activeProjects.set(projectId, {
        ...project,
        lastAccessed: new Date()
      });
      
      // Notify project loaded
      this._notifyProjectEvent('loaded', projectId, { name: project.name });
      
      return project;
    } catch (error) {
      console.error(`Failed to load project ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Import an existing app for modification
   * @param {Object} appBundle - The app bundle to import
   * @param {string} projectName - Optional name override for the project
   * @returns {Promise<string>} The project ID
   */
  async importApp(appBundle, projectName) {
    if (!appBundle || !appBundle.manifest) {
      throw new Error('Valid app bundle is required');
    }
    
    console.log(`Importing app: ${appBundle.manifest.id}`);
    
    try {
      // Generate a unique project ID
      const projectId = `app_factory_${Date.now()}_${Math.floor(Math.random() * 10000)}`;
      
      // Use bundle name if project name not provided
      const name = projectName || `${appBundle.manifest.name} (Imported)`;
      
      // Create initial project state from bundle
      const project = {
        id: projectId,
        type: 'app_factory_project',
        name,
        description: appBundle.manifest.description || '',
        created: new Date().toISOString(),
        modified: new Date().toISOString(),
        currentStep: 'specification', // Start at specification for imports
        progress: {
          domain: { status: 'completed', data: { purpose: appBundle.manifest.description } },
          requirements: { status: 'completed', data: { entities: [] } }, // Will be extracted from code
          specification: { status: 'pending', data: null }, // Will be derived from code
          generation: { status: 'completed', data: { files: [] } },
          testing: { status: 'pending', data: null },
          publishing: { status: 'pending', data: null }
        },
        options: {
          isImported: true,
          originalBundle: {
            id: appBundle.manifest.id,
            version: appBundle.manifest.version
          }
        },
        files: [],
        testResults: null,
        publishingInfo: null,
        conversationContext: []
      };
      
      // Extract files from bundle
      for (const [path, content] of Object.entries(appBundle.code)) {
        project.files.push({
          path,
          content: atob(content), // Decode base64 content
          generated: false,
          modified: false
        });
      }
      
      // Extract resources from bundle
      if (appBundle.resources) {
        for (const [path, content] of Object.entries(appBundle.resources)) {
          project.files.push({
            path: `resources/${path}`,
            content: atob(content), // Decode base64 content
            generated: false,
            modified: false,
            isResource: true
          });
        }
      }
      
      // Save the project to storage
      await this.store.put(project);
      
      // Add to active projects map
      this.activeProjects.set(projectId, {
        ...project,
        lastAccessed: new Date()
      });
      
      // Notify project import
      this._notifyProjectEvent('imported', projectId, {
        name,
        originalId: appBundle.manifest.id
      });
      
      // Extract app specification from imported code
      this._deriveSpecificationFromCode(projectId);
      
      return projectId;
    } catch (error) {
      console.error(`Failed to import app:`, error);
      throw error;
    }
  }
  
  /**
   * Extract app specification from imported code
   * @private
   * @param {string} projectId - The project ID
   * @returns {Promise<void>}
   */
  async _deriveSpecificationFromCode(projectId) {
    try {
      const project = await this.loadProject(projectId);
      
      // Update project status
      project.progress.specification.status = 'in_progress';
      await this._updateProject(projectId, project);
      
      // Extract code content for analysis
      const codeFiles = project.files.filter(file => !file.isResource);
      
      // Use Claude to analyze the code
      const specification = await this.claudeService.deriveSpecificationFromCode(
        codeFiles,
        project.name,
        project.description
      );
      
      // Update project with derived specification
      project.progress.specification = {
        status: 'completed',
        data: specification
      };
      
      // Save updated project
      await this._updateProject(projectId, project);
      
      // Notify specification completion
      this._notifyProjectEvent('specification-derived', projectId, {
        name: project.name
      });
    } catch (error) {
      console.error(`Failed to derive specification from code for ${projectId}:`, error);
      
      // Update project to show error
      const project = await this.loadProject(projectId);
      project.progress.specification.status = 'error';
      project.progress.specification.error = error.message;
      await this._updateProject(projectId, project);
    }
  }
  
  /**
   * Continue the app creation workflow from the current step
   * @param {string} projectId - The project ID
   * @param {string} [specifiedStep] - Optional specific step to navigate to
   * @returns {Promise<Object>} The updated workflow state
   */
  async continueWorkflow(projectId, specifiedStep) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    console.log(`Continuing workflow for project: ${projectId}`);
    
    try {
      // Load the project
      const project = await this.loadProject(projectId);
      
      // Determine current step
      const currentStep = specifiedStep || project.currentStep;
      
      // Validate step exists
      if (!this.workflowSteps.some(step => step.id === currentStep)) {
        throw new Error(`Invalid workflow step: ${currentStep}`);
      }
      
      // Update project with current step
      project.currentStep = currentStep;
      project.modified = new Date().toISOString();
      
      await this._updateProject(projectId, project);
      
      // Process the current step
      const stepHandler = this[`_process${currentStep.charAt(0).toUpperCase() + currentStep.slice(1)}Step`];
      
      if (typeof stepHandler !== 'function') {
        throw new Error(`Handler not implemented for step: ${currentStep}`);
      }
      
      // Handle the step
      const stepResult = await stepHandler.call(this, projectId, project);
      
      // Return current workflow state
      return {
        projectId,
        currentStep,
        progress: project.progress,
        result: stepResult
      };
    } catch (error) {
      console.error(`Workflow continuation failed for ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Process the domain identification step
   * @private
   * @param {string} projectId - The project ID
   * @param {Object} project - Current project data
   * @returns {Promise<Object>} Step result
   */
  async _processDomainStep(projectId, project) {
    console.log(`Processing domain step for project: ${projectId}`);
    
    // If domain is already completed, return the data
    if (project.progress.domain.status === 'completed') {
      return {
        status: 'completed',
        data: project.progress.domain.data
      };
    }
    
    // Mark step as in progress
    project.progress.domain.status = 'in_progress';
    await this._updateProject(projectId, project);
    
    // Return the step interface that needs user interaction
    return {
      status: 'awaiting_input',
      requiredInputs: [
        {
          id: 'purpose',
          label: 'App Purpose',
          type: 'text',
          description: 'Describe the main purpose of your application'
        },
        {
          id: 'domain',
          label: 'App Domain',
          type: 'text',
          description: 'What category or field does this app belong to?'
        },
        {
          id: 'audience',
          label: 'Target Audience',
          type: 'text',
          description: 'Who will use this application?'
        }
      ]
    };
  }
  
  /**
   * Update domain step with user input
   * @param {string} projectId - The project ID
   * @param {Object} domainData - User input for domain step
   * @returns {Promise<Object>} Updated workflow state
   */
  async updateDomainStep(projectId, domainData) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    if (!domainData) {
      throw new Error('Domain data is required');
    }
    
    console.log(`Updating domain step for project: ${projectId}`);
    
    try {
      // Load the project
      const project = await this.loadProject(projectId);
      
      // Validate current step
      if (project.currentStep !== 'domain') {
        throw new Error(`Project is not on domain step, current step: ${project.currentStep}`);
      }
      
      // Apply domain insights from Claude
      const enhancedDomain = await this.claudeService.generateDomainInsights(domainData);
      
      // Update project with domain data
      project.progress.domain = {
        status: 'completed',
        data: enhancedDomain
      };
      
      // Move to next step
      project.currentStep = 'requirements';
      project.modified = new Date().toISOString();
      
      await this._updateProject(projectId, project);
      
      // Notify step completion
      this._notifyProjectEvent('step-completed', projectId, {
        step: 'domain',
        nextStep: 'requirements'
      });
      
      // Continue to the next step
      return this.continueWorkflow(projectId);
    } catch (error) {
      console.error(`Failed to update domain step for ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Process the requirements gathering step
   * @private
   * @param {string} projectId - The project ID
   * @param {Object} project - Current project data
   * @returns {Promise<Object>} Step result
   */
  async _processRequirementsStep(projectId, project) {
    console.log(`Processing requirements step for project: ${projectId}`);
    
    // If requirements are already completed, return the data
    if (project.progress.requirements.status === 'completed') {
      return {
        status: 'completed',
        data: project.progress.requirements.data
      };
    }
    
    // Ensure domain step is completed
    if (project.progress.domain.status !== 'completed') {
      throw new Error('Domain step must be completed before requirements');
    }
    
    // Mark step as in progress
    project.progress.requirements.status = 'in_progress';
    await this._updateProject(projectId, project);
    
    // Use domain data to suggest entities and features
    const suggestions = await this.claudeService.suggestRequirements(
      project.progress.domain.data
    );
    
    // Return the step interface that needs user interaction
    return {
      status: 'awaiting_input',
      suggestions,
      requiredInputs: [
        {
          id: 'entities',
          label: 'Data Entities',
          type: 'entity_editor',
          description: 'Define the main data objects in your application'
        },
        {
          id: 'features',
          label: 'App Features',
          type: 'feature_list',
          description: 'List the main features your app should have'
        },
        {
          id: 'interactions',
          label: 'User Interactions',
          type: 'text',
          description: 'Describe how users will interact with the app'
        }
      ]
    };
  }
  
  /**
   * Update requirements step with user input
   * @param {string} projectId - The project ID
   * @param {Object} requirementsData - User input for requirements step
   * @returns {Promise<Object>} Updated workflow state
   */
  async updateRequirementsStep(projectId, requirementsData) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    if (!requirementsData) {
      throw new Error('Requirements data is required');
    }
    
    console.log(`Updating requirements step for project: ${projectId}`);
    
    try {
      // Load the project
      const project = await this.loadProject(projectId);
      
      // Validate current step
      if (project.currentStep !== 'requirements') {
        throw new Error(`Project is not on requirements step, current step: ${project.currentStep}`);
      }
      
      // Apply requirements enhancements from Claude
      const enhancedRequirements = await this.claudeService.enhanceRequirements(
        requirementsData,
        project.progress.domain.data
      );
      
      // Update project with requirements data
      project.progress.requirements = {
        status: 'completed',
        data: enhancedRequirements
      };
      
      // Move to next step
      project.currentStep = 'specification';
      project.modified = new Date().toISOString();
      
      await this._updateProject(projectId, project);
      
      // Notify step completion
      this._notifyProjectEvent('step-completed', projectId, {
        step: 'requirements',
        nextStep: 'specification'
      });
      
      // Continue to the next step
      return this.continueWorkflow(projectId);
    } catch (error) {
      console.error(`Failed to update requirements step for ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Process the specification creation step
   * @private
   * @param {string} projectId - The project ID
   * @param {Object} project - Current project data
   * @returns {Promise<Object>} Step result
   */
  async _processSpecificationStep(projectId, project) {
    console.log(`Processing specification step for project: ${projectId}`);
    
    // If specification is already completed, return the data
    if (project.progress.specification.status === 'completed') {
      return {
        status: 'completed',
        data: project.progress.specification.data
      };
    }
    
    // For imported apps, we might be deriving the spec from code
    if (project.progress.specification.status === 'in_progress') {
      return {
        status: 'in_progress',
        message: 'Deriving specification from application code...'
      };
    }
    
    // For new apps, ensure requirements step is completed
    if (!project.options.isImported && project.progress.requirements.status !== 'completed') {
      throw new Error('Requirements step must be completed before specification');
    }
    
    // Mark step as in progress
    project.progress.specification.status = 'in_progress';
    await this._updateProject(projectId, project);
    
    try {
      // Use domain and requirements to generate a specification
      const specification = await this.claudeService.generateAppSpecification(
        project.progress.domain.data,
        project.progress.requirements.data
      );
      
      // Update project with specification
      project.progress.specification = {
        status: 'completed',
        data: specification
      };
      
      // Move to next step
      project.currentStep = 'generation';
      project.modified = new Date().toISOString();
      
      await this._updateProject(projectId, project);
      
      // Notify step completion
      this._notifyProjectEvent('step-completed', projectId, {
        step: 'specification',
        nextStep: 'generation'
      });
      
      // Return the completed specification
      return {
        status: 'completed',
        data: specification
      };
    } catch (error) {
      console.error(`Failed to generate specification for ${projectId}:`, error);
      
      // Update project to show error
      project.progress.specification.status = 'error';
      project.progress.specification.error = error.message;
      await this._updateProject(projectId, project);
      
      // Return error status
      return {
        status: 'error',
        message: error.message
      };
    }
  }
  
  /**
   * Update specification step with user edits
   * @param {string} projectId - The project ID
   * @param {Object} specificationData - User edited specification
   * @returns {Promise<Object>} Updated workflow state
   */
  async updateSpecificationStep(projectId, specificationData) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    if (!specificationData) {
      throw new Error('Specification data is required');
    }
    
    console.log(`Updating specification step for project: ${projectId}`);
    
    try {
      // Load the project
      const project = await this.loadProject(projectId);
      
      // Validate spec data
      const validationResult = await this.claudeService.validateSpecification(specificationData);
      
      if (!validationResult.valid) {
        return {
          status: 'error',
          message: 'Invalid specification',
          validationErrors: validationResult.errors
        };
      }
      
      // Update project with specification data
      project.progress.specification = {
        status: 'completed',
        data: specificationData
      };
      
      // Move to next step if we're on the specification step
      if (project.currentStep === 'specification') {
        project.currentStep = 'generation';
      }
      
      project.modified = new Date().toISOString();
      
      await this._updateProject(projectId, project);
      
      // Notify spec update
      this._notifyProjectEvent('specification-updated', projectId, {
        nextStep: project.currentStep
      });
      
      // If we've moved to generation, continue the workflow
      if (project.currentStep === 'generation') {
        return this.continueWorkflow(projectId);
      }
      
      // Otherwise return the current state
      return {
        status: 'completed',
        data: specificationData
      };
    } catch (error) {
      console.error(`Failed to update specification for ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Process the code generation step
   * @private
   * @param {string} projectId - The project ID
   * @param {Object} project - Current project data
   * @returns {Promise<Object>} Step result
   */
  async _processGenerationStep(projectId, project) {
    console.log(`Processing code generation step for project: ${projectId}`);
    
    // If generation is already completed, return the data
    if (project.progress.generation.status === 'completed') {
      return {
        status: 'completed',
        data: {
          fileCount: project.files.length
        }
      };
    }
    
    // Ensure specification step is completed
    if (project.progress.specification.status !== 'completed') {
      throw new Error('Specification step must be completed before generation');
    }
    
    // Mark step as in progress
    project.progress.generation.status = 'in_progress';
    await this._updateProject(projectId, project);
    
    try {
      // Generate app code based on specification
      const generationResult = await this.claudeService.generateAppCode(
        project.progress.specification.data
      );
      
      // Update project with generated files
      project.files = generationResult.files.map(file => ({
        path: file.path,
        content: file.content,
        generated: true,
        modified: false,
        isResource: file.isResource || false
      }));
      
      // Update project progress
      project.progress.generation = {
        status: 'completed',
        data: {
          generatedAt: new Date().toISOString(),
          fileCount: project.files.length,
          structure: generationResult.structure
        }
      };
      
      // Move to next step
      project.currentStep = 'testing';
      project.modified = new Date().toISOString();
      
      await this._updateProject(projectId, project);
      
      // Notify step completion
      this._notifyProjectEvent('step-completed', projectId, {
        step: 'generation',
        nextStep: 'testing',
        fileCount: project.files.length
      });
      
      // Return generation result
      return {
        status: 'completed',
        data: {
          fileCount: project.files.length,
          structure: generationResult.structure
        }
      };
    } catch (error) {
      console.error(`Failed to generate code for ${projectId}:`, error);
      
      // Update project to show error
      project.progress.generation.status = 'error';
      project.progress.generation.error = error.message;
      await this._updateProject(projectId, project);
      
      // Return error status
      return {
        status: 'error',
        message: error.message
      };
    }
  }
  
  /**
   * Update a specific file in the generated code
   * @param {string} projectId - The project ID
   * @param {string} filePath - Path of the file to update
   * @param {string} content - New file content
   * @returns {Promise<Object>} Update result
   */
  async updateGeneratedFile(projectId, filePath, content) {
    if (!projectId || !filePath || content === undefined) {
      throw new Error('Project ID, file path, and content are required');
    }
    
    console.log(`Updating file ${filePath} for project: ${projectId}`);
    
    try {
      // Load the project
      const project = await this.loadProject(projectId);
      
      // Find the file
      const fileIndex = project.files.findIndex(file => file.path === filePath);
      
      if (fileIndex === -1) {
        throw new Error(`File not found: ${filePath}`);
      }
      
      // Update the file
      project.files[fileIndex] = {
        ...project.files[fileIndex],
        content,
        modified: true
      };
      
      // Update project
      project.modified = new Date().toISOString();
      await this._updateProject(projectId, project);
      
      // Notify file update
      this._notifyProjectEvent('file-updated', projectId, {
        filePath
      });
      
      return {
        status: 'success',
        file: {
          path: filePath,
          modified: true
        }
      };
    } catch (error) {
      console.error(`Failed to update file for ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Add a new file to the project
   * @param {string} projectId - The project ID
   * @param {string} filePath - Path for the new file
   * @param {string} content - File content
   * @param {Object} options - Additional options
   * @returns {Promise<Object>} Result of the operation
   */
  async addProjectFile(projectId, filePath, content, options = {}) {
    if (!projectId || !filePath) {
      throw new Error('Project ID and file path are required');
    }
    
    console.log(`Adding file ${filePath} to project: ${projectId}`);
    
    try {
      // Load the project
      const project = await this.loadProject(projectId);
      
      // Check if file already exists
      if (project.files.some(file => file.path === filePath)) {
        throw new Error(`File already exists: ${filePath}`);
      }
      
      // Add the file
      project.files.push({
        path: filePath,
        content: content || '',
        generated: false,
        modified: true,
        isResource: options.isResource || false
      });
      
      // Update project
      project.modified = new Date().toISOString();
      await this._updateProject(projectId, project);
      
      // Notify file addition
      this._notifyProjectEvent('file-added', projectId, {
        filePath
      });
      
      return {
        status: 'success',
        file: {
          path: filePath,
          isResource: options.isResource || false
        }
      };
    } catch (error) {
      console.error(`Failed to add file to ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Delete a file from the project
   * @param {string} projectId - The project ID
   * @param {string} filePath - Path of the file to delete
   * @returns {Promise<Object>} Result of the operation
   */
  async deleteProjectFile(projectId, filePath) {
    if (!projectId || !filePath) {
      throw new Error('Project ID and file path are required');
    }
    
    console.log(`Deleting file ${filePath} from project: ${projectId}`);
    
    try {
      // Load the project
      const project = await this.loadProject(projectId);
      
      // Find the file
      const fileIndex = project.files.findIndex(file => file.path === filePath);
      
      if (fileIndex === -1) {
        throw new Error(`File not found: ${filePath}`);
      }
      
      // Remove the file
      project.files.splice(fileIndex, 1);
      
      // Update project
      project.modified = new Date().toISOString();
      await this._updateProject(projectId, project);
      
      // Notify file deletion
      this._notifyProjectEvent('file-deleted', projectId, {
        filePath
      });
      
      return {
        status: 'success',
        filePath
      };
    } catch (error) {
      console.error(`Failed to delete file from ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Process the testing and validation step
   * @private
   * @param {string} projectId - The project ID
   * @param {Object} project - Current project data
   * @returns {Promise<Object>} Step result
   */
  async _processTestingStep(projectId, project) {
    console.log(`Processing testing step for project: ${projectId}`);
    
    // If testing is already completed, return the data
    if (project.progress.testing.status === 'completed') {
      return {
        status: 'completed',
        data: project.progress.testing.data
      };
    }
    
    // Ensure generation step is completed
    if (project.progress.generation.status !== 'completed') {
      throw new Error('Generation step must be completed before testing');
    }
    
    // Mark step as in progress
    project.progress.testing.status = 'in_progress';
    await this._updateProject(projectId, project);
    
    try {
      // Validate test runner availability
      if (!this.testRunner) {
        throw new Error('Test runner is not available');
      }
      
      // Run tests on the generated code
      const testResults = await this.testRunner.runTests(project.files);
      
      if (testResults.success) {
        // Update project with successful test results
        project.progress.testing = {
          status: 'completed',
          data: testResults
        };
        
        // Save test results
        project.testResults = testResults;
        
        // Move to next step
        project.currentStep = 'publishing';
        project.modified = new Date().toISOString();
        
        await this._updateProject(projectId, project);
        
        // Notify step completion
        this._notifyProjectEvent('step-completed', projectId, {
          step: 'testing',
          nextStep: 'publishing',
          testsPassed: testResults.passed,
          testsTotal: testResults.total
        });
        
        // Return testing result
        return {
          status: 'completed',
          data: testResults
        };
      } else {
        // Tests failed, regenerate code with feedback
        console.log(`Tests failed for project ${projectId}, regenerating code`);
        
        // Attempt code regeneration with test feedback
        const regeneratedCode = await this.claudeService.improveCode(
          project.files,
          testResults,
          project.progress.specification.data
        );
        
        // Update project with regenerated files
        project.files = regeneratedCode.files.map(file => ({
          path: file.path,
          content: file.content,
          generated: true,
          modified: false,
          isResource: file.isResource || false
        }));
        
        // Update project progress
        project.progress.generation = {
          status: 'completed',
          data: {
            generatedAt: new Date().toISOString(),
            fileCount: project.files.length,
            regenerated: true
          }
        };
        
        // Keep testing step as in progress
        project.progress.testing = {
          status: 'in_progress',
          data: {
            lastTestRun: testResults,
            regenerationAttempt: (project.progress.testing.data?.regenerationAttempt || 0) + 1
          }
        };
        
        // Save updated project
        project.modified = new Date().toISOString();
        await this._updateProject(projectId, project);
        
        // Notify regeneration
        this._notifyProjectEvent('code-regenerated', projectId, {
          attempt: project.progress.testing.data.regenerationAttempt,
          testsFailed: testResults.total - testResults.passed
        });
        
        // Return regeneration status
        return {
          status: 'regenerated',
          message: 'Code regenerated based on test feedback',
          attempt: project.progress.testing.data.regenerationAttempt,
          previousResults: testResults
        };
      }
    } catch (error) {
      console.error(`Testing failed for ${projectId}:`, error);
      
      // Update project to show error
      project.progress.testing.status = 'error';
      project.progress.testing.error = error.message;
      await this._updateProject(projectId, project);
      
      // Return error status
      return {
        status: 'error',
        message: error.message
      };
    }
  }
  
  /**
   * Manually run tests for a project
   * @param {string} projectId - The project ID
   * @returns {Promise<Object>} Test results
   */
  async runTests(projectId) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    console.log(`Running tests for project: ${projectId}`);
    
    try {
      // Load the project
      const project = await this.loadProject(projectId);
      
      // Ensure we have files to test
      if (!project.files || project.files.length === 0) {
        throw new Error('No files available to test');
      }
      
      // Mark testing as in progress
      project.progress.testing = {
        status: 'in_progress',
        data: project.progress.testing.data || null
      };
      
      await this._updateProject(projectId, project);
      
      // Validate test runner availability
      if (!this.testRunner) {
        throw new Error('Test runner is not available');
      }
      
      // Run tests on the generated code
      const testResults = await this.testRunner.runTests(project.files);
      
      // Update project with test results
      project.testResults = testResults;
      
      if (testResults.success) {
        project.progress.testing = {
          status: 'completed',
          data: testResults
        };
      } else {
        project.progress.testing = {
          status: 'failed',
          data: {
            ...testResults,
            regenerationAttempt: (project.progress.testing.data?.regenerationAttempt || 0) + 1
          }
        };
      }
      
      // Save updated project
      project.modified = new Date().toISOString();
      await this._updateProject(projectId, project);
      
      // Notify test completion
      this._notifyProjectEvent('tests-run', projectId, {
        success: testResults.success,
        passed: testResults.passed,
        total: testResults.total
      });
      
      return testResults;
    } catch (error) {
      console.error(`Failed to run tests for ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Process the app publishing step
   * @private
   * @param {string} projectId - The project ID
   * @param {Object} project - Current project data
   * @returns {Promise<Object>} Step result
   */
  async _processPublishingStep(projectId, project) {
    console.log(`Processing publishing step for project: ${projectId}`);
    
    // If publishing is already completed, return the data
    if (project.progress.publishing.status === 'completed') {
      return {
        status: 'completed',
        data: project.progress.publishing.data
      };
    }
    
    // Ensure testing step is completed (or at least attempted)
    if (project.progress.testing.status !== 'completed' && 
        project.progress.testing.status !== 'failed') {
      throw new Error('Testing step must be completed before publishing');
    }
    
    // Return the publishing interface for user input
    return {
      status: 'awaiting_input',
      requiredInputs: [
        {
          id: 'publishingMethod',
          label: 'Publishing Method',
          type: 'select',
          options: [
            { value: 'bundle', label: 'App Bundle' },
            { value: 'github', label: 'GitHub Repository' }
          ],
          description: 'How would you like to publish this app?'
        },
        {
          id: 'repositoryUrl',
          label: 'GitHub Repository URL',
          type: 'text',
          description: 'URL for GitHub repository (if using GitHub)',
          conditional: {
            field: 'publishingMethod',
            value: 'github'
          }
        },
        {
          id: 'appMetadata',
          label: 'App Metadata',
          type: 'metadata_editor',
          description: 'Additional information for your app',
          defaultValue: {
            name: project.name,
            version: '1.0.0',
            author: '',
            license: 'MIT'
          }
        }
      ]
    };
  }
  
  /**
   * Update publishing step with user input
   * @param {string} projectId - The project ID
   * @param {Object} publishingData - User input for publishing step
   * @returns {Promise<Object>} Updated workflow state
   */
  async updatePublishingStep(projectId, publishingData) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    if (!publishingData) {
      throw new Error('Publishing data is required');
    }
    
    console.log(`Updating publishing step for project: ${projectId}`);
    
    try {
      // Load the project
      const project = await this.loadProject(projectId);
      
      // Mark publishing as in progress
      project.progress.publishing.status = 'in_progress';
      await this._updateProject(projectId, project);
      
      // Validate bundle manager availability if needed
      if (!this.bundleManager && publishingData.publishingMethod === 'bundle') {
        throw new Error('Bundle manager is not available');
      }
      
      let publishingResult = null;
      
      // Handle different publishing methods
      if (publishingData.publishingMethod === 'bundle') {
        // Create app bundle
        publishingResult = await this._createAppBundle(projectId, publishingData.appMetadata);
      } else if (publishingData.publishingMethod === 'github') {
        // Publish to GitHub
        publishingResult = await this._publishToGitHub(
          projectId,
          publishingData.repositoryUrl,
          publishingData.appMetadata
        );
      } else {
        throw new Error(`Unsupported publishing method: ${publishingData.publishingMethod}`);
      }
      
      // Update project with publishing result
      project.progress.publishing = {
        status: 'completed',
        data: {
          method: publishingData.publishingMethod,
          metadata: publishingData.appMetadata,
          result: publishingResult
        }
      };
      
      // Save publishing info
      project.publishingInfo = {
        publishedAt: new Date().toISOString(),
        method: publishingData.publishingMethod,
        metadata: publishingData.appMetadata,
        result: publishingResult
      };
      
      // Save updated project
      project.modified = new Date().toISOString();
      await this._updateProject(projectId, project);
      
      // Notify publication
      this._notifyProjectEvent('app-published', projectId, {
        method: publishingData.publishingMethod,
        metadata: publishingData.appMetadata
      });
      
      return {
        status: 'completed',
        data: publishingResult
      };
    } catch (error) {
      console.error(`Failed to publish app for ${projectId}:`, error);
      
      // Load the project again (might have changed)
      const project = await this.loadProject(projectId);
      
      // Update project to show error
      project.progress.publishing.status = 'error';
      project.progress.publishing.error = error.message;
      await this._updateProject(projectId, project);
      
      throw error;
    }
  }
  
  /**
   * Create an app bundle for publishing
   * @private
   * @param {string} projectId - The project ID
   * @param {Object} metadata - App metadata
   * @returns {Promise<Object>} Bundle creation result
   */
  async _createAppBundle(projectId, metadata) {
    const project = await this.loadProject(projectId);
    
    // Prepare bundle structure
    const bundleId = metadata.id || `com.primeos.${project.name.toLowerCase().replace(/\s+/g, '-')}`;
    
    // Create app record for bundling
    const appRecord = {
      id: bundleId,
      name: metadata.name || project.name,
      version: metadata.version || '1.0.0',
      author: metadata.author || 'PrimeOS App Factory',
      description: metadata.description || project.description,
      entryPoint: 'index.js',
      tags: metadata.tags || [],
      permissions: metadata.permissions || []
    };
    
    // Register the app
    await this.store.put({
      ...appRecord,
      type: 'app',
      registered: new Date().toISOString(),
      bundleable: true
    });
    
    // Prepare app files for storage
    const codeFiles = project.files.filter(file => !file.isResource).map(file => ({
      id: `${bundleId}:${file.path}`,
      path: file.path,
      appId: bundleId,
      name: file.path.split('/').pop(),
      type: 'file',
      isCode: true,
      content: file.content,
      encoding: 'text',
      created: new Date(),
      modified: new Date()
    }));
    
    const resourceFiles = project.files.filter(file => file.isResource).map(file => ({
      id: `${bundleId}:${file.path}`,
      path: file.path.replace(/^resources\//, ''),
      appId: bundleId,
      name: file.path.split('/').pop(),
      type: 'file',
      isCode: false,
      content: file.content,
      encoding: 'text',
      created: new Date(),
      modified: new Date()
    }));
    
    // Save all files
    await this.store.saveAll(null, [...codeFiles, ...resourceFiles]);
    
    // Create the bundle
    const bundle = await this.bundleManager.createBundle(bundleId);
    
    return {
      bundleId,
      bundle
    };
  }
  
  /**
   * Publish app to GitHub repository
   * @private
   * @param {string} projectId - The project ID
   * @param {string} repositoryUrl - GitHub repository URL
   * @param {Object} metadata - App metadata
   * @returns {Promise<Object>} GitHub publishing result
   */
  async _publishToGitHub(projectId, repositoryUrl, metadata) {
    // This would be implemented with GitHub API integration
    // For now, return instructions for manual publishing
    return {
      status: 'instructions',
      repositoryUrl,
      instructions: [
        '1. Create a new repository on GitHub',
        '2. Initialize with a README',
        '3. Clone the repository locally',
        '4. Copy the app files to the repository',
        '5. Create a bundle.json file with app metadata',
        '6. Commit and push the changes',
        '7. Your app is now published!'
      ]
    };
  }
  
  /**
   * Export the project as an app bundle
   * @param {string} projectId - The project ID
   * @returns {Promise<Object>} Exported bundle
   */
  async exportProject(projectId) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    console.log(`Exporting project: ${projectId}`);
    
    try {
      // Load the project
      const project = await this.loadProject(projectId);
      
      // If the project was already published as a bundle, return that bundle
      if (project.publishingInfo && 
          project.publishingInfo.method === 'bundle' &&
          project.publishingInfo.result.bundle) {
        return project.publishingInfo.result.bundle;
      }
      
      // Otherwise, create a temporary bundle
      const metadata = {
        name: project.name,
        version: '1.0.0',
        author: 'PrimeOS App Factory',
        description: project.description
      };
      
      // Create a unique bundle ID for export
      const bundleId = `temp.export.${project.name.toLowerCase().replace(/\s+/g, '-')}`;
      
      // Prepare bundle structure
      const manifest = {
        id: bundleId,
        name: metadata.name,
        version: metadata.version,
        author: metadata.author,
        description: metadata.description,
        entryPoint: 'index.js',
        tags: [],
        permissions: [],
        compatibilityVersion: '1.0.0',
        created: new Date().toISOString()
      };
      
      // Prepare code and resources
      const code = {};
      const resources = {};
      
      for (const file of project.files) {
        if (file.isResource) {
          resources[file.path.replace(/^resources\//, '')] = btoa(file.content);
        } else {
          code[file.path] = btoa(file.content);
        }
      }
      
      // Create bundle
      const bundle = {
        manifest,
        code,
        resources
      };
      
      return bundle;
    } catch (error) {
      console.error(`Failed to export project ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Get project status and progress
   * @param {string} projectId - The project ID
   * @returns {Promise<Object>} Project status and progress
   */
  async getProjectStatus(projectId) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    try {
      // Load the project
      const project = await this.loadProject(projectId);
      
      // Calculate progress percentage
      const completedSteps = Object.values(project.progress)
        .filter(step => step.status === 'completed').length;
      
      const totalRequiredSteps = this.workflowSteps
        .filter(step => step.required).length;
      
      const progressPercentage = Math.floor(
        (completedSteps / totalRequiredSteps) * 100
      );
      
      return {
        id: project.id,
        name: project.name,
        description: project.description,
        currentStep: project.currentStep,
        stepName: this.workflowSteps.find(step => step.id === project.currentStep)?.name,
        progress: project.progress,
        progressPercentage,
        created: project.created,
        modified: project.modified,
        fileCount: project.files.length,
        isImported: project.options.isImported || false,
        hasErrors: Object.values(project.progress).some(step => step.status === 'error')
      };
    } catch (error) {
      console.error(`Failed to get status for project ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Get all active projects
   * @returns {Promise<Array>} List of active projects
   */
  async getProjects() {
    try {
      // Query all app factory projects from the store
      const projectRecords = await this.store.query({
        index: 'type',
        value: 'app_factory_project'
      });
      
      // Return simplified project list
      return projectRecords.map(project => ({
        id: project.id,
        name: project.name,
        description: project.description,
        currentStep: project.currentStep,
        created: project.created,
        modified: project.modified,
        progress: Object.values(project.progress)
          .filter(step => step.status === 'completed').length
      }));
    } catch (error) {
      console.error('Failed to get projects:', error);
      throw error;
    }
  }
  
  /**
   * Delete a project
   * @param {string} projectId - The project ID
   * @returns {Promise<boolean>} Success indicator
   */
  async deleteProject(projectId) {
    if (!projectId) {
      throw new Error('Project ID is required');
    }
    
    console.log(`Deleting project: ${projectId}`);
    
    try {
      // Load the project to verify it exists
      await this.loadProject(projectId);
      
      // Remove from active projects map
      this.activeProjects.delete(projectId);
      
      // Remove from storage
      await this.store.remove(projectId);
      
      // Notify project deletion
      this._notifyProjectEvent('deleted', projectId);
      
      return true;
    } catch (error) {
      console.error(`Failed to delete project ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Update project data in storage
   * @private
   * @param {string} projectId - The project ID
   * @param {Object} projectData - Updated project data
   * @returns {Promise<void>}
   */
  async _updateProject(projectId, projectData) {
    // Update active projects map
    this.activeProjects.set(projectId, {
      ...projectData,
      lastAccessed: new Date()
    });
    
    // Save to storage
    await this.store.put(projectData);
  }
  
  /**
   * Send a project event notification
   * @private
   * @param {string} event - Event name
   * @param {string} projectId - Project ID
   * @param {Object} data - Event data
   */
  _notifyProjectEvent(event, projectId, data = {}) {
    this.eventBus.publish(`app-factory:${event}`, {
      projectId,
      timestamp: new Date().toISOString(),
      ...data
    });
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