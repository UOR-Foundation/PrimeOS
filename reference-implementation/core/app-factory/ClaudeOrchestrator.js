/**
 * PrimeOS ClaudeOrchestrator
 * 
 * Coordinates AI interactions with Claude throughout the app creation process,
 * managing conversations, prompts, and context to enable a collaborative experience.
 */

class ClaudeOrchestrator {
  /**
   * Creates a new ClaudeOrchestrator instance
   * @param {Object} options - Configuration options
   * @param {Object} options.claudeService - ClaudeService instance for AI interactions
   * @param {Object} options.promptLibrary - Library of prompts for different phases
   * @param {Object} options.eventBus - Event bus for notifications
   */
  constructor(options = {}) {
    this.claudeService = options.claudeService;
    this.eventBus = options.eventBus;
    
    // Initialize prompt library
    this.promptLibrary = options.promptLibrary || {};
    
    // Load default prompt library if not provided
    if (Object.keys(this.promptLibrary).length === 0) {
      this._loadDefaultPromptLibrary();
    }
    
    // Conversation context by project
    this.conversationContext = new Map();
    
    console.log('ClaudeOrchestrator initialized');
  }
  
  /**
   * Run the inspiration phase to help articulate app vision
   * @param {string} projectId - Project identifier
   * @param {Object} initialInput - Initial user input
   * @returns {Promise<Object>} Inspiration phase results
   */
  async runInspirationPhase(projectId, initialInput = {}) {
    console.log(`Running inspiration phase for project: ${projectId}`);
    
    try {
      // Create phase context if needed
      this._initializeProjectContext(projectId, 'inspiration');
      
      // Prepare input for the phase
      const phaseInput = {
        initialInput,
        phase: 'inspiration'
      };
      
      // Get the appropriate prompt
      const prompt = this._getPrompt('inspiration', phaseInput);
      
      // Execute the interaction
      const response = await this._executeClaudeInteraction(
        projectId,
        prompt,
        'inspiration'
      );
      
      // Process the response
      const processedResponse = this._processInspirationResponse(response);
      
      // Store results in context
      this._updateProjectContext(projectId, 'inspiration', {
        completed: true,
        results: processedResponse
      });
      
      return processedResponse;
    } catch (error) {
      console.error(`Inspiration phase failed for ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Run the coherence mapping phase to build mathematical model
   * @param {string} projectId - Project identifier
   * @param {Object} inspirationResults - Results from inspiration phase
   * @returns {Promise<Object>} Coherence mapping results
   */
  async runCoherenceMappingPhase(projectId, inspirationResults) {
    console.log(`Running coherence mapping for project: ${projectId}`);
    
    try {
      // Create phase context if needed
      this._initializeProjectContext(projectId, 'coherenceMapping');
      
      // Prepare input for the phase
      const phaseInput = {
        inspirationResults,
        phase: 'coherenceMapping'
      };
      
      // Get the appropriate prompt
      const prompt = this._getPrompt('coherenceMapping', phaseInput);
      
      // Execute the interaction
      const response = await this._executeClaudeInteraction(
        projectId,
        prompt,
        'coherenceMapping'
      );
      
      // Process the response
      const processedResponse = this._processCoherenceMappingResponse(response);
      
      // Store results in context
      this._updateProjectContext(projectId, 'coherenceMapping', {
        completed: true,
        results: processedResponse
      });
      
      return processedResponse;
    } catch (error) {
      console.error(`Coherence mapping failed for ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Run the bundle specification phase
   * @param {string} projectId - Project identifier
   * @param {Object} coherenceResults - Results from coherence mapping phase
   * @returns {Promise<Object>} Bundle specification results
   */
  async runBundleSpecificationPhase(projectId, coherenceResults) {
    console.log(`Running bundle specification for project: ${projectId}`);
    
    try {
      // Create phase context if needed
      this._initializeProjectContext(projectId, 'bundleSpecification');
      
      // Prepare input for the phase
      const phaseInput = {
        coherenceResults,
        phase: 'bundleSpecification'
      };
      
      // Get the appropriate prompt
      const prompt = this._getPrompt('bundleSpecification', phaseInput);
      
      // Execute the interaction
      const response = await this._executeClaudeInteraction(
        projectId,
        prompt,
        'bundleSpecification'
      );
      
      // Process the response
      const processedResponse = this._processBundleSpecificationResponse(response);
      
      // Store results in context
      this._updateProjectContext(projectId, 'bundleSpecification', {
        completed: true,
        results: processedResponse
      });
      
      return processedResponse;
    } catch (error) {
      console.error(`Bundle specification failed for ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Run the component generation phase
   * @param {string} projectId - Project identifier
   * @param {Object} specificationResults - Results from specification phase
   * @param {Object} options - Generation options
   * @returns {Promise<Object>} Component generation results
   */
  async runComponentGenerationPhase(projectId, specificationResults, options = {}) {
    console.log(`Running component generation for project: ${projectId}`);
    
    try {
      // Create phase context if needed
      this._initializeProjectContext(projectId, 'componentGeneration');
      
      // Determine which components to generate
      const componentsToGenerate = options.components || 
        this._determineComponentGenerationOrder(specificationResults);
      
      // Generate components in dependency order
      const generatedComponents = {};
      
      for (const component of componentsToGenerate) {
        console.log(`Generating component: ${component.name}`);
        
        // Prepare input for component generation
        const componentInput = {
          component,
          specificationResults,
          previouslyGenerated: generatedComponents,
          phase: 'componentGeneration'
        };
        
        // Get component-specific prompt
        const prompt = this._getPrompt('componentGeneration', componentInput);
        
        // Execute the interaction for this component
        const response = await this._executeClaudeInteraction(
          projectId,
          prompt,
          `componentGeneration:${component.name}`
        );
        
        // Process the component response
        const processedComponent = this._processComponentGenerationResponse(
          response, 
          component
        );
        
        // Add to generated components
        generatedComponents[component.name] = processedComponent;
        
        // Notify progress
        if (this.eventBus) {
          this.eventBus.publish('app-factory:component-generated', {
            projectId,
            component: component.name,
            progress: Object.keys(generatedComponents).length / componentsToGenerate.length
          });
        }
      }
      
      // Store results in context
      this._updateProjectContext(projectId, 'componentGeneration', {
        completed: true,
        results: generatedComponents
      });
      
      return {
        components: generatedComponents,
        count: Object.keys(generatedComponents).length
      };
    } catch (error) {
      console.error(`Component generation failed for ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Run the bundle assembly phase
   * @param {string} projectId - Project identifier
   * @param {Object} components - Generated components
   * @param {Object} specification - Bundle specification
   * @returns {Promise<Object>} Assembled bundle
   */
  async runBundleAssemblyPhase(projectId, components, specification) {
    console.log(`Running bundle assembly for project: ${projectId}`);
    
    try {
      // Create phase context if needed
      this._initializeProjectContext(projectId, 'bundleAssembly');
      
      // Prepare input for the phase
      const phaseInput = {
        components,
        specification,
        phase: 'bundleAssembly'
      };
      
      // Get the appropriate prompt
      const prompt = this._getPrompt('bundleAssembly', phaseInput);
      
      // Execute the interaction
      const response = await this._executeClaudeInteraction(
        projectId,
        prompt,
        'bundleAssembly'
      );
      
      // Process the response
      const assembledBundle = this._processBundleAssemblyResponse(response, components);
      
      // Store results in context
      this._updateProjectContext(projectId, 'bundleAssembly', {
        completed: true,
        results: assembledBundle
      });
      
      return assembledBundle;
    } catch (error) {
      console.error(`Bundle assembly failed for ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Create documentation for a bundle
   * @param {string} projectId - Project identifier
   * @param {Object} bundle - Assembled bundle
   * @returns {Promise<Object>} Documentation files
   */
  async generateDocumentation(projectId, bundle) {
    console.log(`Generating documentation for project: ${projectId}`);
    
    try {
      // Prepare input for documentation
      const docInput = {
        bundle,
        phase: 'documentation'
      };
      
      // Get the appropriate prompt
      const prompt = this._getPrompt('documentation', docInput);
      
      // Execute the interaction
      const response = await this._executeClaudeInteraction(
        projectId,
        prompt,
        'documentation'
      );
      
      // Process the response
      const documentation = this._processDocumentationResponse(response);
      
      return documentation;
    } catch (error) {
      console.error(`Documentation generation failed for ${projectId}:`, error);
      throw error;
    }
  }
  
  /**
   * Clear conversation context for a project
   * @param {string} projectId - Project ID to clear
   */
  clearProjectContext(projectId) {
    if (this.conversationContext.has(projectId)) {
      console.log(`Clearing context for project: ${projectId}`);
      this.conversationContext.delete(projectId);
      
      // Also clear context in Claude service if available
      if (this.claudeService) {
        this.claudeService.clearConversationHistory(projectId);
      }
    }
  }
  
  /**
   * Initialize context for a project and phase
   * @private
   * @param {string} projectId - Project identifier
   * @param {string} phase - Project phase
   */
  _initializeProjectContext(projectId, phase) {
    if (!this.conversationContext.has(projectId)) {
      this.conversationContext.set(projectId, {
        phases: {},
        created: new Date().toISOString(),
        lastUpdated: new Date().toISOString()
      });
    }
    
    const projectContext = this.conversationContext.get(projectId);
    
    if (!projectContext.phases[phase]) {
      projectContext.phases[phase] = {
        started: new Date().toISOString(),
        completed: false,
        messages: [],
        results: null
      };
    }
  }
  
  /**
   * Update context for a project and phase
   * @private
   * @param {string} projectId - Project identifier
   * @param {string} phase - Project phase
   * @param {Object} data - Data to update
   */
  _updateProjectContext(projectId, phase, data) {
    this._initializeProjectContext(projectId, phase);
    
    const projectContext = this.conversationContext.get(projectId);
    projectContext.lastUpdated = new Date().toISOString();
    
    Object.assign(projectContext.phases[phase], data);
  }
  
  /**
   * Add a message to the project context
   * @private
   * @param {string} projectId - Project identifier
   * @param {string} phase - Project phase
   * @param {Object} message - Message to add
   */
  _addMessageToContext(projectId, phase, message) {
    this._initializeProjectContext(projectId, phase);
    
    const projectContext = this.conversationContext.get(projectId);
    projectContext.phases[phase].messages.push(message);
    projectContext.lastUpdated = new Date().toISOString();
  }
  
  /**
   * Get a prompt from the library
   * @private
   * @param {string} promptType - Type of prompt
   * @param {Object} data - Data for prompt templating
   * @returns {string} Prepared prompt
   */
  _getPrompt(promptType, data) {
    const promptTemplate = this.promptLibrary[promptType];
    
    if (!promptTemplate) {
      throw new Error(`Prompt template not found for type: ${promptType}`);
    }
    
    // Simple template replacement
    let prompt = promptTemplate;
    
    // Replace placeholders with data
    for (const [key, value] of Object.entries(data)) {
      const placeholder = `{${key}}`;
      
      if (prompt.includes(placeholder)) {
        // Format value based on type
        let formattedValue = value;
        if (typeof value === 'object') {
          formattedValue = JSON.stringify(value, null, 2);
        }
        
        prompt = prompt.replace(new RegExp(placeholder, 'g'), formattedValue);
      }
    }
    
    return prompt;
  }
  
  /**
   * Execute an interaction with Claude
   * @private
   * @param {string} projectId - Project identifier
   * @param {string} prompt - Prompt to send
   * @param {string} conversationId - Conversation identifier
   * @returns {Promise<string>} Claude response
   */
  async _executeClaudeInteraction(projectId, prompt, conversationId) {
    if (!this.claudeService) {
      console.warn('Claude service is not available. Using placeholder response.');
      return this._generatePlaceholderResponse(prompt, conversationId);
    }
    
    try {
      // Add the prompt to context
      this._addMessageToContext(projectId, conversationId.split(':')[0], {
        role: 'user',
        content: prompt,
        timestamp: new Date().toISOString()
      });
      
      // Execute the request
      try {
        const response = await this.claudeService.executeRequest(prompt, conversationId);
        
        // Add the response to context
        this._addMessageToContext(projectId, conversationId.split(':')[0], {
          role: 'assistant',
          content: response,
          timestamp: new Date().toISOString()
        });
        
        return response;
      } catch (error) {
        // Check if the error is related to missing API key
        if (error.message.includes('API key')) {
          console.warn('API key issue detected:', error.message);
          
          // Emit an event so the UI can show a notification
          if (this.eventBus) {
            this.eventBus.publish('app-factory:api-key-required', {
              projectId,
              conversationId,
              error: error.message,
              timestamp: new Date().toISOString()
            });
          }
          
          // Return a helpful message instead of placeholder
          const apiKeyError = `
          I need a Claude API key to assist with app creation. 
          
          To set your Claude API key:
          1. Open the Settings app (can be found in the app launcher)
          2. Navigate to the "API Keys" section
          3. Enter your Claude API key from Anthropic
          4. Save your settings
          
          Once you've added your API key, you can continue with the app creation process.
          `;
          
          // Add this error response to context
          this._addMessageToContext(projectId, conversationId.split(':')[0], {
            role: 'assistant',
            content: apiKeyError,
            timestamp: new Date().toISOString(),
            isError: true
          });
          
          return apiKeyError;
        }
        
        // For other errors, log and fallback to placeholder
        console.error(`Claude interaction failed:`, error);
        return this._generatePlaceholderResponse(prompt, conversationId);
      }
    } catch (error) {
      console.error(`Claude interaction context handling failed:`, error);
      return this._generatePlaceholderResponse(prompt, conversationId);
    }
  }
  
  /**
   * Check if Claude service is ready to use
   * @returns {Promise<boolean>} True if Claude service is ready
   */
  async isClaudeReady() {
    try {
      // Check if Claude service is available
      if (!this.claudeService) {
        return false;
      }
      
      // Check if API key is available - the service may have a method for this,
      // otherwise just check if the apiKey property is set
      if (typeof this.claudeService.hasApiKey === 'function') {
        return await this.claudeService.hasApiKey();
      }
      
      return !!this.claudeService.apiKey;
    } catch (error) {
      console.error('Failed to check Claude readiness:', error);
      return false;
    }
  }
  
  /**
   * Process response from the inspiration phase
   * @private
   * @param {string} response - Claude response
   * @returns {Object} Processed inspiration results
   */
  _processInspirationResponse(response) {
    try {
      // Extract structured data from response
      const data = this._extractJsonFromResponse(response);
      
      // Basic validation of required fields
      if (!data.appPurpose) {
        data.appPurpose = this._extractPurposeFromText(response);
      }
      
      if (!data.targetUsers) {
        data.targetUsers = this._extractTargetUsersFromText(response);
      }
      
      if (!data.keyFeatures) {
        data.keyFeatures = this._extractFeaturesFromText(response);
      }
      
      return {
        appPurpose: data.appPurpose || '',
        appDomain: data.appDomain || data.domain || '',
        targetUsers: data.targetUsers || [],
        useCases: data.useCases || [],
        keyFeatures: data.keyFeatures || [],
        keyTerms: data.keyTerms || []
      };
    } catch (error) {
      console.error('Failed to process inspiration response:', error);
      
      // Return a basic fallback structure
      return {
        appPurpose: 'App purpose could not be determined',
        appDomain: 'General',
        targetUsers: ['Users'],
        useCases: ['Basic functionality'],
        keyFeatures: ['Core features'],
        keyTerms: []
      };
    }
  }
  
  /**
   * Process response from the coherence mapping phase
   * @private
   * @param {string} response - Claude response
   * @returns {Object} Processed coherence mapping
   */
  _processCoherenceMappingResponse(response) {
    try {
      // Extract structured data from response
      const data = this._extractJsonFromResponse(response);
      
      // Ensure required sections exist
      return {
        entities: data.entities || [],
        relationships: data.relationships || [],
        processes: data.processes || data.processFlows || [],
        states: data.states || data.stateTransitions || [],
        invariants: data.invariants || [],
        constraints: data.constraints || [],
        coherenceMetrics: data.coherenceMetrics || {
          score: 0.8,
          interfaceCompleteness: 0.85,
          structuralIntegrity: 0.9
        }
      };
    } catch (error) {
      console.error('Failed to process coherence mapping response:', error);
      
      // Return a basic fallback structure
      return {
        entities: [],
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
    }
  }
  
  /**
   * Process response from the bundle specification phase
   * @private
   * @param {string} response - Claude response
   * @returns {Object} Processed bundle specification
   */
  _processBundleSpecificationResponse(response) {
    try {
      // Extract structured data from response
      const data = this._extractJsonFromResponse(response);
      
      // Ensure required sections exist
      return {
        manifest: data.manifest || {
          name: 'Untitled App',
          version: '1.0.0',
          description: 'App description',
          entryPoint: 'views/main.js'
        },
        components: data.components || [],
        models: data.models || [],
        services: data.services || [],
        views: data.views || [],
        assets: data.assets || [],
        apiSurface: data.apiSurface || data.apis || [],
        shellIntegration: data.shellIntegration || {},
        permissions: data.permissions || []
      };
    } catch (error) {
      console.error('Failed to process bundle specification response:', error);
      
      // Return a basic fallback structure
      return {
        manifest: {
          name: 'Untitled App',
          version: '1.0.0',
          description: 'App description',
          entryPoint: 'views/main.js'
        },
        components: [],
        models: [],
        services: [],
        views: [],
        assets: [],
        apiSurface: [],
        shellIntegration: {},
        permissions: []
      };
    }
  }
  
  /**
   * Process response from component generation
   * @private
   * @param {string} response - Claude response
   * @param {Object} component - Component definition
   * @returns {Object} Processed component with code
   */
  _processComponentGenerationResponse(response, component) {
    try {
      // Extract structured data from response
      const data = this._extractJsonFromResponse(response);
      
      // If we have a files array, convert to more usable structure
      let files = {};
      if (Array.isArray(data.files)) {
        data.files.forEach(file => {
          files[file.path] = {
            content: file.content,
            language: this._determineLanguageFromPath(file.path)
          };
        });
      } else if (data.files && typeof data.files === 'object') {
        files = data.files;
      }
      
      // Return the processed component
      return {
        name: component.name,
        type: component.type,
        files,
        dependencies: data.dependencies || component.dependencies || [],
        tests: data.tests || [],
        documentation: data.documentation || ''
      };
    } catch (error) {
      console.error(`Failed to process component generation response for ${component.name}:`, error);
      
      // Return a basic fallback structure
      return {
        name: component.name,
        type: component.type,
        files: {},
        dependencies: component.dependencies || [],
        tests: [],
        documentation: 'Component documentation could not be generated'
      };
    }
  }
  
  /**
   * Process response from the bundle assembly phase
   * @private
   * @param {string} response - Claude response
   * @param {Object} components - Generated components
   * @returns {Object} Assembled bundle
   */
  _processBundleAssemblyResponse(response, components) {
    try {
      // Extract structured data from response
      const data = this._extractJsonFromResponse(response);
      
      // Merge with components if assembly didn't include them
      if (!data.components && components) {
        data.components = components;
      }
      
      // Ensure required sections exist
      return {
        manifest: data.manifest || {
          name: 'Untitled App',
          version: '1.0.0'
        },
        components: data.components || {},
        structure: data.structure || {},
        entryPoints: data.entryPoints || [],
        coherenceScore: data.coherenceScore || 0.8
      };
    } catch (error) {
      console.error('Failed to process bundle assembly response:', error);
      
      // Return a basic fallback structure
      return {
        manifest: {
          name: 'Untitled App',
          version: '1.0.0'
        },
        components: components || {},
        structure: {},
        entryPoints: [],
        coherenceScore: 0.8
      };
    }
  }
  
  /**
   * Process response from documentation generation
   * @private
   * @param {string} response - Claude response
   * @returns {Object} Documentation files
   */
  _processDocumentationResponse(response) {
    try {
      // Extract structured data from response
      const data = this._extractJsonFromResponse(response);
      
      // If we have a files array, convert to more usable structure
      let files = {};
      if (Array.isArray(data.files)) {
        data.files.forEach(file => {
          files[file.path] = {
            content: file.content,
            language: 'markdown'
          };
        });
      } else if (data.files && typeof data.files === 'object') {
        files = data.files;
      } else {
        // Create default docs if none provided
        files = {
          'docs/README.md': {
            content: '# Application Documentation\n\nThis documentation was auto-generated.',
            language: 'markdown'
          },
          'docs/usage.md': {
            content: '# Usage Guide\n\nInstructions for using the application.',
            language: 'markdown'
          }
        };
      }
      
      return { files };
    } catch (error) {
      console.error('Failed to process documentation response:', error);
      
      // Return basic documentation
      return {
        files: {
          'docs/README.md': {
            content: '# Application Documentation\n\nThis documentation was auto-generated.',
            language: 'markdown'
          }
        }
      };
    }
  }
  
  /**
   * Extract JSON from Claude response
   * @private
   * @param {string} response - Claude response
   * @returns {Object} Extracted JSON
   */
  _extractJsonFromResponse(response) {
    try {
      // Look for JSON blocks in various formats
      const jsonMatch = response.match(/```json\s*([\s\S]*?)\s*```|<json>([\s\S]*?)<\/json>/i);
      
      if (jsonMatch) {
        const jsonContent = jsonMatch[1] || jsonMatch[2];
        return JSON.parse(jsonContent);
      }
      
      // Look for anything that looks like a JSON object or array
      const potentialJson = response.match(/(\{[\s\S]*\}|\[[\s\S]*\])/);
      
      if (potentialJson) {
        return JSON.parse(potentialJson[1]);
      }
      
      // Try parsing the entire response as JSON
      return JSON.parse(response);
    } catch (error) {
      console.error('Failed to extract JSON from response:', error);
      throw new Error('No valid JSON found in response');
    }
  }
  
  /**
   * Generate a placeholder response for testing/fallback
   * @private
   * @param {string} prompt - Original prompt
   * @param {string} conversationId - Conversation ID
   * @returns {string} Placeholder response
   */
  _generatePlaceholderResponse(prompt, conversationId) {
    // Simple placeholder by conversation type
    const responseType = conversationId.split(':')[0];
    
    switch (responseType) {
      case 'inspiration':
        return JSON.stringify({
          appPurpose: 'Demo application purpose',
          appDomain: 'Productivity',
          targetUsers: ['General users', 'Professionals'],
          useCases: ['Daily task management', 'Note taking'],
          keyFeatures: ['Create and manage tasks', 'Save and organize notes'],
          keyTerms: ['task', 'note', 'reminder']
        }, null, 2);
      
      case 'coherenceMapping':
        return JSON.stringify({
          entities: [
            { name: 'Task', properties: ['id', 'title', 'description', 'completed'] },
            { name: 'User', properties: ['id', 'name', 'email'] }
          ],
          relationships: [
            { source: 'User', target: 'Task', type: 'one-to-many' }
          ],
          processes: [
            { name: 'TaskCreation', steps: ['ValidateInput', 'CreateTask', 'NotifyUser'] }
          ],
          coherenceMetrics: { score: 0.85 }
        }, null, 2);
      
      case 'bundleSpecification':
        return JSON.stringify({
          manifest: {
            name: 'Demo App',
            version: '1.0.0',
            description: 'A demo application',
            entryPoint: 'views/main.js'
          },
          components: [
            { name: 'TaskList', type: 'component' },
            { name: 'TaskForm', type: 'component' }
          ],
          models: [
            { name: 'TaskModel', type: 'model' }
          ],
          views: [
            { name: 'MainView', type: 'view' }
          ]
        }, null, 2);
      
      case 'componentGeneration':
        // Extract component name if available
        const componentName = conversationId.split(':')[1] || 'Component';
        return JSON.stringify({
          files: [
            { 
              path: `components/${componentName}.js`,
              content: `/**\n * ${componentName} Component\n */\n\nclass ${componentName} {\n  constructor() {\n    console.log('${componentName} initialized');\n  }\n}`
            }
          ],
          dependencies: []
        }, null, 2);
      
      case 'bundleAssembly':
        return JSON.stringify({
          manifest: {
            name: 'Demo App',
            version: '1.0.0',
            description: 'A demo application',
            entryPoint: 'views/main.js'
          },
          structure: {
            root: {
              components: {},
              models: {},
              views: {}
            }
          },
          entryPoints: ['views/main.js'],
          coherenceScore: 0.85
        }, null, 2);
      
      case 'documentation':
        return JSON.stringify({
          files: [
            { 
              path: 'docs/README.md',
              content: '# Demo Application\n\nThis is automatically generated documentation for the demo application.'
            },
            {
              path: 'docs/usage.md',
              content: '# Usage Guide\n\n## Getting Started\n\nLearn how to use the application.'
            }
          ]
        }, null, 2);
      
      default:
        return JSON.stringify({
          message: 'Placeholder response for ' + conversationId,
          timestamp: new Date().toISOString()
        }, null, 2);
    }
  }
  
  /**
   * Determine programming language from file path
   * @private
   * @param {string} path - File path
   * @returns {string} Language identifier
   */
  _determineLanguageFromPath(path) {
    const extension = path.split('.').pop().toLowerCase();
    
    switch (extension) {
      case 'js':
        return 'javascript';
      case 'ts':
        return 'typescript';
      case 'html':
        return 'html';
      case 'css':
        return 'css';
      case 'json':
        return 'json';
      case 'md':
        return 'markdown';
      default:
        return 'text';
    }
  }
  
  /**
   * Determine component generation order based on dependencies
   * @private
   * @param {Object} specification - Bundle specification
   * @returns {Array} Components in dependency order
   */
  _determineComponentGenerationOrder(specification) {
    // Start with all components
    const allComponents = [];
    
    // Add components from each category
    if (specification.components) {
      allComponents.push(...specification.components.map(c => ({...c, type: 'component'})));
    }
    
    if (specification.models) {
      allComponents.push(...specification.models.map(c => ({...c, type: 'model'})));
    }
    
    if (specification.services) {
      allComponents.push(...specification.services.map(c => ({...c, type: 'service'})));
    }
    
    if (specification.views) {
      allComponents.push(...specification.views.map(c => ({...c, type: 'view'})));
    }
    
    // Sort components based on dependencies
    const componentMap = {};
    allComponents.forEach(component => {
      componentMap[component.name] = component;
    });
    
    // Build dependency graph
    const dependencyGraph = {};
    allComponents.forEach(component => {
      dependencyGraph[component.name] = component.dependencies || [];
    });
    
    // Detect cycles and resolve dependencies
    const componentOrder = [];
    const visited = {};
    const temp = {};
    
    function visit(componentName) {
      if (temp[componentName]) {
        // Cycle detected
        console.warn(`Circular dependency detected involving ${componentName}`);
        return;
      }
      
      if (visited[componentName]) {
        return;
      }
      
      temp[componentName] = true;
      
      // Visit dependencies
      const dependencies = dependencyGraph[componentName] || [];
      for (const dep of dependencies) {
        visit(dep);
      }
      
      delete temp[componentName];
      visited[componentName] = true;
      
      if (componentMap[componentName]) {
        componentOrder.push(componentMap[componentName]);
      }
    }
    
    // Visit all components
    for (const component of allComponents) {
      if (!visited[component.name]) {
        visit(component.name);
      }
    }
    
    // Generate models and services first, then UI components
    return componentOrder.sort((a, b) => {
      // Models first
      if (a.type === 'model' && b.type !== 'model') return -1;
      if (a.type !== 'model' && b.type === 'model') return 1;
      
      // Services second
      if (a.type === 'service' && b.type !== 'service') return -1;
      if (a.type !== 'service' && b.type === 'service') return 1;
      
      // Components third
      if (a.type === 'component' && b.type !== 'component') return -1;
      if (a.type !== 'component' && b.type === 'component') return 1;
      
      // Views last
      if (a.type === 'view' && b.type !== 'view') return 1;
      if (a.type !== 'view' && b.type === 'view') return -1;
      
      return 0;
    });
  }
  
  /**
   * Extract app purpose from text response
   * @private
   * @param {string} text - Response text
   * @returns {string} Extracted purpose
   */
  _extractPurposeFromText(text) {
    // Look for key phrases
    const purposeRegex = /purpose:?\s*([^\n]+)|application(\s+will|\s+should|\s+is\s+designed\s+to)?:?\s*([^\n]+)/i;
    const match = text.match(purposeRegex);
    
    if (match) {
      return match[1] || match[3] || 'General purpose application';
    }
    
    return 'General purpose application';
  }
  
  /**
   * Extract target users from text response
   * @private
   * @param {string} text - Response text
   * @returns {Array} Extracted users
   */
  _extractTargetUsersFromText(text) {
    // Look for user section
    const userSection = text.match(/users:?\s*([^\n]+)|audience:?\s*([^\n]+)/i);
    
    if (userSection) {
      const userText = userSection[1] || userSection[2];
      // Split by commas or 'and'
      return userText.split(/,|\sand\s/).map(user => user.trim()).filter(Boolean);
    }
    
    return ['General users'];
  }
  
  /**
   * Extract features from text response
   * @private
   * @param {string} text - Response text
   * @returns {Array} Extracted features
   */
  _extractFeaturesFromText(text) {
    // Look for feature section or bullet points
    const featureMatch = text.match(/features:?\s*([\s\S]+?)(?=\n\s*\n|\n\s*#|\n\s*\*\*|\n\s*\d+\.|\n\s*-)/i);
    
    if (featureMatch) {
      const featureText = featureMatch[1];
      // Look for bullet points
      const bulletPoints = featureText.match(/[-*•]\s*([^\n]+)/g);
      
      if (bulletPoints) {
        return bulletPoints.map(point => point.replace(/^[-*•]\s*/, '').trim()).filter(Boolean);
      }
      
      // If no bullet points, split by newlines
      return featureText.split('\n').map(line => line.trim()).filter(Boolean);
    }
    
    return ['Basic functionality'];
  }
  
  /**
   * Load default prompt library
   * @private
   */
  _loadDefaultPromptLibrary() {
    this.promptLibrary = {
      inspiration: `
        You are an expert software architect helping design a PrimeOS application. I need your help to refine and articulate my application idea.

        Let's explore what you're trying to build through a collaborative conversation. Think of this as an expert-led brainstorming session.

        Please provide the following information about your application idea:
        {initialInput}

        I'll help you refine this into a clear vision by exploring:

        1. PURPOSE: What primary problem does this app solve? What transformation does it enable?
        2. DOMAIN: What field or category does this application belong to?
        3. USERS: Who will use this application? What are their characteristics?
        4. USE CASES: What specific scenarios will users engage with?
        5. KEY FEATURES: What essential capabilities must the app have?
        6. TERMINOLOGY: What domain-specific terms are important?

        Please be specific and detailed in your responses. I'll provide guidance to help clarify and structure your vision.

        Format your response as structured JSON that defines the app concept.
      `,
      
      coherenceMapping: `
        Based on the inspiration phase results, let's build a mathematically coherent model of the application:

        {inspirationResults}

        I'll guide you through identifying:

        1. ENTITIES: Core data objects that represent the key concepts in your application
        2. RELATIONSHIPS: How these entities relate to each other (one-to-many, many-to-many, etc.)
        3. PROCESS FLOWS: How information and actions flow through your system
        4. STATE TRANSITIONS: How the application changes states during operation
        5. INVARIANTS: Properties that must remain true throughout the system
        6. CONSTRAINTS: Limitations and rules that must be enforced

        For each entity, I'll identify:
        - Properties and their types
        - Validation rules
        - Relationships to other entities
        - Operations that can be performed

        For processes, I'll map:
        - Inputs and preconditions
        - Steps and transformations
        - Outputs and postconditions
        - Error states and handling

        This coherence map will ensure your application has mathematical integrity from its foundation.

        Format your response as structured JSON defining the coherence model.
      `,
      
      bundleSpecification: `
        Based on the coherence mapping, let's create a detailed specification for the PrimeOS application bundle:

        {coherenceResults}

        The specification will define the complete structure following the Prime Bundle format:

        1. MANIFEST: Application metadata including name, version, permissions, and dependencies
        2. COMPONENTS: Reusable UI elements and their properties, methods, and events
        3. MODELS: Data structures and their operations based on the coherence entities
        4. SERVICES: Business logic and external integrations
        5. VIEWS: Application screens and layouts
        6. ASSETS: Required resources like images or fonts
        7. API SURFACE: Interface points between components
        8. SHELL INTEGRATION: How the app interacts with the PrimeOS environment
        9. PERMISSIONS: System capabilities the app requires

        For each component in the specification, I'll define:
        - Purpose and responsibilities
        - Dependencies and relationships
        - Interface contract (inputs, outputs, events)
        - Internal state
        - Mathematical properties and invariants

        This specification will serve as the blueprint for generating the application code.

        Format your response as structured JSON defining the complete bundle specification.
      `,
      
      componentGeneration: `
        Generate code for the {component.name} component based on the bundle specification:

        Component: {component}
        
        Previously generated components:
        {previouslyGenerated}

        Full specification:
        {specificationResults}

        Create complete, production-ready code that follows PrimeOS patterns and conventions. The code should:

        1. Adhere to the mathematical coherence principles established
        2. Implement the complete interface contract
        3. Handle all edge cases and error conditions
        4. Include proper documentation
        5. Follow clean code best practices
        6. Include comprehensive unit tests

        For implementation, follow these specific PrimeOS patterns:
        - Component structure follows Prime manifold principles
        - Mathematical coherence is maintained through invariants
        - Components communicate through clean interface contracts
        - Utilize pure functions and immutability where appropriate
        - Separate concerns between presentation, logic, and data

        Format your response as a JSON object containing the files needed for this component:
        {
          "files": [
            { "path": "path/to/file.js", "content": "file content" }
          ],
          "dependencies": ["list of component dependencies"],
          "tests": ["list of test files"]
        }
      `,
      
      bundleAssembly: `
        Assemble the complete application bundle from the generated components:

        Components:
        {components}

        Specification:
        {specification}

        Create a cohesive bundle that integrates all components according to the specification. The assembly should:

        1. Ensure proper component initialization order
        2. Establish communication channels between components
        3. Configure event subscriptions and routing
        4. Set up proper dependency injection
        5. Implement the application entry point
        6. Validate coherence across the entire system
        7. Generate the final manifest with all metadata

        The assembled bundle should represent a complete, ready-to-deploy PrimeOS application with mathematical coherence throughout.

        Format your response as JSON representing the complete assembled bundle.
      `,
      
      documentation: `
        Generate comprehensive documentation for the assembled application bundle:

        {bundle}

        Create the following documentation files:

        1. README.md - Overview and getting started guide
        2. ARCHITECTURE.md - Detailed component design and interactions
        3. API.md - Complete API reference for all components
        4. USAGE.md - User guide with examples
        5. DEVELOPMENT.md - Guide for future development

        The documentation should:
        - Be clear and accessible for developers of different experience levels
        - Explain the mathematical coherence principles
        - Include diagrams (as text/markdown) where helpful
        - Provide examples of common usage patterns
        - Include troubleshooting information

        Format your response as a JSON object containing the documentation files:
        {
          "files": [
            { "path": "docs/filename.md", "content": "file content" }
          ]
        }
      `
    };
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { ClaudeOrchestrator };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.ClaudeOrchestrator = ClaudeOrchestrator;
}