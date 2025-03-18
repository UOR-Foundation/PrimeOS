/**
 * PrimeOS Claude Service
 * 
 * Service for interacting with the Anthropic Claude API to assist with
 * app creation, code generation, and improvement in the App Factory.
 */

// Import dependencies if in Node environment
let SecureVault;
try {
  if (typeof window === 'undefined' || !window.PrimeOS || !window.PrimeOS.SecureVault) {
    const secureVaultModule = require('../identity/secure-vault');
    SecureVault = secureVaultModule.SecureVault;
  } else {
    SecureVault = window.PrimeOS.SecureVault;
  }
} catch (error) {
  console.warn('SecureVault not available, will use direct API key:', error);
}

class ClaudeService {
  /**
   * Creates a new Claude Service instance
   * @param {Object} options - Configuration options
   * @param {string} options.apiKey - Anthropic API key (optional if secureVault provided)
   * @param {string} options.apiUrl - API endpoint URL
   * @param {Object} options.eventBus - Event bus for notifications
   * @param {Object} options.promptTemplates - Custom prompt templates
   * @param {Object} options.secureVault - Secure vault for API key storage
   * @param {Object} options.configManager - Configuration manager
   */
  constructor(options = {}) {
    // Store dependencies
    this.eventBus = options.eventBus || null;
    
    // Create secure vault if not provided
    if (options.secureVault) {
      this.secureVault = options.secureVault;
    } else if (SecureVault) {
      try {
        this.secureVault = new SecureVault({ eventBus: this.eventBus });
        console.log('Created new SecureVault for API key storage');
      } catch (error) {
        console.error('Failed to create SecureVault:', error);
        this.secureVault = null;
      }
    } else {
      this.secureVault = null;
    }
    
    this.configManager = options.configManager || null;
    
    // Store configuration
    this.apiKey = options.apiKey || '';
    this.apiUrl = options.apiUrl || 'https://api.anthropic.com/v1/messages';
    this.model = options.model || 'claude-3-opus-20240229';
    
    // Load custom prompt templates if provided
    this.promptTemplates = options.promptTemplates || {};
    
    // Default rate limiting settings
    this.rateLimit = {
      maxRequestsPerMinute: options.maxRequestsPerMinute || 10,
      requestQueue: [],
      requestsInLastMinute: 0,
      lastRequestTimestamp: 0
    };
    
    // Conversation history for context
    this.conversationHistory = new Map();
    
    // Load default prompt templates
    this._loadDefaultPromptTemplates();
    
    // Bind methods
    this._executeRequest = this._executeRequest.bind(this);
    this._enforceRateLimit = this._enforceRateLimit.bind(this);
    this._loadApiKey = this._loadApiKey.bind(this);
    
    // Try to load API key from secure vault
    if (this.secureVault) {
      this._loadApiKey()
        .then(() => console.log('API key loaded from secure vault'))
        .catch(err => console.error('Failed to load API key:', err));
    }
    
    // Listen for API key changes from Settings app
    if (this.eventBus) {
      this.eventBus.subscribe('settings:api-key-changed', this._handleApiKeyChange.bind(this));
      
      // Also listen for changes to API URL and model from settings
      this.eventBus.subscribe('settings:changed', event => {
        if (event.category === 'apiKeys') {
          if (event.key === 'claudeApiUrl' && event.value) {
            this.apiUrl = event.value;
            console.log('Claude API URL updated from settings');
          }
          else if (event.key === 'claudeModel' && event.value) {
            this.model = event.value;
            console.log('Claude model updated from settings');
          }
        }
      });
    }
    
    console.log('ClaudeService initialized');
  }
  
  /**
   * Load API key from secure vault
   * @private
   * @returns {Promise<void>}
   */
  async _loadApiKey() {
    try {
      if (!this.secureVault) {
        return;
      }
      
      // Load API key from secure vault
      const apiKey = await this.secureVault.getSecret('claudeApiKey');
      
      if (apiKey) {
        this.apiKey = apiKey;
        console.log('API key loaded from secure vault');
      } else {
        console.warn('No API key found in secure vault');
      }
      
      // Load API URL from configuration manager
      if (this.configManager) {
        const apiUrl = await this.configManager.getConfig('apiEndpoints.claudeApiUrl', this.apiUrl);
        if (apiUrl) {
          this.apiUrl = apiUrl;
        }
      }
    } catch (error) {
      console.error('Failed to load API key from secure vault:', error);
    }
  }
  
  /**
   * Handle API key change event from Settings app
   * @private
   * @param {Object} event - API key change event
   */
  _handleApiKeyChange(event) {
    if (event.key === 'claudeApiKey' && event.value) {
      console.log('API key updated from Settings app');
      this.apiKey = event.value;
    }
  }
  
  /**
   * Load default prompt templates
   * @private
   */
  _loadDefaultPromptTemplates() {
    // Only load defaults if not already provided
    if (Object.keys(this.promptTemplates).length > 0) {
      return;
    }
    
    this.promptTemplates = {
      domainInsights: `
        You are an expert software architect helping design a PrimeOS application. 
        Based on the user's app description, provide insights about the domain, potential entities,
        and key features.
        
        App Description: {description}
        
        Include the following in your analysis:
        1. Domain Area: The primary domain and sub-domains this app belongs to
        2. Target Users: Who would use this application and why
        3. Key Concepts: Important domain-specific concepts and terminology
        4. Potential Entities: Main data objects and their relationships
        5. Core Features: Essential capabilities the app should have
        
        Format your response as structured JSON with the above sections.
      `,
      
      suggestRequirements: `
        Based on the following app domain information, suggest a comprehensive set of
        requirements including entities, features, and user interactions.
        
        Domain Information:
        {domainData}
        
        Provide your suggestions in the following format:
        
        1. Entities: Key data objects with their properties and relationships
        2. Features: Important app capabilities prioritized by core/secondary
        3. User Interactions: How users will interact with the application 
        4. Technical Requirements: Any specific PrimeOS integrations needed
        
        Format your response as structured JSON that can be directly used in the app generation process.
      `,
      
      enhanceRequirements: `
        Enhance and structure the provided application requirements for a PrimeOS app.
        
        Domain Information:
        {domainData}
        
        User-Provided Requirements:
        {requirements}
        
        Please enhance these requirements by:
        1. Adding missing entity properties and relationships
        2. Identifying potential edge cases and validations
        3. Suggesting additional features that would complement the core functionality
        4. Ensuring all requirements are clear, complete and implementable
        
        Return a comprehensive, structured set of requirements as JSON that covers all aspects of the application.
      `,
      
      generateSpecification: `
        Create a detailed technical specification for a PrimeOS application based on the
        domain and requirements information.
        
        Domain Information:
        {domainData}
        
        Requirements:
        {requirements}
        
        Your specification should include:
        
        1. Architecture Overview: High-level architecture diagram (in text form)
        2. Data Models: Complete schema definitions for all entities
        3. Component Structure: UI components and their relationships
        4. API Interfaces: Internal and external API endpoints
        5. Storage Strategy: How data will be persisted
        6. User Interface Design: Layout descriptions for all screens
        7. PrimeOS Integration: How the app integrates with PrimeOS features
        8. Testing Strategy: Test cases for core functionality
        
        Format your specification as a structured JSON document that will be used for code generation.
      `,
      
      validateSpecification: `
        Validate the following PrimeOS app specification for completeness, consistency, and feasibility.
        
        App Specification:
        {specification}
        
        Check for:
        1. Missing required components
        2. Inconsistencies between different parts of the spec
        3. Technical feasibility within PrimeOS
        4. Completeness of data models
        5. API contract correctness
        6. UI component definition completeness
        
        Additionally, validate these Prime Framework requirements:
        1. Proper manifold structure (meta/invariant/variant decomposition)
        2. Base 0-3 hierarchy alignment
        3. Mathematical coherence between components
        4. Interface contract completeness
        5. Proper manifold depth assignments for data properties
        6. Coherence constraints and thresholds
        7. Component responsibility boundaries
        
        Provide a validation report with any issues found and suggestions for improvement.
        Return your response as JSON with valid: true/false and errors/warnings if applicable.
      `,
      
      generateAppCode: `
        Generate complete code for a PrimeOS application based on this specification.
        
        App Specification:
        {specification}
        
        Follow these guidelines:
        1. Create all necessary files for a complete, functional PrimeOS app
        2. Include HTML, CSS, and JavaScript files as needed
        3. Follow PrimeOS coding conventions and patterns
        4. Integrate correctly with PrimeOS AppAPI and other core services
        5. Implement all required business logic and UI components
        6. Include comprehensive unit tests for core functionality
        7. Provide clear comments and documentation
        8. Structure the code for maintainability and performance
        
        Important: Follow these manifold decomposition principles from the Prime Framework:
        1. Break down components into discrete manifolds with the meta/invariant/variant structure
        2. Organize code according to the Base 0-3 hierarchy (Neural Network, Resource, Kernel, Application)
        3. Ensure each component has a clearly defined mathematical coherence
        4. Implement proper interface contracts between components
        5. Use pure functions and immutable data patterns
        6. Maintain single responsibility for each file
        7. Apply depth-based organization for data models with manifest depth indicators
        
        For each file, provide the full path and complete code content.
        Format your response as a JSON array of file objects, each with "path" and "content" properties.
      `,
      
      improveCode: `
        Improve the provided PrimeOS application code to fix test failures and enhance quality.
        
        Original App Specification:
        {specification}
        
        Test Results:
        {testResults}
        
        Code Files:
        {files}
        
        Please:
        1. Analyze the test failures and identify root causes
        2. Fix all issues causing test failures
        3. Improve code quality, readability, and performance
        4. Ensure compliance with PrimeOS patterns and conventions
        5. Add or improve comments and documentation where helpful
        
        Provide a complete set of improved files, including both those that need changes and those that don't.
        Format your response as a JSON array of file objects, each with "path" and "content" properties.
      `,
      
      deriveSpecificationFromCode: `
        Analyze the provided PrimeOS application code and derive a detailed specification from it.
        
        App Name: {appName}
        Description: {description}
        
        Code Files:
        {files}
        
        Create a comprehensive specification including:
        1. Architecture Overview: High-level architecture of the application
        2. Data Models: Entity definitions derived from the code
        3. Component Structure: UI components and their relationships
        4. API Interfaces: Internal and external interfaces
        5. Storage Strategy: How data is persisted
        6. User Interface Design: Layout descriptions for all screens
        7. PrimeOS Integration: How the app integrates with PrimeOS
        
        Format your specification as a structured JSON document that matches the PrimeOS App Factory specification format.
      `
    };
  }
  
  /**
   * Set the API key
   * @param {string} apiKey - Anthropic API key
   * @returns {Promise<boolean>} Success indicator
   */
  async setApiKey(apiKey) {
    if (!apiKey || typeof apiKey !== 'string' || apiKey.trim() === '') {
      throw new Error('API key is required');
    }
    
    // Store API key
    this.apiKey = apiKey;
    
    // Store API key in secure vault if available
    if (this.secureVault) {
      try {
        await this.secureVault.setSecret('claudeApiKey', apiKey, {
          created: new Date().toISOString(),
          source: 'claude-service'
        });
        
        // Notify that the API key has been updated
        if (this.eventBus) {
          this.eventBus.publish('claude-service:api-key-updated', {
            timestamp: new Date().toISOString()
          });
        }
        
        console.log('API key updated and stored in secure vault');
        return true;
      } catch (error) {
        console.error('Failed to store API key in secure vault:', error);
        return false;
      }
    } else {
      console.log('API key updated (secure vault not available)');
      return true;
    }
  }
  
  /**
   * Check if an API key is set
   * @returns {Promise<boolean>} True if an API key is available
   */
  async hasApiKey() {
    // If API key is already loaded in memory, return true
    if (this.apiKey) {
      return true;
    }
    
    // Otherwise, try to load from secure vault
    if (this.secureVault) {
      try {
        await this._loadApiKey();
        return !!this.apiKey;
      } catch (error) {
        console.error('Failed to check for API key:', error);
        return false;
      }
    }
    
    return false;
  }
  
  /**
   * Get the currently set API key
   * @returns {string} Current API key
   */
  getApiKey() {
    return this.apiKey;
  }
  
  /**
   * Execute a request with a prompt - compatibility with ClaudeOrchestrator
   * @param {string} prompt - The prompt to send
   * @param {string} conversationId - The conversation ID for context
   * @returns {Promise<string>} The response from Claude
   */
  async executeRequest(prompt, conversationId) {
    return this._executeRequest(prompt, conversationId);
  }
  
  /**
   * Generate domain insights from user app description
   * @param {Object} domainData - User-provided domain information
   * @returns {Promise<Object>} Enhanced domain insights
   */
  async generateDomainInsights(domainData) {
    console.log('Generating domain insights');
    
    if (!domainData || !domainData.purpose) {
      throw new Error('Valid domain data with purpose is required');
    }
    
    try {
      // Create prompt from template
      const prompt = this.promptTemplates.domainInsights.replace(
        '{description}',
        domainData.purpose
      );
      
      // Send request to Claude
      const response = await this._executeRequest(prompt, 'domain_insights');
      
      // Parse JSON from response
      const domainInsights = this._extractJsonFromResponse(response);
      
      // Combine with original input
      return {
        ...domainData,
        ...domainInsights
      };
    } catch (error) {
      console.error('Failed to generate domain insights:', error);
      throw error;
    }
  }
  
  /**
   * Suggest requirements based on domain information
   * @param {Object} domainData - Domain information
   * @returns {Promise<Object>} Suggested requirements
   */
  async suggestRequirements(domainData) {
    console.log('Suggesting requirements');
    
    if (!domainData) {
      throw new Error('Domain data is required');
    }
    
    try {
      // Create prompt from template
      const prompt = this.promptTemplates.suggestRequirements.replace(
        '{domainData}',
        JSON.stringify(domainData, null, 2)
      );
      
      // Send request to Claude
      const response = await this._executeRequest(prompt, 'suggest_requirements');
      
      // Parse JSON from response
      return this._extractJsonFromResponse(response);
    } catch (error) {
      console.error('Failed to suggest requirements:', error);
      throw error;
    }
  }
  
  /**
   * Enhance user-provided requirements
   * @param {Object} requirementsData - User-provided requirements
   * @param {Object} domainData - Domain information
   * @returns {Promise<Object>} Enhanced requirements
   */
  async enhanceRequirements(requirementsData, domainData) {
    console.log('Enhancing requirements');
    
    if (!requirementsData) {
      throw new Error('Requirements data is required');
    }
    
    try {
      // Create prompt from template
      let prompt = this.promptTemplates.enhanceRequirements
        .replace('{requirements}', JSON.stringify(requirementsData, null, 2));
      
      // Add domain data if available
      if (domainData) {
        prompt = prompt.replace('{domainData}', JSON.stringify(domainData, null, 2));
      } else {
        prompt = prompt.replace('{domainData}', 'Not provided');
      }
      
      // Send request to Claude
      const response = await this._executeRequest(prompt, 'enhance_requirements');
      
      // Parse JSON from response
      return this._extractJsonFromResponse(response);
    } catch (error) {
      console.error('Failed to enhance requirements:', error);
      throw error;
    }
  }
  
  /**
   * Generate app specification from domain and requirements
   * @param {Object} domainData - Domain information
   * @param {Object} requirementsData - Requirements data
   * @returns {Promise<Object>} Application specification
   */
  async generateAppSpecification(domainData, requirementsData) {
    console.log('Generating app specification');
    
    if (!requirementsData) {
      throw new Error('Requirements data is required');
    }
    
    try {
      // Create prompt from template
      let prompt = this.promptTemplates.generateSpecification
        .replace('{requirements}', JSON.stringify(requirementsData, null, 2));
      
      // Add domain data if available
      if (domainData) {
        prompt = prompt.replace('{domainData}', JSON.stringify(domainData, null, 2));
      } else {
        prompt = prompt.replace('{domainData}', 'Not provided');
      }
      
      // Send request to Claude
      const response = await this._executeRequest(prompt, 'generate_specification');
      
      // Parse JSON from response
      return this._extractJsonFromResponse(response);
    } catch (error) {
      console.error('Failed to generate app specification:', error);
      throw error;
    }
  }
  
  /**
   * Validate app specification
   * @param {Object} specification - App specification
   * @returns {Promise<Object>} Validation result
   */
  async validateSpecification(specification) {
    console.log('Validating app specification');
    
    if (!specification) {
      throw new Error('Specification is required');
    }
    
    try {
      // Create prompt from template
      const prompt = this.promptTemplates.validateSpecification
        .replace('{specification}', JSON.stringify(specification, null, 2));
      
      // Send request to Claude
      const response = await this._executeRequest(prompt, 'validate_specification');
      
      // Parse JSON from response
      return this._extractJsonFromResponse(response);
    } catch (error) {
      console.error('Failed to validate specification:', error);
      throw error;
    }
  }
  
  /**
   * Generate app code from specification
   * @param {Object} specification - App specification
   * @returns {Promise<Object>} Generated code files
   */
  async generateAppCode(specification) {
    console.log('Generating app code');
    
    if (!specification) {
      throw new Error('Specification is required');
    }
    
    try {
      // Create prompt from template
      const prompt = this.promptTemplates.generateAppCode
        .replace('{specification}', JSON.stringify(specification, null, 2));
      
      // Send request to Claude
      const response = await this._executeRequest(prompt, 'generate_app_code');
      
      // Parse JSON from response
      const files = this._extractJsonFromResponse(response);
      
      // Add file structure info
      const structure = this._createFileStructure(files);
      
      return {
        files,
        structure
      };
    } catch (error) {
      console.error('Failed to generate app code:', error);
      throw error;
    }
  }
  
  /**
   * Improve code based on test results
   * @param {Array} files - Current code files
   * @param {Object} testResults - Test results
   * @param {Object} specification - App specification
   * @returns {Promise<Object>} Improved code files
   */
  async improveCode(files, testResults, specification) {
    console.log('Improving code based on test results');
    
    if (!files || !Array.isArray(files)) {
      throw new Error('Files array is required');
    }
    
    if (!testResults) {
      throw new Error('Test results are required');
    }
    
    try {
      // Convert files to format for prompt
      const filesString = JSON.stringify(
        files.map(file => ({
          path: file.path,
          content: file.content
        })),
        null,
        2
      );
      
      // Create prompt from template
      let prompt = this.promptTemplates.improveCode
        .replace('{files}', filesString)
        .replace('{testResults}', JSON.stringify(testResults, null, 2));
      
      // Add specification if available
      if (specification) {
        prompt = prompt.replace('{specification}', JSON.stringify(specification, null, 2));
      } else {
        prompt = prompt.replace('{specification}', 'Not provided');
      }
      
      // Send request to Claude
      const response = await this._executeRequest(prompt, 'improve_code');
      
      // Parse JSON from response
      const improvedFiles = this._extractJsonFromResponse(response);
      
      // Add file structure info
      const structure = this._createFileStructure(improvedFiles);
      
      return {
        files: improvedFiles,
        structure
      };
    } catch (error) {
      console.error('Failed to improve code:', error);
      throw error;
    }
  }
  
  /**
   * Derive app specification from existing code
   * @param {Array} files - Code files
   * @param {string} appName - Application name
   * @param {string} description - Application description
   * @returns {Promise<Object>} Derived specification
   */
  async deriveSpecificationFromCode(files, appName, description) {
    console.log('Deriving specification from code');
    
    if (!files || !Array.isArray(files)) {
      throw new Error('Files array is required');
    }
    
    try {
      // Convert files to format for prompt
      const filesString = JSON.stringify(
        files.map(file => ({
          path: file.path,
          content: file.content
        })),
        null,
        2
      );
      
      // Create prompt from template
      let prompt = this.promptTemplates.deriveSpecificationFromCode
        .replace('{files}', filesString)
        .replace('{appName}', appName || 'Unnamed App');
      
      // Add description if available
      if (description) {
        prompt = prompt.replace('{description}', description);
      } else {
        prompt = prompt.replace('{description}', 'No description provided');
      }
      
      // Send request to Claude
      const response = await this._executeRequest(prompt, 'derive_specification');
      
      // Parse JSON from response
      return this._extractJsonFromResponse(response);
    } catch (error) {
      console.error('Failed to derive specification from code:', error);
      throw error;
    }
  }
  
  /**
   * Create a file structure representation from files array
   * @private
   * @param {Array} files - Array of file objects
   * @returns {Object} File structure representation
   */
  _createFileStructure(files) {
    // Create a directory tree structure
    const structure = {
      name: 'root',
      type: 'directory',
      children: {}
    };
    
    // Process each file
    for (const file of files) {
      const pathParts = file.path.split('/');
      const fileName = pathParts.pop();
      
      // Create directory structure
      let currentLevel = structure.children;
      
      for (const part of pathParts) {
        if (!currentLevel[part]) {
          currentLevel[part] = {
            name: part,
            type: 'directory',
            children: {}
          };
        }
        currentLevel = currentLevel[part].children;
      }
      
      // Add file at current level
      currentLevel[fileName] = {
        name: fileName,
        type: 'file',
        path: file.path
      };
    }
    
    return structure;
  }
  
  /**
   * Extract JSON from Claude API response
   * @private
   * @param {string} response - Claude API response content
   * @returns {Object} Parsed JSON object
   */
  _extractJsonFromResponse(response) {
    try {
      // First try to parse the entire response as JSON
      try {
        return JSON.parse(response);
      } catch (e) {
        // If that fails, look for JSON inside the response
        const jsonMatch = response.match(/```json\s*([\s\S]*?)\s*```|<json>([\s\S]*?)<\/json>/i);
        
        if (jsonMatch) {
          const jsonContent = jsonMatch[1] || jsonMatch[2];
          return JSON.parse(jsonContent);
        } else {
          // Look for anything that looks like a JSON object or array
          const potentialJson = response.match(/(\{[\s\S]*\}|\[[\s\S]*\])/);
          
          if (potentialJson) {
            return JSON.parse(potentialJson[1]);
          }
          
          throw new Error('No valid JSON found in response');
        }
      }
    } catch (error) {
      console.error('Failed to extract JSON from response:', error);
      throw new Error(`Failed to parse Claude response: ${error.message}`);
    }
  }
  
  /**
   * Execute a request to the Claude API
   * @private
   * @param {string} prompt - Prompt to send
   * @param {string} conversationId - Conversation ID for context
   * @returns {Promise<string>} Claude API response
   */
  async _executeRequest(prompt, conversationId) {
    // If API key not already loaded, try to load it from secure vault
    if (!this.apiKey && this.secureVault) {
      await this._loadApiKey();
    }
    
    if (!this.apiKey) {
      // In a real implementation, this would redirect to settings
      // For now, show a more helpful error message
      throw new Error('API key is required. Please set a Claude API key in the Settings app.');
    }
    
    // Apply rate limiting
    await this._enforceRateLimit();
    
    try {
      // Get conversation history if available
      const messages = this._getConversationHistory(conversationId);
      
      // Add system instructions for app development
      const systemPrompt = `
        You are Claude, an AI assistant specialized in PrimeOS application development.
        
        When generating code or specifications:
        1. Focus on creating practical, working implementations
        2. Follow PrimeOS patterns and conventions
        3. Prioritize clean, maintainable code
        4. Balance simplicity with proper architecture
        5. Use PrimeOS core libraries and services
        6. Return JSON responses when requested
        
        Be concise and focused in your responses.
      `;
      
      // Prepare the API request
      const requestBody = {
        model: this.model,
        messages: [
          { role: 'system', content: systemPrompt },
          ...messages,
          { role: 'user', content: prompt }
        ],
        temperature: 0.2,
        max_tokens: 40000
      };
      
      // Execute the request
      const response = await fetch(this.apiUrl, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          'x-api-key': this.apiKey,
          'anthropic-version': '2023-06-01'
        },
        body: JSON.stringify(requestBody)
      });
      
      // Check for HTTP errors
      if (!response.ok) {
        const errorData = await response.json();
        
        // Check if the error is due to an invalid API key
        if (response.status === 401 || response.status === 403) {
          // Notify about invalid API key
          if (this.eventBus) {
            this.eventBus.publish('claude-service:api-key-invalid', {
              error: errorData.error?.message || 'Invalid API key',
              timestamp: new Date().toISOString()
            });
          }
          
          throw new Error('Invalid Claude API key. Please check your API key in the Settings app.');
        }
        
        throw new Error(`Claude API error: ${errorData.error?.message || response.statusText}`);
      }
      
      // Parse and return the response
      const responseData = await response.json();
      
      // Track API usage if event bus is available
      if (this.eventBus) {
        const inputTokens = prompt.length / 4; // Rough estimate
        const outputTokens = responseData.content[0].text.length / 4; // Rough estimate
        
        this.eventBus.publish('claude-service:api-usage', {
          inputTokens,
          outputTokens,
          totalTokens: inputTokens + outputTokens,
          model: this.model,
          operation: conversationId || 'unknown',
          timestamp: new Date().toISOString()
        });
      }
      
      // Store in conversation history
      this._updateConversationHistory(conversationId, prompt, responseData.content[0].text);
      
      return responseData.content[0].text;
    } catch (error) {
      console.error('Claude API request failed:', error);
      throw error;
    }
  }
  
  /**
   * Get conversation history for a given ID
   * @private
   * @param {string} conversationId - Conversation identifier
   * @returns {Array} Conversation messages
   */
  _getConversationHistory(conversationId) {
    if (!conversationId) {
      return [];
    }
    
    return this.conversationHistory.get(conversationId) || [];
  }
  
  /**
   * Update conversation history with new messages
   * @private
   * @param {string} conversationId - Conversation identifier
   * @param {string} userMessage - User message
   * @param {string} assistantMessage - Assistant response
   */
  _updateConversationHistory(conversationId, userMessage, assistantMessage) {
    if (!conversationId) {
      return;
    }
    
    // Get current history or initialize
    const history = this.conversationHistory.get(conversationId) || [];
    
    // Add new messages
    history.push({ role: 'user', content: userMessage });
    history.push({ role: 'assistant', content: assistantMessage });
    
    // Limit history length (keep last 10 messages)
    const trimmedHistory = history.slice(-10);
    
    // Update conversation history
    this.conversationHistory.set(conversationId, trimmedHistory);
  }
  
  /**
   * Clear conversation history for a given ID
   * @param {string} conversationId - Conversation identifier
   */
  clearConversationHistory(conversationId) {
    if (!conversationId) {
      return;
    }
    
    this.conversationHistory.delete(conversationId);
    console.log(`Cleared conversation history for ${conversationId}`);
  }
  
  /**
   * Enforce rate limiting for API requests
   * @private
   * @returns {Promise<void>}
   */
  async _enforceRateLimit() {
    const now = Date.now();
    const oneMinuteAgo = now - 60000;
    
    // Remove requests older than one minute
    this.rateLimit.requestQueue = this.rateLimit.requestQueue.filter(
      timestamp => timestamp > oneMinuteAgo
    );
    
    // Count requests in the last minute
    this.rateLimit.requestsInLastMinute = this.rateLimit.requestQueue.length;
    
    // Check if rate limit reached
    if (this.rateLimit.requestsInLastMinute >= this.rateLimit.maxRequestsPerMinute) {
      // Calculate delay needed
      const oldestTimestamp = this.rateLimit.requestQueue[0];
      const delayNeeded = 60000 - (now - oldestTimestamp);
      
      console.log(`Rate limit reached, delaying request for ${delayNeeded}ms`);
      
      // Wait until we can make another request
      await new Promise(resolve => setTimeout(resolve, delayNeeded + 100));
    }
    
    // Add this request to the queue
    this.rateLimit.requestQueue.push(now);
    this.rateLimit.lastRequestTimestamp = now;
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { ClaudeService };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.ClaudeService = ClaudeService;
}