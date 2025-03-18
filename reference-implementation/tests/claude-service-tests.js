/**
 * PrimeOS Reference Implementation - ClaudeService Tests
 * 
 * Tests for the ClaudeService, which integrates with the SecureVault
 * for API key management and provides AI capabilities to the App Factory.
 */

// Import the modules to test
const { ClaudeService } = require('../core/app-factory/claude-service');
const { SecureVault } = require('../core/identity/secure-vault');

describe('ClaudeService', () => {
  let claudeService;
  let mockEventBus;
  let mockSecureVault;
  let originalFetch;
  let originalCrypto;
  
  beforeEach(() => {
    // Store original fetch
    originalFetch = global.fetch;
    
    // Store original crypto
    originalCrypto = global.crypto;
    
    // Mock fetch for API calls
    global.fetch = jest.fn().mockImplementation((url, options) => {
      return Promise.resolve({
        ok: true,
        json: () => Promise.resolve({
          id: 'test-completion',
          content: [{
            type: 'text',
            text: '```json\n{"result": "success"}\n```'
          }],
          model: 'claude-3-opus-20240229',
          role: 'assistant'
        })
      });
    });
    
    // Mock event bus
    mockEventBus = {
      publish: jest.fn(),
      subscribe: jest.fn(),
      unsubscribe: jest.fn()
    };
    
    // Mock secure vault
    mockSecureVault = {
      setSecret: jest.fn().mockResolvedValue(true),
      getSecret: jest.fn().mockImplementation((key) => {
        if (key === 'claudeApiKey') {
          return Promise.resolve('sk-test-12345');
        }
        return Promise.resolve(null);
      }),
      removeSecret: jest.fn().mockResolvedValue(true)
    };
    
    // Create test instance with mocks
    claudeService = new ClaudeService({
      eventBus: mockEventBus,
      secureVault: mockSecureVault,
      model: 'claude-3-opus-20240229',
      maxRequestsPerMinute: 20
    });
    
    // Spy on console methods
    jest.spyOn(console, 'log').mockImplementation(() => {});
    jest.spyOn(console, 'error').mockImplementation(() => {});
    jest.spyOn(console, 'warn').mockImplementation(() => {});
  });
  
  afterEach(() => {
    // Restore originals
    global.fetch = originalFetch;
    global.crypto = originalCrypto;
    
    // Restore console methods
    console.log.mockRestore();
    console.error.mockRestore();
    console.warn.mockRestore();
    
    // Clear mocks
    jest.clearAllMocks();
  });
  
  describe('constructor', () => {
    it('should initialize with provided options', () => {
      expect(claudeService.eventBus).toBe(mockEventBus);
      expect(claudeService.secureVault).toBe(mockSecureVault);
      expect(claudeService.model).toBe('claude-3-opus-20240229');
      expect(claudeService.apiUrl).toBe('https://api.anthropic.com/v1/messages');
      expect(claudeService.rateLimit.maxRequestsPerMinute).toBe(20);
    });
    
    it('should create new SecureVault if not provided', () => {
      const serviceWithoutVault = new ClaudeService({
        eventBus: mockEventBus
      });
      
      expect(serviceWithoutVault.secureVault).toBeInstanceOf(SecureVault);
    });
    
    it('should initialize with default options when not provided', () => {
      const defaultService = new ClaudeService();
      
      expect(defaultService.apiKey).toBe('');
      expect(defaultService.model).toBe('claude-3-opus-20240229');
      expect(defaultService.apiUrl).toBe('https://api.anthropic.com/v1/messages');
      expect(defaultService.rateLimit.maxRequestsPerMinute).toBe(10);
    });
    
    it('should setup prompt templates', () => {
      expect(claudeService.promptTemplates).toBeDefined();
      expect(Object.keys(claudeService.promptTemplates)).toContain('domainInsights');
      expect(Object.keys(claudeService.promptTemplates)).toContain('generateAppCode');
    });
    
    it('should set up conversation history tracking', () => {
      expect(claudeService.conversationHistory).toBeInstanceOf(Map);
    });
    
    it('should attempt to load API key from SecureVault', () => {
      const service = new ClaudeService({
        secureVault: mockSecureVault
      });
      
      // Should have attempted to load API key
      setTimeout(() => {
        expect(mockSecureVault.getSecret).toHaveBeenCalledWith('claudeApiKey');
      }, 0);
    });
    
    it('should set up event listeners for API key changes', () => {
      const service = new ClaudeService({
        eventBus: mockEventBus,
        secureVault: mockSecureVault
      });
      
      // Should subscribe to API key change events
      expect(mockEventBus.subscribe).toHaveBeenCalledWith(
        'settings:api-key-changed',
        expect.any(Function)
      );
      
      // Should subscribe to settings change events
      expect(mockEventBus.subscribe).toHaveBeenCalledWith(
        'settings:changed',
        expect.any(Function)
      );
    });
  });
  
  describe('_loadApiKey', () => {
    it('should load API key from SecureVault', async () => {
      const originalApiKey = claudeService.apiKey;
      
      await claudeService._loadApiKey();
      
      expect(mockSecureVault.getSecret).toHaveBeenCalledWith('claudeApiKey');
      expect(claudeService.apiKey).toBe('sk-test-12345');
    });
    
    it('should handle missing API key', async () => {
      mockSecureVault.getSecret.mockResolvedValueOnce(null);
      
      await claudeService._loadApiKey();
      
      expect(console.warn).toHaveBeenCalledWith('No API key found in secure vault');
    });
    
    it('should handle SecureVault errors', async () => {
      mockSecureVault.getSecret.mockRejectedValueOnce(new Error('Vault error'));
      
      await claudeService._loadApiKey();
      
      expect(console.error).toHaveBeenCalled();
    });
  });
  
  describe('setApiKey', () => {
    it('should set API key and store in SecureVault', async () => {
      const result = await claudeService.setApiKey('sk-new-api-key');
      
      expect(result).toBe(true);
      expect(claudeService.apiKey).toBe('sk-new-api-key');
      expect(mockSecureVault.setSecret).toHaveBeenCalledWith(
        'claudeApiKey',
        'sk-new-api-key',
        expect.objectContaining({
          created: expect.any(String),
          source: 'claude-service'
        })
      );
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'claude-service:api-key-updated',
        expect.any(Object)
      );
    });
    
    it('should throw error for empty API key', async () => {
      await expect(claudeService.setApiKey('')).rejects.toThrow('API key is required');
    });
    
    it('should handle SecureVault errors', async () => {
      mockSecureVault.setSecret.mockRejectedValueOnce(new Error('Vault error'));
      
      const result = await claudeService.setApiKey('sk-test-12345');
      
      expect(result).toBe(false);
      expect(console.error).toHaveBeenCalled();
    });
    
    it('should handle missing SecureVault', async () => {
      claudeService.secureVault = null;
      
      const result = await claudeService.setApiKey('sk-test-12345');
      
      expect(result).toBe(true);
      expect(claudeService.apiKey).toBe('sk-test-12345');
    });
  });
  
  describe('hasApiKey', () => {
    it('should return true if API key is already loaded', async () => {
      claudeService.apiKey = 'sk-existing-key';
      
      // Clear any previous calls
      mockSecureVault.getSecret.mockClear();
      
      const result = await claudeService.hasApiKey();
      
      expect(result).toBe(true);
      expect(mockSecureVault.getSecret).not.toHaveBeenCalled();
    });
    
    it('should check SecureVault if API key is not loaded', async () => {
      claudeService.apiKey = '';
      
      const result = await claudeService.hasApiKey();
      
      expect(mockSecureVault.getSecret).toHaveBeenCalledWith('claudeApiKey');
      expect(result).toBe(true);
    });
    
    it('should return false if no API key is available', async () => {
      claudeService.apiKey = '';
      mockSecureVault.getSecret.mockResolvedValueOnce(null);
      
      const result = await claudeService.hasApiKey();
      
      expect(result).toBe(false);
    });
    
    it('should handle SecureVault errors', async () => {
      claudeService.apiKey = '';
      mockSecureVault.getSecret.mockRejectedValueOnce(new Error('Vault error'));
      
      const result = await claudeService.hasApiKey();
      
      expect(result).toBe(false);
      expect(console.error).toHaveBeenCalled();
    });
  });
  
  describe('_executeRequest', () => {
    let originalApiKey;
    
    beforeEach(() => {
      originalApiKey = claudeService.apiKey;
      claudeService.apiKey = 'sk-test-12345';
    });
    
    afterEach(() => {
      claudeService.apiKey = originalApiKey;
    });
    
    it('should execute request to Claude API', async () => {
      const response = await claudeService._executeRequest('Test prompt', 'test_conversation');
      
      expect(global.fetch).toHaveBeenCalledWith(
        'https://api.anthropic.com/v1/messages',
        expect.objectContaining({
          method: 'POST',
          headers: expect.objectContaining({
            'Content-Type': 'application/json',
            'x-api-key': 'sk-test-12345'
          }),
          body: expect.any(String)
        })
      );
      
      // Check request body
      const requestBody = JSON.parse(global.fetch.mock.calls[0][1].body);
      expect(requestBody.messages).toContainEqual({ role: 'user', content: 'Test prompt' });
      expect(requestBody.model).toBe('claude-3-opus-20240229');
      
      // Check response
      expect(response).toContain('success');
    });
    
    it('should load API key from SecureVault if not set', async () => {
      claudeService.apiKey = '';
      
      const response = await claudeService._executeRequest('Test prompt', 'test_conversation');
      
      expect(mockSecureVault.getSecret).toHaveBeenCalledWith('claudeApiKey');
      
      // Should have loaded and used the API key
      expect(global.fetch).toHaveBeenCalledWith(
        expect.any(String),
        expect.objectContaining({
          headers: expect.objectContaining({
            'x-api-key': 'sk-test-12345'
          })
        })
      );
    });
    
    it('should throw error if no API key is available', async () => {
      claudeService.apiKey = '';
      mockSecureVault.getSecret.mockResolvedValueOnce(null);
      
      await expect(claudeService._executeRequest('Test prompt', 'test_conversation'))
        .rejects.toThrow('API key is required');
    });
    
    it('should include conversation history if available', async () => {
      // Add some history
      claudeService._updateConversationHistory(
        'test_conversation',
        'Previous prompt',
        'Previous response'
      );
      
      await claudeService._executeRequest('Test prompt', 'test_conversation');
      
      // Check request body
      const requestBody = JSON.parse(global.fetch.mock.calls[0][1].body);
      
      // Should include history
      expect(requestBody.messages).toContainEqual({ role: 'user', content: 'Previous prompt' });
      expect(requestBody.messages).toContainEqual({ role: 'assistant', content: 'Previous response' });
      expect(requestBody.messages).toContainEqual({ role: 'user', content: 'Test prompt' });
    });
    
    it('should handle API errors', async () => {
      // Mock an API error
      global.fetch.mockImplementationOnce(() => {
        return Promise.resolve({
          ok: false,
          status: 401,
          statusText: 'Unauthorized',
          json: () => Promise.resolve({
            error: { message: 'Invalid API key' }
          })
        });
      });
      
      await expect(claudeService._executeRequest('Test prompt', 'test_conversation'))
        .rejects.toThrow('Invalid Claude API key');
      
      // Should publish event about invalid API key
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'claude-service:api-key-invalid',
        expect.any(Object)
      );
    });
    
    it('should track API usage', async () => {
      await claudeService._executeRequest('Test prompt', 'test_conversation');
      
      // Should publish usage event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'claude-service:api-usage',
        expect.objectContaining({
          inputTokens: expect.any(Number),
          outputTokens: expect.any(Number),
          totalTokens: expect.any(Number),
          model: 'claude-3-opus-20240229'
        })
      );
    });
    
    it('should track rate limiting', async () => {
      // Set a low rate limit for testing
      claudeService.rateLimit.maxRequestsPerMinute = 2;
      
      // Replace _enforceRateLimit with a mock that doesn't actually wait
      const originalEnforceRateLimit = claudeService._enforceRateLimit;
      claudeService._enforceRateLimit = jest.fn().mockResolvedValue(true);
      
      // Execute request
      await claudeService._executeRequest('Test prompt', 'test_conversation');
      
      // Should have called _enforceRateLimit
      expect(claudeService._enforceRateLimit).toHaveBeenCalled();
      
      // Request should have been executed
      expect(global.fetch).toHaveBeenCalled();
      
      // Restore original method
      claudeService._enforceRateLimit = originalEnforceRateLimit;
    });
  });
  
  describe('generateDomainInsights', () => {
    it('should generate domain insights from user input', async () => {
      // Mock the _executeRequest method
      claudeService._executeRequest = jest.fn().mockResolvedValue(`
        \`\`\`json
        {
          "insights": ["Insight 1", "Insight 2"],
          "personas": ["Persona 1", "Persona 2"],
          "functionalAreas": ["Area 1", "Area 2"]
        }
        \`\`\`
      `);
      
      const domainData = {
        purpose: 'Create a task management application',
        audience: 'Business professionals'
      };
      
      const result = await claudeService.generateDomainInsights(domainData);
      
      // Should use prompt template
      expect(claudeService._executeRequest).toHaveBeenCalledWith(
        expect.stringContaining('App Description: Create a task management application'),
        'domain_insights'
      );
      
      // Should return enhanced domain data
      expect(result.purpose).toBe('Create a task management application');
      expect(result.audience).toBe('Business professionals');
      expect(result.insights).toEqual(['Insight 1', 'Insight 2']);
      expect(result.personas).toEqual(['Persona 1', 'Persona 2']);
      expect(result.functionalAreas).toEqual(['Area 1', 'Area 2']);
    });
    
    it('should throw error for missing domain data', async () => {
      await expect(claudeService.generateDomainInsights()).rejects.toThrow(
        'Valid domain data with purpose is required'
      );
      
      await expect(claudeService.generateDomainInsights({})).rejects.toThrow(
        'Valid domain data with purpose is required'
      );
    });
    
    it('should handle API errors', async () => {
      // Mock API error
      claudeService._executeRequest = jest.fn().mockRejectedValue(
        new Error('API error')
      );
      
      const domainData = {
        purpose: 'Create a task management application'
      };
      
      await expect(claudeService.generateDomainInsights(domainData)).rejects.toThrow('API error');
    });
  });
  
  describe('suggestRequirements', () => {
    it('should suggest requirements based on domain', async () => {
      // Mock the _executeRequest method
      claudeService._executeRequest = jest.fn().mockResolvedValue(`
        \`\`\`json
        {
          "entities": [
            {
              "name": "Task",
              "description": "A task to be completed",
              "fields": [
                { "name": "title", "type": "string", "description": "Task title" },
                { "name": "dueDate", "type": "date", "description": "Due date" }
              ]
            }
          ],
          "features": [
            { "name": "Task Creation", "description": "Create tasks", "priority": "High" }
          ],
          "nonFunctionalRequirements": [
            { "category": "Performance", "description": "Fast loading times" }
          ]
        }
        \`\`\`
      `);
      
      const domainData = {
        purpose: 'Task management',
        insights: ['Insight 1'],
        personas: ['Persona 1'],
        functionalAreas: ['Area 1']
      };
      
      const result = await claudeService.suggestRequirements(domainData);
      
      // Check that the prompt contains the domain data
      expect(claudeService._executeRequest).toHaveBeenCalledWith(
        expect.stringContaining('"purpose": "Task management"'),
        'suggest_requirements'
      );
      
      // Should return requirements
      expect(result.entities).toHaveLength(1);
      expect(result.entities[0].name).toBe('Task');
      expect(result.features).toHaveLength(1);
      expect(result.features[0].name).toBe('Task Creation');
      expect(result.nonFunctionalRequirements).toHaveLength(1);
      expect(result.nonFunctionalRequirements[0].category).toBe('Performance');
    });
    
    it('should throw error for missing domain data', async () => {
      await expect(claudeService.suggestRequirements()).rejects.toThrow(
        'Domain data is required'
      );
    });
    
    it('should handle API errors', async () => {
      // Mock API error
      claudeService._executeRequest = jest.fn().mockRejectedValue(
        new Error('API error')
      );
      
      const domainData = {
        purpose: 'Task management'
      };
      
      await expect(claudeService.suggestRequirements(domainData)).rejects.toThrow('API error');
    });
  });
  
  describe('generateAppCode', () => {
    it('should generate app code from specification', async () => {
      // Mock the _executeRequest method
      claudeService._executeRequest = jest.fn().mockResolvedValue(`
        \`\`\`json
        [
          {
            "path": "index.js",
            "content": "console.log('Hello, world!');"
          },
          {
            "path": "styles/main.css",
            "content": "body { font-family: sans-serif; }"
          }
        ]
        \`\`\`
      `);
      
      const specification = {
        name: 'TestApp',
        components: ['Component1', 'Component2']
      };
      
      const result = await claudeService.generateAppCode(specification);
      
      // Check that the prompt contains the specification
      expect(claudeService._executeRequest).toHaveBeenCalledWith(
        expect.stringContaining('"name": "TestApp"'),
        'generate_app_code'
      );
      
      // Should return files and structure
      expect(result.files).toHaveLength(2);
      expect(result.files[0].path).toBe('index.js');
      expect(result.files[1].path).toBe('styles/main.css');
      expect(result.structure).toBeDefined();
      expect(result.structure.name).toBe('root');
      expect(result.structure.children).toBeDefined();
    });
    
    it('should throw error for missing specification', async () => {
      await expect(claudeService.generateAppCode()).rejects.toThrow(
        'Specification is required'
      );
    });
    
    it('should handle API errors', async () => {
      // Mock API error
      claudeService._executeRequest = jest.fn().mockRejectedValue(
        new Error('API error')
      );
      
      const specification = {
        name: 'TestApp'
      };
      
      await expect(claudeService.generateAppCode(specification)).rejects.toThrow('API error');
    });
  });
  
  describe('conversation management', () => {
    it('should get empty history for new conversation', () => {
      const history = claudeService._getConversationHistory('new_conversation');
      
      expect(history).toEqual([]);
    });
    
    it('should update conversation history', () => {
      claudeService._updateConversationHistory(
        'test_conversation',
        'User prompt',
        'Assistant response'
      );
      
      const history = claudeService._getConversationHistory('test_conversation');
      
      expect(history).toHaveLength(2);
      expect(history[0]).toEqual({ role: 'user', content: 'User prompt' });
      expect(history[1]).toEqual({ role: 'assistant', content: 'Assistant response' });
    });
    
    it('should limit history length', () => {
      // Add more than 10 message pairs
      for (let i = 0; i < 12; i++) {
        claudeService._updateConversationHistory(
          'test_conversation',
          `User prompt ${i}`,
          `Assistant response ${i}`
        );
      }
      
      const history = claudeService._getConversationHistory('test_conversation');
      
      // Should be limited to 10 messages (5 exchanges)
      expect(history).toHaveLength(10);
      
      // Should have the most recent messages
      expect(history[8].content).toBe('User prompt 11');
      expect(history[9].content).toBe('Assistant response 11');
    });
    
    it('should clear conversation history', () => {
      // Add some history
      claudeService._updateConversationHistory(
        'test_conversation',
        'User prompt',
        'Assistant response'
      );
      
      // Clear it
      claudeService.clearConversationHistory('test_conversation');
      
      // Should be empty
      const history = claudeService._getConversationHistory('test_conversation');
      expect(history).toEqual([]);
    });
  });
  
  describe('JSON extraction', () => {
    it('should extract JSON from response', () => {
      const response = '```json\n{"key": "value"}\n```';
      
      const result = claudeService._extractJsonFromResponse(response);
      
      expect(result).toEqual({ key: 'value' });
    });
    
    it('should handle plain JSON response', () => {
      const response = '{"key": "value"}';
      
      const result = claudeService._extractJsonFromResponse(response);
      
      expect(result).toEqual({ key: 'value' });
    });
    
    it('should handle XML-style JSON response', () => {
      const response = '<json>{"key": "value"}</json>';
      
      const result = claudeService._extractJsonFromResponse(response);
      
      expect(result).toEqual({ key: 'value' });
    });
    
    it('should extract JSON from text with other content', () => {
      const response = 'Here is the JSON you requested:\n\n```json\n{"key": "value"}\n```\n\nI hope this helps!';
      
      const result = claudeService._extractJsonFromResponse(response);
      
      expect(result).toEqual({ key: 'value' });
    });
    
    it('should throw error for invalid JSON', () => {
      const response = 'This is not JSON';
      
      expect(() => claudeService._extractJsonFromResponse(response)).toThrow(
        'Failed to parse Claude response'
      );
    });
  });
  
  describe('integration with event bus', () => {
    it('should handle API key change from settings', () => {
      // Simulate event from settings
      const handler = mockEventBus.subscribe.mock.calls.find(
        call => call[0] === 'settings:api-key-changed'
      )[1];
      
      // Call the handler
      handler({
        key: 'claudeApiKey',
        value: 'sk-settings-key'
      });
      
      // Should update API key
      expect(claudeService.apiKey).toBe('sk-settings-key');
    });
    
    it('should handle model change from settings', () => {
      // Simulate event from settings
      const handler = mockEventBus.subscribe.mock.calls.find(
        call => call[0] === 'settings:changed'
      )[1];
      
      // Call the handler
      handler({
        category: 'apiKeys',
        key: 'claudeModel',
        value: 'claude-3-haiku-20240307'
      });
      
      // Should update model
      expect(claudeService.model).toBe('claude-3-haiku-20240307');
    });
  });
});