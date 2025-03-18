/**
 * PrimeOS Reference Implementation - App Factory Utils Tests
 * 
 * Tests for the App Factory utility modules including ClaudeAPIClient,
 * AppFactoryStorage, and AppFactoryConfig.
 */

// Jest globals are automatically available in the test environment

// Import app factory utility modules
const { ClaudeAPIClient, getApiKey } = require('../core/app-factory/utils/claude-api');
const { AppFactoryStorage } = require('../core/app-factory/utils/persistence');
const { AppFactoryConfig } = require('../core/app-factory/utils/configuration');

// Tests for ClaudeAPIClient
describe('ClaudeAPIClient', () => {
  let claudeClient;
  let originalFetch;
  
  beforeEach(() => {
    // Store original fetch
    originalFetch = global.fetch;
    
    // Mock fetch
    global.fetch = jest.fn().mockImplementation((url, options) => {
      return Promise.resolve({
        ok: true,
        json: () => Promise.resolve({
          id: 'test-completion',
          content: [{
            type: 'text',
            text: '```json\n{"result": "success"}\n```'
          }],
          model: 'claude-3-sonnet-20240229',
          role: 'assistant'
        })
      });
    });
    
    // Create test instance with mock API key
    claudeClient = new ClaudeAPIClient({
      apiKey: 'test-api-key'
    });
    
    // Spy on console.error to prevent test output noise
    jest.spyOn(console, 'error').mockImplementation(() => {});
  });
  
  afterEach(() => {
    // Restore fetch
    global.fetch = originalFetch;
    
    // Restore console.error
    console.error.mockRestore();
  });
  
  describe('constructor', () => {
    it('should initialize with provided API key', () => {
      expect(claudeClient.apiKey).toBe('test-api-key');
      expect(claudeClient.model).toBe('claude-3-sonnet-20240229');
      expect(claudeClient.baseUrl).toBe('https://api.anthropic.com/v1/messages');
    });
    
    it('should initialize with default model', () => {
      const client = new ClaudeAPIClient({
        apiKey: 'test-api-key',
        model: 'claude-3-opus-20240229'
      });
      
      expect(client.model).toBe('claude-3-opus-20240229');
    });
    
    // No longer throw error as API key is now optional since it can be retrieved from SecureVault
    it('should handle missing API key (will get from SecureVault later)', () => {
      // Create a client with explicitly null API key to bypass getApiKey()
      const client = new ClaudeAPIClient({ apiKey: null });
      
      // Check that constructor doesn't throw error with null API key
      expect(client).toBeDefined();
      // Verify the model is set correctly
      expect(client.model).toBe('claude-3-sonnet-20240229');
    });
  });
  
  describe('completion', () => {
    it('should send request to Claude API', async () => {
      const prompt = 'Test prompt';
      
      const response = await claudeClient.completion(prompt);
      
      expect(global.fetch).toHaveBeenCalledWith(
        'https://api.anthropic.com/v1/messages',
        expect.objectContaining({
          method: 'POST',
          headers: expect.objectContaining({
            'Content-Type': 'application/json',
            'x-api-key': 'test-api-key',
            'anthropic-version': '2023-06-01'
          }),
          body: expect.any(String)
        })
      );
      
      // Check request body
      const requestBody = JSON.parse(global.fetch.mock.calls[0][1].body);
      expect(requestBody.messages[0].content).toBe(prompt);
      expect(requestBody.model).toBe('claude-3-sonnet-20240229');
      expect(requestBody.max_tokens).toBe(4000);
      expect(requestBody.temperature).toBe(0.7);
      
      // Check response
      expect(response.id).toBe('test-completion');
      expect(response.content[0].text).toContain('success');
    });
    
    it('should handle API errors', async () => {
      // Mock a failed response
      global.fetch.mockImplementationOnce(() => {
        return Promise.resolve({
          ok: false,
          status: 401,
          json: () => Promise.resolve({
            error: {
              message: 'Invalid API key'
            }
          })
        });
      });
      
      await expect(claudeClient.completion('Test prompt')).rejects.toThrow('Claude API error: 401');
    });
    
    it('should handle network errors', async () => {
      // Mock a network error
      global.fetch.mockImplementationOnce(() => {
        return Promise.reject(new Error('Network error'));
      });
      
      await expect(claudeClient.completion('Test prompt')).rejects.toThrow('Network error');
    });
    
    it('should use custom parameters when provided', async () => {
      const prompt = 'Test prompt';
      const options = {
        model: 'claude-3-opus-20240229',
        max_tokens: 2000,
        temperature: 0.3
      };
      
      await claudeClient.completion(prompt, options);
      
      // Check request body
      const requestBody = JSON.parse(global.fetch.mock.calls[0][1].body);
      expect(requestBody.model).toBe('claude-3-opus-20240229');
      expect(requestBody.max_tokens).toBe(2000);
      expect(requestBody.temperature).toBe(0.3);
    });
  });
  
  describe('generateDomainInsights', () => {
    it('should process domain data correctly', async () => {
      // Prepare a custom response
      const customResponse = {
        insights: ['Insight 1', 'Insight 2'],
        personas: ['Persona 1', 'Persona 2'],
        functionalAreas: ['Area 1', 'Area 2']
      };
      
      // Mock the completion method
      claudeClient.completion = jest.fn().mockResolvedValue({
        content: [{
          text: `\`\`\`json\n${JSON.stringify(customResponse)}\n\`\`\``
        }]
      });
      
      const domainData = {
        purpose: 'Test purpose',
        audience: 'Test audience'
      };
      
      const result = await claudeClient.generateDomainInsights(domainData);
      
      // Check that completion was called with correct prompt
      expect(claudeClient.completion).toHaveBeenCalledWith(
        expect.stringContaining('Purpose: Test purpose'),
        expect.any(Object)
      );
      
      // Check result combines original data with insights
      expect(result).toHaveProperty('purpose', 'Test purpose');
      expect(result).toHaveProperty('audience', 'Test audience');
      expect(result).toHaveProperty('insights');
      expect(result.insights).toEqual(['Insight 1', 'Insight 2']);
      expect(result).toHaveProperty('personas');
      expect(result.personas).toEqual(['Persona 1', 'Persona 2']);
      expect(result).toHaveProperty('functionalAreas');
      expect(result.functionalAreas).toEqual(['Area 1', 'Area 2']);
    });
    
    it('should handle errors gracefully', async () => {
      // Mock a failure
      claudeClient.completion = jest.fn().mockRejectedValue(new Error('API failure'));
      
      const domainData = {
        purpose: 'Test purpose',
        audience: 'Test audience'
      };
      
      const result = await claudeClient.generateDomainInsights(domainData);
      
      // Should return original data with error flag
      expect(result).toHaveProperty('purpose', 'Test purpose');
      expect(result).toHaveProperty('audience', 'Test audience');
      expect(result).toHaveProperty('insights');
      expect(result.insights[0]).toContain('Error');
      expect(result).toHaveProperty('error', true);
    });
    
    it('should handle malformed JSON response', async () => {
      // Mock a bad JSON response
      claudeClient.completion = jest.fn().mockResolvedValue({
        content: [{
          text: 'This is not JSON'
        }]
      });
      
      const domainData = {
        purpose: 'Test purpose',
        audience: 'Test audience'
      };
      
      const result = await claudeClient.generateDomainInsights(domainData);
      
      // Should return original data with error flag
      expect(result).toHaveProperty('purpose', 'Test purpose');
      expect(result).toHaveProperty('audience', 'Test audience');
      expect(result).toHaveProperty('insights');
      expect(result.insights[0]).toContain('Error');
      expect(result).toHaveProperty('error', true);
    });
  });
  
  describe('suggestRequirements', () => {
    it('should process domain insights correctly', async () => {
      // Prepare a custom response
      const customResponse = {
        entities: [
          {
            name: 'User',
            description: 'Application user',
            fields: [
              { name: 'id', type: 'string', description: 'User ID' },
              { name: 'name', type: 'string', description: 'User name' }
            ]
          }
        ],
        features: [
          { name: 'Authentication', description: 'User authentication', priority: 'High' }
        ],
        nonFunctionalRequirements: [
          { category: 'Performance', description: 'The app should be fast' }
        ]
      };
      
      // Mock the completion method
      claudeClient.completion = jest.fn().mockResolvedValue({
        content: [{
          text: `\`\`\`json\n${JSON.stringify(customResponse)}\n\`\`\``
        }]
      });
      
      const domain = {
        purpose: 'Test purpose',
        audience: 'Test audience',
        insights: ['Insight 1', 'Insight 2'],
        personas: ['Persona 1', 'Persona 2'],
        functionalAreas: ['Area 1', 'Area 2']
      };
      
      const result = await claudeClient.suggestRequirements(domain);
      
      // Check that completion was called with correct prompt
      expect(claudeClient.completion).toHaveBeenCalledWith(
        expect.stringContaining('Purpose: Test purpose'),
        expect.any(Object)
      );
      
      // Check result
      expect(result).toHaveProperty('entities');
      expect(result.entities[0].name).toBe('User');
      expect(result).toHaveProperty('features');
      expect(result.features[0].name).toBe('Authentication');
      expect(result).toHaveProperty('nonFunctionalRequirements');
      expect(result.nonFunctionalRequirements[0].category).toBe('Performance');
    });
    
    it('should handle errors gracefully', async () => {
      // Mock a failure
      claudeClient.completion = jest.fn().mockRejectedValue(new Error('API failure'));
      
      const domain = {
        purpose: 'Test purpose',
        audience: 'Test audience',
        insights: ['Insight 1', 'Insight 2']
      };
      
      const result = await claudeClient.suggestRequirements(domain);
      
      // Should return fallback data with error flag
      expect(result).toHaveProperty('entities');
      expect(result).toHaveProperty('features');
      expect(result).toHaveProperty('nonFunctionalRequirements');
      expect(result).toHaveProperty('error', true);
    });
  });
});

// Tests for AppFactoryStorage
describe('AppFactoryStorage', () => {
  let storage;
  let mockStore;
  
  beforeEach(() => {
    // Create mock store
    mockStore = {
      getCollections: jest.fn().mockResolvedValue(['system']),
      createCollection: jest.fn().mockResolvedValue(true),
      ensureIndex: jest.fn().mockResolvedValue(true),
      put: jest.fn().mockResolvedValue(true),
      get: jest.fn(),
      query: jest.fn(),
      delete: jest.fn().mockResolvedValue(true),
      saveAll: jest.fn().mockResolvedValue(true)
    };
    
    // Create test instance
    storage = new AppFactoryStorage(mockStore, {
      projectCollection: 'test_projects',
      fileCollection: 'test_files'
    });
    
    // Spy on console.log and error
    jest.spyOn(console, 'log').mockImplementation(() => {});
    jest.spyOn(console, 'error').mockImplementation(() => {});
  });
  
  afterEach(() => {
    console.log.mockRestore();
    console.error.mockRestore();
  });
  
  describe('constructor', () => {
    it('should initialize with provided options', () => {
      expect(storage.store).toBe(mockStore);
      expect(storage.projectCollection).toBe('test_projects');
      expect(storage.fileCollection).toBe('test_files');
    });
    
    it('should initialize with default options when not provided', () => {
      const defaultStorage = new AppFactoryStorage(mockStore);
      
      expect(defaultStorage.projectCollection).toBe('app_factory_projects');
      expect(defaultStorage.fileCollection).toBe('files');
    });
    
    it('should throw error if store is not provided', () => {
      expect(() => {
        new AppFactoryStorage();
      }).toThrow('AppFactoryStorage requires a store instance');
    });
    
    // Skipping this test as _initializeStorage is called asynchronously
    it.skip('should call _initializeStorage during construction', () => {
      // This would require testing an async operation in the constructor
      // which is difficult to test properly
    });
  });
  
  describe('project operations', () => {
    let testProject;
    
    beforeEach(() => {
      testProject = {
        id: 'test-project',
        name: 'Test Project',
        description: 'A test project',
        status: 'in_progress',
        userId: 'test-user'
      };
      
      mockStore.get.mockImplementation((collection, id) => {
        if (collection === storage.projectCollection && id === 'test-project') {
          return Promise.resolve(testProject);
        }
        return Promise.resolve(null);
      });
      
      mockStore.query.mockImplementation(({ collection, index, value }) => {
        if (collection === storage.projectCollection && index === 'userId' && value === 'test-user') {
          return Promise.resolve([testProject]);
        }
        return Promise.resolve([]);
      });
    });
    
    it('should save a project', async () => {
      await storage.saveProject(testProject);
      
      expect(mockStore.put).toHaveBeenCalledWith(
        storage.projectCollection,
        expect.objectContaining({
          id: 'test-project',
          name: 'Test Project',
          updatedAt: expect.any(Date)
        })
      );
    });
    
    it('should add createdAt timestamp if not present', async () => {
      await storage.saveProject(testProject);
      
      // Check that the store.put was called with a project containing createdAt
      const savedProject = mockStore.put.mock.calls[0][1];
      expect(savedProject).toHaveProperty('createdAt');
      expect(savedProject.createdAt).toBeInstanceOf(Date);
    });
    
    it('should get a project by ID', async () => {
      const project = await storage.getProject('test-project');
      
      expect(mockStore.get).toHaveBeenCalledWith(storage.projectCollection, 'test-project');
      expect(project).toBe(testProject);
    });
    
    it('should return null for non-existent project', async () => {
      mockStore.get.mockRejectedValueOnce(new Error('Not found'));
      
      const project = await storage.getProject('non-existent');
      
      expect(project).toBeNull();
    });
    
    it('should get projects by user ID', async () => {
      const projects = await storage.getUserProjects('test-user');
      
      expect(mockStore.query).toHaveBeenCalledWith({
        collection: storage.projectCollection,
        index: 'userId',
        value: 'test-user'
      });
      
      expect(projects).toEqual([testProject]);
    });
    
    it('should delete a project and its files', async () => {
      // Mock getProjectFiles to return test files
      const testFiles = [
        { id: 'file1', path: 'file1.js' },
        { id: 'file2', path: 'file2.js' }
      ];
      
      storage.getProjectFiles = jest.fn().mockResolvedValue(testFiles);
      
      await storage.deleteProject('test-project');
      
      // Should delete each file
      expect(mockStore.delete).toHaveBeenCalledWith(storage.fileCollection, 'file1');
      expect(mockStore.delete).toHaveBeenCalledWith(storage.fileCollection, 'file2');
      
      // And finally delete the project
      expect(mockStore.delete).toHaveBeenCalledWith(storage.projectCollection, 'test-project');
    });
  });
  
  describe('file operations', () => {
    it('should save project files', async () => {
      const projectId = 'test-project';
      const files = [
        { path: 'file1.js', content: 'console.log("file1");' },
        { path: 'file2.js', content: 'console.log("file2");' }
      ];
      
      await storage.saveProjectFiles(projectId, files);
      
      expect(mockStore.saveAll).toHaveBeenCalledWith(
        storage.fileCollection,
        expect.arrayContaining([
          expect.objectContaining({
            id: 'test-project_file1.js',
            projectId: 'test-project',
            path: 'file1.js',
            content: 'console.log("file1");'
          }),
          expect.objectContaining({
            id: 'test-project_file2.js',
            projectId: 'test-project',
            path: 'file2.js',
            content: 'console.log("file2");'
          })
        ])
      );
    });
    
    it('should get project files', async () => {
      const projectId = 'test-project';
      const testFiles = [
        { id: 'file1', path: 'file1.js' },
        { id: 'file2', path: 'file2.js' }
      ];
      
      mockStore.query.mockResolvedValueOnce(testFiles);
      
      const files = await storage.getProjectFiles(projectId);
      
      expect(mockStore.query).toHaveBeenCalledWith({
        collection: storage.fileCollection,
        index: 'projectId',
        value: 'test-project'
      });
      
      expect(files).toEqual(testFiles);
    });
    
    it('should get a specific project file', async () => {
      const projectId = 'test-project';
      const filePath = 'file1.js';
      const testFile = { id: 'test-project_file1.js', path: 'file1.js', content: 'test content' };
      
      mockStore.get.mockResolvedValueOnce(testFile);
      
      const file = await storage.getProjectFile(projectId, filePath);
      
      expect(mockStore.get).toHaveBeenCalledWith(storage.fileCollection, 'test-project_file1.js');
      expect(file).toEqual(testFile);
    });
    
    it('should save a specific project file', async () => {
      const projectId = 'test-project';
      const filePath = 'file1.js';
      const content = 'console.log("updated");';
      
      // Mock file doesn't exist yet
      mockStore.get.mockResolvedValueOnce(null);
      
      await storage.saveProjectFile(projectId, filePath, content);
      
      expect(mockStore.put).toHaveBeenCalledWith(
        storage.fileCollection,
        expect.objectContaining({
          id: 'test-project_file1.js',
          projectId: 'test-project',
          path: 'file1.js',
          content: 'console.log("updated");',
          createdAt: expect.any(Date),
          updatedAt: expect.any(Date)
        })
      );
    });
    
    it('should update an existing file', async () => {
      const projectId = 'test-project';
      const filePath = 'file1.js';
      const content = 'console.log("updated");';
      const existingFile = {
        id: 'test-project_file1.js',
        projectId: 'test-project',
        path: 'file1.js',
        content: 'console.log("original");',
        createdAt: new Date(2023, 1, 1)
      };
      
      // Mock file exists
      mockStore.get.mockResolvedValueOnce(existingFile);
      
      await storage.saveProjectFile(projectId, filePath, content);
      
      expect(mockStore.put).toHaveBeenCalledWith(
        storage.fileCollection,
        expect.objectContaining({
          id: 'test-project_file1.js',
          content: 'console.log("updated");',
          createdAt: existingFile.createdAt, // Should preserve original creation date
          updatedAt: expect.any(Date)
        })
      );
    });
    
    it('should delete a project file', async () => {
      const projectId = 'test-project';
      const filePath = 'file1.js';
      
      await storage.deleteProjectFile(projectId, filePath);
      
      expect(mockStore.delete).toHaveBeenCalledWith(storage.fileCollection, 'test-project_file1.js');
    });
  });
  
  describe('version operations', () => {
    let testProject;
    let testFiles;
    
    beforeEach(() => {
      testProject = {
        id: 'test-project',
        name: 'Test Project',
        specification: { name: 'TestApp' },
        generatedCode: { files: [] },
        testResults: { passed: true },
        status: 'in_progress'
      };
      
      testFiles = [
        { id: 'file1', path: 'file1.js', content: 'content1' },
        { id: 'file2', path: 'file2.js', content: 'content2' }
      ];
      
      mockStore.get.mockResolvedValueOnce(testProject);
      mockStore.query.mockResolvedValueOnce(testFiles);
    });
    
    it('should create a project version', async () => {
      const versionName = 'v1.0';
      
      await storage.createProjectVersion('test-project', versionName);
      
      // Should save version metadata
      expect(mockStore.put).toHaveBeenCalledWith(
        storage.projectCollection,
        expect.objectContaining({
          id: expect.stringContaining('test-project_version_'),
          projectId: 'test-project',
          name: 'v1.0',
          timestamp: expect.any(Date),
          specification: testProject.specification,
          generatedCode: testProject.generatedCode,
          testResults: testProject.testResults,
          status: testProject.status
        })
      );
      
      // Should save version files
      for (const file of testFiles) {
        expect(mockStore.put).toHaveBeenCalledWith(
          storage.fileCollection,
          expect.objectContaining({
            id: expect.stringContaining(file.path.replace(/\//g, '_')),
            versionId: expect.stringContaining('test-project_version_'),
            projectId: 'test-project',
            path: file.path,
            content: file.content,
            type: 'app_factory_version_file'
          })
        );
      }
    });
    
    it('should get project versions', async () => {
      const versions = [
        { id: 'test-project_version_1', name: 'v1.0' },
        { id: 'test-project_version_2', name: 'v2.0' }
      ];
      
      mockStore.query.mockReset();
      mockStore.query.mockResolvedValueOnce(versions);
      
      const result = await storage.getProjectVersions('test-project');
      
      expect(mockStore.query).toHaveBeenCalledWith({
        collection: storage.projectCollection,
        index: 'projectId',
        value: 'test-project',
        filter: expect.any(Function)
      });
      
      expect(result).toEqual(versions);
    });
  });
});

// Tests for AppFactoryConfig
describe('AppFactoryConfig', () => {
  let config;
  let mockStore;
  let mockEventBus;
  
  beforeEach(() => {
    // Create mock store
    mockStore = {
      get: jest.fn(),
      put: jest.fn().mockResolvedValue(true)
    };
    
    // Create mock event bus
    mockEventBus = {
      publish: jest.fn()
    };
    
    // Create test instance
    config = new AppFactoryConfig(mockStore, {
      userId: 'test-user',
      eventBus: mockEventBus
    });
    
    // Spy on console.log and error
    jest.spyOn(console, 'log').mockImplementation(() => {});
    jest.spyOn(console, 'error').mockImplementation(() => {});
  });
  
  afterEach(() => {
    console.log.mockRestore();
    console.error.mockRestore();
  });
  
  describe('constructor', () => {
    it('should initialize with provided options', () => {
      expect(config.store).toBe(mockStore);
      expect(config.userId).toBe('test-user');
      expect(config.eventBus).toBe(mockEventBus);
      expect(config.preferencesKey).toBe('user_preferences_test-user');
    });
    
    it('should initialize with default options when not provided', () => {
      const defaultConfig = new AppFactoryConfig(mockStore);
      
      expect(defaultConfig.userId).toBe('default');
      expect(defaultConfig.eventBus).toBeNull();
      expect(defaultConfig.preferencesKey).toBe('user_preferences_default');
    });
    
    it('should throw error if store is not provided', () => {
      expect(() => {
        new AppFactoryConfig();
      }).toThrow('AppFactoryConfig requires a store instance');
    });
  });
  
  describe('preference operations', () => {
    beforeEach(() => {
      // Mock user preferences
      mockStore.get.mockImplementation((collection, key) => {
        if (collection === 'system' && key === 'user_preferences_test-user') {
          return Promise.resolve({
            appFactory: {
              apiKey: 'test-api-key',
              templates: 'custom',
              defaultPublishTarget: 'github',
              githubUsername: 'testuser',
              githubToken: 'test-token',
              apiKeyRotation: true,
              apiUsageQuota: 200,
              showPromptReview: true,
              localOnlyMode: false
            }
          });
        }
        return Promise.resolve(null);
      });
    });
    
    it('should get App Factory preferences', async () => {
      const prefs = await config.getPreferences();
      
      expect(mockStore.get).toHaveBeenCalledWith('system', 'user_preferences_test-user');
      
      expect(prefs).toHaveProperty('apiKey', 'test-api-key');
      expect(prefs).toHaveProperty('templates', 'custom');
      expect(prefs).toHaveProperty('defaultPublishTarget', 'github');
      expect(prefs).toHaveProperty('githubUsername', 'testuser');
      expect(prefs).toHaveProperty('githubToken', 'test-token');
      expect(prefs).toHaveProperty('apiKeyRotation', true);
      expect(prefs).toHaveProperty('apiUsageQuota', 200);
      expect(prefs).toHaveProperty('showPromptReview', true);
      expect(prefs).toHaveProperty('localOnlyMode', false);
    });
    
    it('should return default preferences when not found', async () => {
      // Mock no preferences found
      mockStore.get.mockResolvedValueOnce(null);
      
      const prefs = await config.getPreferences();
      
      expect(prefs).toHaveProperty('apiKey', '');
      expect(prefs).toHaveProperty('templates', 'default');
      expect(prefs).toHaveProperty('defaultPublishTarget', 'local');
      expect(prefs).toHaveProperty('githubUsername', '');
      expect(prefs).toHaveProperty('githubToken', '');
      expect(prefs).toHaveProperty('apiKeyRotation', false);
      expect(prefs).toHaveProperty('apiUsageQuota', 100);
      expect(prefs).toHaveProperty('showPromptReview', false);
      expect(prefs).toHaveProperty('localOnlyMode', false);
    });
    
    it('should handle errors during preference retrieval', async () => {
      // Mock an error
      mockStore.get.mockRejectedValueOnce(new Error('Store error'));
      
      const prefs = await config.getPreferences();
      
      // Should return defaults
      expect(prefs).toHaveProperty('apiKey', '');
      expect(prefs).toHaveProperty('templates', 'default');
    });
    
    it('should save App Factory preferences', async () => {
      const newPrefs = {
        apiKey: 'new-api-key',
        templates: 'new-template'
      };
      
      await config.savePreferences(newPrefs);
      
      // Should first get current preferences
      expect(mockStore.get).toHaveBeenCalledWith('system', 'user_preferences_test-user');
      
      // Should save updated preferences
      expect(mockStore.put).toHaveBeenCalledWith(
        'system',
        'user_preferences_test-user',
        expect.objectContaining({
          appFactory: expect.objectContaining({
            apiKey: 'new-api-key',
            templates: 'new-template',
            // Should preserve existing preferences
            defaultPublishTarget: 'github',
            githubUsername: 'testuser',
            githubToken: 'test-token'
          })
        })
      );
      
      // Should publish event
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'app-factory:preferences-updated',
        expect.objectContaining({
          userId: 'test-user',
          preferences: expect.objectContaining({
            apiKey: 'new-api-key',
            templates: 'new-template'
          })
        })
      );
    });
    
    it('should create new preferences object if none exists', async () => {
      // Mock no preferences found
      mockStore.get.mockResolvedValueOnce(null);
      
      const newPrefs = {
        apiKey: 'new-api-key'
      };
      
      await config.savePreferences(newPrefs);
      
      // Should save new preferences
      expect(mockStore.put).toHaveBeenCalledWith(
        'system',
        'user_preferences_test-user',
        expect.objectContaining({
          appFactory: expect.objectContaining({
            apiKey: 'new-api-key'
          })
        })
      );
    });
  });
  
  describe('API key management', () => {
    it('should get API key', async () => {
      // Mock preferences
      config.getPreferences = jest.fn().mockResolvedValue({
        apiKey: 'test-api-key'
      });
      
      const apiKey = await config.getApiKey();
      
      expect(config.getPreferences).toHaveBeenCalled();
      expect(apiKey).toBe('test-api-key');
    });
    
    it('should save API key', async () => {
      // Mock savePreferences
      config.savePreferences = jest.fn().mockResolvedValue({
        apiKey: 'new-api-key'
      });
      
      await config.saveApiKey('new-api-key');
      
      expect(config.savePreferences).toHaveBeenCalledWith({
        apiKey: 'new-api-key'
      });
    });
    
    it('should validate API key is not empty when saving', async () => {
      await expect(config.saveApiKey('')).rejects.toThrow('API key is required');
    });
  });
  
  describe('GitHub credentials management', () => {
    it('should get GitHub credentials', async () => {
      // Mock preferences
      config.getPreferences = jest.fn().mockResolvedValue({
        githubUsername: 'testuser',
        githubToken: 'test-token'
      });
      
      const credentials = await config.getGitHubCredentials();
      
      expect(config.getPreferences).toHaveBeenCalled();
      expect(credentials).toEqual({
        username: 'testuser',
        token: 'test-token'
      });
    });
    
    it('should save GitHub credentials', async () => {
      // Mock savePreferences
      config.savePreferences = jest.fn().mockResolvedValue({
        githubUsername: 'newuser',
        githubToken: 'new-token'
      });
      
      await config.saveGitHubCredentials({
        username: 'newuser',
        token: 'new-token'
      });
      
      expect(config.savePreferences).toHaveBeenCalledWith({
        githubUsername: 'newuser',
        githubToken: 'new-token'
      });
    });
    
    it('should validate credentials are provided when saving', async () => {
      await expect(config.saveGitHubCredentials()).rejects.toThrow('Credentials are required');
    });
  });
  
  describe('API usage tracking', () => {
    beforeEach(() => {
      // Mock store for usage data
      mockStore.get.mockImplementation((collection, key) => {
        if (key === 'app_factory_api_usage_test-user') {
          return Promise.resolve({
            total: 1000,
            operations: {
              'inspiration': 500,
              'code-generation': 500
            },
            history: [
              { timestamp: new Date(), operation: 'inspiration', tokens: 500 },
              { timestamp: new Date(), operation: 'code-generation', tokens: 500 }
            ]
          });
        } else if (key === 'user_preferences_test-user') {
          return Promise.resolve({
            appFactory: {
              apiUsageQuota: 2000
            }
          });
        }
        return Promise.resolve(null);
      });
    });
    
    it('should track API usage', async () => {
      const operation = 'code-generation';
      const tokens = 200;
      
      await config.trackApiUsage(operation, tokens);
      
      // Should get current usage
      expect(mockStore.get).toHaveBeenCalledWith('system', 'app_factory_api_usage_test-user');
      
      // Should update and save usage
      expect(mockStore.put).toHaveBeenCalledWith(
        'system',
        'app_factory_api_usage_test-user',
        expect.objectContaining({
          total: 1200, // 1000 + 200
          operations: expect.objectContaining({
            'inspiration': 500,
            'code-generation': 700 // 500 + 200
          }),
          history: expect.arrayContaining([
            expect.objectContaining({
              operation: 'code-generation',
              tokens: 200
            })
          ])
        })
      );
    });
    
    it('should create usage data if none exists', async () => {
      // Mock no usage data
      mockStore.get.mockImplementation((collection, key) => {
        if (key === 'user_preferences_test-user') {
          return Promise.resolve({
            appFactory: {
              apiUsageQuota: 2000
            }
          });
        }
        return Promise.resolve(null);
      });
      
      const operation = 'inspiration';
      const tokens = 300;
      
      await config.trackApiUsage(operation, tokens);
      
      // Should save new usage data
      expect(mockStore.put).toHaveBeenCalledWith(
        'system',
        'app_factory_api_usage_test-user',
        expect.objectContaining({
          total: 300,
          operations: expect.objectContaining({
            'inspiration': 300
          }),
          history: expect.arrayContaining([
            expect.objectContaining({
              operation: 'inspiration',
              tokens: 300
            })
          ])
        })
      );
    });
    
    it('should notify of approaching quota', async () => {
      mockStore.get.mockImplementation((collection, key) => {
        if (key === 'app_factory_api_usage_test-user') {
          return Promise.resolve({
            total: 1700, // 85% of quota
            operations: {
              'inspiration': 1700
            },
            history: [
              { timestamp: new Date(), operation: 'inspiration', tokens: 1700 }
            ]
          });
        } else if (key === 'user_preferences_test-user') {
          return Promise.resolve({
            appFactory: {
              apiUsageQuota: 2000
            }
          });
        }
        return Promise.resolve(null);
      });
      
      await config.trackApiUsage('inspiration', 100);
      
      // Should notify of approaching quota
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'app-factory:api-quota-warning',
        expect.objectContaining({
          userId: 'test-user',
          percentUsed: 90, // (1700 + 100) / 2000 * 100
          total: 1800,
          quota: 2000
        })
      );
    });
    
    it('should limit history to 100 entries', async () => {
      // Create 120 history entries
      const history = Array(120).fill(0).map((_, i) => ({
        timestamp: new Date(),
        operation: 'test',
        tokens: 10
      }));
      
      mockStore.get.mockImplementation((collection, key) => {
        if (key === 'app_factory_api_usage_test-user') {
          return Promise.resolve({
            total: 1200,
            operations: {
              'test': 1200
            },
            history
          });
        } else if (key === 'user_preferences_test-user') {
          return Promise.resolve({
            appFactory: {
              apiUsageQuota: 2000
            }
          });
        }
        return Promise.resolve(null);
      });
      
      await config.trackApiUsage('test', 10);
      
      // Should trim history to 100 entries
      const putCall = mockStore.put.mock.calls[0];
      const savedData = putCall[2];
      expect(savedData.history.length).toBe(100);
      
      // Should keep the most recent entries
      expect(savedData.history[99]).toEqual(expect.objectContaining({
        operation: 'test',
        tokens: 10
      }));
    });
    
    it('should get API usage data', async () => {
      const usage = await config.getApiUsage();
      
      expect(mockStore.get).toHaveBeenCalledWith('system', 'app_factory_api_usage_test-user');
      expect(usage).toHaveProperty('total', 1000);
      expect(usage).toHaveProperty('operations');
      expect(usage.operations).toHaveProperty('inspiration', 500);
      expect(usage.operations).toHaveProperty('code-generation', 500);
      expect(usage).toHaveProperty('history');
      expect(usage.history.length).toBe(2);
    });
    
    it('should reset API usage data', async () => {
      // Add delete method if not present
      if (!mockStore.delete) {
        mockStore.delete = jest.fn().mockResolvedValue(true);
      }
      
      await config.resetApiUsage();
      
      expect(mockStore.delete).toHaveBeenCalledWith('system', 'app_factory_api_usage_test-user');
    });
  });
});