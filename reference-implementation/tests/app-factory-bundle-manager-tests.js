/**
 * PrimeOS Reference Implementation - BundleManager Tests
 * 
 * Tests for the BundleManager component in the App Factory system.
 * These tests focus on the BundleManager's ability to create, manipulate, 
 * validate, and export bundles.
 */

// Import Jest globals
const { describe, it, expect, beforeEach, afterEach } = require('@jest/globals');
// jest is already global, so don't need to import it

// Import the BundleManager component
const { BundleManager } = require('../core/app-factory/BundleManager');

describe('App Factory BundleManager', () => {
  let bundleManager;
  let mockStore;
  let mockCoherenceEngine;
  let mockEventBus;
  
  // Setup mocks for each test
  beforeEach(() => {
    // Create mock store
    mockStore = {
      put: jest.fn().mockResolvedValue(true),
      get: jest.fn(),
      query: jest.fn(),
      remove: jest.fn()
    };
    
    // Create mock coherence engine
    mockCoherenceEngine = {
      validateBundleCoherence: jest.fn().mockResolvedValue({
        valid: true,
        metrics: { score: 0.85 },
        issues: []
      }),
      generateCoherenceDoc: jest.fn().mockReturnValue({
        coherenceScore: 0.85,
        coherenceTimestamp: new Date().toISOString(),
        metrics: {
          interfaceCompleteness: 0.88,
          structuralIntegrity: 0.82,
          functionalCoverage: 0.9
        },
        entityRelationships: {
          entities: [],
          relationships: []
        },
        invariants: [],
        constraints: [],
        interfaceContracts: []
      })
    };
    
    // Create mock event bus
    mockEventBus = {
      publish: jest.fn()
    };
    
    // Initialize BundleManager instance with mocks
    bundleManager = new BundleManager({
      store: mockStore,
      coherenceEngine: mockCoherenceEngine,
      eventBus: mockEventBus
    });
    
    // Mock console methods to keep test output clean
    jest.spyOn(console, 'log').mockImplementation(() => {});
    jest.spyOn(console, 'error').mockImplementation(() => {});
    jest.spyOn(console, 'warn').mockImplementation(() => {});
    
    // Setup test bundle data
    const testBundle = {
      id: 'record_test-bundle_123',
      bundleId: 'test-bundle',
      type: 'prime_bundle',
      created: new Date().toISOString(),
      modified: new Date().toISOString(),
      manifest: {
        id: 'test-bundle',
        name: 'Test Bundle',
        version: '1.0.0',
        description: 'Test bundle for tests',
        entryPoint: 'views/main.js'
      },
      components: {
        'TestComponent.js': {
          path: 'components/TestComponent.js',
          content: 'class TestComponent {}',
          type: 'javascript',
          generated: true,
          modified: new Date().toISOString()
        }
      },
      models: {
        'TestModel.js': {
          path: 'models/TestModel.js',
          content: 'class TestModel {}',
          type: 'javascript',
          generated: true,
          modified: new Date().toISOString()
        }
      },
      services: {},
      views: {
        'main.js': {
          path: 'views/main.js',
          content: 'import TestComponent from "../components/TestComponent.js";',
          type: 'javascript',
          generated: true,
          modified: new Date().toISOString()
        }
      },
      assets: {
        'icon.svg': {
          path: 'assets/icon.svg',
          content: '<svg></svg>',
          type: 'image',
          generated: false,
          modified: new Date().toISOString()
        }
      }
    };
    
    // Setup mock responses
    mockStore.get.mockResolvedValue(testBundle);
    mockStore.query.mockResolvedValue([testBundle]);
  });
  
  // Clean up mocks after each test
  afterEach(() => {
    jest.restoreAllMocks();
  });
  
  describe('Initialization', () => {
    it('should require a store in constructor', () => {
      expect(() => new BundleManager({})).toThrow('BundleManager requires a store instance');
    });
    
    it('should initialize with required dependencies', () => {
      expect(bundleManager.store).toBe(mockStore);
      expect(bundleManager.coherenceEngine).toBe(mockCoherenceEngine);
      expect(bundleManager.eventBus).toBe(mockEventBus);
    });
    
    it('should initialize bundle template structure', () => {
      expect(bundleManager.bundleTemplate).toBeDefined();
      expect(bundleManager.bundleTemplate.manifest).toBeDefined();
      expect(bundleManager.bundleTemplate.components).toBeDefined();
      expect(bundleManager.bundleTemplate.models).toBeDefined();
      expect(bundleManager.bundleTemplate.services).toBeDefined();
      expect(bundleManager.bundleTemplate.views).toBeDefined();
      expect(bundleManager.bundleTemplate.assets).toBeDefined();
    });

    it('should initialize with minimal dependencies', () => {
      const minimalManager = new BundleManager({
        store: mockStore
      });
      
      expect(minimalManager.store).toBe(mockStore);
      expect(minimalManager.coherenceEngine).toBeUndefined();
      expect(minimalManager.eventBus).toBeUndefined();
    });
  });
  
  describe('Bundle Creation', () => {
    it('should create a new bundle with required fields', async () => {
      const bundleId = 'test-bundle';
      const initialData = {
        name: 'Test Bundle',
        description: 'A test bundle'
      };
      
      const result = await bundleManager.createBundle(bundleId, initialData);
      
      expect(mockStore.put).toHaveBeenCalled();
      expect(result).toHaveProperty('bundleId', bundleId);
      expect(result).toHaveProperty('type', 'prime_bundle');
      expect(result).toHaveProperty('manifest.name', initialData.name);
      expect(result).toHaveProperty('manifest.description', initialData.description);
      expect(result).toHaveProperty('manifest.id', bundleId);
      expect(result).toHaveProperty('manifest.version', '1.0.0');
      expect(result).toHaveProperty('created');
      expect(result).toHaveProperty('modified');
      
      // Check for event notification
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:created', expect.any(Object));
    });
    
    it('should throw error when bundleId is not provided', async () => {
      await expect(bundleManager.createBundle()).rejects.toThrow('Bundle ID is required');
    });
    
    it('should create a bundle with default structure when no initialData provided', async () => {
      const bundleId = 'minimal-bundle';
      
      const result = await bundleManager.createBundle(bundleId);
      
      expect(result).toHaveProperty('manifest.id', bundleId);
      expect(result).toHaveProperty('manifest.name', bundleId);
      expect(result).toHaveProperty('manifest.description', '');
      expect(result).toHaveProperty('components');
      expect(result).toHaveProperty('models');
      expect(result).toHaveProperty('services');
      expect(result).toHaveProperty('views');
      expect(result).toHaveProperty('assets');
    });
    
    it('should incorporate initialData into the bundle structure', async () => {
      const bundleId = 'custom-bundle';
      const initialData = {
        name: 'Custom Bundle',
        description: 'Custom bundle with initial data',
        components: {
          'CustomComponent.js': {
            path: 'components/CustomComponent.js',
            content: 'class CustomComponent {}',
            type: 'javascript'
          }
        },
        models: {
          'CustomModel.js': {
            path: 'models/CustomModel.js',
            content: 'class CustomModel {}',
            type: 'javascript'
          }
        }
      };
      
      const result = await bundleManager.createBundle(bundleId, initialData);
      
      expect(result.components).toEqual(initialData.components);
      expect(result.models).toEqual(initialData.models);
      expect(result.manifest.name).toBe(initialData.name);
    });
    
    it('should handle errors during bundle creation', async () => {
      const bundleId = 'error-bundle';
      
      // Force an error by making store.put reject
      mockStore.put.mockRejectedValueOnce(new Error('Store error'));
      
      await expect(bundleManager.createBundle(bundleId)).rejects.toThrow('Store error');
    });
  });
  
  describe('Bundle Loading', () => {
    it('should load an existing bundle', async () => {
      const bundleId = 'test-bundle';
      
      const result = await bundleManager.loadBundle(bundleId);
      
      expect(mockStore.query).toHaveBeenCalledWith({
        index: 'bundleId',
        value: bundleId,
        type: 'prime_bundle'
      });
      
      expect(result).toHaveProperty('bundleId', bundleId);
      expect(result).toHaveProperty('manifest.name', 'Test Bundle');
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:loaded', expect.any(Object));
    });
    
    it('should throw error when bundleId is not provided for loading', async () => {
      await expect(bundleManager.loadBundle()).rejects.toThrow('Bundle ID is required');
    });
    
    it('should throw error when bundle is not found', async () => {
      const bundleId = 'nonexistent-bundle';
      
      // Mock empty query result
      mockStore.query.mockResolvedValueOnce([]);
      
      await expect(bundleManager.loadBundle(bundleId)).rejects.toThrow(`Bundle not found: ${bundleId}`);
    });
    
    it('should return the most recent bundle when multiple versions exist', async () => {
      const bundleId = 'versioned-bundle';
      
      // Mock multiple bundle versions with different timestamps
      const olderBundle = {
        id: 'record_versioned-bundle_1',
        bundleId: bundleId,
        modified: '2025-01-01T00:00:00.000Z',
        manifest: { name: 'Older Version' }
      };
      
      const newerBundle = {
        id: 'record_versioned-bundle_2',
        bundleId: bundleId,
        modified: '2025-02-01T00:00:00.000Z',
        manifest: { name: 'Newer Version' }
      };
      
      mockStore.query.mockResolvedValueOnce([olderBundle, newerBundle]);
      
      const result = await bundleManager.loadBundle(bundleId);
      
      expect(result.manifest.name).toBe('Newer Version');
    });
    
    it('should handle error during bundle loading', async () => {
      const bundleId = 'error-bundle';
      
      // Force an error by making store.query reject
      mockStore.query.mockRejectedValueOnce(new Error('Query error'));
      
      await expect(bundleManager.loadBundle(bundleId)).rejects.toThrow('Query error');
    });
  });
  
  describe('Bundle Updating', () => {
    it('should update an existing bundle', async () => {
      const bundleId = 'test-bundle';
      const updatedData = {
        manifest: {
          name: 'Updated Bundle Name',
          description: 'Updated description'
        }
      };
      
      const result = await bundleManager.updateBundle(bundleId, updatedData);
      
      expect(mockStore.query).toHaveBeenCalled(); // For loadBundle
      expect(mockStore.put).toHaveBeenCalled(); // For saving updated bundle
      
      expect(result).toHaveProperty('manifest.name', 'Updated Bundle Name');
      expect(result).toHaveProperty('manifest.description', 'Updated description');
      expect(result).toHaveProperty('bundleId', bundleId); // Ensure bundleId remains constant
      expect(result).toHaveProperty('modified'); // Modified timestamp should be updated
      
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:updated', expect.any(Object));
    });
    
    it('should throw error when bundleId is not provided for updating', async () => {
      await expect(bundleManager.updateBundle(null, {})).rejects.toThrow('Bundle ID is required');
    });
    
    it('should throw error when bundleData is not provided for updating', async () => {
      await expect(bundleManager.updateBundle('test-bundle')).rejects.toThrow('Bundle data is required');
    });
    
    it('should ensure bundleId remains constant during update', async () => {
      const bundleId = 'test-bundle';
      const updatedData = {
        bundleId: 'different-id', // Try to change bundleId
        manifest: {
          name: 'Updated Bundle'
        }
      };
      
      const result = await bundleManager.updateBundle(bundleId, updatedData);
      
      expect(result.bundleId).toBe(bundleId); // Should keep original bundleId
    });
    
    it('should handle error during bundle update', async () => {
      const bundleId = 'test-bundle';
      
      // Force an error by making store.put reject
      mockStore.put.mockRejectedValueOnce(new Error('Update error'));
      
      await expect(bundleManager.updateBundle(bundleId, { manifest: { name: 'Updated' } }))
        .rejects.toThrow('Update error');
    });
  });
  
  describe('File Management', () => {
    it('should add a file to the bundle', async () => {
      const bundleId = 'test-bundle';
      const filePath = 'components/NewComponent.js';
      const content = 'class NewComponent {}';
      
      const result = await bundleManager.addBundleFile(bundleId, filePath, content);
      
      expect(mockStore.query).toHaveBeenCalled(); // For loadBundle
      expect(mockStore.put).toHaveBeenCalled(); // For saving updated bundle
      
      // Check if file was added to the appropriate category
      expect(result.components['NewComponent.js']).toBeDefined();
      expect(result.components['NewComponent.js'].path).toBe(filePath);
      expect(result.components['NewComponent.js'].content).toBe(content);
      expect(result.components['NewComponent.js'].type).toBe('javascript');
      
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:file-added', expect.any(Object));
    });
    
    it('should determine correct file category from path', async () => {
      // Test different file paths
      const bundleId = 'test-bundle';
      
      // Add files to different categories
      await bundleManager.addBundleFile(bundleId, 'models/NewModel.js', 'class NewModel {}');
      await bundleManager.addBundleFile(bundleId, 'services/NewService.js', 'class NewService {}');
      await bundleManager.addBundleFile(bundleId, 'views/NewView.js', 'class NewView {}');
      await bundleManager.addBundleFile(bundleId, 'assets/new-icon.svg', '<svg></svg>');
      
      // Check if each file was added to the correct category
      const bundle = await bundleManager.loadBundle(bundleId);
      
      expect(bundle.models['NewModel.js']).toBeDefined();
      expect(bundle.services['NewService.js']).toBeDefined();
      expect(bundle.views['NewView.js']).toBeDefined();
      expect(bundle.assets['new-icon.svg']).toBeDefined();
    });
    
    it('should determine file type from extension', async () => {
      const bundleId = 'test-bundle';
      
      // Test different file extensions
      await bundleManager.addBundleFile(bundleId, 'assets/styles.css', 'body { color: red; }');
      await bundleManager.addBundleFile(bundleId, 'assets/template.html', '<div>Template</div>');
      await bundleManager.addBundleFile(bundleId, 'assets/data.json', '{"key": "value"}');
      await bundleManager.addBundleFile(bundleId, 'assets/readme.md', '# Title');
      
      const bundle = await bundleManager.loadBundle(bundleId);
      
      expect(bundle.assets['styles.css'].type).toBe('css');
      expect(bundle.assets['template.html'].type).toBe('html');
      expect(bundle.assets['data.json'].type).toBe('json');
      expect(bundle.assets['readme.md'].type).toBe('markdown');
    });
    
    it('should throw error when bundleId or filePath is not provided', async () => {
      await expect(bundleManager.addBundleFile()).rejects.toThrow('Bundle ID and file path are required');
      await expect(bundleManager.addBundleFile('test-bundle')).rejects.toThrow('Bundle ID and file path are required');
    });
    
    it('should handle JSON content properly', async () => {
      const bundleId = 'test-bundle';
      const filePath = 'models/config.json';
      const content = { key: 'value', nested: { items: [1, 2, 3] } };
      
      const result = await bundleManager.addBundleFile(bundleId, filePath, content);
      
      expect(result.models['config.json'].content).toBe(JSON.stringify(content));
      expect(result.models['config.json'].type).toBe('json');
    });
    
    it('should remove a file from the bundle', async () => {
      const bundleId = 'test-bundle';
      const filePath = 'components/TestComponent.js';
      
      const result = await bundleManager.removeBundleFile(bundleId, filePath);
      
      expect(mockStore.query).toHaveBeenCalled(); // For loadBundle
      expect(mockStore.put).toHaveBeenCalled(); // For saving updated bundle
      
      // Check if file was removed
      expect(result.components['TestComponent.js']).toBeUndefined();
      
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:file-removed', expect.any(Object));
    });
    
    it('should throw error when removing a file that does not exist', async () => {
      const bundleId = 'test-bundle';
      const filePath = 'components/NonExistentComponent.js';
      
      await expect(bundleManager.removeBundleFile(bundleId, filePath))
        .rejects.toThrow(`File NonExistentComponent.js not found in bundle category components`);
    });
    
    it('should throw error when removing a file from a category that does not exist', async () => {
      const bundleId = 'test-bundle';
      const filePath = 'nonexistent-category/file.js';
      
      // Create a custom mock bundle with no categories
      const emptyBundle = {
        id: 'record_test-bundle_123',
        bundleId: bundleId,
        type: 'prime_bundle',
        manifest: {}
        // Missing all bundle categories
      };
      
      // Mock the removeBundleFile method to resolve our specific error
      const originalMethod = bundleManager._determineFileCategory;
      bundleManager._determineFileCategory = jest.fn().mockReturnValue('nonexistent-category');
      
      // Override the default mock for this specific test
      mockStore.query.mockResolvedValueOnce([emptyBundle]);
      
      await expect(bundleManager.removeBundleFile(bundleId, filePath))
        .rejects.toThrow('Category nonexistent-category not found in bundle');
        
      // Restore original method
      bundleManager._determineFileCategory = originalMethod;
    });
  });
  
  describe('Bundle Validation', () => {
    it('should validate a bundle successfully', async () => {
      const bundleId = 'test-bundle';
      
      // Mock the _validateBundleStructure method
      const validateStructureSpy = jest.spyOn(bundleManager, '_validateBundleStructure')
        .mockReturnValue({ valid: true });
      
      const result = await bundleManager.validateBundle(bundleId);
      
      expect(mockStore.query).toHaveBeenCalled(); // For loadBundle
      expect(validateStructureSpy).toHaveBeenCalled();
      expect(mockCoherenceEngine.validateBundleCoherence).toHaveBeenCalled();
      
      expect(result).toHaveProperty('valid', true);
      expect(result).toHaveProperty('structureValidation');
      expect(result).toHaveProperty('coherenceValidation');
      
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:validated', expect.any(Object));
      
      validateStructureSpy.mockRestore();
    });
    
    it('should throw error when bundleId is not provided for validation', async () => {
      await expect(bundleManager.validateBundle()).rejects.toThrow('Bundle ID is required');
    });
    
    it('should handle structure validation failure', async () => {
      const bundleId = 'test-bundle';
      
      // Mock structure validation failure
      const validateStructureSpy = jest.spyOn(bundleManager, '_validateBundleStructure')
        .mockReturnValue({ valid: false, issues: ['Missing required fields'] });
      
      const result = await bundleManager.validateBundle(bundleId);
      
      expect(result.valid).toBe(false);
      expect(result.structureValidation.valid).toBe(false);
      
      validateStructureSpy.mockRestore();
    });
    
    it('should handle coherence validation failure', async () => {
      const bundleId = 'test-bundle';
      
      // Mock structure validation success but coherence validation failure
      const validateStructureSpy = jest.spyOn(bundleManager, '_validateBundleStructure')
        .mockReturnValue({ valid: true });
      
      mockCoherenceEngine.validateBundleCoherence.mockResolvedValueOnce({
        valid: false,
        metrics: { score: 0.6 }, // Below threshold
        issues: ['Low coherence score']
      });
      
      const result = await bundleManager.validateBundle(bundleId);
      
      expect(result.valid).toBe(false);
      expect(result.structureValidation.valid).toBe(true);
      expect(result.coherenceValidation.valid).toBe(false);
      
      validateStructureSpy.mockRestore();
    });
    
    it('should validate bundle structure correctly', () => {
      // Create complete bundle to validate
      const completeBundle = {
        manifest: {
          id: 'test-bundle',
          version: '1.0.0',
          name: 'Test Bundle',
          entryPoint: 'views/main.js'
        },
        components: {},
        models: {},
        services: {},
        views: {
          'main.js': {
            path: 'views/main.js',
            content: '// Entry point'
          }
        }
      };
      
      const result = bundleManager._validateBundleStructure(completeBundle);
      expect(result.valid).toBe(true);
      
      // Test missing required categories
      const incompleteBundle = {
        manifest: {
          id: 'test-bundle',
          version: '1.0.0',
          name: 'Test Bundle',
          entryPoint: 'views/main.js'
        },
        // Missing components, models, services
        views: {}
      };
      
      const result2 = bundleManager._validateBundleStructure(incompleteBundle);
      expect(result2.valid).toBe(false);
      expect(result2.issues.length).toBeGreaterThan(0);
      
      // Test missing manifest fields
      const bundleWithIncompleteManifest = {
        manifest: {
          // Missing id, version
          name: 'Test Bundle',
          entryPoint: 'views/main.js'
        },
        components: {},
        models: {},
        services: {},
        views: {}
      };
      
      const result3 = bundleManager._validateBundleStructure(bundleWithIncompleteManifest);
      expect(result3.valid).toBe(false);
      expect(result3.issues.length).toBeGreaterThan(0);
      
      // Test missing entry point
      const bundleWithMissingEntryPoint = {
        manifest: {
          id: 'test-bundle',
          version: '1.0.0',
          name: 'Test Bundle',
          entryPoint: 'views/missing.js'
        },
        components: {},
        models: {},
        services: {},
        views: {} // Entry point file not present
      };
      
      const result4 = bundleManager._validateBundleStructure(bundleWithMissingEntryPoint);
      expect(result4.valid).toBe(false);
      expect(result4.issues.length).toBeGreaterThan(0);
    });
  });
  
  describe('Bundle Export', () => {
    it('should export a bundle successfully', async () => {
      const bundleId = 'test-bundle';
      
      // Mock validate bundle to return valid result
      jest.spyOn(bundleManager, 'validateBundle').mockResolvedValueOnce({
        valid: true,
        structureValidation: { valid: true },
        coherenceValidation: {
          valid: true,
          metrics: { score: 0.85 }
        }
      });
      
      // Mock _encodeFileContent
      const encodeContentSpy = jest.spyOn(bundleManager, '_encodeFileContent')
        .mockReturnValue('encoded-content');
      
      const result = await bundleManager.exportBundle(bundleId);
      
      expect(mockStore.query).toHaveBeenCalled(); // For loadBundle
      expect(bundleManager.validateBundle).toHaveBeenCalled();
      expect(encodeContentSpy).toHaveBeenCalled();
      
      expect(result).toHaveProperty('manifest');
      expect(result).toHaveProperty('code');
      expect(result).toHaveProperty('resources');
      
      // Check manifest
      expect(result.manifest.id).toBe('test-bundle');
      
      // Check code files
      expect(Object.keys(result.code).length).toBeGreaterThan(0);
      
      // Check if coherence doc was generated
      expect(mockCoherenceEngine.generateCoherenceDoc).toHaveBeenCalled();
      expect(result.code['coherence.json']).toBeDefined();
      
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:exported', expect.any(Object));
      
      encodeContentSpy.mockRestore();
    });
    
    it('should throw error when bundleId is not provided for export', async () => {
      await expect(bundleManager.exportBundle()).rejects.toThrow('Bundle ID is required');
    });
    
    it('should throw error when bundle validation fails', async () => {
      const bundleId = 'test-bundle';
      
      // Mock validation failure
      jest.spyOn(bundleManager, 'validateBundle').mockResolvedValueOnce({
        valid: false,
        structureValidation: { valid: false, issues: ['Missing required fields'] }
      });
      
      await expect(bundleManager.exportBundle(bundleId))
        .rejects.toThrow(`Cannot export invalid bundle: ${bundleId}`);
    });
    
    it('should handle file encoding properly', () => {
      // Test different content types
      const textContent = 'Text content';
      const result1 = bundleManager._encodeFileContent(textContent);
      expect(result1).toBe(btoa(textContent));
      
      // Test already encoded content
      const alreadyEncoded = 'already-encoded';
      
      // Save original btoa function
      const originalBtoa = global.btoa;
      
      // Mock btoa to throw an error
      global.btoa = jest.fn().mockImplementation(() => {
        throw new Error('btoa error');
      });
      
      const result2 = bundleManager._encodeFileContent(alreadyEncoded);
      expect(result2).toBe(alreadyEncoded);
      
      // Restore original btoa function
      global.btoa = originalBtoa;
    });
    
    it('should export without coherence engine if not available', async () => {
      // Create bundle manager without coherence engine
      const managerWithoutCoherence = new BundleManager({
        store: mockStore,
        eventBus: mockEventBus
      });
      
      const bundleId = 'test-bundle';
      
      // Mock validate bundle to return valid result
      jest.spyOn(managerWithoutCoherence, 'validateBundle').mockResolvedValueOnce({
        valid: true
      });
      
      // Mock _encodeFileContent
      const encodeContentSpy = jest.spyOn(managerWithoutCoherence, '_encodeFileContent')
        .mockReturnValue('encoded-content');
      
      const result = await managerWithoutCoherence.exportBundle(bundleId);
      
      expect(result).toHaveProperty('manifest');
      expect(result).toHaveProperty('code');
      
      // Should not have coherence.json when no coherence engine
      expect(result.code['coherence.json']).toBeUndefined();
      
      encodeContentSpy.mockRestore();
    });
  });
  
  describe('File Category and Type Detection', () => {
    it('should correctly determine file category from path', () => {
      // Test various file paths
      expect(bundleManager._determineFileCategory('assets/icon.svg')).toBe('assets');
      expect(bundleManager._determineFileCategory('components/Button.js')).toBe('components');
      expect(bundleManager._determineFileCategory('models/User.js')).toBe('models');
      expect(bundleManager._determineFileCategory('services/API.js')).toBe('services');
      expect(bundleManager._determineFileCategory('views/Main.js')).toBe('views');
      expect(bundleManager._determineFileCategory('tests/test.js')).toBe('tests');
      expect(bundleManager._determineFileCategory('docs/readme.md')).toBe('docs');
      
      // Test with path prefixes
      expect(bundleManager._determineFileCategory('src/assets/icon.svg')).toBe('assets');
      expect(bundleManager._determineFileCategory('app/components/Button.js')).toBe('components');
      
      // Test with uppercase
      expect(bundleManager._determineFileCategory('ASSETS/icon.svg')).toBe('assets');
      
      // Test unknown category (should default to components)
      expect(bundleManager._determineFileCategory('unknown/file.js')).toBe('components');
    });
    
    it('should correctly determine file type from extension', () => {
      // Test various file extensions
      expect(bundleManager._determineFileType('file.js')).toBe('javascript');
      expect(bundleManager._determineFileType('file.json')).toBe('json');
      expect(bundleManager._determineFileType('file.css')).toBe('css');
      expect(bundleManager._determineFileType('file.html')).toBe('html');
      expect(bundleManager._determineFileType('file.md')).toBe('markdown');
      
      // Test image types
      expect(bundleManager._determineFileType('image.png')).toBe('image');
      expect(bundleManager._determineFileType('image.jpg')).toBe('image');
      expect(bundleManager._determineFileType('image.jpeg')).toBe('image');
      expect(bundleManager._determineFileType('image.gif')).toBe('image');
      expect(bundleManager._determineFileType('image.svg')).toBe('image');
      
      // Test unknown type
      expect(bundleManager._determineFileType('file.unknown')).toBe('text');
      
      // Test case insensitivity
      expect(bundleManager._determineFileType('file.JS')).toBe('javascript');
    });
  });
  
  describe('Event Notifications', () => {
    it('should notify bundle events through the event bus', async () => {
      // Test the _notifyBundleEvent method
      // Reset the mock to ensure clean test
      mockEventBus.publish.mockClear();
      
      // Call the method - note the parameter order: event, bundleId, data
      bundleManager._notifyBundleEvent('test-event', 'test-bundle-id', { extraData: 'test-data' });
      
      // Check if method was called with the right event name and data structure
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'bundle:test-event', 
        expect.objectContaining({
          bundleId: 'test-bundle-id',
          timestamp: expect.any(String),
          extraData: 'test-data'
        })
      );
    });
    
    it('should handle event notification when event bus is unavailable', () => {
      // Create bundle manager without event bus
      const managerWithoutEventBus = new BundleManager({
        store: mockStore
      });
      
      // Should not throw error when no event bus is available
      expect(() => {
        managerWithoutEventBus._notifyBundleEvent('test-event', { id: 'test-bundle' });
      }).not.toThrow();
    });
    
    it('should publish events for all major bundle operations', async () => {
      const bundleId = 'test-bundle';
      
      // Clear previous mock calls
      mockEventBus.publish.mockClear();
      
      // Test create
      await bundleManager.createBundle(bundleId, { name: 'Test Bundle' });
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:created', expect.any(Object));
      
      // Test load
      mockEventBus.publish.mockClear();
      await bundleManager.loadBundle(bundleId);
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:loaded', expect.any(Object));
      
      // Test update
      mockEventBus.publish.mockClear();
      await bundleManager.updateBundle(bundleId, { manifest: { name: 'Updated' } });
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:updated', expect.any(Object));
      
      // Test file operations
      mockEventBus.publish.mockClear();
      await bundleManager.addBundleFile(bundleId, 'test/file.js', 'content');
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:file-added', expect.any(Object));
      
      mockEventBus.publish.mockClear();
      await bundleManager.removeBundleFile(bundleId, 'test/file.js');
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:file-removed', expect.any(Object));
      
      // Test validation
      mockEventBus.publish.mockClear();
      await bundleManager.validateBundle(bundleId);
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:validated', expect.any(Object));
      
      // Test export
      mockEventBus.publish.mockClear();
      jest.spyOn(bundleManager, 'validateBundle').mockResolvedValueOnce({ valid: true });
      await bundleManager.exportBundle(bundleId);
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:exported', expect.any(Object));
    });
  });
  
  // Test fallback behavior when dependencies are missing
  describe('Fallback Behavior', () => {
    it('should handle validation without coherence engine', async () => {
      // Create bundle manager without coherence engine
      const managerWithoutCoherence = new BundleManager({
        store: mockStore,
        eventBus: mockEventBus
      });
      
      const bundleId = 'test-bundle';
      
      // Mock _validateBundleStructure to return valid
      jest.spyOn(managerWithoutCoherence, '_validateBundleStructure')
        .mockReturnValue({ valid: true });
      
      const result = await managerWithoutCoherence.validateBundle(bundleId);
      
      expect(result.valid).toBe(true);
      expect(result.coherenceValidation.valid).toBe(true);
      expect(result.coherenceValidation.score).toBe(0.8); // Default fallback value
    });
  });
});