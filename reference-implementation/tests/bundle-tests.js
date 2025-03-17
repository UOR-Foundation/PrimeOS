/**
 * PrimeOS App Bundle Tests
 * 
 * Tests for the PrimeOS App Bundle system that provides portable app packaging.
 */

// Mock dependencies
const mockStore = {
  get: jest.fn(),
  put: jest.fn(),
  query: jest.fn(),
  saveAll: jest.fn(),
  remove: jest.fn()
};

const mockEventBus = {
  publish: jest.fn(),
  subscribe: jest.fn(),
  unsubscribe: jest.fn()
};

const mockIdentity = {
  isAuthenticated: jest.fn(),
  sign: jest.fn(),
  verify: jest.fn()
};

// Import bundle module
const { BundleManager } = require('../core/bundle/bundle-manager');
const { BundleAPI } = require('../core/bundle/bundle-api');

describe('PrimeOS App Bundle System', () => {
  let bundleManager;
  let bundleAPI;
  
  beforeEach(() => {
    // Reset mocks
    jest.clearAllMocks();
    
    // Initialize bundle manager with mocked dependencies
    bundleManager = new BundleManager({
      store: mockStore,
      eventBus: mockEventBus,
      identity: mockIdentity
    });
    
    // Mock installedBundles map with test data
    bundleManager.installedBundles = new Map([
      ['com.example.test-app', {
        manifest: {
          id: 'com.example.test-app',
          name: 'Test App',
          version: '1.0.0',
          author: 'Test Author',
          description: 'Test Description',
          entryPoint: 'index.js'
        },
        installed: '2025-03-17T12:00:00.000Z',
        enabled: true
      }]
    ]);
    
    // Initialize bundle API
    bundleAPI = new BundleAPI({
      bundleManager,
      eventBus: mockEventBus,
      appId: 'test-app'
    });
  });
  
  describe('BundleManager', () => {
    test('should initialize with required dependencies', () => {
      expect(bundleManager).toBeDefined();
      expect(mockEventBus.subscribe).toHaveBeenCalledWith('system:ready', expect.any(Function));
    });
    
    test('should throw error if store is not provided', () => {
      expect(() => {
        new BundleManager({ eventBus: mockEventBus });
      }).toThrow('BundleManager requires a store instance');
    });
    
    test('should throw error if eventBus is not provided', () => {
      expect(() => {
        new BundleManager({ store: mockStore });
      }).toThrow('BundleManager requires an eventBus instance');
    });
    
    test('should load installed bundles on initialization', async () => {
      mockStore.query.mockResolvedValue([
        {
          id: 'com.example.app1',
          type: 'bundle',
          manifest: {
            id: 'com.example.app1',
            name: 'App 1',
            version: '1.0.0'
          },
          installed: '2025-03-17T12:00:00.000Z',
          enabled: true
        },
        {
          id: 'com.example.app2',
          type: 'bundle',
          manifest: {
            id: 'com.example.app2',
            name: 'App 2',
            version: '1.0.0'
          },
          installed: '2025-03-17T12:00:00.000Z',
          enabled: false
        }
      ]);
      
      await bundleManager._loadInstalledBundles();
      
      expect(mockStore.query).toHaveBeenCalledWith({
        index: 'type',
        value: 'bundle'
      });
      
      expect(bundleManager.installedBundles.size).toBe(2);
      expect(bundleManager.installedBundles.has('com.example.app1')).toBe(true);
      expect(bundleManager.installedBundles.has('com.example.app2')).toBe(true);
    });
    
    test('should validate bundle manifest correctly', () => {
      // Valid manifest
      const validManifest = {
        id: 'com.example.app',
        name: 'Example App',
        version: '1.0.0',
        entryPoint: 'index.js'
      };
      
      const validResult = bundleManager._validateBundleManifest(validManifest);
      expect(validResult.valid).toBe(true);
      
      // Invalid manifest - missing required field
      const invalidManifest1 = {
        id: 'com.example.app',
        name: 'Example App',
        version: '1.0.0'
        // Missing entryPoint
      };
      
      const invalidResult1 = bundleManager._validateBundleManifest(invalidManifest1);
      expect(invalidResult1.valid).toBe(false);
      
      // Invalid manifest - invalid version format
      const invalidManifest2 = {
        id: 'com.example.app',
        name: 'Example App',
        version: '1.0', // Invalid format
        entryPoint: 'index.js'
      };
      
      const invalidResult2 = bundleManager._validateBundleManifest(invalidManifest2);
      expect(invalidResult2.valid).toBe(false);
    });
    
    test('should create a bundle from an app', async () => {
      // Mock app record
      mockStore.get.mockResolvedValue({
        id: 'com.example.app',
        name: 'Example App',
        version: '1.0.0',
        author: 'Example Author',
        description: 'Example Description',
        entryPoint: 'index.js',
        tags: ['utility', 'productivity']
      });
      
      // Mock app code files
      mockStore.query.mockImplementation(query => {
        if (query.filter && typeof query.filter === 'function') {
          if (query.filter({ appId: 'com.example.app', isCode: true })) {
            return Promise.resolve([
              {
                appId: 'com.example.app',
                path: 'index.js',
                content: 'console.log("Hello world");',
                encoding: 'text'
              }
            ]);
          } else if (query.filter({ appId: 'com.example.app', isCode: false })) {
            return Promise.resolve([
              {
                appId: 'com.example.app',
                path: 'icon.png',
                content: new Uint8Array([1, 2, 3, 4]),
                encoding: 'binary'
              }
            ]);
          }
        }
        return Promise.resolve([]);
      });
      
      // Create the bundle
      const bundle = await bundleManager.createBundle('com.example.app');
      
      // Verify bundle structure
      expect(bundle).toBeDefined();
      expect(bundle.manifest).toBeDefined();
      expect(bundle.manifest.id).toBe('com.example.app');
      expect(bundle.manifest.name).toBe('Example App');
      expect(bundle.manifest.version).toBe('1.0.0');
      expect(bundle.code).toBeDefined();
      expect(bundle.code['index.js']).toBeDefined();
      expect(bundle.resources).toBeDefined();
      expect(bundle.resources['icon.png']).toBeDefined();
      
      // Verify event notification
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:created', expect.any(Object));
    });
    
    test('should import a bundle', async () => {
      // Create test bundle
      const testBundle = {
        manifest: {
          id: 'com.example.import-app',
          name: 'Import App',
          version: '1.0.0',
          author: 'Test Author',
          description: 'Test Description',
          entryPoint: 'index.js'
        },
        code: {
          'index.js': btoa('console.log("Hello world");')
        },
        resources: {
          'icon.png': btoa('fake-binary-data')
        }
      };
      
      // Mock validation to return success
      jest.spyOn(bundleManager, 'validateBundle').mockResolvedValue({
        valid: true,
        manifest: { valid: true },
        content: { valid: true },
        signature: { valid: true },
        version: { valid: true }
      });
      
      // Import the bundle
      const result = await bundleManager.importBundle(testBundle);
      
      // Verify result
      expect(result.success).toBe(true);
      expect(result.bundleId).toBe('com.example.import-app');
      
      // Verify store operations
      expect(mockStore.put).toHaveBeenCalledWith({
        id: 'com.example.import-app',
        type: 'bundle',
        manifest: testBundle.manifest,
        installed: expect.any(String),
        enabled: true
      });
      
      // Verify file storage
      expect(mockStore.saveAll).toHaveBeenCalled();
      
      // Verify event notification
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:imported', expect.any(Object));
    });
    
    test('should uninstall a bundle', async () => {
      // Mock store operations
      mockStore.query.mockResolvedValue([
        { id: 'com.example.test-app:index.js' },
        { id: 'com.example.test-app:icon.png' }
      ]);
      
      // Uninstall the bundle
      const result = await bundleManager.uninstallBundle('com.example.test-app');
      
      // Verify result
      expect(result).toBe(true);
      
      // Verify store operations
      expect(mockStore.query).toHaveBeenCalled();
      expect(mockStore.remove).toHaveBeenCalledTimes(3); // 2 files + 1 bundle record
      
      // Verify installedBundles map update
      expect(bundleManager.installedBundles.has('com.example.test-app')).toBe(false);
      
      // Verify event notifications
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:uninstalling', expect.any(Object));
      expect(mockEventBus.publish).toHaveBeenCalledWith('bundle:uninstalled', expect.any(Object));
    });
  });
  
  describe('BundleAPI', () => {
    test('should initialize with required dependencies', () => {
      expect(bundleAPI).toBeDefined();
      expect(mockEventBus.subscribe).toHaveBeenCalledWith('bundle:imported', expect.any(Function));
      expect(mockEventBus.subscribe).toHaveBeenCalledWith('bundle:uninstalled', expect.any(Function));
    });
    
    test('should throw error if bundleManager is not provided', () => {
      expect(() => {
        new BundleAPI({
          eventBus: mockEventBus,
          appId: 'test-app'
        });
      }).toThrow('BundleAPI requires a bundleManager instance');
    });
    
    test('should get locally installed bundles', async () => {
      // Mock bundleManager.getInstalledBundles
      jest.spyOn(bundleManager, 'getInstalledBundles').mockResolvedValue([
        {
          id: 'com.example.app1',
          name: 'App 1',
          version: '1.0.0',
          author: 'Author 1',
          description: 'Description 1',
          installed: '2025-03-17T12:00:00.000Z',
          enabled: true
        },
        {
          id: 'com.example.app2',
          name: 'App 2',
          version: '1.0.0',
          author: 'Author 2',
          description: 'Description 2',
          installed: '2025-03-17T12:00:00.000Z',
          enabled: false
        }
      ]);
      
      const bundles = await bundleAPI.getLocallyInstalledBundles();
      
      expect(bundles).toHaveLength(2);
      expect(bundles[0].id).toBe('com.example.app1');
      expect(bundles[1].id).toBe('com.example.app2');
      expect(bundleManager.getInstalledBundles).toHaveBeenCalled();
    });
    
    test('should install a bundle from a remote', async () => {
      // Mock bundleManager.installBundleFromRemote
      jest.spyOn(bundleManager, 'installBundleFromRemote').mockResolvedValue({
        success: true,
        bundleId: 'com.example.remote-app'
      });
      
      const result = await bundleAPI.installBundle(
        'com.example.remote-app',
        'https://example.com/bundles'
      );
      
      expect(result.success).toBe(true);
      expect(bundleManager.installBundleFromRemote).toHaveBeenCalledWith(
        'com.example.remote-app',
        'https://example.com/bundles'
      );
    });
    
    test('should uninstall a bundle', async () => {
      // Mock bundleManager.uninstallBundle
      jest.spyOn(bundleManager, 'uninstallBundle').mockResolvedValue(true);
      
      const result = await bundleAPI.uninstallBundle('com.example.test-app');
      
      expect(result.success).toBe(true);
      expect(result.bundleId).toBe('com.example.test-app');
      expect(bundleManager.uninstallBundle).toHaveBeenCalledWith('com.example.test-app');
    });
    
    test('should export a bundle', async () => {
      // Mock bundleManager.exportBundle
      const mockBundle = {
        manifest: {
          id: 'com.example.test-app',
          name: 'Test App',
          version: '1.0.0'
        },
        code: { 'index.js': 'Y29uc29sZS5sb2coIkhlbGxvIHdvcmxkIik7' },
        resources: {}
      };
      
      jest.spyOn(bundleManager, 'exportBundle').mockResolvedValue(mockBundle);
      
      const result = await bundleAPI.exportBundle('com.example.test-app');
      
      expect(result.success).toBe(true);
      expect(result.bundle).toBeDefined();
      expect(result.bundle.manifest.id).toBe('com.example.test-app');
      expect(bundleManager.exportBundle).toHaveBeenCalledWith('com.example.test-app', 'json');
    });
    
    test('should register an app for bundling', async () => {
      // Mock store
      mockStore.put.mockResolvedValue({
        id: 'com.example.new-app',
        type: 'app',
        name: 'New App',
        version: '1.0.0'
      });
      
      const appInfo = {
        id: 'com.example.new-app',
        name: 'New App',
        version: '1.0.0',
        author: 'Test Author',
        description: 'Test Description',
        entryPoint: 'index.js'
      };
      
      const options = {
        permissions: ['storage'],
        tags: ['utility']
      };
      
      const result = await bundleAPI.registerApp(appInfo, options);
      
      expect(result.success).toBe(true);
      expect(result.appId).toBe('com.example.new-app');
      expect(mockStore.put).toHaveBeenCalledWith(expect.objectContaining({
        id: 'com.example.new-app',
        type: 'app',
        name: 'New App',
        version: '1.0.0',
        permissions: ['storage'],
        tags: ['utility'],
        bundleable: true
      }));
    });
  });
});