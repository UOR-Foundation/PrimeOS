/**
 * PrimeOS Reference Implementation - App Factory Integration Tests
 * 
 * Tests for the App Factory integration components, including:
 * - BundleIntegration
 * - AppAPIIntegration
 * - ShellIntegration
 */

// Import Jest globals
const { describe, it, expect, beforeEach, afterEach } = require('@jest/globals');

// Import the integration components
const { AppFactoryBundleIntegration } = require('../core/app-factory/integration/bundle-integration');
const { AppFactoryAppAPIIntegration } = require('../core/app-factory/integration/app-api-integration');
const { AppFactoryShellIntegration } = require('../core/app-factory/integration/shell-integration');

describe('App Factory Integration Components', () => {
  // BundleIntegration Tests
  describe('AppFactoryBundleIntegration', () => {
    let bundleIntegration;
    let mockBundleManager;
    let mockEventBus;
    
    // Setup test fixtures
    beforeEach(() => {
      // Create mock bundle manager
      mockBundleManager = {
        getBundle: jest.fn(),
        extractBundleFiles: jest.fn(),
        createBundle: jest.fn(),
        installBundle: jest.fn(),
        uninstallBundle: jest.fn(),
        exportBundle: jest.fn()
      };
      
      // Create mock event bus
      mockEventBus = {
        publish: jest.fn(),
        subscribe: jest.fn()
      };
      
      // Initialize bundle integration with mocks
      bundleIntegration = new AppFactoryBundleIntegration(mockBundleManager, {
        eventBus: mockEventBus
      });
      
      // Mock console methods to keep test output clean
      jest.spyOn(console, 'log').mockImplementation(() => {});
      jest.spyOn(console, 'error').mockImplementation(() => {});
    });
    
    // Clean up after tests
    afterEach(() => {
      jest.restoreAllMocks();
    });
    
    describe('Initialization', () => {
      it('should require a bundleManager instance', () => {
        expect(() => new AppFactoryBundleIntegration()).toThrow('requires a bundleManager instance');
      });
      
      it('should initialize with the provided dependencies', () => {
        expect(bundleIntegration.bundleManager).toBe(mockBundleManager);
        expect(bundleIntegration.eventBus).toBe(mockEventBus);
      });
      
      it('should initialize with eventBus as null if not provided', () => {
        const integration = new AppFactoryBundleIntegration(mockBundleManager);
        expect(integration.bundleManager).toBe(mockBundleManager);
        expect(integration.eventBus).toBeNull();
      });
    });
    
    describe('Bundle Import', () => {
      it('should import bundle successfully', async () => {
        // Setup mocks
        const bundleId = 'test-bundle';
        const mockBundle = {
          name: 'Test Bundle',
          description: 'A test bundle',
          version: '1.0.0',
          manifest: { key: 'value' }
        };
        
        const mockFiles = [
          { path: 'index.js', content: 'console.log("Hello");' },
          { path: 'style.css', content: 'body { color: red; }' }
        ];
        
        mockBundleManager.getBundle.mockResolvedValue(mockBundle);
        mockBundleManager.extractBundleFiles.mockResolvedValue(mockFiles);
        
        // Test import
        const result = await bundleIntegration.importBundle(bundleId);
        
        // Verify manager was called
        expect(mockBundleManager.getBundle).toHaveBeenCalledWith(bundleId);
        expect(mockBundleManager.extractBundleFiles).toHaveBeenCalledWith(bundleId);
        
        // Verify result structure
        expect(result).toHaveProperty('bundleId', bundleId);
        expect(result).toHaveProperty('metadata.name', mockBundle.name);
        expect(result).toHaveProperty('metadata.description', mockBundle.description);
        expect(result).toHaveProperty('metadata.version', mockBundle.version);
        expect(result).toHaveProperty('metadata.manifest', mockBundle.manifest);
        expect(result).toHaveProperty('files');
        expect(result.files).toHaveLength(2);
        
        // Verify event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith(
          'app-factory:bundle-imported',
          expect.objectContaining({ bundleId, metadata: expect.any(Object) })
        );
      });
      
      it('should require a bundle ID', async () => {
        await expect(bundleIntegration.importBundle()).rejects.toThrow('Bundle ID is required');
      });
      
      it('should handle bundle not found error', async () => {
        // Setup mocks
        mockBundleManager.getBundle.mockResolvedValue(null);
        
        // Test import with non-existent bundle
        await expect(bundleIntegration.importBundle('nonexistent')).rejects.toThrow('not found');
        
        // Verify no event was published
        expect(mockEventBus.publish).not.toHaveBeenCalledWith('app-factory:bundle-imported', expect.any(Object));
      });
      
      it('should handle import error and publish event', async () => {
        // Setup mocks for error
        mockBundleManager.getBundle.mockRejectedValue(new Error('Database error'));
        
        // Test import with error
        await expect(bundleIntegration.importBundle('error-bundle')).rejects.toThrow('Database error');
        
        // Verify failure event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith(
          'app-factory:bundle-import-failed',
          expect.objectContaining({ bundleId: 'error-bundle', error: expect.any(String) })
        );
      });
    });
    
    describe('Bundle Creation', () => {
      it('should create bundle successfully', async () => {
        // Setup test data
        const project = {
          id: 'test-project',
          name: 'Test Project',
          description: 'A test project',
          version: '1.0.0',
          specification: {
            architecture: {
              bases: [0, 1, 2]
            },
            manifestStructure: {
              meta: { requiredFields: ['name'] }
            },
            appInterfaces: ['ui', 'storage'],
            coherence: { score: 0.95 }
          }
        };
        
        const files = [
          { path: 'index.js', content: 'console.log("Hello");' },
          { path: 'style.css', content: 'body { color: red; }' }
        ];
        
        const expectedBundleId = 'test-bundle';
        mockBundleManager.createBundle.mockResolvedValue(expectedBundleId);
        
        // Generate manifest spy
        const generateManifestSpy = jest.spyOn(bundleIntegration, '_generateBundleManifest');
        
        // Test bundle creation
        const result = await bundleIntegration.createAppBundle(project, files);
        
        // Verify manifest generation
        expect(generateManifestSpy).toHaveBeenCalledWith(project);
        
        // Verify bundle manager was called
        expect(mockBundleManager.createBundle).toHaveBeenCalledWith(
          expect.objectContaining({
            name: project.name,
            description: project.description,
            type: 'app',
            files: files,
            manifest: expect.any(Object)
          })
        );
        
        // Verify result
        expect(result).toBe(expectedBundleId);
        
        // Verify event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith(
          'app-factory:bundle-created',
          expect.objectContaining({
            bundleId: expectedBundleId,
            projectId: project.id
          })
        );
      });
      
      it('should require project data', async () => {
        await expect(bundleIntegration.createAppBundle()).rejects.toThrow('Project data is required');
      });
      
      it('should require files array', async () => {
        const project = { id: 'test-project', name: 'Test Project' };
        
        await expect(bundleIntegration.createAppBundle(project)).rejects.toThrow('Files array is required');
        await expect(bundleIntegration.createAppBundle(project, 'invalid')).rejects.toThrow('Files array is required');
      });
      
      it('should handle bundle creation error', async () => {
        // Setup test data
        const project = {
          id: 'test-project',
          name: 'Test Project',
          description: 'A test project'
        };
        
        const files = [
          { path: 'index.js', content: 'console.log("Hello");' }
        ];
        
        // Setup mock for error
        mockBundleManager.createBundle.mockRejectedValue(new Error('Creation failed'));
        
        // Test bundle creation with error
        await expect(bundleIntegration.createAppBundle(project, files)).rejects.toThrow('Creation failed');
        
        // Verify failure event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith(
          'app-factory:bundle-creation-failed',
          expect.objectContaining({
            projectId: project.id,
            error: expect.any(String)
          })
        );
      });
      
      it('should generate correct bundle manifest', () => {
        // Setup test data
        const project = {
          id: 'test-project',
          name: 'Test Project',
          description: 'A test project',
          version: '1.0.0',
          specification: {
            architecture: {
              bases: [0, 1, 2]
            },
            manifestStructure: {
              meta: { requiredFields: ['name'] }
            },
            appInterfaces: ['ui', 'storage'],
            coherence: { score: 0.95 }
          }
        };
        
        // Generate manifest
        const manifest = bundleIntegration._generateBundleManifest(project);
        
        // Verify manifest structure
        expect(manifest).toHaveProperty('name', project.name);
        expect(manifest).toHaveProperty('description', project.description);
        expect(manifest).toHaveProperty('version', project.version);
        expect(manifest).toHaveProperty('type', 'primeOS-app');
        expect(manifest).toHaveProperty('createdBy', 'AppFactory');
        expect(manifest).toHaveProperty('createdAt');
        
        // Verify app factory metadata
        expect(manifest).toHaveProperty('appFactory.projectId', project.id);
        expect(manifest).toHaveProperty('appFactory.manifestStructure.meta.requiredFields');
        
        // Verify bases from specification
        expect(manifest).toHaveProperty('bases', project.specification.architecture.bases);
        
        // Verify app interfaces from specification
        expect(manifest).toHaveProperty('interfaces', project.specification.appInterfaces);
        
        // Verify coherence from specification
        expect(manifest).toHaveProperty('coherence', project.specification.coherence);
        
        // Verify default fields
        expect(manifest).toHaveProperty('main', 'index.js');
        expect(manifest).toHaveProperty('permissions');
        expect(Array.isArray(manifest.permissions)).toBe(true);
      });
      
      it('should handle missing specification in project', () => {
        // Setup minimal project data
        const project = {
          id: 'minimal-project',
          name: 'Minimal Project',
          description: 'A minimal project'
        };
        
        // Generate manifest
        const manifest = bundleIntegration._generateBundleManifest(project);
        
        // Verify essential fields are present
        expect(manifest).toHaveProperty('name', project.name);
        expect(manifest).toHaveProperty('description', project.description);
        expect(manifest).toHaveProperty('version', '1.0.0');  // Default version
        expect(manifest).toHaveProperty('main', 'index.js');
      });
    });
    
    describe('Bundle Installation', () => {
      it('should install bundle successfully', async () => {
        // Setup test data
        const bundleId = 'test-bundle';
        const installResult = {
          success: true,
          appId: 'test-app'
        };
        
        mockBundleManager.installBundle.mockResolvedValue(installResult);
        
        // Test installation
        const result = await bundleIntegration.installBundle(bundleId);
        
        // Verify bundle manager was called
        expect(mockBundleManager.installBundle).toHaveBeenCalledWith(bundleId);
        
        // Verify result
        expect(result).toEqual(installResult);
        
        // Verify event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith(
          'app-factory:bundle-installed',
          expect.objectContaining({
            bundleId,
            appId: installResult.appId
          })
        );
      });
      
      it('should require a bundle ID', async () => {
        await expect(bundleIntegration.installBundle()).rejects.toThrow('Bundle ID is required');
      });
      
      it('should handle installation error', async () => {
        // Setup test data
        const bundleId = 'test-bundle';
        
        // Setup mock for error
        mockBundleManager.installBundle.mockRejectedValue(new Error('Installation failed'));
        
        // Test installation with error
        await expect(bundleIntegration.installBundle(bundleId)).rejects.toThrow('Installation failed');
        
        // Verify failure event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith(
          'app-factory:bundle-installation-failed',
          expect.objectContaining({
            bundleId,
            error: expect.any(String)
          })
        );
      });
    });
    
    describe('Bundle Uninstallation', () => {
      it('should uninstall bundle successfully', async () => {
        // Setup test data
        const bundleId = 'test-bundle';
        
        mockBundleManager.uninstallBundle.mockResolvedValue(true);
        
        // Test uninstallation
        const result = await bundleIntegration.uninstallBundle(bundleId);
        
        // Verify bundle manager was called
        expect(mockBundleManager.uninstallBundle).toHaveBeenCalledWith(bundleId);
        
        // Verify result
        expect(result).toBe(true);
        
        // Verify event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith(
          'app-factory:bundle-uninstalled',
          expect.objectContaining({ bundleId })
        );
      });
      
      it('should require a bundle ID', async () => {
        await expect(bundleIntegration.uninstallBundle()).rejects.toThrow('Bundle ID is required');
      });
      
      it('should handle uninstallation error', async () => {
        // Setup test data
        const bundleId = 'test-bundle';
        
        // Setup mock for error
        mockBundleManager.uninstallBundle.mockRejectedValue(new Error('Uninstallation failed'));
        
        // Test uninstallation with error
        await expect(bundleIntegration.uninstallBundle(bundleId)).rejects.toThrow('Uninstallation failed');
        
        // Verify failure event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith(
          'app-factory:bundle-uninstallation-failed',
          expect.objectContaining({
            bundleId,
            error: expect.any(String)
          })
        );
      });
    });
    
    describe('Bundle Export', () => {
      it('should export bundle successfully in default format', async () => {
        // Setup test data
        const bundleId = 'test-bundle';
        const exportResult = {
          manifest: { name: 'Test Bundle' },
          code: { 'index.js': 'Y29uc29sZS5sb2coInRlc3QiKQ==' },
          resources: {}
        };
        
        mockBundleManager.exportBundle.mockResolvedValue(exportResult);
        
        // Test export
        const result = await bundleIntegration.exportBundle(bundleId);
        
        // Verify bundle manager was called with default format
        expect(mockBundleManager.exportBundle).toHaveBeenCalledWith(bundleId, 'json');
        
        // Verify result
        expect(result).toEqual(exportResult);
        
        // Verify event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith(
          'app-factory:bundle-exported',
          expect.objectContaining({
            bundleId,
            format: 'json'
          })
        );
      });
      
      it('should export bundle in binary format', async () => {
        // Setup test data
        const bundleId = 'test-bundle';
        const format = 'binary';
        const exportResult = new Uint8Array([1, 2, 3, 4]);
        
        mockBundleManager.exportBundle.mockResolvedValue(exportResult);
        
        // Test export with binary format
        const result = await bundleIntegration.exportBundle(bundleId, format);
        
        // Verify bundle manager was called with binary format
        expect(mockBundleManager.exportBundle).toHaveBeenCalledWith(bundleId, format);
        
        // Verify result
        expect(result).toEqual(exportResult);
        
        // Verify event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith(
          'app-factory:bundle-exported',
          expect.objectContaining({
            bundleId,
            format
          })
        );
      });
      
      it('should require a bundle ID', async () => {
        await expect(bundleIntegration.exportBundle()).rejects.toThrow('Bundle ID is required');
      });
      
      it('should handle export error', async () => {
        // Setup test data
        const bundleId = 'test-bundle';
        
        // Setup mock for error
        mockBundleManager.exportBundle.mockRejectedValue(new Error('Export failed'));
        
        // Test export with error
        await expect(bundleIntegration.exportBundle(bundleId)).rejects.toThrow('Export failed');
        
        // Verify failure event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith(
          'app-factory:bundle-export-failed',
          expect.objectContaining({
            bundleId,
            error: expect.any(String)
          })
        );
      });
    });
  });
  
  // AppAPIIntegration Tests
  describe('AppFactoryAppAPIIntegration', () => {
    let appAPIIntegration;
    let mockAppAPI;
    let mockEventBus;
    
    // Setup test fixtures
    beforeEach(() => {
      // Create mock AppAPI
      mockAppAPI = {
        onFocus: jest.fn().mockImplementation(callback => {
          mockAppAPI._focusCallback = callback;
          return () => {}; // Unsubscribe function
        }),
        onBlur: jest.fn().mockImplementation(callback => {
          mockAppAPI._blurCallback = callback;
          return () => {};
        }),
        onResize: jest.fn().mockImplementation(callback => {
          mockAppAPI._resizeCallback = callback;
          return () => {};
        }),
        onSuspend: jest.fn().mockImplementation(callback => {
          mockAppAPI._suspendCallback = callback;
          return () => {};
        }),
        onResume: jest.fn().mockImplementation(callback => {
          mockAppAPI._resumeCallback = callback;
          return () => {};
        }),
        onBeforeClose: jest.fn().mockImplementation(callback => {
          mockAppAPI._beforeCloseCallback = callback;
          return () => {};
        }),
        onClose: jest.fn().mockImplementation(callback => {
          mockAppAPI._closeCallback = callback;
          return () => {};
        }),
        getCurrentUser: jest.fn(),
        showDialog: jest.fn(),
        showNotification: jest.fn(),
        savePreferences: jest.fn(),
        loadPreferences: jest.fn()
      };
      
      // Create mock event bus
      mockEventBus = {
        publish: jest.fn(),
        subscribe: jest.fn().mockImplementation((event, callback) => {
          // Store the callback for testing
          if (!mockEventBus._subscriptions) {
            mockEventBus._subscriptions = {};
          }
          mockEventBus._subscriptions[event] = callback;
          
          // Return unsubscribe function
          return () => {
            delete mockEventBus._subscriptions[event];
          };
        })
      };
      
      // Initialize AppAPI integration with mocks
      appAPIIntegration = new AppFactoryAppAPIIntegration(mockAppAPI, {
        eventBus: mockEventBus
      });
      
      // Mock console methods to keep test output clean
      jest.spyOn(console, 'log').mockImplementation(() => {});
      jest.spyOn(console, 'error').mockImplementation(() => {});
    });
    
    // Clean up after tests
    afterEach(() => {
      jest.restoreAllMocks();
    });
    
    describe('Initialization', () => {
      it('should require an appAPI instance', () => {
        expect(() => new AppFactoryAppAPIIntegration()).toThrow('requires an appAPI instance');
      });
      
      it('should initialize with the provided dependencies', () => {
        expect(appAPIIntegration.appAPI).toBe(mockAppAPI);
        expect(appAPIIntegration.eventBus).toBe(mockEventBus);
      });
      
      it('should initialize with eventBus as null if not provided', () => {
        const integration = new AppFactoryAppAPIIntegration(mockAppAPI);
        expect(integration.appAPI).toBe(mockAppAPI);
        expect(integration.eventBus).toBeNull();
      });
      
      it('should register lifecycle hooks on initialization', () => {
        // Verify all lifecycle hooks were registered
        expect(mockAppAPI.onFocus).toHaveBeenCalled();
        expect(mockAppAPI.onBlur).toHaveBeenCalled();
        expect(mockAppAPI.onResize).toHaveBeenCalled();
        expect(mockAppAPI.onSuspend).toHaveBeenCalled();
        expect(mockAppAPI.onResume).toHaveBeenCalled();
        expect(mockAppAPI.onBeforeClose).toHaveBeenCalled();
        expect(mockAppAPI.onClose).toHaveBeenCalled();
      });
    });
    
    describe('Lifecycle Event Handling', () => {
      it('should handle focus event', () => {
        // Trigger focus callback
        mockAppAPI._focusCallback();
        
        // Verify event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith('app-factory:focused');
      });
      
      it('should handle blur event', () => {
        // Trigger blur callback
        mockAppAPI._blurCallback();
        
        // Verify event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith('app-factory:blurred');
      });
      
      it('should handle resize event', () => {
        // Test data
        const dimensions = { width: 800, height: 600 };
        
        // Trigger resize callback
        mockAppAPI._resizeCallback(dimensions);
        
        // Verify event was published with dimensions
        expect(mockEventBus.publish).toHaveBeenCalledWith('app-factory:resized', dimensions);
      });
      
      it('should handle suspend event', () => {
        // Spy on _savePendingWork
        const saveSpy = jest.spyOn(appAPIIntegration, '_savePendingWork').mockResolvedValue(true);
        
        // Trigger suspend callback
        mockAppAPI._suspendCallback();
        
        // Verify event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith('app-factory:suspended');
        
        // Verify save was called
        expect(saveSpy).toHaveBeenCalled();
      });
      
      it('should handle resume event', () => {
        // Spy on _restoreState
        const restoreSpy = jest.spyOn(appAPIIntegration, '_restoreState').mockResolvedValue(true);
        
        // Trigger resume callback
        mockAppAPI._resumeCallback();
        
        // Verify event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith('app-factory:resumed');
        
        // Verify restore was called
        expect(restoreSpy).toHaveBeenCalled();
      });
      
      it('should handle close event', () => {
        // Trigger close callback
        mockAppAPI._closeCallback();
        
        // Verify event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith('app-factory:closed');
      });
      
      it('should handle beforeClose event with no unsaved work', async () => {
        // Spy on _checkUnsavedWork
        const checkSpy = jest.spyOn(appAPIIntegration, '_checkUnsavedWork').mockResolvedValue(false);
        
        // Trigger beforeClose callback
        const result = await mockAppAPI._beforeCloseCallback();
        
        // Verify result is true (allow close)
        expect(result).toBe(true);
        
        // Verify check was called
        expect(checkSpy).toHaveBeenCalled();
        
        // Verify no dialog was shown
        expect(mockAppAPI.showDialog).not.toHaveBeenCalled();
      });
      
      it('should handle beforeClose event with unsaved work and save', async () => {
        // Spy on _checkUnsavedWork and _savePendingWork
        const checkSpy = jest.spyOn(appAPIIntegration, '_checkUnsavedWork').mockResolvedValue(true);
        const saveSpy = jest.spyOn(appAPIIntegration, '_savePendingWork').mockResolvedValue(true);
        
        // Setup dialog result
        mockAppAPI.showDialog.mockResolvedValue('Save');
        
        // Trigger beforeClose callback
        const result = await mockAppAPI._beforeCloseCallback();
        
        // Verify dialog was shown
        expect(mockAppAPI.showDialog).toHaveBeenCalled();
        
        // Verify save was called
        expect(saveSpy).toHaveBeenCalled();
        
        // Verify result is true (allow close)
        expect(result).toBe(true);
      });
      
      it('should handle beforeClose event with unsaved work and discard', async () => {
        // Spy on _checkUnsavedWork
        const checkSpy = jest.spyOn(appAPIIntegration, '_checkUnsavedWork').mockResolvedValue(true);
        const saveSpy = jest.spyOn(appAPIIntegration, '_savePendingWork');
        
        // Setup dialog result
        mockAppAPI.showDialog.mockResolvedValue('Discard');
        
        // Trigger beforeClose callback
        const result = await mockAppAPI._beforeCloseCallback();
        
        // Verify dialog was shown
        expect(mockAppAPI.showDialog).toHaveBeenCalled();
        
        // Verify save was not called
        expect(saveSpy).not.toHaveBeenCalled();
        
        // Verify result is true (allow close)
        expect(result).toBe(true);
      });
      
      it('should handle beforeClose event with unsaved work and cancel', async () => {
        // Spy on _checkUnsavedWork
        const checkSpy = jest.spyOn(appAPIIntegration, '_checkUnsavedWork').mockResolvedValue(true);
        
        // Setup dialog result
        mockAppAPI.showDialog.mockResolvedValue('Cancel');
        
        // Trigger beforeClose callback
        const result = await mockAppAPI._beforeCloseCallback();
        
        // Verify dialog was shown
        expect(mockAppAPI.showDialog).toHaveBeenCalled();
        
        // Verify result is false (prevent close)
        expect(result).toBe(false);
      });
    });
    
    describe('AppAPI Methods', () => {
      it('should get current user', async () => {
        // Setup mock data
        const mockUser = { id: 'user1', name: 'Test User' };
        mockAppAPI.getCurrentUser.mockResolvedValue(mockUser);
        
        // Call method
        const result = await appAPIIntegration.getCurrentUser();
        
        // Verify result
        expect(result).toEqual(mockUser);
        expect(mockAppAPI.getCurrentUser).toHaveBeenCalled();
      });
      
      it('should handle error in getCurrentUser', async () => {
        // Setup mock error
        mockAppAPI.getCurrentUser.mockRejectedValue(new Error('API error'));
        
        // Call method
        const result = await appAPIIntegration.getCurrentUser();
        
        // Verify result is null
        expect(result).toBeNull();
      });
      
      it('should show dialog', async () => {
        // Setup mock data
        const dialogOptions = {
          title: 'Test Dialog',
          message: 'Test message',
          buttons: ['OK', 'Cancel']
        };
        
        const dialogResult = 'OK';
        mockAppAPI.showDialog.mockResolvedValue(dialogResult);
        
        // Call method
        const result = await appAPIIntegration.showDialog(dialogOptions);
        
        // Verify result
        expect(result).toEqual(dialogResult);
        expect(mockAppAPI.showDialog).toHaveBeenCalledWith(dialogOptions);
      });
      
      it('should handle error in showDialog', async () => {
        // Setup mock error
        mockAppAPI.showDialog.mockRejectedValue(new Error('Dialog error'));
        
        // Call method and verify it throws
        await expect(appAPIIntegration.showDialog({})).rejects.toThrow('Dialog error');
      });
      
      it('should show notification', async () => {
        // Setup mock data
        const notificationOptions = {
          title: 'Test Notification',
          message: 'Test message'
        };
        
        const notificationId = 'notification1';
        mockAppAPI.showNotification.mockResolvedValue(notificationId);
        
        // Call method
        const result = await appAPIIntegration.showNotification(notificationOptions);
        
        // Verify result
        expect(result).toEqual(notificationId);
        expect(mockAppAPI.showNotification).toHaveBeenCalledWith(notificationOptions);
      });
      
      it('should handle error in showNotification', async () => {
        // Setup mock error
        mockAppAPI.showNotification.mockRejectedValue(new Error('Notification error'));
        
        // Call method and verify it throws
        await expect(appAPIIntegration.showNotification({})).rejects.toThrow('Notification error');
      });
      
      it('should save preferences', async () => {
        // Setup mock data
        const preferences = { theme: 'dark', fontSize: 14 };
        mockAppAPI.savePreferences.mockResolvedValue(true);
        
        // Call method
        const result = await appAPIIntegration.savePreferences(preferences);
        
        // Verify result
        expect(result).toBe(true);
        expect(mockAppAPI.savePreferences).toHaveBeenCalledWith(preferences);
      });
      
      it('should handle error in savePreferences', async () => {
        // Setup mock error
        mockAppAPI.savePreferences.mockRejectedValue(new Error('Save error'));
        
        // Call method
        const result = await appAPIIntegration.savePreferences({});
        
        // Verify result is false
        expect(result).toBe(false);
      });
      
      it('should load preferences', async () => {
        // Setup mock data
        const preferences = { theme: 'dark', fontSize: 14 };
        mockAppAPI.loadPreferences.mockResolvedValue(preferences);
        
        // Call method
        const result = await appAPIIntegration.loadPreferences();
        
        // Verify result
        expect(result).toEqual(preferences);
        expect(mockAppAPI.loadPreferences).toHaveBeenCalled();
      });
      
      it('should handle error in loadPreferences', async () => {
        // Setup mock error
        mockAppAPI.loadPreferences.mockRejectedValue(new Error('Load error'));
        
        // Call method
        const result = await appAPIIntegration.loadPreferences();
        
        // Verify result is empty object
        expect(result).toEqual({});
      });
    });
    
    describe('Internal Methods', () => {
      it('should check for unsaved work', async () => {
        // Call method with no event bus
        appAPIIntegration.eventBus = null;
        let result = await appAPIIntegration._checkUnsavedWork();
        
        // Verify default result
        expect(result).toBe(false);
        
        // Restore event bus
        appAPIIntegration.eventBus = mockEventBus;
        
        // Setup subscription to respond
        mockEventBus.subscribe.mockImplementation((event, callback) => {
          if (event === 'app-factory:unsaved-work-result') {
            mockEventBus._unsavedCallback = callback;
          }
          return () => {};
        });
        
        // Call method again
        const checkPromise = appAPIIntegration._checkUnsavedWork();
        
        // Get the event ID from the published event
        const publishCall = mockEventBus.publish.mock.calls.find(
          call => call[0] === 'app-factory:check-unsaved-work'
        );
        const eventId = publishCall[1].eventId;
        
        // Simulate response
        mockEventBus._unsavedCallback({ eventId, hasUnsavedWork: true });
        
        // Verify result
        result = await checkPromise;
        expect(result).toBe(true);
      });
      
      it('should save pending work', async () => {
        // Call method with no event bus
        appAPIIntegration.eventBus = null;
        let result = await appAPIIntegration._savePendingWork();
        
        // Verify default result
        expect(result).toBe(true);
        
        // Restore event bus
        appAPIIntegration.eventBus = mockEventBus;
        
        // Setup subscription to respond
        mockEventBus.subscribe.mockImplementation((event, callback) => {
          if (event === 'app-factory:save-work-result') {
            mockEventBus._saveCallback = callback;
          }
          return () => {};
        });
        
        // Call method again
        const savePromise = appAPIIntegration._savePendingWork();
        
        // Get the event ID from the published event
        const publishCall = mockEventBus.publish.mock.calls.find(
          call => call[0] === 'app-factory:save-pending-work'
        );
        const eventId = publishCall[1].eventId;
        
        // Simulate response
        mockEventBus._saveCallback({ eventId, success: true });
        
        // Verify result
        result = await savePromise;
        expect(result).toBe(true);
      });
      
      it('should restore application state', async () => {
        // Call method
        const result = await appAPIIntegration._restoreState();
        
        // Verify result and event
        expect(result).toBe(true);
        expect(mockEventBus.publish).toHaveBeenCalledWith('app-factory:restore-state');
      });
    });
  });
  
  // ShellIntegration Tests
  describe('AppFactoryShellIntegration', () => {
    let shellIntegration;
    let mockShell;
    let mockEventBus;
    
    // Setup test fixtures
    beforeEach(() => {
      // Create mock shell
      mockShell = {
        registerApp: jest.fn().mockResolvedValue(true),
        launchApp: jest.fn().mockResolvedValue('window1'),
        createWindow: jest.fn().mockResolvedValue('window2')
      };
      
      // Create mock event bus
      mockEventBus = {
        publish: jest.fn(),
        subscribe: jest.fn().mockImplementation((event, callback) => {
          // Store the callback for testing
          if (!mockEventBus._subscriptions) {
            mockEventBus._subscriptions = {};
          }
          mockEventBus._subscriptions[event] = callback;
          
          // Return unsubscribe function
          return () => {
            delete mockEventBus._subscriptions[event];
          };
        })
      };
      
      // Initialize Shell integration with mocks
      shellIntegration = new AppFactoryShellIntegration(mockShell, {
        eventBus: mockEventBus
      });
      
      // Mock console methods to keep test output clean
      jest.spyOn(console, 'log').mockImplementation(() => {});
      jest.spyOn(console, 'error').mockImplementation(() => {});
    });
    
    // Clean up after tests
    afterEach(() => {
      jest.restoreAllMocks();
    });
    
    describe('Initialization', () => {
      it('should require a shell instance', () => {
        expect(() => new AppFactoryShellIntegration()).toThrow('requires a shell instance');
      });
      
      it('should initialize with the provided dependencies', () => {
        expect(shellIntegration.shell).toBe(mockShell);
        expect(shellIntegration.eventBus).toBe(mockEventBus);
        expect(shellIntegration.appFactoryId).toBe('app-factory');
        expect(shellIntegration.appFactoryRegistered).toBe(false);
      });
      
      it('should initialize with eventBus as null if not provided', () => {
        const integration = new AppFactoryShellIntegration(mockShell);
        expect(integration.shell).toBe(mockShell);
        expect(integration.eventBus).toBeNull();
      });
      
      it('should subscribe to shell events', () => {
        expect(mockEventBus.subscribe).toHaveBeenCalledWith('shell:app-launched', expect.any(Function));
        expect(mockEventBus.subscribe).toHaveBeenCalledWith('shell:app-closed', expect.any(Function));
      });
    });
    
    describe('App Registration', () => {
      it('should register App Factory with default info', async () => {
        // Call method
        const result = await shellIntegration.registerAppFactory();
        
        // Verify shell was called with default info
        expect(mockShell.registerApp).toHaveBeenCalledWith(expect.objectContaining({
          id: 'app-factory',
          name: 'App Factory',
          description: expect.any(String),
          icon: expect.any(String),
          isSystem: true
        }));
        
        // Verify result and state
        expect(result).toBe(true);
        expect(shellIntegration.appFactoryRegistered).toBe(true);
        
        // Verify event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith(
          'app-factory:registered',
          expect.objectContaining({ appId: 'app-factory' })
        );
      });
      
      it('should register App Factory with custom info', async () => {
        // Custom info
        const customInfo = {
          name: 'Custom App Factory',
          description: 'Custom description',
          icon: '🔨'
        };
        
        // Call method
        const result = await shellIntegration.registerAppFactory(customInfo);
        
        // Verify shell was called with merged info
        expect(mockShell.registerApp).toHaveBeenCalledWith(expect.objectContaining({
          id: 'app-factory',
          name: customInfo.name,
          description: customInfo.description,
          icon: customInfo.icon,
          isSystem: true
        }));
        
        // Verify result and state
        expect(result).toBe(true);
        expect(shellIntegration.appFactoryRegistered).toBe(true);
      });
      
      it('should handle registration error', async () => {
        // Setup mock error
        mockShell.registerApp.mockRejectedValue(new Error('Registration failed'));
        
        // Call method
        const result = await shellIntegration.registerAppFactory();
        
        // Verify result
        expect(result).toBe(false);
        expect(shellIntegration.appFactoryRegistered).toBe(false);
        
        // Verify failure event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith(
          'app-factory:registration-failed',
          expect.objectContaining({ error: expect.any(String) })
        );
      });
    });
    
    describe('App Launch', () => {
      it('should launch App Factory when already registered', async () => {
        // Set registered state
        shellIntegration.appFactoryRegistered = true;
        
        // Launch options
        const options = { param1: 'value1' };
        
        // Call method
        const result = await shellIntegration.launchAppFactory(options);
        
        // Verify shell was called
        expect(mockShell.launchApp).toHaveBeenCalledWith('app-factory', options);
        
        // Verify result
        expect(result).toHaveProperty('windowId', 'window1');
      });
      
      it('should register App Factory before launch if not registered', async () => {
        // Spy on registerAppFactory
        const registerSpy = jest.spyOn(shellIntegration, 'registerAppFactory')
          .mockResolvedValue(true);
        
        // Call method
        const result = await shellIntegration.launchAppFactory();
        
        // Verify register was called
        expect(registerSpy).toHaveBeenCalled();
        
        // Verify shell was called
        expect(mockShell.launchApp).toHaveBeenCalledWith('app-factory', {});
        
        // Verify result
        expect(result).toHaveProperty('windowId', 'window1');
      });
      
      it('should handle launch error', async () => {
        // Setup mock error
        mockShell.launchApp.mockRejectedValue(new Error('Launch failed'));
        
        // Set registered state
        shellIntegration.appFactoryRegistered = true;
        
        // Call method and verify it throws
        await expect(shellIntegration.launchAppFactory()).rejects.toThrow('Launch failed');
      });
    });
    
    describe('Window Management', () => {
      it('should create project window', async () => {
        // Setup test data
        const projectId = 'test-project';
        const projectName = 'Test Project';
        
        // Call method
        const result = await shellIntegration.createProjectWindow(projectId, projectName);
        
        // Verify shell was called with correct params
        expect(mockShell.createWindow).toHaveBeenCalledWith(expect.objectContaining({
          title: `App Factory - ${projectName}`,
          app: 'app-factory',
          params: {
            projectId,
            mode: 'project'
          }
        }));
        
        // Verify result
        expect(result).toHaveProperty('windowId', 'window2');
      });
      
      it('should require project ID for project window', async () => {
        await expect(shellIntegration.createProjectWindow()).rejects.toThrow('Project ID is required');
      });
      
      it('should use default title when project name not provided', async () => {
        // Setup test data
        const projectId = 'test-project';
        
        // Call method
        await shellIntegration.createProjectWindow(projectId);
        
        // Verify shell was called with default title
        expect(mockShell.createWindow).toHaveBeenCalledWith(expect.objectContaining({
          title: 'App Factory - Project'
        }));
      });
      
      it('should create code preview window', async () => {
        // Setup test data
        const file = {
          path: 'src/index.js',
          content: 'console.log("Hello");'
        };
        const projectId = 'test-project';
        
        // Call method
        const result = await shellIntegration.createCodePreviewWindow(file, projectId);
        
        // Verify shell was called with correct params
        expect(mockShell.createWindow).toHaveBeenCalledWith(expect.objectContaining({
          title: `Preview - ${file.path}`,
          app: 'app-factory',
          params: {
            projectId,
            mode: 'preview',
            filePath: file.path
          }
        }));
        
        // Verify result
        expect(result).toHaveProperty('windowId', 'window2');
      });
      
      it('should require file for preview window', async () => {
        await expect(shellIntegration.createCodePreviewWindow()).rejects.toThrow('File is required');
      });
      
      it('should handle window creation error', async () => {
        // Setup mock error
        mockShell.createWindow.mockRejectedValue(new Error('Window creation failed'));
        
        // Call method and verify it throws
        await expect(shellIntegration.createProjectWindow('test-project')).rejects.toThrow('Window creation failed');
      });
    });
    
    describe('App List Refresh', () => {
      it('should publish refresh event', async () => {
        // Call method
        const result = await shellIntegration.refreshAppList();
        
        // Verify event was published
        expect(mockEventBus.publish).toHaveBeenCalledWith('apps:refresh', { source: 'appFactory' });
        
        // Verify result
        expect(result).toBe(true);
      });
      
      it('should handle refresh error', async () => {
        // Setup mock error by making publish throw
        mockEventBus.publish.mockImplementation(() => {
          throw new Error('Publish error');
        });
        
        // Call method
        const result = await shellIntegration.refreshAppList();
        
        // Verify result
        expect(result).toBe(false);
      });
    });
    
    describe('Event Handling', () => {
      it('should handle app launch event for App Factory', () => {
        // Create event data
        const eventData = {
          appId: 'app-factory',
          windowId: 'window1'
        };
        
        // Call handler directly
        shellIntegration._handleAppLaunch(eventData);
        
        // No explicit assertions needed as we're just checking it doesn't throw
        // and the console.log is mocked
      });
      
      it('should handle app launch event for other apps', () => {
        // Create event data for different app
        const eventData = {
          appId: 'other-app',
          windowId: 'window1'
        };
        
        // Call handler directly
        shellIntegration._handleAppLaunch(eventData);
        
        // No assertions needed
      });
      
      it('should handle app close event for App Factory', () => {
        // Create event data
        const eventData = {
          appId: 'app-factory',
          windowId: 'window1'
        };
        
        // Call handler directly
        shellIntegration._handleAppClose(eventData);
        
        // No assertions needed
      });
    });
  });
});