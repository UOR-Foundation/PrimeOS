/**
 * PrimeOS Reference Implementation - File Explorer Component Tests
 * 
 * Tests for the File Explorer application, including file system operations,
 * navigation, selection, and inter-app communication.
 */

// Import test utilities
const { describe, it, expect, beforeEach, afterEach } = require('@jest/globals');

// Mock dependencies
const mockEventBus = {
  publish: jest.fn(),
  subscribe: jest.fn(() => jest.fn()), // Return unsubscribe function
  unsubscribe: jest.fn()
};

const mockStore = {
  get: jest.fn(),
  put: jest.fn(),
  delete: jest.fn(),
  query: jest.fn(),
  saveAll: jest.fn()
};

// Mock AppAPI class
class MockAppAPI {
  constructor(options) {
    this.appId = options.appId;
    this.eventBus = options.eventBus || mockEventBus;
    this.store = options.store || mockStore;
    this.state = { 
      preferences: {},
      isActive: true,
      isSuspended: false
    };
    
    // Create spy methods
    this.showNotification = jest.fn();
    this.loadPreferences = jest.fn().mockResolvedValue(this.state.preferences);
    this.savePreferences = jest.fn().mockImplementation(async (preferences) => {
      this.state.preferences = { ...this.state.preferences, ...preferences };
      return this.state.preferences;
    });
    this.requestAppData = jest.fn();
    this.registerRequestHandler = jest.fn((handler) => {
      return this.eventBus.subscribe(`app:request:${this.appId}`, async (requestData) => {
        try {
          const { requestId, sourceAppId, request } = requestData;
          const response = await handler(request, sourceAppId);
          return response;
        } catch (error) {
          console.error('Error handling app request:', error);
          return null;
        }
      });
    });
  }
}

// Create a minimal DOM environment for testing
// Define HTMLElement constructor for instanceof checks
class HTMLElement {
  constructor() {
    this.className = '';
    this.style = {};
    this.innerHTML = '';
  }
  appendChild = jest.fn();
  addEventListener = jest.fn();
  setAttribute = jest.fn();
  remove = jest.fn();
  querySelector = jest.fn();
  querySelectorAll = jest.fn(() => []);
}

global.HTMLElement = HTMLElement;

// Mock DOM elements
const mockDomElements = {
  'path-input': {
    value: '/',
    addEventListener: jest.fn()
  },
  'back-button': {
    addEventListener: jest.fn()
  },
  'up-button': {
    addEventListener: jest.fn()
  },
  'refresh-button': {
    addEventListener: jest.fn()
  },
  'new-folder': {
    addEventListener: jest.fn()
  },
  'new-file': {
    addEventListener: jest.fn()
  },
  'delete': {
    addEventListener: jest.fn(),
    disabled: false
  },
  'copy': {
    addEventListener: jest.fn(),
    disabled: false
  },
  'cut': {
    addEventListener: jest.fn(),
    disabled: false
  },
  'paste': {
    addEventListener: jest.fn(),
    disabled: false
  },
  'file-list': {
    innerHTML: '',
    addEventListener: jest.fn()
  },
  'status': {
    textContent: ''
  },
  'selection-info': {
    textContent: ''
  }
};

global.document = {
  createElement: jest.fn(() => new HTMLElement()),
  getElementById: jest.fn(id => mockDomElements[id] || null)
};

// Mock window object
global.window = {
  PrimeOS: {
    FileExplorer: null, // Will be replaced with actual implementation
    AppAPI: MockAppAPI
  }
};

// Mock confirm and prompt
global.confirm = jest.fn(() => true);
global.prompt = jest.fn(() => 'test-file.txt');

// Import the FileExplorer class - this is done after we set up the mocks
const FileExplorer = require('../apps/file-explorer/index').default;

describe('File Explorer Component', () => {
  let container;
  let fileExplorer;
  let options;

  beforeEach(() => {
    // Reset mocks
    jest.clearAllMocks();
    
    // Create mock container as HTMLElement instance
    container = new HTMLElement();
    
    // Set up container's querySelector and querySelectorAll
    container.querySelector = jest.fn(selector => {
      if (selector === '#status') return mockDomElements['status'];
      if (selector === '#selection-info') return mockDomElements['selection-info'];
      if (selector === '#file-list') return mockDomElements['file-list'];
      if (selector === '#delete') return mockDomElements['delete'];
      if (selector === '#copy') return mockDomElements['copy'];
      if (selector === '#cut') return mockDomElements['cut'];
      if (selector === '#paste') return mockDomElements['paste'];
      if (selector === '#path-input') return mockDomElements['path-input'];
      return null;
    });
    
    container.querySelectorAll = jest.fn(selector => {
      if (selector === '.quick-access li') return [];
      if (selector === '.file-item') return [];
      return [];
    });
    
    // Create options for FileExplorer
    options = {
      eventBus: mockEventBus,
      store: mockStore,
      windowId: 'test-window-123',
      identity: {}
    };
    
    // Spy on FileExplorer static methods
    jest.spyOn(FileExplorer, 'initialize');
  });

  describe('Initialization', () => {
    it('should create FileExplorer instance with required properties', async () => {
      // Initialize FileExplorer
      fileExplorer = new FileExplorer(container, options);
      
      // Check that instance was created properly
      expect(fileExplorer).toBeDefined();
      expect(fileExplorer.container).toBe(container);
      expect(fileExplorer.options).toBe(options);
      expect(fileExplorer.appId).toBe('file-explorer');
      expect(fileExplorer.currentPath).toBe('/');
      expect(fileExplorer.selectedFiles).toEqual([]);
      expect(fileExplorer.api).toBeDefined();
    });

    it('should initialize file system with default directories', async () => {
      // Initialize FileExplorer
      fileExplorer = new FileExplorer(container, options);
      
      // Check default file system
      expect(fileExplorer.fileSystem['/']).toBeDefined();
      expect(fileExplorer.fileSystem['/'].type).toBe('directory');
      expect(fileExplorer.fileSystem['/'].children).toContain('Documents');
      expect(fileExplorer.fileSystem['/'].children).toContain('Pictures');
      expect(fileExplorer.fileSystem['/'].children).toContain('Music');
      expect(fileExplorer.fileSystem['/'].children).toContain('Videos');
      
      expect(fileExplorer.fileSystem['/Documents']).toBeDefined();
      expect(fileExplorer.fileSystem['/Documents'].type).toBe('directory');
      
      expect(fileExplorer.fileSystem['/Documents/notes.txt']).toBeDefined();
      expect(fileExplorer.fileSystem['/Documents/notes.txt'].type).toBe('file');
    });
    
    it('should render UI properly', async () => {
      // Initialize FileExplorer
      fileExplorer = new FileExplorer(container, options);
      
      // Call renderUI method
      fileExplorer.renderUI();
      
      // Check that container innerHTML was set
      expect(container.innerHTML).toContain('<div class="file-explorer">');
      expect(container.innerHTML).toContain('<button id="new-folder">New Folder</button>');
      expect(container.innerHTML).toContain('<div class="file-list" id="file-list"></div>');
    });
    
    it('should initialize event handlers', async () => {
      // Skip the actual implementation of initEventHandlers
      // since we're just testing that it's called
      fileExplorer = new FileExplorer(container, options);
      fileExplorer.initEventHandlers = jest.fn();
      
      // Call init method which calls initEventHandlers
      fileExplorer.renderUI = jest.fn();
      fileExplorer.loadFileSystem = jest.fn().mockResolvedValue();
      fileExplorer.navigateTo = jest.fn();
      await fileExplorer.init();
      
      // Verify initEventHandlers was called
      expect(fileExplorer.initEventHandlers).toHaveBeenCalled();
    });
    
    it('should register request handler for inter-app communication', async () => {
      // Initialize FileExplorer with mocked methods
      fileExplorer = new FileExplorer(container, options);
      fileExplorer.renderUI = jest.fn();
      fileExplorer.initEventHandlers = jest.fn();
      fileExplorer.loadFileSystem = jest.fn().mockResolvedValue();
      fileExplorer.navigateTo = jest.fn();
      
      // Mock the registerRequestHandler method to check if it's called
      let handlerRegistered = false;
      fileExplorer.api.registerRequestHandler = jest.fn(handler => {
        handlerRegistered = true;
        // Simply return a dummy unsubscribe function
        return () => {};
      });
      
      // Call init method
      await fileExplorer.init();
      
      // Check that request handler was registered
      expect(handlerRegistered).toBe(true);
    });
    
    it('should load saved file system if available', async () => {
      // Mock saved file system
      const savedFileSystem = {
        fileSystem: {
          '/': {
            type: 'directory',
            name: 'Root',
            children: ['CustomFolder'],
            created: Date.now(),
            modified: Date.now()
          },
          '/CustomFolder': {
            type: 'directory',
            name: 'CustomFolder',
            children: ['custom.txt'],
            created: Date.now(),
            modified: Date.now()
          },
          '/CustomFolder/custom.txt': {
            type: 'file',
            name: 'custom.txt',
            extension: 'txt',
            content: 'Custom content',
            size: 14,
            created: Date.now(),
            modified: Date.now()
          }
        },
        lastPath: '/CustomFolder'
      };
      
      // Set up API mock to return saved file system
      fileExplorer = new FileExplorer(container, options);
      fileExplorer.api.loadPreferences = jest.fn().mockResolvedValue(savedFileSystem);
      fileExplorer.navigateTo = jest.fn();
      
      // Call loadFileSystem method
      await fileExplorer.loadFileSystem();
      
      // Check that file system was loaded from storage
      expect(fileExplorer.fileSystem).toEqual(savedFileSystem.fileSystem);
    });
    
    it('should save initial file system if none exists', async () => {
      // Initialize FileExplorer with empty preferences
      fileExplorer = new FileExplorer(container, options);
      fileExplorer.api.loadPreferences = jest.fn().mockResolvedValue({});
      
      // Mock saveFileSystem to avoid actual implementation
      fileExplorer.saveFileSystem = jest.fn();
      
      // Call loadFileSystem method
      await fileExplorer.loadFileSystem();
      
      // Check that saveFileSystem was called to save initial file system
      expect(fileExplorer.saveFileSystem).toHaveBeenCalled();
    });
  });

  describe('Navigation', () => {
    beforeEach(() => {
      // Initialize FileExplorer with default file system
      fileExplorer = new FileExplorer(container, options);
      fileExplorer.updateFileList = jest.fn();
      fileExplorer.clearSelection = jest.fn();
      fileExplorer.updateStatus = jest.fn();
      
      // Mock path input
      mockDomElements['path-input'] = { value: '/' };
    });
    
    it('should navigate to a directory', async () => {
      // Call navigateTo method
      fileExplorer.navigateTo('/Documents');
      
      // Check that current path was updated
      expect(fileExplorer.currentPath).toBe('/Documents');
      expect(fileExplorer.clearSelection).toHaveBeenCalled();
      expect(fileExplorer.updateFileList).toHaveBeenCalled();
      
      // Check that path input was updated
      expect(mockDomElements['path-input'].value).toBe('/Documents');
      
      // Check that status was updated
      expect(fileExplorer.updateStatus).toHaveBeenCalledWith('Navigated to /Documents');
      
      // We don't check api.savePreferences here because it's already mocked as a function,
      // not a Jest spy, so we can't use toHaveBeenCalledWith
    });
    
    it('should show error when navigating to invalid directory', async () => {
      // Directly check behavior without relying on showNotification
      // First record current path
      const initialPath = fileExplorer.currentPath;
      
      // Override showNotification to not actually call the real one
      fileExplorer.api.showNotification = jest.fn();
      
      // Call navigateTo with invalid path
      fileExplorer.navigateTo('/NonExistentFolder');
      
      // Check that notification function was called
      expect(fileExplorer.api.showNotification).toHaveBeenCalled();
      
      // Check that current path wasn't changed
      expect(fileExplorer.currentPath).toBe(initialPath);
    });
    
    it('should navigate up one directory', async () => {
      // Set current path to subfolder
      fileExplorer.currentPath = '/Documents';
      
      // Create a spy for navigateTo
      const originalNavigateTo = fileExplorer.navigateTo;
      let navigatedToPath = null;
      fileExplorer.navigateTo = jest.fn(path => {
        navigatedToPath = path;
        return originalNavigateTo(path);
      });
      
      // Call navigateUp method
      fileExplorer.navigateUp();
      
      // Should navigate to parent directory
      expect(navigatedToPath).toBe('/');
    });
    
    it('should not navigate up from root directory', async () => {
      // Set current path to root
      fileExplorer.currentPath = '/';
      
      // Create a spy for navigateTo
      const originalNavigateTo = fileExplorer.navigateTo;
      let navigateWasCalled = false;
      fileExplorer.navigateTo = jest.fn(path => {
        navigateWasCalled = true;
        return originalNavigateTo(path);
      });
      
      // Call navigateUp method
      fileExplorer.navigateUp();
      
      // Should not call navigateTo
      expect(navigateWasCalled).toBe(false);
    });
    
    it('should refresh current view', async () => {
      // Call refreshView method
      fileExplorer.refreshView();
      
      // Should update file list and status
      expect(fileExplorer.updateFileList).toHaveBeenCalled();
      expect(fileExplorer.updateStatus).toHaveBeenCalledWith('View refreshed');
    });
  });

  describe('File Operations', () => {
    beforeEach(() => {
      // Initialize FileExplorer
      fileExplorer = new FileExplorer(container, options);
      fileExplorer.updateFileList = jest.fn();
      fileExplorer.updateStatus = jest.fn();
      fileExplorer.saveFileSystem = jest.fn();
      fileExplorer.navigateTo = jest.fn();
    });
    
    it('should create a new folder', async () => {
      // Set up current path
      fileExplorer.currentPath = '/';
      
      // Mock prompt to return folder name
      prompt.mockReturnValueOnce('TestFolder');
      
      // Call createNewFolder method
      fileExplorer.createNewFolder();
      
      // Check that folder was created
      expect(fileExplorer.fileSystem['/TestFolder']).toBeDefined();
      expect(fileExplorer.fileSystem['/TestFolder'].type).toBe('directory');
      expect(fileExplorer.fileSystem['/TestFolder'].children).toEqual([]);
      
      // Check that folder was added to parent directory
      expect(fileExplorer.fileSystem['/'].children).toContain('TestFolder');
      
      // Check that UI was updated
      expect(fileExplorer.updateFileList).toHaveBeenCalled();
      expect(fileExplorer.updateStatus).toHaveBeenCalledWith('Created folder: TestFolder');
      
      // Check that file system was saved
      expect(fileExplorer.saveFileSystem).toHaveBeenCalled();
    });
    
    it('should not create folder with invalid name', async () => {
      // Set up current path
      fileExplorer.currentPath = '/';
      
      // Mock prompt to return invalid folder name
      prompt.mockReturnValueOnce('Test/Folder');
      
      // Override showNotification to not actually call the real one
      fileExplorer.api.showNotification = jest.fn();
      
      // Call createNewFolder method
      fileExplorer.createNewFolder();
      
      // Check that notification was called
      expect(fileExplorer.api.showNotification).toHaveBeenCalled();
      
      // Check that folder was not created
      expect(fileExplorer.fileSystem['/Test/Folder']).toBeUndefined();
    });
    
    it('should create a new file', async () => {
      // Set up current path
      fileExplorer.currentPath = '/';
      
      // Mock prompt to return file name
      prompt.mockReturnValueOnce('test.txt');
      
      // Mock setTimeout
      jest.spyOn(global, 'setTimeout').mockImplementation(callback => {
        callback();
        return 123;
      });
      
      // Mock openFile
      fileExplorer.openFile = jest.fn();
      
      // Call createNewFile method
      fileExplorer.createNewFile();
      
      // Check that file was created
      expect(fileExplorer.fileSystem['/test.txt']).toBeDefined();
      expect(fileExplorer.fileSystem['/test.txt'].type).toBe('file');
      expect(fileExplorer.fileSystem['/test.txt'].extension).toBe('txt');
      expect(fileExplorer.fileSystem['/test.txt'].content).toBe('');
      
      // Check that file was added to parent directory
      expect(fileExplorer.fileSystem['/'].children).toContain('test.txt');
      
      // Check that UI was updated
      expect(fileExplorer.updateFileList).toHaveBeenCalled();
      expect(fileExplorer.updateStatus).toHaveBeenCalledWith('Created file: test.txt');
      
      // Check that file system was saved
      expect(fileExplorer.saveFileSystem).toHaveBeenCalled();
      
      // Check that file was opened
      expect(fileExplorer.openFile).toHaveBeenCalledWith('/test.txt');
    });
    
    it('should delete selected files', async () => {
      // Create a fresh FileExplorer instance for this test
      const freshExplorer = new FileExplorer(container, options);
      
      // Set up current path and selected files
      freshExplorer.currentPath = '/';
      freshExplorer.selectedFiles = ['/Documents/notes.txt'];
      
      // Mock functions we'll use
      freshExplorer.updateFileList = jest.fn();
      freshExplorer.updateStatus = jest.fn();
      freshExplorer.saveFileSystem = jest.fn();
      freshExplorer.clearSelection = jest.fn();
      
      // Mock confirm to return true
      confirm.mockReturnValueOnce(true);
      
      // Call deleteSelectedFiles method
      freshExplorer.deleteSelectedFiles();
      
      // Check that file was deleted
      expect(freshExplorer.fileSystem['/Documents/notes.txt']).toBeUndefined();
      
      // Check that file was removed from parent directory
      expect(freshExplorer.fileSystem['/Documents'].children).not.toContain('notes.txt');
      
      // Check that selection was cleared
      expect(freshExplorer.clearSelection).toHaveBeenCalled();
      
      // Check that UI was updated
      expect(freshExplorer.updateFileList).toHaveBeenCalled();
      expect(freshExplorer.updateStatus).toHaveBeenCalled();
      
      // Check that file system was saved
      expect(freshExplorer.saveFileSystem).toHaveBeenCalled();
    });
    
    it('should recursively delete directories', async () => {
      // Create a directory structure
      fileExplorer.fileSystem['/TestDir'] = {
        type: 'directory',
        name: 'TestDir',
        children: ['SubDir', 'test.txt'],
        created: Date.now(),
        modified: Date.now()
      };
      
      fileExplorer.fileSystem['/TestDir/SubDir'] = {
        type: 'directory',
        name: 'SubDir',
        children: ['subfile.txt'],
        created: Date.now(),
        modified: Date.now()
      };
      
      fileExplorer.fileSystem['/TestDir/test.txt'] = {
        type: 'file',
        name: 'test.txt',
        extension: 'txt',
        content: 'Test content',
        size: 12,
        created: Date.now(),
        modified: Date.now()
      };
      
      fileExplorer.fileSystem['/TestDir/SubDir/subfile.txt'] = {
        type: 'file',
        name: 'subfile.txt',
        extension: 'txt',
        content: 'Subfile content',
        size: 15,
        created: Date.now(),
        modified: Date.now()
      };
      
      fileExplorer.fileSystem['/'].children.push('TestDir');
      
      // Select the directory for deletion
      fileExplorer.selectedFiles = ['/TestDir'];
      
      // Call deleteSelectedFiles method
      fileExplorer.deleteSelectedFiles();
      
      // Check that directory and all its contents were deleted
      expect(fileExplorer.fileSystem['/TestDir']).toBeUndefined();
      expect(fileExplorer.fileSystem['/TestDir/SubDir']).toBeUndefined();
      expect(fileExplorer.fileSystem['/TestDir/test.txt']).toBeUndefined();
      expect(fileExplorer.fileSystem['/TestDir/SubDir/subfile.txt']).toBeUndefined();
      
      // Check that directory was removed from parent
      expect(fileExplorer.fileSystem['/'].children).not.toContain('TestDir');
    });
    
    it('should copy selected files to clipboard', async () => {
      // Set up selected files
      fileExplorer.selectedFiles = ['/Documents/notes.txt'];
      
      // Call copySelectedFiles method
      fileExplorer.copySelectedFiles();
      
      // Check clipboard
      expect(fileExplorer.clipboard.files).toEqual(['/Documents/notes.txt']);
      expect(fileExplorer.clipboard.operation).toBe('copy');
      
      // Check status
      expect(fileExplorer.updateStatus).toHaveBeenCalledWith('Copied to clipboard: notes.txt');
    });
    
    it('should cut selected files to clipboard', async () => {
      // Set up selected files
      fileExplorer.selectedFiles = ['/Documents/notes.txt'];
      
      // Call cutSelectedFiles method
      fileExplorer.cutSelectedFiles();
      
      // Check clipboard
      expect(fileExplorer.clipboard.files).toEqual(['/Documents/notes.txt']);
      expect(fileExplorer.clipboard.operation).toBe('cut');
      
      // Check status
      expect(fileExplorer.updateStatus).toHaveBeenCalledWith('Cut to clipboard: notes.txt');
    });
    
    it('should paste copied files', async () => {
      // Set up clipboard with copy operation
      fileExplorer.clipboard = {
        files: ['/Documents/notes.txt'],
        operation: 'copy'
      };
      
      // Set current path to pictures folder
      fileExplorer.currentPath = '/Pictures';
      
      // Call pasteFiles method
      fileExplorer.pasteFiles();
      
      // Check that file was copied
      expect(fileExplorer.fileSystem['/Pictures/notes.txt']).toBeDefined();
      expect(fileExplorer.fileSystem['/Pictures/notes.txt'].type).toBe('file');
      expect(fileExplorer.fileSystem['/Pictures/notes.txt'].content).toBe(
        fileExplorer.fileSystem['/Documents/notes.txt'].content
      );
      
      // Check that file was added to target directory
      expect(fileExplorer.fileSystem['/Pictures'].children).toContain('notes.txt');
      
      // Check that original file still exists (copy operation)
      expect(fileExplorer.fileSystem['/Documents/notes.txt']).toBeDefined();
      expect(fileExplorer.fileSystem['/Documents'].children).toContain('notes.txt');
      
      // Check that UI was updated
      expect(fileExplorer.updateFileList).toHaveBeenCalled();
      expect(fileExplorer.updateStatus).toHaveBeenCalledWith('Paste complete');
      
      // Check that file system was saved
      expect(fileExplorer.saveFileSystem).toHaveBeenCalled();
    });
    
    it('should paste cut files', async () => {
      // Set up clipboard with cut operation
      fileExplorer.clipboard = {
        files: ['/Documents/notes.txt'],
        operation: 'cut'
      };
      
      // Set current path to pictures folder
      fileExplorer.currentPath = '/Pictures';
      
      // Call pasteFiles method
      fileExplorer.pasteFiles();
      
      // Check that file was moved
      expect(fileExplorer.fileSystem['/Pictures/notes.txt']).toBeDefined();
      expect(fileExplorer.fileSystem['/Pictures/notes.txt'].type).toBe('file');
      
      // Check that file was added to target directory
      expect(fileExplorer.fileSystem['/Pictures'].children).toContain('notes.txt');
      
      // Check that original file no longer exists (cut operation)
      expect(fileExplorer.fileSystem['/Documents/notes.txt']).toBeUndefined();
      expect(fileExplorer.fileSystem['/Documents'].children).not.toContain('notes.txt');
      
      // Check that clipboard was cleared
      expect(fileExplorer.clipboard.files).toEqual([]);
      expect(fileExplorer.clipboard.operation).toBeNull();
    });
    
    it('should create unique name when pasting to same directory', async () => {
      // Create a fresh instance for this test
      const freshExplorer = new FileExplorer(container, options);
      freshExplorer.updateFileList = jest.fn();
      freshExplorer.updateStatus = jest.fn();
      freshExplorer.saveFileSystem = jest.fn();
      
      // Manually ensure notes.txt exists and is in children array
      freshExplorer.fileSystem['/Documents/notes.txt'] = {
        type: 'file',
        name: 'notes.txt',
        extension: 'txt',
        content: 'Test content',
        size: 12,
        created: Date.now(),
        modified: Date.now()
      };
      
      // Make sure it's in the children array
      if (!freshExplorer.fileSystem['/Documents'].children.includes('notes.txt')) {
        freshExplorer.fileSystem['/Documents'].children.push('notes.txt');
      }
      
      // Set up clipboard with copy operation for the file
      freshExplorer.clipboard = {
        files: ['/Documents/notes.txt'],
        operation: 'copy'
      };
      
      // Set current path to Documents folder (same as source)
      freshExplorer.currentPath = '/Documents';
      
      // Record number of children before operation
      const childCountBefore = freshExplorer.fileSystem['/Documents'].children.length;
      
      // Call pasteFiles method
      freshExplorer.pasteFiles();
      
      // Check that a new file was added to the directory
      expect(freshExplorer.fileSystem['/Documents'].children.length).toBeGreaterThan(childCountBefore);
      
      // Original should still exist
      expect(freshExplorer.fileSystem['/Documents/notes.txt']).toBeDefined();
      
      // Verify that a new file with a unique name exists (notes (1).txt)
      expect(freshExplorer.fileSystem['/Documents'].children).toContain('notes (1).txt');
      expect(freshExplorer.fileSystem['/Documents/notes (1).txt']).toBeDefined();
    });
  });

  describe('File Selection', () => {
    beforeEach(() => {
      // Initialize FileExplorer
      fileExplorer = new FileExplorer(container, options);
      fileExplorer.updateSelectionUI = jest.fn();
    });
    
    it('should handle single file click selection', async () => {
      // Set up initial state
      fileExplorer.selectedFiles = [];
      
      // Create mock event
      const event = { ctrlKey: false };
      
      // Call handleFileClick method
      fileExplorer.handleFileClick(event, '/Documents/notes.txt');
      
      // Check selection
      expect(fileExplorer.selectedFiles).toEqual(['/Documents/notes.txt']);
      expect(fileExplorer.updateSelectionUI).toHaveBeenCalled();
    });
    
    it('should handle multiple file selection with Ctrl key', async () => {
      // Set up initial state with one file already selected
      fileExplorer.selectedFiles = ['/Documents/notes.txt'];
      
      // Create mock event with Ctrl key
      const event = { ctrlKey: true };
      
      // Call handleFileClick method for a second file
      fileExplorer.handleFileClick(event, '/Documents/report.doc');
      
      // Check that both files are selected
      expect(fileExplorer.selectedFiles).toEqual(['/Documents/notes.txt', '/Documents/report.doc']);
      expect(fileExplorer.updateSelectionUI).toHaveBeenCalled();
    });
    
    it('should toggle selection with Ctrl key', async () => {
      // Set up initial state with one file already selected
      fileExplorer.selectedFiles = ['/Documents/notes.txt'];
      
      // Create mock event with Ctrl key
      const event = { ctrlKey: true };
      
      // Call handleFileClick method for the same file
      fileExplorer.handleFileClick(event, '/Documents/notes.txt');
      
      // Check that file was deselected
      expect(fileExplorer.selectedFiles).toEqual([]);
      expect(fileExplorer.updateSelectionUI).toHaveBeenCalled();
    });
    
    it('should select all files in current directory', async () => {
      // Set up current path
      fileExplorer.currentPath = '/Documents';
      
      // Call selectAll method
      fileExplorer.selectAll();
      
      // Check that all files in directory are selected
      expect(fileExplorer.selectedFiles).toEqual(['/Documents/notes.txt', '/Documents/report.doc']);
      expect(fileExplorer.updateSelectionUI).toHaveBeenCalled();
    });
    
    it('should clear selection', async () => {
      // Set up initial selection
      fileExplorer.selectedFiles = ['/Documents/notes.txt', '/Documents/report.doc'];
      
      // Call clearSelection method
      fileExplorer.clearSelection();
      
      // Check that selection was cleared
      expect(fileExplorer.selectedFiles).toEqual([]);
      expect(fileExplorer.updateSelectionUI).toHaveBeenCalled();
    });
  });

  describe('Inter-App Communication', () => {
    beforeEach(() => {
      // Initialize FileExplorer
      fileExplorer = new FileExplorer(container, options);
    });
    
    it('should handle getFileList requests from other apps', async () => {
      // Create request from another app
      const request = {
        type: 'getFileList',
        path: '/Documents'
      };
      
      // Call handleAppRequest method
      const result = await fileExplorer.handleAppRequest(request, 'text-editor');
      
      // Check that correct file list was returned
      expect(result.path).toBe('/Documents');
      expect(result.items.length).toBe(2);
      expect(result.items[0].name).toBe('notes.txt');
      expect(result.items[1].name).toBe('report.doc');
    });
    
    it('should handle getFile requests from other apps', async () => {
      // Create request from another app
      const request = {
        type: 'getFile',
        path: '/Documents/notes.txt'
      };
      
      // Call handleAppRequest method
      const result = await fileExplorer.handleAppRequest(request, 'text-editor');
      
      // Check that correct file was returned
      expect(result.name).toBe('notes.txt');
      expect(result.path).toBe('/Documents/notes.txt');
      expect(result.type).toBe('file');
      expect(result.content).toBe('These are my important notes.');
    });
    
    it('should handle saveFile requests from other apps', async () => {
      // Create request from another app
      const request = {
        type: 'saveFile',
        path: '/Documents/notes.txt',
        content: 'Updated content'
      };
      
      // Mock saveFileSystem
      fileExplorer.saveFileSystem = jest.fn();
      
      // Call handleAppRequest method
      const result = await fileExplorer.handleAppRequest(request, 'text-editor');
      
      // Check that file was updated
      expect(fileExplorer.fileSystem['/Documents/notes.txt'].content).toBe('Updated content');
      expect(fileExplorer.fileSystem['/Documents/notes.txt'].size).toBe('Updated content'.length);
      
      // Check that file system was saved
      expect(fileExplorer.saveFileSystem).toHaveBeenCalled();
      
      // Check that correct result was returned
      expect(result.name).toBe('notes.txt');
      expect(result.path).toBe('/Documents/notes.txt');
      expect(result.size).toBe('Updated content'.length);
    });
    
    it('should create a new file when saving to a non-existent path', async () => {
      // Create request from another app for a new file
      const request = {
        type: 'saveFile',
        path: '/Documents/new-file.txt',
        content: 'New content'
      };
      
      // Mock saveFileSystem
      fileExplorer.saveFileSystem = jest.fn();
      
      // Call handleAppRequest method
      const result = await fileExplorer.handleAppRequest(request, 'text-editor');
      
      // Check that new file was created
      expect(fileExplorer.fileSystem['/Documents/new-file.txt']).toBeDefined();
      expect(fileExplorer.fileSystem['/Documents/new-file.txt'].type).toBe('file');
      expect(fileExplorer.fileSystem['/Documents/new-file.txt'].content).toBe('New content');
      
      // Check that file was added to parent directory
      expect(fileExplorer.fileSystem['/Documents'].children).toContain('new-file.txt');
      
      // Check that file system was saved
      expect(fileExplorer.saveFileSystem).toHaveBeenCalled();
      
      // Check that correct result was returned
      expect(result.name).toBe('new-file.txt');
      expect(result.path).toBe('/Documents/new-file.txt');
    });
    
    it('should open files with appropriate application', async () => {
      // Call openFile method
      fileExplorer.openFile('/Documents/notes.txt');
      
      // Check that appropriate app was launched
      expect(fileExplorer.api.eventBus.publish).toHaveBeenCalledWith('shell:launch-app', {
        appId: 'text-editor',
        fileToOpen: {
          path: '/Documents/notes.txt',
          name: 'notes.txt',
          content: 'These are my important notes.'
        }
      });
    });
    
    it('should handle file double click to open files', async () => {
      // Mock openFile
      fileExplorer.openFile = jest.fn();
      
      // Call handleFileDoubleClick for a file
      fileExplorer.handleFileDoubleClick('/Documents/notes.txt');
      
      // Check that openFile was called
      expect(fileExplorer.openFile).toHaveBeenCalledWith('/Documents/notes.txt');
    });
    
    it('should handle directory double click to navigate', async () => {
      // Mock navigateTo
      fileExplorer.navigateTo = jest.fn();
      
      // Call handleFileDoubleClick for a directory
      fileExplorer.handleFileDoubleClick('/Documents');
      
      // Check that navigateTo was called
      expect(fileExplorer.navigateTo).toHaveBeenCalledWith('/Documents');
    });
  });
});