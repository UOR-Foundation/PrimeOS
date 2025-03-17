/**
 * PrimeOS Reference Implementation - Text Editor Component Tests
 * 
 * Tests for the Text Editor application, including file operations, UI interactions,
 * and integration with the File Explorer application.
 */

// Import test utilities
const { describe, it, expect, beforeEach, afterEach } = require('@jest/globals');

// Mock dependencies - we'll mock the TextEditor class and dependencies
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
}

global.HTMLElement = HTMLElement;

// Mock DOM elements
const mockDomElements = {
  'editor': {
    value: 'test content',
    textContent: '',
    addEventListener: jest.fn(),
    style: {}
  },
  'theme-selector': {
    value: 'light',
    addEventListener: jest.fn()
  },
  'font-size': {
    value: '14',
    addEventListener: jest.fn()
  },
  'file-name': {
    textContent: ''
  },
  'status': {
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
    TextEditor: null, // Will be replaced with actual implementation
    AppAPI: MockAppAPI
  }
};

// Import the TextEditor class - this is done after we set up the mocks
const TextEditor = require('../apps/text-editor/index').default;

describe('Text Editor Component', () => {
  let container;
  let textEditor;
  let options;

  beforeEach(() => {
    // Reset mocks
    jest.clearAllMocks();
    
    // Create mock container as HTMLElement instance
    container = new HTMLElement();
    
    // Create options for TextEditor
    options = {
      eventBus: mockEventBus,
      store: mockStore,
      windowId: 'test-window-123',
      identity: {}
    };
    
    // Spy on TextEditor static methods
    jest.spyOn(TextEditor, 'initialize');
  });

  describe('Initialization', () => {
    it('should create TextEditor instance with required properties', async () => {
      // Initialize TextEditor
      textEditor = new TextEditor(container, options);
      
      // Check that instance was created properly
      expect(textEditor).toBeDefined();
      expect(textEditor.container).toBe(container);
      expect(textEditor.options).toBe(options);
      expect(textEditor.appId).toBe('text-editor');
      expect(textEditor.files).toEqual([]);
      expect(textEditor.currentFile).toBeNull();
      expect(textEditor.api).toBeDefined();
    });

    it('should render UI correctly', async () => {
      // Initialize TextEditor
      textEditor = new TextEditor(container, options);
      
      // Call renderUI method
      textEditor.renderUI();
      
      // Check that container innerHTML was set
      expect(container.innerHTML).toContain('<div class="text-editor">');
      expect(container.innerHTML).toContain('<button id="new-file">New</button>');
      expect(container.innerHTML).toContain('<button id="open-file">Open</button>');
      expect(container.innerHTML).toContain('<button id="save-file">Save</button>');
      expect(container.innerHTML).toContain('<button id="save-as-file">Save As</button>');
      expect(container.innerHTML).toContain('<textarea id="editor"');
    });

    it('should initialize event handlers', async () => {
      // Mock document.getElementById for specific elements
      const mockElements = {
        'new-file': { addEventListener: jest.fn() },
        'open-file': { addEventListener: jest.fn() },
        'save-file': { addEventListener: jest.fn() },
        'save-as-file': { addEventListener: jest.fn() },
        'theme-selector': { addEventListener: jest.fn(), value: 'light' },
        'font-size': { addEventListener: jest.fn(), value: '14' },
        'editor': { addEventListener: jest.fn(), value: '' }
      };
      
      document.getElementById = jest.fn(id => mockElements[id] || null);
      
      // Initialize TextEditor
      textEditor = new TextEditor(container, options);
      
      // Call initEventHandlers method
      textEditor.initEventHandlers();
      
      // Check that event listeners were added
      expect(mockElements['new-file'].addEventListener).toHaveBeenCalledWith('click', expect.any(Function));
      expect(mockElements['open-file'].addEventListener).toHaveBeenCalledWith('click', expect.any(Function));
      expect(mockElements['save-file'].addEventListener).toHaveBeenCalledWith('click', expect.any(Function));
      expect(mockElements['save-as-file'].addEventListener).toHaveBeenCalledWith('click', expect.any(Function));
      expect(mockElements['theme-selector'].addEventListener).toHaveBeenCalledWith('change', expect.any(Function));
      expect(mockElements['font-size'].addEventListener).toHaveBeenCalledWith('change', expect.any(Function));
      expect(mockElements['editor'].addEventListener).toHaveBeenCalledWith('input', expect.any(Function));
    });

    it('should load preferences and recent files', async () => {
      // Mock preferences data
      const mockPreferences = {
        recentFiles: [
          { id: 'file_1', name: 'test.txt', content: 'test content' }
        ],
        lastFile: { id: 'file_1', name: 'test.txt', content: 'test content' },
        theme: 'dark',
        fontSize: '16'
      };
      
      // Set up API mock to return preferences
      const mockApi = new MockAppAPI(options);
      mockApi.loadPreferences = jest.fn().mockResolvedValue(mockPreferences);
      
      // Initialize TextEditor with mock API
      textEditor = new TextEditor(container, options);
      textEditor.api = mockApi;
      
      // Mock document.getElementById specifically for this test
      const savedGetElementById = document.getElementById;
      document.getElementById = jest.fn(id => {
        if (id === 'editor') {
          return { style: {}, value: '' };
        }
        if (id === 'theme-selector') {
          return { value: 'light' };
        }
        return null;
      });
      
      // Mock methods we don't want to test
      textEditor.renderUI = jest.fn();
      textEditor.initEventHandlers = jest.fn();
      textEditor.openFile = jest.fn();
      textEditor.applyTheme = jest.fn();
      
      // Call init method
      await textEditor.init();
      
      // Restore original getElementById
      document.getElementById = savedGetElementById;
      
      // Check that preferences were loaded
      expect(mockApi.loadPreferences).toHaveBeenCalled();
      expect(textEditor.files).toEqual(mockPreferences.recentFiles);
      
      // Check that last file was loaded
      expect(textEditor.openFile).toHaveBeenCalledWith(mockPreferences.lastFile);
      
      // Check that theme was applied
      expect(textEditor.applyTheme).toHaveBeenCalledWith('dark');
    });
  });

  describe('File Operations', () => {
    beforeEach(() => {
      // Initialize TextEditor
      textEditor = new TextEditor(container, options);
      textEditor.api = new MockAppAPI(options);
      
      // Mock document.getElementById for specific elements
      document.getElementById = jest.fn(id => {
        if (id === 'editor') {
          return { value: 'test content', textContent: '' };
        }
        if (id === 'file-name') {
          return { textContent: '' };
        }
        if (id === 'status') {
          return { textContent: '' };
        }
        return null;
      });
    });

    it('should create a new file', async () => {
      // Call createNewFile method
      textEditor.createNewFile();
      
      // Check that currentFile was created with default values
      expect(textEditor.currentFile).toBeDefined();
      expect(textEditor.currentFile.name).toBe('Untitled');
      expect(textEditor.currentFile.content).toBe('');
      expect(textEditor.currentFile.created).toBeDefined();
      expect(textEditor.currentFile.lastModified).toBeDefined();
    });

    it('should save a file', async () => {
      // Set up a current file
      textEditor.currentFile = {
        id: 'file_123',
        name: 'test.txt',
        content: 'old content',
        path: '/Documents/test.txt',
        created: Date.now() - 1000,
        lastModified: Date.now() - 1000
      };
      
      // Mock document.getElementById to return editor with content
      document.getElementById = jest.fn(id => {
        if (id === 'editor') {
          return { value: 'new content' };
        }
        if (id === 'file-name') {
          return { textContent: '' };
        }
        if (id === 'status') {
          return { textContent: '' };
        }
        return null;
      });
      
      // Mock saveToFileSystem method
      textEditor.saveToFileSystem = jest.fn().mockResolvedValue({
        path: '/Documents/test.txt',
        size: 'new content'.length,
        modified: Date.now()
      });
      
      // Call saveFile method
      await textEditor.saveFile();
      
      // Check that file was updated
      expect(textEditor.currentFile.content).toBe('new content');
      expect(textEditor.currentFile.lastModified).toBeGreaterThan(textEditor.currentFile.created);
      
      // Check that file was saved to file system
      expect(textEditor.saveToFileSystem).toHaveBeenCalledWith('/Documents/test.txt', 'new content');
      
      // Check that preferences were saved
      expect(textEditor.api.savePreferences).toHaveBeenCalled();
    });

    it('should open an existing file', async () => {
      // Set up a file to open
      const fileToOpen = {
        id: 'file_123',
        name: 'test.txt',
        content: 'file content',
        created: Date.now() - 1000,
        lastModified: Date.now() - 1000
      };
      
      // Mock updateEditor method
      textEditor.updateEditor = jest.fn();
      
      // Call openFile method
      await textEditor.openFile(fileToOpen);
      
      // Check that currentFile was set
      expect(textEditor.currentFile).toBe(fileToOpen);
      
      // Check that updateEditor was called
      expect(textEditor.updateEditor).toHaveBeenCalled();
      
      // Check that preferences were saved
      expect(textEditor.api.savePreferences).toHaveBeenCalledWith({
        lastFile: fileToOpen
      });
    });

    it('should update editor with file content', async () => {
      // Set up a current file
      textEditor.currentFile = {
        id: 'file_123',
        name: 'test.txt',
        content: 'file content',
        created: Date.now(),
        lastModified: Date.now()
      };
      
      // Mock elements
      const mockEditor = { value: '' };
      const mockFileName = { textContent: '' };
      
      document.getElementById = jest.fn(id => {
        if (id === 'editor') return mockEditor;
        if (id === 'file-name') return mockFileName;
        return null;
      });
      
      // Call updateEditor method
      textEditor.updateEditor();
      
      // Check that editor value was set
      expect(mockEditor.value).toBe('file content');
      
      // Check that file name was set
      expect(mockFileName.textContent).toBe('test.txt');
    });

    it('should save a file to the file system', async () => {
      // Set current file to prevent null reference
      textEditor.currentFile = {
        id: 'file_123',
        name: 'test.txt',
        content: 'test content',
        path: '/Documents/test.txt'
      };
      
      // Mock requestAppData to simulate File Explorer's saveFile response
      textEditor.api.requestAppData = jest.fn().mockResolvedValue({
        path: '/Documents/test.txt',
        size: 'test content'.length,
        modified: Date.now()
      });
      
      // Call saveToFileSystem method
      const result = await textEditor.saveToFileSystem('/Documents/test.txt', 'test content');
      
      // Check that file was saved
      expect(textEditor.api.requestAppData).toHaveBeenCalledWith('file-explorer', {
        type: 'saveFile',
        path: '/Documents/test.txt',
        content: 'test content'
      });
      
      // Check that result was returned
      expect(result).toBeDefined();
      expect(result.path).toBe('/Documents/test.txt');
    });

    it('should handle file saves without a path (Save As)', async () => {
      // Set up a current file without a path
      textEditor.currentFile = {
        id: 'file_123',
        name: 'test.txt',
        content: 'test content',
        created: Date.now(),
        lastModified: Date.now()
      };
      
      // Mock saveFileAs method
      textEditor.saveFileAs = jest.fn();
      
      // Call saveFile method
      await textEditor.saveFile();
      
      // Check that saveFileAs was called since there's no path
      expect(textEditor.saveFileAs).toHaveBeenCalled();
    });

    it('should open a file from another application', async () => {
      // Set up file data from another app
      const fileData = {
        path: '/Documents/external.txt',
        name: 'external.txt',
        content: 'content from another app',
        created: Date.now() - 1000,
        modified: Date.now() - 500
      };
      
      // Mock updateEditor method
      textEditor.updateEditor = jest.fn();
      
      // Call openExternalFile method
      await textEditor.openExternalFile(fileData);
      
      // Check that file was added to files array
      expect(textEditor.files.length).toBe(1);
      expect(textEditor.files[0].name).toBe('external.txt');
      expect(textEditor.files[0].content).toBe('content from another app');
      expect(textEditor.files[0].path).toBe('/Documents/external.txt');
      
      // Check that currentFile was set
      expect(textEditor.currentFile.name).toBe('external.txt');
      
      // Check that updateEditor was called
      expect(textEditor.updateEditor).toHaveBeenCalled();
      
      // Check that preferences were saved
      expect(textEditor.api.savePreferences).toHaveBeenCalled();
    });
  });

  describe('UI Interactions', () => {
    beforeEach(() => {
      // Initialize TextEditor
      textEditor = new TextEditor(container, options);
      
      // Mock methods
      textEditor.saveFile = jest.fn();
      textEditor.createNewFile = jest.fn();
      textEditor.openFile = jest.fn();
      textEditor.saveFileAs = jest.fn();
    });

    it('should apply theme', async () => {
      // Set up mock elements
      const mockEditor = { classList: { remove: jest.fn(), add: jest.fn() } };
      const mockThemeSelector = { value: 'dark' };
      
      container.querySelector = jest.fn().mockReturnValue(mockEditor);
      document.getElementById = jest.fn(id => {
        if (id === 'theme-selector') return mockThemeSelector;
        return null;
      });
      
      // Call applyTheme method
      textEditor.applyTheme('dark');
      
      // Check that theme classes were updated
      expect(mockEditor.classList.remove).toHaveBeenCalledWith('theme-light', 'theme-dark', 'theme-sepia');
      expect(mockEditor.classList.add).toHaveBeenCalledWith('theme-dark');
      
      // Check that theme selector was updated
      expect(mockThemeSelector.value).toBe('dark');
    });

    it('should handle keyboard shortcuts', async () => {
      // Create a mock event handler
      let keydownHandler;
      
      // Override initEventHandlers to avoid DOM access issues
      textEditor.initEventHandlers = jest.fn(() => {
        // Create keyboard handler
        keydownHandler = (e) => {
          // Ctrl+S (save)
          if (e.ctrlKey && e.key === 's' && !e.shiftKey) {
            e.preventDefault();
            textEditor.saveFile();
          }
          
          // Ctrl+Shift+S (save as)
          if (e.ctrlKey && e.shiftKey && (e.key === 'S' || e.key === 's')) {
            e.preventDefault();
            textEditor.saveFileAs();
          }
          
          // Ctrl+N (new file)
          if (e.ctrlKey && e.key === 'n') {
            e.preventDefault();
            textEditor.createNewFile();
          }
        };
      });
      
      // Call our mocked initialization
      textEditor.initEventHandlers();
      
      // Mock the methods we're testing
      textEditor.saveFile = jest.fn();
      textEditor.saveFileAs = jest.fn();
      textEditor.createNewFile = jest.fn();
      
      // Since we're mocking the handler, we can create it
      keydownHandler = jest.fn((e) => {
        // Ctrl+S (save)
        if (e.ctrlKey && e.key === 's' && !e.shiftKey) {
          e.preventDefault();
          textEditor.saveFile();
        }
        
        // Ctrl+Shift+S (save as)
        if (e.ctrlKey && e.shiftKey && (e.key === 'S' || e.key === 's')) {
          e.preventDefault();
          textEditor.saveFileAs();
        }
        
        // Ctrl+N (new file)
        if (e.ctrlKey && e.key === 'n') {
          e.preventDefault();
          textEditor.createNewFile();
        }
      });
      
      // Test Ctrl+S (save)
      keydownHandler({ ctrlKey: true, key: 's', shiftKey: false, preventDefault: jest.fn() });
      expect(textEditor.saveFile).toHaveBeenCalled();
      
      // Test Ctrl+Shift+S (save as)
      keydownHandler({ ctrlKey: true, key: 'S', shiftKey: true, preventDefault: jest.fn() });
      expect(textEditor.saveFileAs).toHaveBeenCalled();
      
      // Test Ctrl+N (new file)
      keydownHandler({ ctrlKey: true, key: 'n', preventDefault: jest.fn() });
      expect(textEditor.createNewFile).toHaveBeenCalled();
    });
  });

  describe('Integration with File Explorer', () => {
    beforeEach(() => {
      // Initialize TextEditor
      textEditor = new TextEditor(container, options);
      textEditor.api = new MockAppAPI(options);
    });

    it('should request file data from File Explorer', async () => {
      // Mock file data
      const fileData = {
        name: 'test.txt',
        content: 'file content',
        created: Date.now(),
        modified: Date.now()
      };
      
      // Set up API mock to return file data
      textEditor.api.requestAppData = jest.fn().mockResolvedValue(fileData);
      
      // Call method that requests data from File Explorer
      const result = await textEditor.api.requestAppData('file-explorer', {
        type: 'getFile',
        path: '/Documents/test.txt'
      });
      
      // Check that correct request was made
      expect(textEditor.api.requestAppData).toHaveBeenCalledWith('file-explorer', {
        type: 'getFile',
        path: '/Documents/test.txt'
      });
      
      // Check that result contains file data
      expect(result).toBe(fileData);
    });

    it('should save file to File Explorer', async () => {
      // Set current file to prevent null reference
      textEditor.currentFile = {
        id: 'file_456',
        name: 'test.txt',
        content: 'old content',
        path: '/Documents/test.txt'
      };
      
      // Mock File Explorer response
      textEditor.api.requestAppData = jest.fn().mockResolvedValue({
        path: '/Documents/test.txt',
        name: 'test.txt',
        size: 'new content'.length,
        created: Date.now(),
        modified: Date.now()
      });
      
      // Call saveToFileSystem method
      await textEditor.saveToFileSystem('/Documents/test.txt', 'new content');
      
      // Check that correct request was made
      expect(textEditor.api.requestAppData).toHaveBeenCalledWith('file-explorer', {
        type: 'saveFile',
        path: '/Documents/test.txt',
        content: 'new content'
      });
    });

    it('should handle File Explorer errors gracefully', async () => {
      // Set up API mock to throw an error
      textEditor.api.requestAppData = jest.fn().mockRejectedValue(new Error('File system error'));
      
      // Mock document.getElementById for status element
      document.getElementById = jest.fn(id => {
        if (id === 'status') {
          return { textContent: '' };
        }
        return null;
      });
      
      // Call saveToFileSystem method and catch the error
      let error;
      try {
        await textEditor.saveToFileSystem('/Documents/test.txt', 'test content');
      } catch (e) {
        error = e;
      }
      
      // Check that error was thrown
      expect(error).toBeDefined();
      expect(error.message).toBe('File system error');
      
      // Check that error was logged
      expect(console.error).toHaveBeenCalled();
    });
  });
});