/**
 * PrimeOS Text Editor Application
 * 
 * A simple text editor application that demonstrates the PrimeOS application API.
 */

// Import dependencies - use a unique variable name for this app
let TextEditorAppAPI;

try {
  if (typeof window !== 'undefined' && window.PrimeOS && window.PrimeOS.AppAPI) {
    console.log('TextEditor: Using global AppAPI');
    TextEditorAppAPI = window.PrimeOS.AppAPI;
  } else {
    // For Node.js or when not available in window
    console.log('TextEditor: Attempting to require app-api module');
    const appApiModule = require('../../core/apps/app-api');
    TextEditorAppAPI = appApiModule.AppAPI;
  }
} catch (error) {
  console.error('TextEditor: Failed to import AppAPI:', error);
  // Mock implementation for testing
  TextEditorAppAPI = class {
    constructor(options) {
      this.appId = options.appId;
      this.container = options.containerElement;
      this.eventBus = options.eventBus || { publish: () => {}, subscribe: () => () => {} };
      this.store = options.store || null;
      this.windowId = options.windowId || null;
      this.state = { preferences: {} };
    }
    
    showNotification(notification) {
      console.log('NOTIFICATION:', notification);
    }
    
    async loadPreferences() {
      return this.state.preferences;
    }
    
    async savePreferences(preferences) {
      this.state.preferences = { ...this.state.preferences, ...preferences };
    }
  };
}

/**
 * Text Editor Application
 */
class TextEditor {
  /**
   * Initialize the text editor
   * @param {HTMLElement} container - Container element
   * @param {Object} options - Initialization options
   * @param {Object} [options.fileToOpen] - File to open initially
   */
  static async initialize(container, options) {
    const textEditor = new TextEditor(container, options);
    await textEditor.init();
    
    // Open file if specified
    if (options.fileToOpen) {
      await textEditor.openExternalFile(options.fileToOpen);
    }
    
    return textEditor;
  }
  
  /**
   * Constructor
   * @param {HTMLElement} container - Container element
   * @param {Object} options - Initialization options
   */
  constructor(container, options) {
    this.container = container;
    this.options = options;
    this.appId = 'text-editor';
    this.files = [];
    this.currentFile = null;
    
    // Initialize AppAPI with our renamed constructor
    this.api = new TextEditorAppAPI({
      appId: this.appId,
      containerElement: container,
      eventBus: options.eventBus,
      store: options.store,
      identity: options.identity,
      windowId: options.windowId
    });
    
    // Bind methods
    this.createNewFile = this.createNewFile.bind(this);
    this.saveFile = this.saveFile.bind(this);
    this.openFile = this.openFile.bind(this);
    this.openExternalFile = this.openExternalFile.bind(this);
    this.updateEditor = this.updateEditor.bind(this);
    this.getTitle = this.getTitle.bind(this);
    
    // Register an event handler for opening files from other apps
    if (options.eventBus) {
      options.eventBus.subscribe(`app:${this.appId}:open-file`, async (data) => {
        if (data.windowId === options.windowId && data.file) {
          await this.openExternalFile(data.file);
        }
      });
    }
  }
  
  /**
   * Get the current window title (for shell integration)
   * @returns {string} Window title
   */
  getTitle() {
    return this.currentFile 
      ? `${this.currentFile.name} - Text Editor`
      : 'Text Editor';
  }
  
  /**
   * Initialize the application
   */
  async init() {
    // Render initial UI
    this.renderUI();
    
    // Load preferences
    const preferences = await this.api.loadPreferences();
    
    // Load recent files
    if (preferences.recentFiles) {
      this.files = preferences.recentFiles;
    }
    
    // Set up event handlers
    this.initEventHandlers();
    
    // Auto-load last file if available
    if (preferences.lastFile) {
      await this.openFile(preferences.lastFile);
    } else {
      this.createNewFile();
    }
    
    // Update UI based on preferences
    if (preferences.fontSize) {
      document.getElementById('editor').style.fontSize = `${preferences.fontSize}px`;
    }
    
    if (preferences.theme) {
      this.applyTheme(preferences.theme);
    }
    
    // Notify shell that we're ready
    this.api.showNotification({
      title: 'Text Editor',
      message: 'Text Editor initialized successfully',
      type: 'success',
      timeout: 3000
    });
    
    return this;
  }
  
  /**
   * Render the UI
   */
  renderUI() {
    this.container.innerHTML = `
      <div class="text-editor">
        <div class="toolbar">
          <div class="file-actions">
            <button id="new-file">New</button>
            <button id="open-file">Open</button>
            <button id="save-file">Save</button>
            <button id="save-as-file">Save As</button>
          </div>
          <div class="editor-actions">
            <select id="theme-selector">
              <option value="light">Light Theme</option>
              <option value="dark">Dark Theme</option>
              <option value="sepia">Sepia Theme</option>
            </select>
            <select id="font-size">
              <option value="12">12px</option>
              <option value="14">14px</option>
              <option value="16">16px</option>
              <option value="18">18px</option>
              <option value="20">20px</option>
            </select>
          </div>
        </div>
        <div class="editor-container">
          <textarea id="editor" spellcheck="true"></textarea>
        </div>
        <div class="status-bar">
          <div id="file-name">Untitled</div>
          <div id="status">Ready</div>
        </div>
      </div>
    `;
    
    // Add styles
    const style = document.createElement('style');
    style.textContent = `
      .text-editor {
        display: flex;
        flex-direction: column;
        height: 100%;
        font-family: Arial, sans-serif;
      }
      
      .toolbar {
        display: flex;
        justify-content: space-between;
        padding: 10px;
        background-color: #f5f5f5;
        border-bottom: 1px solid #ddd;
      }
      
      .editor-container {
        flex: 1;
        overflow: hidden;
      }
      
      #editor {
        width: 100%;
        height: 100%;
        border: none;
        padding: 10px;
        resize: none;
        font-family: 'Courier New', monospace;
        font-size: 14px;
        line-height: 1.5;
      }
      
      .status-bar {
        display: flex;
        justify-content: space-between;
        padding: 5px 10px;
        background-color: #f5f5f5;
        border-top: 1px solid #ddd;
        font-size: 12px;
      }
      
      button {
        margin-right: 5px;
        padding: 5px 10px;
        background-color: #d0d0d0;
        border: 1px solid #aaa;
        border-radius: 3px;
        cursor: pointer;
        color: #222;
        font-weight: 500;
      }
      
      button:hover {
        background-color: #c0c0c0;
      }
      
      select {
        margin-left: 10px;
        padding: 5px;
      }
      
      /* Themes */
      .theme-light #editor {
        background-color: #fff;
        color: #333;
      }
      
      .theme-dark #editor {
        background-color: #2d2d2d;
        color: #f5f5f5;
      }
      
      .theme-sepia #editor {
        background-color: #f4ecd8;
        color: #5b4636;
      }
    `;
    
    this.container.appendChild(style);
  }
  
  /**
   * Initialize event handlers
   */
  initEventHandlers() {
    // New file
    document.getElementById('new-file').addEventListener('click', this.createNewFile);
    
    // Open file
    document.getElementById('open-file').addEventListener('click', async () => {
      try {
        // Check if File Explorer is accessible
        await this.api.requestAppData('file-explorer', {
          type: 'getFileList',
          path: '/'
        });
        
        // Show file browser dialog
        this.showOpenFileDialog();
      } catch (error) {
        console.error('Could not connect to File Explorer, using fallback:', error);
        
        // Fallback to simple file list if file explorer is not accessible
        this.showRecentFilesDialog();
      }
    });
    
    // Save file
    document.getElementById('save-file').addEventListener('click', this.saveFile);
    
    // Save As file
    document.getElementById('save-as-file').addEventListener('click', () => this.saveFileAs());
    
    // Theme selector
    document.getElementById('theme-selector').addEventListener('change', (e) => {
      const theme = e.target.value;
      this.applyTheme(theme);
      this.api.savePreferences({ theme });
    });
    
    // Font size
    document.getElementById('font-size').addEventListener('change', (e) => {
      const fontSize = parseInt(e.target.value);
      document.getElementById('editor').style.fontSize = `${fontSize}px`;
      this.api.savePreferences({ fontSize });
    });
    
    // Auto-save on content change (debounced)
    let autoSaveTimeout;
    document.getElementById('editor').addEventListener('input', () => {
      document.getElementById('status').textContent = 'Editing...';
      
      clearTimeout(autoSaveTimeout);
      autoSaveTimeout = setTimeout(() => {
        if (this.currentFile) {
          this.saveFile(true); // Auto-save
        }
      }, 2000); // 2 second debounce
    });
    
    // Keyboard shortcuts
    document.addEventListener('keydown', (e) => {
      // Save: Ctrl+S
      if (e.ctrlKey && e.key === 's' && !e.shiftKey) {
        e.preventDefault();
        this.saveFile();
      }
      
      // Save As: Ctrl+Shift+S
      if (e.ctrlKey && e.shiftKey && e.key === 'S') {
        e.preventDefault();
        this.saveFileAs();
      }
      
      // New: Ctrl+N
      if (e.ctrlKey && e.key === 'n') {
        e.preventDefault();
        this.createNewFile();
      }
      
      // Open: Ctrl+O
      if (e.ctrlKey && e.key === 'o') {
        e.preventDefault();
        document.getElementById('open-file').click();
      }
    });
    
    // Lifecycle hooks
    this.api.onBeforeClose = async () => {
      // Auto-save before closing
      if (this.currentFile) {
        await this.saveFile(true);
      }
    };
  }
  
  /**
   * Ensure file explorer is launched
   * @returns {Promise<void>}
   */
  ensureFileExplorer() {
    if (this.api.eventBus) {
      console.log('Ensuring file-explorer is launched...');
      this.api.eventBus.publish('shell:launch-app', { 
        appId: 'file-explorer',
        background: true  // Launch in background
      });
    }
  }
  
  /**
   * Show dialog with recent files
   */
  showRecentFilesDialog() {
    // Show file picker
    const fileList = document.createElement('div');
    fileList.className = 'file-list-overlay';
    fileList.innerHTML = `
      <div class="file-list">
        <h3>Open Recent File</h3>
        <div class="file-items">
          ${this.files.length > 0 ? 
            this.files.map(file => `
              <div class="file-item" data-file-id="${file.id}">
                <span class="file-name">${file.name}</span>
                <span class="file-date">${new Date(file.lastModified).toLocaleString()}</span>
              </div>
            `).join('') : 
            '<div class="empty-files">No recent files available</div>'
          }
        </div>
        <div class="file-list-actions">
          <button id="browse-files">Browse Files...</button>
          <button id="cancel-open">Cancel</button>
        </div>
      </div>
    `;
    
    // Add styles
    const style = document.createElement('style');
    style.textContent = `
      .file-list-overlay {
        position: fixed;
        top: 0;
        left: 0;
        right: 0;
        bottom: 0;
        background-color: rgba(0, 0, 0, 0.5);
        display: flex;
        align-items: center;
        justify-content: center;
        z-index: 1000;
      }
      
      .file-list {
        background-color: #fff;
        border-radius: 5px;
        box-shadow: 0 0 10px rgba(0, 0, 0, 0.2);
        width: 80%;
        max-width: 500px;
        padding: 20px;
      }
      
      .file-items {
        max-height: 300px;
        overflow-y: auto;
        margin: 10px 0;
      }
      
      .file-item {
        padding: 10px;
        border-bottom: 1px solid #eee;
        cursor: pointer;
        display: flex;
        justify-content: space-between;
      }
      
      .file-item:hover {
        background-color: #f5f5f5;
      }
      
      .empty-files {
        padding: 20px;
        text-align: center;
        color: #999;
      }
      
      .file-list-actions {
        display: flex;
        justify-content: space-between;
        margin-top: 10px;
      }
      
      .file-list-actions button {
        margin-left: 5px;
      }
    `;
    
    this.container.appendChild(style);
    this.container.appendChild(fileList);
    
    // Handle file selection
    const fileItems = fileList.querySelectorAll('.file-item');
    fileItems.forEach(item => {
      item.addEventListener('click', () => {
        const fileId = item.getAttribute('data-file-id');
        const file = this.files.find(f => f.id === fileId);
        if (file) {
          this.openFile(file);
        }
        fileList.remove();
        style.remove();
      });
    });
    
    // Handle browse button
    const browseButton = document.getElementById('browse-files');
    browseButton.addEventListener('click', () => {
      fileList.remove();
      style.remove();
      this.showOpenFileDialog();
    });
    
    // Handle cancel
    document.getElementById('cancel-open').addEventListener('click', () => {
      fileList.remove();
      style.remove();
    });
  }
  
  /**
   * Show open file dialog using file explorer API
   */
  async showOpenFileDialog() {
    // Default to Documents directory
    const defaultDir = '/Documents';
    
    try {
      // Ensure file explorer is launched
      this.ensureFileExplorer();
      
      // First, check if File Explorer is accessible
      const fileExplorerData = await this.api.requestAppData('file-explorer', {
        type: 'getFileList',
        path: defaultDir
      });
      
      // Create a file browser dialog
      const dialog = document.createElement('div');
      dialog.className = 'open-file-dialog';
      
      // Get current directory contents
      let currentPath = defaultDir;
      let currentFiles = fileExplorerData.items || [];
      
      dialog.innerHTML = `
        <div class="open-dialog-content">
          <h3>Open File</h3>
          
          <div class="open-dialog-path">
            <label>Location:</label>
            <div class="path-display">${currentPath}</div>
          </div>
          
          <div class="open-dialog-browser">
            <div class="folder-navigation">
              <div class="folder-item" data-path="/">Root</div>
              <div class="folder-item" data-path="/Documents">Documents</div>
              <div class="folder-item" data-path="/Pictures">Pictures</div>
              <div class="folder-item" data-path="/Music">Music</div>
              <div class="folder-item" data-path="/Videos">Videos</div>
            </div>
            
            <div class="file-browser-items">
              ${currentFiles.map(item => `
                <div class="browser-item ${item.type}" data-path="${item.path}" data-type="${item.type}">
                  <span class="item-icon">${item.type === 'directory' ? '📁' : '📄'}</span>
                  <span class="item-name">${item.name}</span>
                </div>
              `).join('')}
            </div>
          </div>
          
          <div class="open-dialog-actions">
            <button id="open-dialog-cancel">Cancel</button>
            <button id="open-dialog-open" disabled>Open</button>
          </div>
        </div>
      `;
      
      // Add styles
      const style = document.createElement('style');
      style.textContent = `
        .open-file-dialog {
          position: fixed;
          top: 0;
          left: 0;
          right: 0;
          bottom: 0;
          background-color: rgba(0, 0, 0, 0.5);
          display: flex;
          align-items: center;
          justify-content: center;
          z-index: 1000;
        }
        
        .open-dialog-content {
          background-color: #fff;
          border-radius: 5px;
          box-shadow: 0 0 10px rgba(0, 0, 0, 0.3);
          width: 80%;
          max-width: 600px;
          max-height: 80vh;
          display: flex;
          flex-direction: column;
          padding: 20px;
        }
        
        .open-dialog-path {
          display: flex;
          align-items: center;
          margin-bottom: 10px;
        }
        
        .path-display {
          margin-left: 10px;
          padding: 5px 10px;
          background-color: #f5f5f5;
          border-radius: 3px;
          flex: 1;
        }
        
        .open-dialog-browser {
          display: flex;
          border: 1px solid #ddd;
          height: 300px;
          margin-bottom: 15px;
        }
        
        .folder-navigation {
          width: 120px;
          border-right: 1px solid #ddd;
          overflow-y: auto;
        }
        
        .folder-item {
          padding: 8px;
          cursor: pointer;
          border-bottom: 1px solid #eee;
        }
        
        .folder-item:hover, .folder-item.selected {
          background-color: #e9ecef;
        }
        
        .file-browser-items {
          flex: 1;
          overflow-y: auto;
          padding: 5px;
          display: flex;
          flex-wrap: wrap;
          align-content: flex-start;
        }
        
        .browser-item {
          padding: 8px;
          margin: 5px;
          cursor: pointer;
          text-align: center;
          width: 100px;
          border-radius: 5px;
        }
        
        .browser-item:hover {
          background-color: #f5f5f5;
        }
        
        .browser-item.selected {
          background-color: #e2f0fd;
        }
        
        .item-icon {
          display: block;
          font-size: 24px;
          margin-bottom: 5px;
        }
        
        .open-dialog-actions {
          display: flex;
          justify-content: flex-end;
        }
        
        .open-dialog-actions button {
          margin-left: 10px;
          padding: 8px 15px;
        }
      `;
      
      // Add to document
      document.body.appendChild(style);
      document.body.appendChild(dialog);
      
      // Track selected file
      let selectedFilePath = null;
      const openButton = document.getElementById('open-dialog-open');
      
      // Helper function to update file browser
      const updateFileBrowser = async (path) => {
        try {
          const data = await this.api.requestAppData('file-explorer', {
            type: 'getFileList',
            path: path
          });
          
          currentPath = path;
          currentFiles = data.items || [];
          
          // Update path display
          const pathDisplay = dialog.querySelector('.path-display');
          pathDisplay.textContent = currentPath;
          
          // Update folder navigation
          const folderItems = dialog.querySelectorAll('.folder-item');
          folderItems.forEach(item => {
            item.classList.remove('selected');
            if (item.getAttribute('data-path') === currentPath) {
              item.classList.add('selected');
            }
          });
          
          // Update file browser
          const fileBrowser = dialog.querySelector('.file-browser-items');
          fileBrowser.innerHTML = currentFiles.map(item => `
            <div class="browser-item ${item.type}" data-path="${item.path}" data-type="${item.type}">
              <span class="item-icon">${item.type === 'directory' ? '📁' : '📄'}</span>
              <span class="item-name">${item.name}</span>
            </div>
          `).join('');
          
          // Reset selected file
          selectedFilePath = null;
          openButton.disabled = true;
          
          // Add event listeners for browser items
          const browserItems = dialog.querySelectorAll('.browser-item');
          browserItems.forEach(item => {
            item.addEventListener('click', async () => {
              const itemPath = item.getAttribute('data-path');
              const itemType = item.getAttribute('data-type');
              
              // Clear all selections
              browserItems.forEach(i => i.classList.remove('selected'));
              
              // If it's a directory, navigate to it
              if (itemType === 'directory') {
                await updateFileBrowser(itemPath);
              } else {
                // If it's a file, select it
                item.classList.add('selected');
                selectedFilePath = itemPath;
                openButton.disabled = false;
              }
            });
            
            item.addEventListener('dblclick', async () => {
              const itemPath = item.getAttribute('data-path');
              const itemType = item.getAttribute('data-type');
              
              // If it's a directory, navigate to it
              if (itemType === 'directory') {
                await updateFileBrowser(itemPath);
              } else {
                // If it's a file, open it
                selectedFilePath = itemPath;
                openSelectedFile();
              }
            });
          });
        } catch (error) {
          console.error('Failed to update file browser:', error);
        }
      };
      
      // Function to open the selected file
      const openSelectedFile = async () => {
        if (!selectedFilePath) return;
        
        try {
          // Get file content through File Explorer
          const fileInfo = await this.api.requestAppData('file-explorer', {
            type: 'getFile',
            path: selectedFilePath
          });
          
          if (fileInfo) {
            // Create a file object for our internal format
            const file = {
              id: `file_${Date.now()}`,
              name: fileInfo.name,
              content: fileInfo.content || '',
              path: fileInfo.path,
              created: fileInfo.created || Date.now(),
              lastModified: fileInfo.modified || Date.now()
            };
            
            // Check if this file is already in our recent files
            const existingFile = this.files.find(f => f.path === file.path);
            if (existingFile) {
              // Update existing file with new content
              existingFile.content = file.content;
              existingFile.lastModified = Date.now();
              this.currentFile = existingFile;
            } else {
              // Add to recent files
              this.files.push(file);
              this.currentFile = file;
            }
            
            // Update editor
            this.updateEditor();
            
            // Update status
            document.getElementById('status').textContent = `Opened file: ${file.name}`;
            
            // Save metadata to preferences
            await this.api.savePreferences({
              recentFiles: this.files.map(f => ({
                id: f.id,
                name: f.name,
                path: f.path,
                created: f.created,
                lastModified: f.lastModified
              })),
              lastFile: {
                id: this.currentFile.id,
                name: this.currentFile.name,
                path: this.currentFile.path,
                created: this.currentFile.created,
                lastModified: this.currentFile.lastModified
              }
            });
            
            // Show success notification
            this.api.showNotification({
              title: 'File Opened',
              message: `Opened ${fileInfo.name}`,
              type: 'success',
              timeout: 2000
            });
          }
          
          // Close dialog
          dialog.remove();
          style.remove();
        } catch (error) {
          console.error('Failed to open file:', error);
          this.api.showNotification({
            title: 'Error',
            message: 'Failed to open file: ' + error.message,
            type: 'error'
          });
        }
      };
      
      // Event listeners for folder navigation
      const folderItems = dialog.querySelectorAll('.folder-item');
      folderItems.forEach(item => {
        item.addEventListener('click', async () => {
          const path = item.getAttribute('data-path');
          await updateFileBrowser(path);
        });
      });
      
      // Initialize the first folder
      await updateFileBrowser(currentPath);
      
      // Handle cancel
      document.getElementById('open-dialog-cancel').addEventListener('click', () => {
        dialog.remove();
        style.remove();
      });
      
      // Handle open
      document.getElementById('open-dialog-open').addEventListener('click', () => {
        openSelectedFile();
      });
      
      // Add keyboard navigation
      dialog.addEventListener('keydown', (e) => {
        // Enter - Open
        if (e.key === 'Enter' && !openButton.disabled) {
          e.preventDefault();
          openSelectedFile();
        }
        
        // Escape - Cancel
        if (e.key === 'Escape') {
          e.preventDefault();
          document.getElementById('open-dialog-cancel').click();
        }
      });
      
    } catch (error) {
      console.error('Failed to open file dialog:', error);
      this.api.showNotification({
        title: 'Error',
        message: 'Could not open file browser: ' + error.message,
        type: 'error'
      });
      
      // Fall back to simple recent files dialog
      this.showRecentFilesDialog();
    }
  }
  
  /**
   * Apply theme to editor
   * @param {string} theme - Theme name
   */
  applyTheme(theme) {
    const editor = this.container.querySelector('.text-editor');
    
    // Remove existing theme classes
    editor.classList.remove('theme-light', 'theme-dark', 'theme-sepia');
    
    // Add new theme class
    editor.classList.add(`theme-${theme}`);
    
    // Update theme selector
    document.getElementById('theme-selector').value = theme;
  }
  
  /**
   * Create a new file
   */
  createNewFile() {
    this.currentFile = {
      id: `file_${Date.now()}`,
      name: 'Untitled',
      content: '',
      created: Date.now(),
      lastModified: Date.now()
    };
    
    this.updateEditor();
    
    document.getElementById('status').textContent = 'New file created';
  }
  
  /**
   * Save current file
   * @param {boolean} [isAutoSave=false] - Whether this is an auto-save
   */
  async saveFile(isAutoSave = false) {
    if (!this.currentFile) {
      return;
    }
    
    // Get content from editor
    const content = document.getElementById('editor').value;
    
    // If it's a new file, prompt for name
    if (this.currentFile.name === 'Untitled' && !isAutoSave) {
      const fileName = prompt('Enter file name:', 'Untitled');
      if (fileName) {
        this.currentFile.name = fileName;
      }
    }
    
    // Update file object
    this.currentFile.content = content;
    this.currentFile.lastModified = Date.now();
    
    // Find existing file in array or add new one
    const existingIndex = this.files.findIndex(file => file.id === this.currentFile.id);
    if (existingIndex >= 0) {
      this.files[existingIndex] = this.currentFile;
    } else {
      this.files.push(this.currentFile);
    }
    
    try {
      // First, save metadata to preferences (recent files list)
      await this.api.savePreferences({
        recentFiles: this.files.map(f => ({
          id: f.id,
          name: f.name,
          path: f.path,
          created: f.created,
          lastModified: f.lastModified
        })),
        lastFile: {
          id: this.currentFile.id,
          name: this.currentFile.name,
          path: this.currentFile.path,
          created: this.currentFile.created,
          lastModified: this.currentFile.lastModified
        }
      });
      
      // If there's a path, save to File Explorer
      if (this.currentFile.path) {
        // Save through File Explorer using inter-app API
        await this.saveToFileSystem(this.currentFile.path, content);
      } else {
        // It's a new file that hasn't been saved to the filesystem yet
        // Ask for path and location
        if (!isAutoSave) {
          this.saveFileAs();
          return;
        }
      }
      
      // Update status
      if (!isAutoSave) {
        document.getElementById('status').textContent = 'File saved';
        this.api.showNotification({
          title: 'Text Editor',
          message: `File "${this.currentFile.name}" saved successfully`,
          type: 'success',
          timeout: 2000
        });
      } else {
        document.getElementById('status').textContent = 'Auto-saved';
      }
    } catch (error) {
      document.getElementById('status').textContent = 'Error saving file';
      console.error('Failed to save file:', error);
      
      this.api.showNotification({
        title: 'Save Error',
        message: 'Failed to save file: ' + error.message,
        type: 'error'
      });
    }
    
    // Update UI
    document.getElementById('file-name').textContent = this.currentFile.name;
  }
  
  /**
   * Save file to a different location
   */
  async saveFileAs() {
    // Default to Documents directory
    const defaultDir = '/Documents';
    const defaultFileName = 'untitled.txt';
    
    try {
      // Ensure file explorer is launched
      this.ensureFileExplorer();
      
      // First, check if File Explorer is accessible
      const fileExplorerData = await this.api.requestAppData('file-explorer', {
        type: 'getFileList',
        path: defaultDir
      });
      
      // Create a file browser dialog
      const dialog = document.createElement('div');
      dialog.className = 'save-as-dialog';
      
      // Determine default file name to suggest
      const suggestedName = this.currentFile?.name || defaultFileName;
      
      // Get current directory contents
      let currentPath = defaultDir;
      let currentFiles = fileExplorerData.items || [];
      
      dialog.innerHTML = `
        <div class="save-dialog-content">
          <h3>Save As</h3>
          
          <div class="save-dialog-path">
            <label>Location:</label>
            <div class="path-display">${currentPath}</div>
          </div>
          
          <div class="save-dialog-browser">
            <div class="folder-navigation">
              <div class="folder-item" data-path="/">Root</div>
              <div class="folder-item" data-path="/Documents">Documents</div>
              <div class="folder-item" data-path="/Pictures">Pictures</div>
              <div class="folder-item" data-path="/Music">Music</div>
              <div class="folder-item" data-path="/Videos">Videos</div>
            </div>
            
            <div class="file-browser-items">
              ${currentFiles.map(item => `
                <div class="browser-item ${item.type}" data-path="${item.path}" data-type="${item.type}">
                  <span class="item-icon">${item.type === 'directory' ? '📁' : '📄'}</span>
                  <span class="item-name">${item.name}</span>
                </div>
              `).join('')}
            </div>
          </div>
          
          <div class="save-dialog-filename">
            <label for="save-filename">File name:</label>
            <input type="text" id="save-filename" value="${suggestedName}">
          </div>
          
          <div class="save-dialog-actions">
            <button id="save-dialog-cancel">Cancel</button>
            <button id="save-dialog-save">Save</button>
          </div>
        </div>
      `;
      
      // Add styles
      const style = document.createElement('style');
      style.textContent = `
        .save-as-dialog {
          position: fixed;
          top: 0;
          left: 0;
          right: 0;
          bottom: 0;
          background-color: rgba(0, 0, 0, 0.5);
          display: flex;
          align-items: center;
          justify-content: center;
          z-index: 1000;
        }
        
        .save-dialog-content {
          background-color: #fff;
          border-radius: 5px;
          box-shadow: 0 0 10px rgba(0, 0, 0, 0.3);
          width: 80%;
          max-width: 600px;
          max-height: 80vh;
          display: flex;
          flex-direction: column;
          padding: 20px;
        }
        
        .save-dialog-path {
          display: flex;
          align-items: center;
          margin-bottom: 10px;
        }
        
        .path-display {
          margin-left: 10px;
          padding: 5px 10px;
          background-color: #f5f5f5;
          border-radius: 3px;
          flex: 1;
        }
        
        .save-dialog-browser {
          display: flex;
          border: 1px solid #ddd;
          height: 300px;
          margin-bottom: 15px;
        }
        
        .folder-navigation {
          width: 120px;
          border-right: 1px solid #ddd;
          overflow-y: auto;
        }
        
        .folder-item {
          padding: 8px;
          cursor: pointer;
          border-bottom: 1px solid #eee;
        }
        
        .folder-item:hover, .folder-item.selected {
          background-color: #e9ecef;
        }
        
        .file-browser-items {
          flex: 1;
          overflow-y: auto;
          padding: 5px;
          display: flex;
          flex-wrap: wrap;
          align-content: flex-start;
        }
        
        .browser-item {
          padding: 8px;
          margin: 5px;
          cursor: pointer;
          text-align: center;
          width: 100px;
          border-radius: 5px;
        }
        
        .browser-item:hover {
          background-color: #f5f5f5;
        }
        
        .browser-item.selected {
          background-color: #e2f0fd;
        }
        
        .item-icon {
          display: block;
          font-size: 24px;
          margin-bottom: 5px;
        }
        
        .save-dialog-filename {
          display: flex;
          align-items: center;
          margin-bottom: 15px;
        }
        
        .save-dialog-filename label {
          margin-right: 10px;
        }
        
        .save-dialog-filename input {
          flex: 1;
          padding: 8px;
          border: 1px solid #ddd;
          border-radius: 3px;
        }
        
        .save-dialog-actions {
          display: flex;
          justify-content: flex-end;
        }
        
        .save-dialog-actions button {
          margin-left: 10px;
          padding: 8px 15px;
        }
      `;
      
      // Add to document
      document.body.appendChild(style);
      document.body.appendChild(dialog);
      
      // Set focus on the filename input
      setTimeout(() => {
        const filenameInput = document.getElementById('save-filename');
        if (filenameInput) {
          filenameInput.focus();
          filenameInput.select();
        }
      }, 100);
      
      // Add keyboard navigation
      dialog.addEventListener('keydown', (e) => {
        // Enter - Save
        if (e.key === 'Enter') {
          e.preventDefault();
          document.getElementById('save-dialog-save').click();
        }
        
        // Escape - Cancel
        if (e.key === 'Escape') {
          e.preventDefault();
          document.getElementById('save-dialog-cancel').click();
        }
      });
      
      // Helper function to update file browser
      const updateFileBrowser = async (path) => {
        try {
          const data = await this.api.requestAppData('file-explorer', {
            type: 'getFileList',
            path: path
          });
          
          currentPath = path;
          currentFiles = data.items || [];
          
          // Update path display
          const pathDisplay = dialog.querySelector('.path-display');
          pathDisplay.textContent = currentPath;
          
          // Update folder navigation
          const folderItems = dialog.querySelectorAll('.folder-item');
          folderItems.forEach(item => {
            item.classList.remove('selected');
            if (item.getAttribute('data-path') === currentPath) {
              item.classList.add('selected');
            }
          });
          
          // Update file browser
          const fileBrowser = dialog.querySelector('.file-browser-items');
          fileBrowser.innerHTML = currentFiles.map(item => `
            <div class="browser-item ${item.type}" data-path="${item.path}" data-type="${item.type}">
              <span class="item-icon">${item.type === 'directory' ? '📁' : '📄'}</span>
              <span class="item-name">${item.name}</span>
            </div>
          `).join('');
          
          // Add event listeners for browser items
          const browserItems = dialog.querySelectorAll('.browser-item');
          browserItems.forEach(item => {
            item.addEventListener('click', async () => {
              const itemPath = item.getAttribute('data-path');
              const itemType = item.getAttribute('data-type');
              
              // Clear all selections
              browserItems.forEach(i => i.classList.remove('selected'));
              
              // If it's a directory, navigate to it
              if (itemType === 'directory') {
                await updateFileBrowser(itemPath);
              } else {
                // If it's a file, select it and update filename
                item.classList.add('selected');
                document.getElementById('save-filename').value = itemPath.split('/').pop();
              }
            });
            
            item.addEventListener('dblclick', async () => {
              const itemPath = item.getAttribute('data-path');
              const itemType = item.getAttribute('data-type');
              
              // If it's a directory, navigate to it
              if (itemType === 'directory') {
                await updateFileBrowser(itemPath);
              }
            });
          });
        } catch (error) {
          console.error('Failed to update file browser:', error);
        }
      };
      
      // Event listeners for folder navigation
      const folderItems = dialog.querySelectorAll('.folder-item');
      folderItems.forEach(item => {
        item.addEventListener('click', async () => {
          const path = item.getAttribute('data-path');
          await updateFileBrowser(path);
        });
      });
      
      // Initialize the first folder
      await updateFileBrowser(currentPath);
      
      // Handle cancel
      document.getElementById('save-dialog-cancel').addEventListener('click', () => {
        dialog.remove();
        style.remove();
      });
      
      // Handle save
      document.getElementById('save-dialog-save').addEventListener('click', async () => {
        const fileName = document.getElementById('save-filename').value;
        if (!fileName) {
          this.api.showNotification({
            title: 'Error',
            message: 'Please enter a file name',
            type: 'error'
          });
          return;
        }
        
        // Construct full path
        const fullPath = currentPath === '/' 
          ? `/${fileName}`
          : `${currentPath}/${fileName}`;
        
        // Get current content from editor
        const content = document.getElementById('editor').value || '';
        
        // If currentFile doesn't exist, create it
        if (!this.currentFile) {
          this.currentFile = {
            id: `file_${Date.now()}`,
            name: fileName,
            content: content,
            created: Date.now(),
            lastModified: Date.now()
          };
        }
        
        // Update file path
        this.currentFile.path = fullPath;
        this.currentFile.name = fileName;
        this.currentFile.content = content;
        
        try {
          // Save content to file system
          await this.saveToFileSystem(fullPath, this.currentFile.content);
          
          // Update UI
          document.getElementById('file-name').textContent = this.currentFile.name;
          document.getElementById('status').textContent = 'File saved as ' + fullPath;
          
          // Add to recent files if not already there
          const existingIndex = this.files.findIndex(file => file.id === this.currentFile.id);
          if (existingIndex >= 0) {
            this.files[existingIndex] = this.currentFile;
          } else {
            this.files.push(this.currentFile);
          }
          
          // Save as last opened file
          await this.api.savePreferences({
            lastFile: this.currentFile,
            recentFiles: this.files.map(f => ({
              id: f.id,
              name: f.name,
              path: f.path,
              created: f.created,
              lastModified: f.lastModified
            }))
          });
          
          // Show success notification
          this.api.showNotification({
            title: 'File Saved',
            message: `File saved successfully to ${fullPath}`,
            type: 'success',
            timeout: 3000
          });
          
          // Remove dialog
          dialog.remove();
          style.remove();
        } catch (error) {
          console.error('Failed to save file:', error);
          this.api.showNotification({
            title: 'Save Error',
            message: 'Could not save file: ' + error.message,
            type: 'error'
          });
        }
      });
      
    } catch (error) {
      console.error('Failed to open Save As dialog:', error);
      this.api.showNotification({
        title: 'Save Error',
        message: 'Could not open Save As dialog: ' + error.message,
        type: 'error'
      });
      
      // Fall back to simple prompt if dialog fails
      const fileName = prompt('Enter file name with path (e.g. /Documents/myfile.txt):', 
                             `${defaultDir}/${this.currentFile?.name || defaultFileName}`);
      
      if (!fileName) return;
      
      // Get current content from editor
      const content = document.getElementById('editor').value || '';
      
      // If currentFile doesn't exist, create it
      if (!this.currentFile) {
        this.currentFile = {
          id: `file_${Date.now()}`,
          name: fileName.split('/').pop(),
          content: content,
          created: Date.now(),
          lastModified: Date.now()
        };
      }
      
      // Update file path
      this.currentFile.path = fileName;
      const pathParts = fileName.split('/');
      this.currentFile.name = pathParts.pop();
      this.currentFile.content = content;
      
      try {
        // Save content to file system
        await this.saveToFileSystem(fileName, this.currentFile.content);
        
        // Update UI
        document.getElementById('file-name').textContent = this.currentFile.name;
        document.getElementById('status').textContent = 'File saved as ' + fileName;
        
        // Add to recent files if not already there
        const existingIndex = this.files.findIndex(file => file.id === this.currentFile.id);
        if (existingIndex >= 0) {
          this.files[existingIndex] = this.currentFile;
        } else {
          this.files.push(this.currentFile);
        }
        
        // Save as last opened file
        await this.api.savePreferences({
          lastFile: this.currentFile,
          recentFiles: this.files.map(f => ({
            id: f.id,
            name: f.name,
            path: f.path,
            created: f.created,
            lastModified: f.lastModified
          }))
        });
      } catch (error) {
        console.error('Failed to save file as:', error);
        this.api.showNotification({
          title: 'Save Error',
          message: 'Could not save file. Please try a different location.',
          type: 'error'
        });
      }
    }
  }
  
  /**
   * Save file to the file system using File Explorer's API
   * @param {string} path - File path
   * @param {string} content - File content
   */
  async saveToFileSystem(path, content) {
    try {
      // Ensure file explorer is launched
      this.ensureFileExplorer();
      
      // Request to save through File Explorer
      const result = await this.api.requestAppData('file-explorer', {
        type: 'saveFile',
        path: path,
        content: content
      });
      
      // Update our file object with any updates from file system
      if (result) {
        // Ensure currentFile is initialized
        if (!this.currentFile) {
          this.currentFile = {
            name: path.split('/').pop(),
            content: content
          };
        }
        
        this.currentFile.path = result.path;
        this.currentFile.size = result.size;
        this.currentFile.modified = result.modified;
      }
      
      return result;
    } catch (error) {
      console.error('Failed to save to file system:', error);
      
      // Show a more user-friendly error message
      this.api.showNotification({
        title: 'Save Error',
        message: 'Could not save file. Please try a different location.',
        type: 'error'
      });
      
      throw error;
    }
  }
  
  /**
   * Open a file
   * @param {Object} file - File to open
   */
  async openFile(file) {
    this.currentFile = file;
    this.updateEditor();
    
    document.getElementById('status').textContent = 'File opened';
    
    // Save as last opened file
    await this.api.savePreferences({
      lastFile: this.currentFile
    });
  }
  
  /**
   * Update editor with current file content
   */
  updateEditor() {
    if (!this.currentFile) return;
    
    const editor = document.getElementById('editor');
    editor.value = this.currentFile.content || '';
    
    document.getElementById('file-name').textContent = this.currentFile.name;
  }
  
  /**
   * Open a file from another application
   * @param {Object} fileData - File data from another app
   * @param {string} fileData.path - File path
   * @param {string} fileData.name - File name
   * @param {string} fileData.content - File content
   */
  async openExternalFile(fileData) {
    if (!fileData || !fileData.name) return;
    
    // If only path is provided, try to load content from File Explorer
    if (fileData.path && !fileData.content) {
      try {
        // Ensure file explorer is launched
        this.ensureFileExplorer();
        
        const fileInfo = await this.api.requestAppData('file-explorer', {
          type: 'getFile',
          path: fileData.path
        });
        
        if (fileInfo) {
          fileData = {
            ...fileData,
            name: fileInfo.name,
            content: fileInfo.content,
            created: fileInfo.created,
            modified: fileInfo.modified
          };
        }
      } catch (error) {
        console.error('Failed to get file content from File Explorer:', error);
      }
    }
    
    // Create a file object compatible with our internal format
    const file = {
      id: `file_${Date.now()}`,
      name: fileData.name,
      content: fileData.content || '',
      path: fileData.path || null,
      created: fileData.created || Date.now(),
      lastModified: fileData.modified || Date.now()
    };
    
    // Check if this file is already in our recent files
    const existingFile = this.files.find(f => f.path === file.path);
    if (existingFile) {
      // Update existing file with new content
      existingFile.content = file.content;
      existingFile.lastModified = Date.now();
      this.currentFile = existingFile;
    } else {
      // Add to recent files
      this.files.push(file);
      this.currentFile = file;
    }
    
    // Update editor
    this.updateEditor();
    
    // Update status
    document.getElementById('status').textContent = `Opened file: ${file.name}`;
    
    // Save metadata to preferences
    await this.api.savePreferences({
      recentFiles: this.files.map(f => ({
        id: f.id,
        name: f.name,
        path: f.path,
        created: f.created,
        lastModified: f.lastModified
      })),
      lastFile: {
        id: this.currentFile.id,
        name: this.currentFile.name,
        path: this.currentFile.path,
        created: this.currentFile.created,
        lastModified: this.currentFile.lastModified
      }
    });
    
    // Update window title if possible
    const windowId = this.options.windowId;
    if (windowId) {
      this.api.eventBus.publish('shell:update-window-title', {
        windowId,
        title: this.getTitle()
      });
    }
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { default: TextEditor };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.TextEditor = TextEditor;
}