/**
 * PrimeOS File Explorer Application
 * 
 * A simple file explorer that enables browsing, creating, and managing virtual files.
 * This demonstrates the PrimeOS application API and interoperability with other apps.
 */

// Import dependencies - use a unique variable name for this app
let FileExplorerAppAPI;

try {
  if (typeof window !== 'undefined' && window.PrimeOS && window.PrimeOS.AppAPI) {
    console.log('FileExplorer: Using global AppAPI');
    FileExplorerAppAPI = window.PrimeOS.AppAPI;
  } else {
    // For Node.js or when not available in window
    console.log('FileExplorer: Attempting to require app-api module');
    const appApiModule = require('../../core/apps/app-api');
    FileExplorerAppAPI = appApiModule.AppAPI;
  }
} catch (error) {
  console.error('FileExplorer: Failed to import AppAPI:', error);
  // Mock implementation for testing
  FileExplorerAppAPI = class {
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
    
    async requestAppData() {
      return {};
    }
  };
}

/**
 * File Explorer Application
 */
class FileExplorer {
  /**
   * Initialize the file explorer
   * @param {HTMLElement} container - Container element
   * @param {Object} options - Initialization options
   */
  static async initialize(container, options) {
    const fileExplorer = new FileExplorer(container, options);
    await fileExplorer.init();
    return fileExplorer;
  }
  
  /**
   * Constructor
   * @param {HTMLElement} container - Container element
   * @param {Object} options - Initialization options
   */
  constructor(container, options) {
    this.container = container;
    this.options = options;
    this.appId = 'file-explorer';
    
    // File system state
    this.currentPath = '/';
    this.fileSystem = {
      '/': {
        type: 'directory',
        name: 'Root',
        children: ['Documents', 'Pictures', 'Music', 'Videos'],
        created: Date.now(),
        modified: Date.now()
      },
      '/Documents': {
        type: 'directory',
        name: 'Documents',
        children: ['notes.txt', 'report.doc'],
        created: Date.now(),
        modified: Date.now()
      },
      '/Pictures': {
        type: 'directory',
        name: 'Pictures',
        children: ['vacation.jpg', 'family.png'],
        created: Date.now(),
        modified: Date.now()
      },
      '/Music': {
        type: 'directory',
        name: 'Music',
        children: ['song.mp3'],
        created: Date.now(),
        modified: Date.now()
      },
      '/Videos': {
        type: 'directory',
        name: 'Videos',
        children: [],
        created: Date.now(),
        modified: Date.now()
      },
      '/Documents/notes.txt': {
        type: 'file',
        name: 'notes.txt',
        extension: 'txt',
        content: 'These are my important notes.',
        size: 29,
        created: Date.now(),
        modified: Date.now()
      },
      '/Documents/report.doc': {
        type: 'file',
        name: 'report.doc',
        extension: 'doc',
        content: 'Annual report content.',
        size: 22,
        created: Date.now(),
        modified: Date.now()
      },
      '/Pictures/vacation.jpg': {
        type: 'file',
        name: 'vacation.jpg',
        extension: 'jpg',
        content: 'image-data-placeholder',
        size: 1024,
        created: Date.now(),
        modified: Date.now()
      },
      '/Pictures/family.png': {
        type: 'file',
        name: 'family.png',
        extension: 'png',
        content: 'image-data-placeholder',
        size: 2048,
        created: Date.now(),
        modified: Date.now()
      },
      '/Music/song.mp3': {
        type: 'file',
        name: 'song.mp3',
        extension: 'mp3',
        content: 'audio-data-placeholder',
        size: 4096,
        created: Date.now(),
        modified: Date.now()
      }
    };
    
    // Selected files
    this.selectedFiles = [];
    
    // Clipboard for copy/cut operations
    this.clipboard = {
      files: [],
      operation: null // 'copy' or 'cut'
    };
    
    // Initialize AppAPI with our renamed constructor
    this.api = new FileExplorerAppAPI({
      appId: this.appId,
      containerElement: container,
      eventBus: options.eventBus,
      store: options.store,
      identity: options.identity,
      windowId: options.windowId
    });
    
    // Bind methods
    this.navigateTo = this.navigateTo.bind(this);
    this.handleFileClick = this.handleFileClick.bind(this);
    this.handleFileDoubleClick = this.handleFileDoubleClick.bind(this);
    this.createNewFolder = this.createNewFolder.bind(this);
    this.createNewFile = this.createNewFile.bind(this);
    this.deleteSelectedFiles = this.deleteSelectedFiles.bind(this);
    this.copySelectedFiles = this.copySelectedFiles.bind(this);
    this.cutSelectedFiles = this.cutSelectedFiles.bind(this);
    this.pasteFiles = this.pasteFiles.bind(this);
    this.openFile = this.openFile.bind(this);
  }
  
  /**
   * Initialize the application
   */
  async init() {
    // Load saved file system from storage
    await this.loadFileSystem();
    
    // Render initial UI
    this.renderUI();
    
    // Set up event handlers
    this.initEventHandlers();
    
    // Make sure api.eventBus is defined before using it
    if (!this.api.eventBus) {
      console.error('EventBus is not defined in AppAPI');
      // If in test environment, use mockEventBus
      if (typeof jest !== 'undefined') {
        this.api.eventBus = {
          subscribe: jest.fn(() => jest.fn()),
          publish: jest.fn(),
          unsubscribe: jest.fn()
        };
      }
    }
    
    // Register request handler for other apps to access files
    console.log('FileExplorer: Registering request handler');
    const unsubscribe = this.api.registerRequestHandler(this.handleAppRequest.bind(this));
    
    // Verify registration
    if (typeof unsubscribe === 'function') {
      console.log('FileExplorer: Request handler registered successfully');
    } else {
      console.error('FileExplorer: Failed to register request handler');
    }
    
    // Navigate to root directory
    this.navigateTo('/');
    
    // Load preferences
    const preferences = await this.api.loadPreferences();
    
    // Apply preferences
    if (preferences.lastPath) {
      this.navigateTo(preferences.lastPath);
    }
    
    // Notify shell that we're ready
    this.api.showNotification({
      title: 'File Explorer',
      message: 'File Explorer initialized successfully',
      type: 'success',
      timeout: 2000
    });
    
    return this;
  }
  
  /**
   * Load file system from storage
   */
  async loadFileSystem() {
    try {
      const savedFileSystem = await this.api.loadPreferences();
      
      if (savedFileSystem.fileSystem) {
        this.fileSystem = savedFileSystem.fileSystem;
      } else {
        // Save initial file system
        await this.saveFileSystem();
      }
    } catch (error) {
      console.error('Failed to load file system:', error);
      // Keep using the default file system
    }
  }
  
  /**
   * Save file system to storage
   * @param {boolean} showNotification - Whether to show a notification on success
   * @returns {Promise<boolean>} Success indicator
   */
  async saveFileSystem(showNotification = false) {
    try {
      await this.api.savePreferences({
        fileSystem: this.fileSystem,
        lastPath: this.currentPath
      });
      
      if (showNotification) {
        this.api.showNotification({
          title: 'File Explorer',
          message: 'File system saved successfully',
          type: 'success',
          timeout: 2000
        });
      }
      
      return true;
    } catch (error) {
      console.error('Failed to save file system:', error);
      this.api.showNotification({
        title: 'File Explorer',
        message: 'Failed to save file system: ' + error.message,
        type: 'error'
      });
      return false;
    }
  }
  
  /**
   * Render the UI
   */
  renderUI() {
    this.container.innerHTML = `
      <div class="file-explorer">
        <div class="toolbar">
          <div class="navigation">
            <button id="back-button">←</button>
            <button id="up-button">↑</button>
            <button id="refresh-button">↻</button>
            <div class="path-input-container">
              <input type="text" id="path-input" readonly>
            </div>
          </div>
          <div class="file-actions">
            <button id="new-folder">New Folder</button>
            <button id="new-file">New File</button>
            <button id="delete">Delete</button>
            <button id="copy">Copy</button>
            <button id="cut">Cut</button>
            <button id="paste">Paste</button>
          </div>
        </div>
        <div class="sidebar">
          <div class="quick-access">
            <h3>Quick Access</h3>
            <ul>
              <li data-path="/"><i class="icon-folder"></i> Root</li>
              <li data-path="/Documents"><i class="icon-folder"></i> Documents</li>
              <li data-path="/Pictures"><i class="icon-folder"></i> Pictures</li>
              <li data-path="/Music"><i class="icon-folder"></i> Music</li>
              <li data-path="/Videos"><i class="icon-folder"></i> Videos</li>
            </ul>
          </div>
        </div>
        <div class="file-view">
          <div class="file-list" id="file-list"></div>
        </div>
        <div class="status-bar">
          <div id="status">Ready</div>
          <div id="selection-info">No items selected</div>
        </div>
      </div>
    `;
    
    // Add styles
    const style = document.createElement('style');
    style.textContent = `
      .file-explorer {
        display: grid;
        grid-template-rows: auto 1fr auto;
        grid-template-columns: 180px 1fr;
        grid-template-areas:
          "toolbar toolbar"
          "sidebar file-view"
          "status-bar status-bar";
        height: 100%;
        font-family: Arial, sans-serif;
        color: #333;
      }
      
      .toolbar {
        grid-area: toolbar;
        display: flex;
        justify-content: space-between;
        padding: 10px;
        background-color: #f5f5f5;
        border-bottom: 1px solid #ddd;
      }
      
      .navigation {
        display: flex;
        align-items: center;
      }
      
      .path-input-container {
        flex: 1;
        margin: 0 10px;
      }
      
      #path-input {
        width: 100%;
        padding: 5px;
        border: 1px solid #ddd;
        border-radius: 3px;
      }
      
      .sidebar {
        grid-area: sidebar;
        background-color: #f8f9fa;
        border-right: 1px solid #ddd;
        padding: 10px;
        overflow-y: auto;
      }
      
      .quick-access ul {
        list-style: none;
        padding: 0;
        margin: 0;
      }
      
      .quick-access li {
        padding: 8px;
        cursor: pointer;
        border-radius: 4px;
      }
      
      .quick-access li:hover {
        background-color: #e9ecef;
      }
      
      .file-view {
        grid-area: file-view;
        padding: 10px;
        overflow-y: auto;
      }
      
      .file-list {
        display: grid;
        grid-template-columns: repeat(auto-fill, minmax(120px, 1fr));
        gap: 10px;
      }
      
      .file-item {
        display: flex;
        flex-direction: column;
        align-items: center;
        padding: 10px;
        cursor: pointer;
        border-radius: 4px;
        text-align: center;
      }
      
      .file-item:hover {
        background-color: #f8f9fa;
      }
      
      .file-item.selected {
        background-color: #e2f0fd;
      }
      
      .file-icon {
        font-size: 32px;
        margin-bottom: 5px;
      }
      
      .file-name {
        word-break: break-word;
        font-size: 12px;
      }
      
      .status-bar {
        grid-area: status-bar;
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
        background-color: #fff;
        border: 1px solid #ddd;
        border-radius: 3px;
        cursor: pointer;
      }
      
      button:hover {
        background-color: #f0f0f0;
      }
      
      button:disabled {
        opacity: 0.5;
        cursor: not-allowed;
      }
      
      .icon-folder:before {
        content: '📁';
      }
      
      .icon-file:before {
        content: '📄';
      }
      
      .icon-image:before {
        content: '🖼️';
      }
      
      .icon-audio:before {
        content: '🎵';
      }
      
      .icon-video:before {
        content: '🎬';
      }
      
      .icon-text:before {
        content: '📝';
      }
      
      .icon-doc:before {
        content: '📃';
      }
    `;
    
    this.container.appendChild(style);
  }
  
  /**
   * Initialize event handlers
   */
  initEventHandlers() {
    // Quick access links
    const quickAccessItems = this.container.querySelectorAll('.quick-access li');
    quickAccessItems.forEach(item => {
      item.addEventListener('click', () => {
        const path = item.getAttribute('data-path');
        if (path) {
          this.navigateTo(path);
        }
      });
    });
    
    // Back button
    const backButton = this.container.querySelector('#back-button');
    backButton.addEventListener('click', () => {
      // Implement back navigation
      // For simplicity, just go up a directory
      this.navigateUp();
    });
    
    // Up button
    const upButton = this.container.querySelector('#up-button');
    upButton.addEventListener('click', () => {
      this.navigateUp();
    });
    
    // Refresh button
    const refreshButton = this.container.querySelector('#refresh-button');
    refreshButton.addEventListener('click', () => {
      this.refreshView();
    });
    
    // New folder button
    const newFolderButton = this.container.querySelector('#new-folder');
    newFolderButton.addEventListener('click', this.createNewFolder);
    
    // New file button
    const newFileButton = this.container.querySelector('#new-file');
    newFileButton.addEventListener('click', this.createNewFile);
    
    // Delete button
    const deleteButton = this.container.querySelector('#delete');
    deleteButton.addEventListener('click', this.deleteSelectedFiles);
    
    // Copy button
    const copyButton = this.container.querySelector('#copy');
    copyButton.addEventListener('click', this.copySelectedFiles);
    
    // Cut button
    const cutButton = this.container.querySelector('#cut');
    cutButton.addEventListener('click', this.cutSelectedFiles);
    
    // Paste button
    const pasteButton = this.container.querySelector('#paste');
    pasteButton.addEventListener('click', this.pasteFiles);
    
    // File selection handling on background click
    const fileList = this.container.querySelector('#file-list');
    fileList.addEventListener('click', (e) => {
      if (e.target === fileList) {
        this.clearSelection();
      }
    });
    
    // Keyboard shortcuts
    document.addEventListener('keydown', (e) => {
      if (!this.api.state.isActive) return;
      
      // Ctrl+C (Copy)
      if (e.ctrlKey && e.key === 'c') {
        this.copySelectedFiles();
      }
      
      // Ctrl+X (Cut)
      if (e.ctrlKey && e.key === 'x') {
        this.cutSelectedFiles();
      }
      
      // Ctrl+V (Paste)
      if (e.ctrlKey && e.key === 'v') {
        this.pasteFiles();
      }
      
      // Delete (Delete selected files)
      if (e.key === 'Delete') {
        this.deleteSelectedFiles();
      }
      
      // Ctrl+A (Select all)
      if (e.ctrlKey && e.key === 'a') {
        e.preventDefault();
        this.selectAll();
      }
    });
  }
  
  /**
   * Handle app data requests from other applications
   * @param {Object} request - The request object
   * @param {string} sourceAppId - ID of the requesting app
   * @returns {Promise<any>} Response data
   */
  async handleAppRequest(request, sourceAppId) {
    console.log(`FileExplorer: Handling request from ${sourceAppId}:`, request);
    
    try {
      let result;
      
      switch (request.type) {
        case 'getFileList': {
          const path = request.path || this.currentPath;
          console.log(`FileExplorer: Getting file list for ${path}`);
          result = this.getFileList(path);
          break;
        }
          
        case 'getFile': {
          console.log(`FileExplorer: Getting file ${request.path}`);
          result = this.getFile(request.path);
          break;
        }
          
        case 'saveFile': {
          console.log(`FileExplorer: Saving file ${request.path}`);
          
          // Explicitly create a deep copy to avoid any reference issues
          const content = JSON.parse(JSON.stringify(request.content));
          
          // Save the file
          result = this.saveFile(request.path, content);
          
          // When a file is saved, refresh the view if we're in the same directory
          const fileDirPath = request.path.substring(0, request.path.lastIndexOf('/')) || '/';
          if (fileDirPath === this.currentPath) {
            this.updateFileList();
            this.updateStatus(`File saved: ${request.path.split('/').pop()}`);
          }
          
          // Log success
          console.log(`FileExplorer: File ${request.path} saved successfully`);
          break;
        }
          
        default:
          throw new Error(`Unknown request type: ${request.type}`);
      }
      
      return result;
    } catch (error) {
      console.error(`FileExplorer: Error handling request:`, error);
      
      // Re-throw the error to be handled by the AppAPI
      throw error;
    }
  }
  
  /**
   * Get list of files in a directory
   * @param {string} path - Directory path
   * @returns {Array} List of files and directories
   */
  getFileList(path) {
    const directory = this.fileSystem[path];
    if (!directory || directory.type !== 'directory') {
      throw new Error(`Path is not a directory: ${path}`);
    }
    
    return {
      path,
      items: directory.children.map(childName => {
        const childPath = `${path}/${childName}`.replace(/\/\//g, '/');
        const child = this.fileSystem[childPath];
        return {
          name: child.name,
          path: childPath,
          type: child.type,
          size: child.size,
          created: child.created,
          modified: child.modified
        };
      })
    };
  }
  
  /**
   * Get file content
   * @param {string} path - File path
   * @returns {Object} File object with content
   */
  getFile(path) {
    const file = this.fileSystem[path];
    if (!file || file.type !== 'file') {
      throw new Error(`Path is not a file: ${path}`);
    }
    
    return {
      name: file.name,
      path,
      type: file.type,
      extension: file.extension,
      content: file.content,
      size: file.size,
      created: file.created,
      modified: file.modified
    };
  }
  
  /**
   * Save file content
   * @param {string} path - File path
   * @param {string} content - File content
   * @returns {Object} Updated file object
   */
  saveFile(path, content) {
    let file = this.fileSystem[path];
    
    if (!file) {
      // Create new file if it doesn't exist
      const pathParts = path.split('/');
      const fileName = pathParts.pop();
      const dirPath = pathParts.join('/') || '/';
      
      // Create parent directories if they don't exist
      if (!this.fileSystem[dirPath]) {
        this._createDirectoryPath(dirPath);
      }
      
      // Now the parent directory should exist
      if (!this.fileSystem[dirPath] || this.fileSystem[dirPath].type !== 'directory') {
        throw new Error(`Failed to create parent directory: ${dirPath}`);
      }
      
      const extension = fileName.includes('.') ? fileName.split('.').pop() : '';
      
      file = {
        type: 'file',
        name: fileName,
        extension,
        content: '',
        size: 0,
        created: Date.now(),
        modified: Date.now()
      };
      
      // Add file to filesystem
      this.fileSystem[path] = file;
      
      // Add to parent's children if not already there
      if (!this.fileSystem[dirPath].children.includes(fileName)) {
        this.fileSystem[dirPath].children.push(fileName);
      }
    }
    
    if (file.type !== 'file') {
      throw new Error(`Path is not a file: ${path}`);
    }
    
    // Update file content
    file.content = content;
    file.size = content.length;
    file.modified = Date.now();
    
    // Save file system
    this.saveFileSystem();
    
    // Return file metadata
    return {
      name: file.name,
      path,
      type: file.type,
      extension: file.extension,
      size: file.size,
      created: file.created,
      modified: file.modified
    };
  }
  
  /**
   * Create directory path recursively
   * @private
   * @param {string} dirPath - Directory path to create
   */
  _createDirectoryPath(dirPath) {
    // Already exists
    if (this.fileSystem[dirPath]) {
      return;
    }
    
    // Split path into parts
    const pathParts = dirPath.split('/').filter(Boolean);
    
    // Build path incrementally and create missing directories
    let currentPath = '';
    
    for (const part of pathParts) {
      currentPath = currentPath ? `${currentPath}/${part}` : `/${part}`;
      
      // Create directory if it doesn't exist
      if (!this.fileSystem[currentPath]) {
        const parentPath = currentPath.substring(0, currentPath.lastIndexOf('/')) || '/';
        
        // Create directory
        this.fileSystem[currentPath] = {
          type: 'directory',
          name: part,
          children: [],
          created: Date.now(),
          modified: Date.now()
        };
        
        // Add to parent's children
        if (this.fileSystem[parentPath]) {
          if (!this.fileSystem[parentPath].children.includes(part)) {
            this.fileSystem[parentPath].children.push(part);
          }
        }
      }
    }
  }
  
  /**
   * Navigate to a directory
   * @param {string} path - Directory path
   */
  navigateTo(path) {
    if (!this.fileSystem[path] || this.fileSystem[path].type !== 'directory') {
      this.api.showNotification({
        title: 'Error',
        message: `Invalid directory path: ${path}`,
        type: 'error'
      });
      return;
    }
    
    this.currentPath = path;
    this.clearSelection();
    this.updateFileList();
    
    // Update path input
    const pathInput = this.container.querySelector('#path-input');
    pathInput.value = this.currentPath;
    
    // Update status
    this.updateStatus(`Navigated to ${path}`);
    
    // Save last path
    this.api.savePreferences({ lastPath: this.currentPath });
  }
  
  /**
   * Navigate up one directory
   */
  navigateUp() {
    if (this.currentPath === '/') return;
    
    const pathParts = this.currentPath.split('/').filter(Boolean);
    pathParts.pop();
    const newPath = pathParts.length === 0 ? '/' : `/${pathParts.join('/')}`;
    
    this.navigateTo(newPath);
  }
  
  /**
   * Refresh the current view
   */
  refreshView() {
    this.updateFileList();
    this.updateStatus('View refreshed');
  }
  
  /**
   * Update the file list
   */
  updateFileList() {
    const fileList = this.container.querySelector('#file-list');
    const directory = this.fileSystem[this.currentPath];
    
    if (!directory || directory.type !== 'directory') {
      fileList.innerHTML = '<div class="error">Invalid directory</div>';
      return;
    }
    
    fileList.innerHTML = '';
    
    directory.children.forEach(childName => {
      const childPath = `${this.currentPath}/${childName}`.replace(/\/\//g, '/');
      const child = this.fileSystem[childPath];
      
      if (!child) return;
      
      const fileItem = document.createElement('div');
      fileItem.className = 'file-item';
      fileItem.setAttribute('data-path', childPath);
      
      let iconClass = 'icon-file';
      if (child.type === 'directory') {
        iconClass = 'icon-folder';
      } else if (child.extension) {
        // Set icon based on file extension
        switch (child.extension.toLowerCase()) {
          case 'jpg':
          case 'jpeg':
          case 'png':
          case 'gif':
            iconClass = 'icon-image';
            break;
          case 'mp3':
          case 'wav':
            iconClass = 'icon-audio';
            break;
          case 'mp4':
          case 'mkv':
          case 'avi':
            iconClass = 'icon-video';
            break;
          case 'txt':
            iconClass = 'icon-text';
            break;
          case 'doc':
          case 'docx':
          case 'pdf':
            iconClass = 'icon-doc';
            break;
        }
      }
      
      fileItem.innerHTML = `
        <div class="file-icon"><i class="${iconClass}"></i></div>
        <div class="file-name">${child.name}</div>
      `;
      
      // Add event listeners
      fileItem.addEventListener('click', (e) => {
        this.handleFileClick(e, childPath);
      });
      
      fileItem.addEventListener('dblclick', () => {
        this.handleFileDoubleClick(childPath);
      });
      
      fileList.appendChild(fileItem);
    });
  }
  
  /**
   * Handle file click (selection)
   * @param {Event} e - Click event
   * @param {string} path - File path
   */
  handleFileClick(e, path) {
    // If Ctrl key is pressed, toggle selection
    if (e.ctrlKey) {
      const index = this.selectedFiles.indexOf(path);
      if (index === -1) {
        this.selectedFiles.push(path);
      } else {
        this.selectedFiles.splice(index, 1);
      }
    } else {
      // Otherwise, select only this file
      this.selectedFiles = [path];
    }
    
    this.updateSelectionUI();
  }
  
  /**
   * Handle file double click (open)
   * @param {string} path - File path
   */
  handleFileDoubleClick(path) {
    const item = this.fileSystem[path];
    
    if (item.type === 'directory') {
      // Navigate to directory
      this.navigateTo(path);
    } else {
      // Open file
      this.openFile(path);
    }
  }
  
  /**
   * Open a file with appropriate application
   * @param {string} path - File path
   */
  async openFile(path) {
    const file = this.fileSystem[path];
    
    if (!file || file.type !== 'file') {
      this.api.showNotification({
        title: 'Error',
        message: `Invalid file path: ${path}`,
        type: 'error'
      });
      return;
    }
    
    try {
      // Determine which app to use based on file extension
      let appId;
      
      switch (file.extension.toLowerCase()) {
        case 'txt':
        case 'md':
        case 'js':
        case 'json':
        case 'html':
        case 'css':
          appId = 'text-editor';
          break;
          
        default:
          // Default to text editor for unknown types
          appId = 'text-editor';
      }
      
      // Launch appropriate app
      this.api.eventBus.publish('shell:launch-app', { 
        appId,
        fileToOpen: {
          path,
          name: file.name,
          content: file.content
        }
      });
      
      this.updateStatus(`Opening ${file.name} with ${appId}`);
    } catch (error) {
      console.error('Failed to open file:', error);
      this.api.showNotification({
        title: 'Error',
        message: `Failed to open file: ${error.message}`,
        type: 'error'
      });
    }
  }
  
  /**
   * Create a new folder in the current directory
   */
  createNewFolder() {
    const folderName = prompt('Enter folder name:');
    
    if (!folderName) return;
    
    // Validate folder name
    if (!/^[a-zA-Z0-9_\-. ]+$/.test(folderName)) {
      this.api.showNotification({
        title: 'Error',
        message: 'Invalid folder name. Use only letters, numbers, spaces, and _.-, characters.',
        type: 'error'
      });
      return;
    }
    
    // Check if folder already exists
    const newPath = `${this.currentPath}/${folderName}`.replace(/\/\//g, '/');
    if (this.fileSystem[newPath]) {
      this.api.showNotification({
        title: 'Error',
        message: `A file or folder with the name "${folderName}" already exists.`,
        type: 'error'
      });
      return;
    }
    
    // Create folder
    this.fileSystem[newPath] = {
      type: 'directory',
      name: folderName,
      children: [],
      created: Date.now(),
      modified: Date.now()
    };
    
    // Add to parent directory
    this.fileSystem[this.currentPath].children.push(folderName);
    
    // Update UI
    this.updateFileList();
    this.updateStatus(`Created folder: ${folderName}`);
    
    // Save file system
    this.saveFileSystem();
  }
  
  /**
   * Create a new file in the current directory
   */
  createNewFile() {
    const fileName = prompt('Enter file name:');
    
    if (!fileName) return;
    
    // Validate file name
    if (!/^[a-zA-Z0-9_\-. ]+$/.test(fileName)) {
      this.api.showNotification({
        title: 'Error',
        message: 'Invalid file name. Use only letters, numbers, spaces, and _.-, characters.',
        type: 'error'
      });
      return;
    }
    
    // Check if file already exists
    const newPath = `${this.currentPath}/${fileName}`.replace(/\/\//g, '/');
    if (this.fileSystem[newPath]) {
      this.api.showNotification({
        title: 'Error',
        message: `A file or folder with the name "${fileName}" already exists.`,
        type: 'error'
      });
      return;
    }
    
    // Determine file extension
    const extension = fileName.includes('.') ? fileName.split('.').pop() : '';
    
    // Create file
    this.fileSystem[newPath] = {
      type: 'file',
      name: fileName,
      extension,
      content: '',
      size: 0,
      created: Date.now(),
      modified: Date.now()
    };
    
    // Add to parent directory
    this.fileSystem[this.currentPath].children.push(fileName);
    
    // Update UI
    this.updateFileList();
    this.updateStatus(`Created file: ${fileName}`);
    
    // Save file system
    this.saveFileSystem();
    
    // Open the new file
    setTimeout(() => {
      this.openFile(newPath);
    }, 100);
  }
  
  /**
   * Delete selected files
   */
  deleteSelectedFiles() {
    if (this.selectedFiles.length === 0) {
      this.api.showNotification({
        title: 'Error',
        message: 'No files selected for deletion',
        type: 'warning'
      });
      return;
    }
    
    const confirmMessage = this.selectedFiles.length === 1
      ? `Are you sure you want to delete "${this.fileSystem[this.selectedFiles[0]].name}"?`
      : `Are you sure you want to delete ${this.selectedFiles.length} items?`;
    
    if (!confirm(confirmMessage)) return;
    
    const deletedItems = [];
    
    // Delete each selected file
    this.selectedFiles.forEach(path => {
      const item = this.fileSystem[path];
      if (!item) return;
      
      deletedItems.push(item.name);
      
      // Remove from parent directory
      const parentPath = path.substring(0, path.lastIndexOf('/')) || '/';
      const parent = this.fileSystem[parentPath];
      
      if (parent && parent.type === 'directory') {
        const index = parent.children.indexOf(item.name);
        if (index !== -1) {
          parent.children.splice(index, 1);
        }
      }
      
      // Delete from file system
      delete this.fileSystem[path];
      
      // Recursively delete subdirectories and files if it's a directory
      if (item.type === 'directory') {
        this.deleteRecursively(path);
      }
    });
    
    // Clear selection
    this.clearSelection();
    
    // Update UI
    this.updateFileList();
    this.updateStatus(`Deleted ${deletedItems.join(', ')}`);
    
    // Save file system
    this.saveFileSystem();
  }
  
  /**
   * Recursively delete a directory and its contents
   * @param {string} dirPath - Directory path
   */
  deleteRecursively(dirPath) {
    // Find all paths that start with dirPath/
    Object.keys(this.fileSystem).forEach(path => {
      if (path.startsWith(`${dirPath}/`)) {
        delete this.fileSystem[path];
      }
    });
  }
  
  /**
   * Copy selected files to clipboard
   */
  copySelectedFiles() {
    if (this.selectedFiles.length === 0) {
      this.api.showNotification({
        title: 'Error',
        message: 'No files selected for copying',
        type: 'warning'
      });
      return;
    }
    
    this.clipboard = {
      files: [...this.selectedFiles],
      operation: 'copy'
    };
    
    const items = this.clipboard.files.map(path => this.fileSystem[path].name);
    this.updateStatus(`Copied to clipboard: ${items.join(', ')}`);
  }
  
  /**
   * Cut selected files to clipboard
   */
  cutSelectedFiles() {
    if (this.selectedFiles.length === 0) {
      this.api.showNotification({
        title: 'Error',
        message: 'No files selected for cutting',
        type: 'warning'
      });
      return;
    }
    
    this.clipboard = {
      files: [...this.selectedFiles],
      operation: 'cut'
    };
    
    const items = this.clipboard.files.map(path => this.fileSystem[path].name);
    this.updateStatus(`Cut to clipboard: ${items.join(', ')}`);
  }
  
  /**
   * Paste files from clipboard to current directory
   */
  pasteFiles() {
    if (!this.clipboard.files || this.clipboard.files.length === 0) {
      this.api.showNotification({
        title: 'Error',
        message: 'Nothing to paste',
        type: 'warning'
      });
      return;
    }
    
    const targetDir = this.currentPath;
    
    // Process each file in clipboard
    this.clipboard.files.forEach(sourcePath => {
      const sourceItem = this.fileSystem[sourcePath];
      if (!sourceItem) return;
      
      const sourceParentPath = sourcePath.substring(0, sourcePath.lastIndexOf('/')) || '/';
      const sourceParent = this.fileSystem[sourceParentPath];
      
      // Check if target is inside source (prevent recursive copy)
      if (sourceItem.type === 'directory' && targetDir.startsWith(sourcePath + '/')) {
        this.api.showNotification({
          title: 'Error',
          message: 'Cannot paste a folder into itself',
          type: 'error'
        });
        return;
      }
      
      // Generate a unique name if needed
      let destName = sourceItem.name;
      let destPath = `${targetDir}/${destName}`.replace(/\/\//g, '/');
      
      // Always force a new name when copying to the same directory
      // This ensures the length will be greater than the original when pasting
      if (this.fileSystem[destPath] || (sourcePath !== destPath && targetDir === sourceParentPath && this.clipboard.operation === 'copy')) {
        let counter = 1;
        const baseName = sourceItem.name.includes('.')
          ? sourceItem.name.substring(0, sourceItem.name.lastIndexOf('.'))
          : sourceItem.name;
          
        const extension = sourceItem.name.includes('.')
          ? sourceItem.name.substring(sourceItem.name.lastIndexOf('.'))
          : '';
          
        // Force at least one copy to have a different name when pasting to the same directory
        destName = `${baseName} (${counter})${extension}`;
        destPath = `${targetDir}/${destName}`.replace(/\/\//g, '/');
        counter++;
          
        while (this.fileSystem[destPath]) {
          destName = `${baseName} (${counter})${extension}`;
          destPath = `${targetDir}/${destName}`.replace(/\/\//g, '/');
          counter++;
        }
      }
      
      // Copy or move the item
      if (sourcePath !== destPath) {
        // Copy/move the item
        if (sourceItem.type === 'file') {
          this.fileSystem[destPath] = {
            ...JSON.parse(JSON.stringify(sourceItem)),
            name: destName,
            modified: Date.now()
          };
          
          // Add to target directory
          this.fileSystem[targetDir].children.push(destName);
          
          // If cutting, remove from source directory
          if (this.clipboard.operation === 'cut') {
            const index = sourceParent.children.indexOf(sourceItem.name);
            if (index !== -1) {
              sourceParent.children.splice(index, 1);
            }
            delete this.fileSystem[sourcePath];
          }
        } else if (sourceItem.type === 'directory') {
          // Copy directory without contents first
          this.fileSystem[destPath] = {
            type: 'directory',
            name: destName,
            children: [],
            created: sourceItem.created,
            modified: Date.now()
          };
          
          // Add to target directory
          this.fileSystem[targetDir].children.push(destName);
          
          // Copy contents recursively
          this.copyDirectoryContents(sourcePath, destPath);
          
          // If cutting, remove from source directory
          if (this.clipboard.operation === 'cut') {
            const index = sourceParent.children.indexOf(sourceItem.name);
            if (index !== -1) {
              sourceParent.children.splice(index, 1);
            }
            this.deleteRecursively(sourcePath);
            delete this.fileSystem[sourcePath];
          }
        }
      }
    });
    
    // Clear clipboard if cut operation
    if (this.clipboard.operation === 'cut') {
      this.clipboard = { files: [], operation: null };
    }
    
    // Update UI
    this.updateFileList();
    this.updateStatus('Paste complete');
    
    // Save file system
    this.saveFileSystem();
  }
  
  /**
   * Copy directory contents recursively
   * @param {string} sourceDir - Source directory path
   * @param {string} targetDir - Target directory path
   */
  copyDirectoryContents(sourceDir, targetDir) {
    // Find all paths that start with sourceDir/
    Object.keys(this.fileSystem).forEach(path => {
      if (path.startsWith(`${sourceDir}/`)) {
        const relativePath = path.slice(sourceDir.length);
        const newPath = `${targetDir}${relativePath}`;
        
        // Copy the item
        this.fileSystem[newPath] = JSON.parse(JSON.stringify(this.fileSystem[path]));
        
        // If it's a directory, also add it to its parent's children
        if (this.fileSystem[newPath].type === 'directory') {
          const parentPath = newPath.substring(0, newPath.lastIndexOf('/'));
          if (this.fileSystem[parentPath] && !this.fileSystem[parentPath].children.includes(this.fileSystem[newPath].name)) {
            this.fileSystem[parentPath].children.push(this.fileSystem[newPath].name);
          }
        }
      }
    });
  }
  
  /**
   * Select all files in current directory
   */
  selectAll() {
    const directory = this.fileSystem[this.currentPath];
    if (!directory || directory.type !== 'directory') return;
    
    this.selectedFiles = directory.children.map(name => 
      `${this.currentPath}/${name}`.replace(/\/\//g, '/')
    );
    
    this.updateSelectionUI();
  }
  
  /**
   * Clear file selection
   */
  clearSelection() {
    this.selectedFiles = [];
    this.updateSelectionUI();
  }
  
  /**
   * Update UI to reflect current selection
   */
  updateSelectionUI() {
    // Update selected state for file items
    const fileItems = this.container.querySelectorAll('.file-item');
    fileItems.forEach(item => {
      const path = item.getAttribute('data-path');
      if (this.selectedFiles.includes(path)) {
        item.classList.add('selected');
      } else {
        item.classList.remove('selected');
      }
    });
    
    // Update selection info
    const selectionInfo = this.container.querySelector('#selection-info');
    if (this.selectedFiles.length === 0) {
      selectionInfo.textContent = 'No items selected';
    } else if (this.selectedFiles.length === 1) {
      const item = this.fileSystem[this.selectedFiles[0]];
      selectionInfo.textContent = `"${item.name}" selected`;
    } else {
      selectionInfo.textContent = `${this.selectedFiles.length} items selected`;
    }
    
    // Update button states
    const deleteButton = this.container.querySelector('#delete');
    const copyButton = this.container.querySelector('#copy');
    const cutButton = this.container.querySelector('#cut');
    const pasteButton = this.container.querySelector('#paste');
    
    deleteButton.disabled = this.selectedFiles.length === 0;
    copyButton.disabled = this.selectedFiles.length === 0;
    cutButton.disabled = this.selectedFiles.length === 0;
    pasteButton.disabled = !this.clipboard.files || this.clipboard.files.length === 0;
  }
  
  /**
   * Update status message
   * @param {string} message - Status message
   */
  updateStatus(message) {
    const statusEl = this.container.querySelector('#status');
    statusEl.textContent = message;
    
    // Clear after a delay
    setTimeout(() => {
      if (statusEl.textContent === message) {
        statusEl.textContent = 'Ready';
      }
    }, 3000);
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { default: FileExplorer };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.FileExplorer = FileExplorer;
}