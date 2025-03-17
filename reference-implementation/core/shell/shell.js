/**
 * PrimeOS Shell Environment
 * 
 * The Shell forms the primary user interface for PrimeOS, providing
 * window management, application launching, and system interaction.
 * It implements the four-tier architecture using the PrimeOS framework.
 */

// Import from global modules if available, otherwise attempt to import modules
let EventBus, createComponent, PrimeStore, PrimeIdentity;

try {
  if (typeof window !== 'undefined' && window.Prime && window.Prime.EventBus) {
    // Browser environment with global Prime available
    EventBus = window.Prime.EventBus;
    
    // Create a simple component factory if not available
    createComponent = window.Prime.createComponent || function(config) {
      const id = config.id || `component-${Date.now()}-${Math.floor(Math.random() * 1000)}`;
      const component = {
        id,
        variant: config.variant || {},
        invariant: config.invariant || {},
        render: function() {
          if (typeof this.updateDesktop === 'function') {
            this.updateDesktop();
          } else if (typeof this.updateTaskbar === 'function') {
            this.updateTaskbar();
          } else if (typeof this.updateAppLauncher === 'function') {
            this.updateAppLauncher();
          } else if (typeof this.updateNotificationCenter === 'function') {
            this.updateNotificationCenter();
          }
        }
      };
      return component;
    };
    
    // Use global PrimeStore or import it
    PrimeStore = window.PrimeStore;
    PrimeIdentity = window.PrimeIdentity;
  }
} catch (error) {
  console.error('Failed to import dependencies:', error);
  
  // Create minimal mock implementations for testing
  EventBus = {
    events: {},
    subscribe: function(event, callback) {
      if (!this.events[event]) this.events[event] = [];
      this.events[event].push(callback);
      return () => this.unsubscribe(event, callback);
    },
    publish: function(event, data) {
      if (!this.events[event]) return [];
      return this.events[event].map(callback => callback(data));
    },
    unsubscribe: function(event, callback) {
      if (!this.events[event]) return false;
      const index = this.events[event].indexOf(callback);
      if (index !== -1) {
        this.events[event].splice(index, 1);
        return true;
      }
      return false;
    }
  };
  
  createComponent = function(config) {
    return {
      id: config.id || `component-${Date.now()}`,
      variant: config.variant || {},
      invariant: config.invariant || {},
      render: function() {}
    };
  };
  
  PrimeStore = function(storeName) {
    // Validate storeName and default to system if invalid
    if (!['system', 'files', 'apps', 'identity'].includes(storeName)) {
      console.warn(`Mock PrimeStore: Unknown store "${storeName}", defaulting to "system"`);
      storeName = 'system';
    }
    
    this.storeName = storeName;
    this.data = {};
    
    this.initialize = async function() {
      console.log(`Mock PrimeStore: Initialized ${this.storeName} store`);
      return true;
    };
    
    this.get = async function(key) {
      return this.data[key];
    };
    
    this.put = async function(key, value) {
      this.data[key] = value;
      return value;
    };
    
    this.query = async function() {
      return Object.values(this.data);
    };
    
    this.saveAll = async function(key, values) {
      this.data[key] = values;
      return values;
    };
  };
  
  PrimeIdentity = {
    checkSession: async function() {
      return false;
    },
    getCurrentUser: async function() {
      return null;
    },
    login: async function() {
      return true;
    },
    createUser: async function() {
      return true;
    }
  };
}

/**
 * @class Shell
 * @description The main shell environment for PrimeOS
 */
class Shell {
  constructor() {
    this.windows = [];
    this.activeWindow = null;
    this.apps = [];
    this.notifications = [];
    this.eventBus = EventBus;
    
    // Initialize store - handle both object pattern and constructor pattern
    if (typeof PrimeStore === 'function') {
      // Constructor pattern - use 'system' store instead of 'shell' to match available stores
      this.store = new PrimeStore('system');
    } else if (typeof PrimeStore === 'object') {
      // Module pattern (object with methods)
      this.store = PrimeStore;
    } else {
      console.error('PrimeStore not found or not properly initialized');
      // Create a minimal mock
      this.store = {
        storeName: 'system',
        get: async function(key) { return null; },
        put: async function(key, value) { return value; },
        query: async function() { return []; },
        saveAll: async function(key, values) { return values; }
      };
    }
    
    // Initialize identity - handle both object pattern and constructor pattern
    if (typeof PrimeIdentity === 'function') {
      // Constructor pattern
      this.identity = new PrimeIdentity();
    } else if (typeof PrimeIdentity === 'object') {
      // Module pattern (object with methods)
      this.identity = PrimeIdentity;
    } else {
      console.error('PrimeIdentity not found or not properly initialized');
      // Create a minimal mock
      this.identity = {
        checkSession: async function() { return false; },
        getCurrentUser: async function() { return null; },
        login: async function() { return true; },
        createUser: async function() { return true; }
      };
    }
    
    // Register shell events
    this.eventBus.subscribe('shell:launch-app', this.launchApp.bind(this));
    this.eventBus.subscribe('shell:close-window', this.closeWindow.bind(this));
    this.eventBus.subscribe('shell:minimize-window', this.minimizeWindow.bind(this));
    this.eventBus.subscribe('shell:maximize-window', this.maximizeWindow.bind(this));
    this.eventBus.subscribe('shell:focus-window', this.focusWindow.bind(this));
    this.eventBus.subscribe('shell:show-notification', this.showNotification.bind(this));
    this.eventBus.subscribe('shell:dismiss-notification', this.dismissNotification.bind(this));
    this.eventBus.subscribe('shell:update-window-title', this.updateWindowTitle.bind(this));
    
    // Initialize desktop
    this.desktop = createComponent({
      id: 'desktop',
      variant: {
        windows: [],
        notifications: [],
        apps: [],
        activeWindowId: null
      },
      invariant: {
        render: function() {
          this.updateDesktop();
        },
        handleEvent: function(event) {
          // Handle desktop-level events
          if (event.type === 'click' && event.target.matches('.desktop')) {
            EventBus.publish('shell:focus-desktop');
          }
        }
      }
    });
    
    // Initialize taskbar
    this.taskbar = createComponent({
      id: 'taskbar',
      variant: {
        apps: [],
        openWindows: []
      },
      invariant: {
        render: function() {
          this.updateTaskbar();
        },
        launchApp: function(appId) {
          EventBus.publish('shell:launch-app', { appId });
        }
      }
    });
    
    // Initialize apps array
    this.apps = [];
    
    // Initialize app launcher
    this.appLauncher = createComponent({
      id: 'app-launcher',
      variant: {
        visible: false, // Ensure launcher is initially hidden
        apps: [],
        searchQuery: '',
        filteredApps: []
      },
      invariant: {
        render: function() {
          this.updateAppLauncher();
        },
        toggleVisible: function() {
          this.variant.visible = !this.variant.visible;
          EventBus.publish('shell:app-launcher-toggled', { visible: this.variant.visible });
        },
        search: function(query) {
          this.variant.searchQuery = query;
          // Filter apps based on query
          this.variant.filteredApps = this.variant.apps.filter(app => 
            app.name.toLowerCase().includes(query.toLowerCase()) ||
            app.description.toLowerCase().includes(query.toLowerCase())
          );
        }
      }
    });
    
    // Initialize notification center
    this.notificationCenter = createComponent({
      id: 'notification-center',
      variant: {
        visible: false,
        notifications: []
      },
      invariant: {
        render: function() {
          this.updateNotificationCenter();
        },
        toggleVisible: function() {
          this.variant.visible = !this.variant.visible;
          EventBus.publish('shell:notification-center-toggled', { visible: this.variant.visible });
        },
        dismissNotification: function(notificationId) {
          EventBus.publish('shell:dismiss-notification', { notificationId });
        }
      }
    });
  }
  
  /**
   * Initialize the shell environment
   * @returns {Promise<void>}
   */
  async initialize() {
    try {
      console.log('Initializing PrimeOS Shell...');
      
      // Initialize store first if it has an initialize method
      if (this.store && typeof this.store.initialize === 'function') {
        await this.store.initialize();
      }
      
      // Initialize identity provider if it has an initialize method
      if (this.identity && typeof this.identity.initialize === 'function') {
        await this.identity.initialize();
      }
      
      // Load available applications
      await this.loadApplications();
      
      // Render shell components first to ensure DOM elements exist
      this.renderShell();
      
      // Now load user preferences (DOM elements will be available for preference application)
      await this.loadPreferences();
      
      // Check user authentication with improved error handling
      let isAuthenticated = false;
      try {
        console.log('Checking user authentication...');
        isAuthenticated = await this.identity.checkSession();
        console.log('Authentication check result:', isAuthenticated);
      } catch (authError) {
        console.error('Authentication check failed:', authError);
        isAuthenticated = false;
      }
      
      // Show login screen if not authenticated
      if (!isAuthenticated) {
        console.log('User is not authenticated, showing login screen');
        this.showLoginScreen();
      } else {
        console.log('User is authenticated, proceeding with shell initialization');
      }
      
      console.log('PrimeOS Shell initialized');
      
      // Publish shell ready event
      this.eventBus.publish('shell:ready', { timestamp: Date.now() });
    } catch (error) {
      console.error('Failed to initialize shell:', error);
      
      // Show login screen even if initialization fails
      try {
        console.log('Showing login screen due to initialization failure');
        this.showLoginScreen();
      } catch (loginError) {
        console.error('Failed to show login screen after initialization error:', loginError);
      }
      
      throw error;
    }
  }
  
  /**
   * Load available applications
   * @returns {Promise<void>}
   */
  async loadApplications() {
    try {
      // Fetch installed apps from storage - use 'apps' instead of 'applications'
      // to match the store name defined in primestore.js
      const apps = await this.store.query('apps');
      if (apps && apps.length > 0) {
        this.apps = apps;
      } else {
        // Load default applications if none are found
        this.apps = [
          {
            id: 'file-explorer',
            name: 'File Explorer',
            icon: '📁',
            description: 'Browse and manage your files',
            path: '/reference-implementation/apps/file-explorer/index.js'
          },
          {
            id: 'text-editor',
            name: 'Text Editor',
            icon: '📝',
            description: 'Create and edit documents',
            path: '/reference-implementation/apps/text-editor/index.js'
          },
          {
            id: 'calculator',
            name: 'Calculator',
            icon: '🧮',
            description: 'Perform calculations',
            path: '/reference-implementation/apps/calculator/index.js'
          }
        ];
        
        // Store default apps in the correct store ('apps' instead of 'applications')
        await this.store.saveAll('apps', this.apps);
      }
      
      // Try to detect installed applications from the filesystem
      try {
        // We can't directly access the filesystem in the browser,
        // but in a real system we would scan for installed apps.
        // For now, we'll just make sure our three demo apps are registered.
        
        // Make sure our three demo apps are included
        const requiredApps = [
          {
            id: 'file-explorer',
            name: 'File Explorer',
            icon: '📁',
            description: 'Browse and manage your files',
            path: '/reference-implementation/apps/file-explorer/index.js'
          },
          {
            id: 'text-editor',
            name: 'Text Editor',
            icon: '📝',
            description: 'Create and edit documents',
            path: '/reference-implementation/apps/text-editor/index.js'
          },
          {
            id: 'calculator',
            name: 'Calculator',
            icon: '🧮',
            description: 'Perform calculations',
            path: '/reference-implementation/apps/calculator/index.js'
          }
        ];
        
        // Add any missing apps
        for (const app of requiredApps) {
          if (!this.apps.find(a => a.id === app.id)) {
            this.apps.push(app);
          }
        }
        
        // Store the updated app list
        await this.store.saveAll('apps', this.apps);
      } catch (error) {
        console.warn('Failed to scan for installed applications:', error);
      }
      
      // Update app launcher component
      if (this.appLauncher && this.appLauncher.variant) {
        this.appLauncher.variant.apps = this.apps;
        // Make sure filteredApps is initialized with all apps initially
        this.appLauncher.variant.filteredApps = [...this.apps];
        
        // Debug the apps array to make sure it's correct
        console.log('Available apps:', this.apps.map(app => `${app.name} (${app.id})`).join(', '));
        console.log(`Initialized app launcher with ${this.apps.length} apps`);
      }
      
      if (this.taskbar && this.taskbar.variant) {
        this.taskbar.variant.apps = this.apps;
      }
      
      console.log(`Loaded ${this.apps.length} applications`);
    } catch (error) {
      console.error('Failed to load applications:', error);
      // Handle error - show notification
      this.showNotification({
        type: 'error',
        title: 'Application Error',
        message: 'Failed to load applications. Some features may be unavailable.',
        timeout: 5000
      });
    }
  }
  
  /**
   * Load user preferences
   * @returns {Promise<void>}
   */
  async loadPreferences() {
    try {
      const currentUser = await this.identity.getCurrentUser();
      if (!currentUser) return;
      
      // We'll store preferences in the 'system' store as that's one of the stores defined in primestore.js
      const prefStore = new PrimeStore('system');
      
      // Initialize the store before using it
      if (typeof prefStore.initialize === 'function') {
        await prefStore.initialize();
      }
      
      const prefKey = `user_preferences_${currentUser.id}`;
      const preferences = await prefStore.get(prefKey);
      
      // Default preferences
      const defaultPrefs = {
        id: prefKey,
        type: 'preferences',
        theme: 'light',
        fontSize: '16px',
        taskbarPosition: 'bottom'
      };
      
      // Use stored preferences or defaults
      const prefs = preferences || defaultPrefs;
      
      try {
        // Apply theme if document root exists
        if (prefs.theme && document.documentElement) {
          document.documentElement.setAttribute('data-theme', prefs.theme);
        }
        
        // Apply font size if document root exists
        if (prefs.fontSize && document.documentElement) {
          document.documentElement.style.setProperty('--font-size-base', prefs.fontSize);
        }
        
        // Apply taskbar position if element exists
        const taskbar = document.getElementById('taskbar');
        if (prefs.taskbarPosition && taskbar) {
          taskbar.setAttribute('data-position', prefs.taskbarPosition);
        } else {
          console.log('Taskbar element not found. Will apply preferences after rendering.');
          
          // Save preferences to apply after rendering
          this._pendingPreferences = {
            taskbarPosition: prefs.taskbarPosition
          };
        }
        
        // Save default preferences if none existed
        if (!preferences) {
          await prefStore.put(defaultPrefs);
        }
        
        console.log('Applied user preferences');
      } catch (e) {
        console.error('Error applying preferences:', e);
      }
    } catch (error) {
      console.error('Failed to load preferences:', error);
    }
  }
  
  /**
   * Render the shell UI
   */
  renderShell() {
    try {
      // Create shell container if it doesn't exist
      let shellContainer = document.getElementById('prime-shell');
      if (!shellContainer) {
        shellContainer = document.createElement('div');
        shellContainer.id = 'prime-shell';
        if (document.body) {
          document.body.appendChild(shellContainer);
        } else {
          console.warn('Document body not available, creating shell container will be deferred');
          // For testing purposes, we might need to defer this
          setTimeout(() => {
            if (document.body) {
              document.body.appendChild(shellContainer);
              this.continueRenderShell(shellContainer);
            } else {
              console.error('Document body still not available, shell rendering failed');
            }
          }, 100);
          return; // Exit early and wait for the deferred rendering
        }
      }
      
      this.continueRenderShell(shellContainer);
    } catch (error) {
      console.error('Error rendering shell:', error);
      // Create a minimal DOM for testing if needed
      if (typeof window !== 'undefined' && window._testMode) {
        this.createTestShellDOM();
      }
    }
  }
  
  /**
   * Continue shell rendering with the container
   * @private
   * @param {HTMLElement} shellContainer - The shell container element
   */
  continueRenderShell(shellContainer) {
    // Create desktop, taskbar, and other shell elements
    shellContainer.innerHTML = `
      <div id="desktop" class="desktop">
        <div id="windows-container" class="windows-container"></div>
      </div>
      <div id="taskbar" class="taskbar">
        <div class="start-button" id="start-button">
          <span class="icon">P</span>
        </div>
        <div class="taskbar-items" id="taskbar-items"></div>
        <div class="system-tray" id="system-tray">
          <div class="clock" id="clock"></div>
          <div class="notification-icon" id="notification-icon">
            <span class="icon">🔔</span>
          </div>
        </div>
      </div>
      <div id="app-launcher" class="app-launcher hidden">
        <div class="app-launcher-search">
          <input type="text" placeholder="Search applications..." id="app-search">
        </div>
        <div class="app-grid" id="app-grid"></div>
      </div>
      <div id="notification-center" class="notification-center hidden">
        <div class="notification-header">
          <h3>Notifications</h3>
          <button id="clear-notifications">Clear All</button>
        </div>
        <div class="notifications-list" id="notifications-list"></div>
      </div>
    `;
    
    // Ensure app launcher is hidden by default
    if (this.appLauncher && this.appLauncher.variant) {
      this.appLauncher.variant.visible = false;
    }
    
    // Initialize event listeners
    this.initializeEventListeners();
    
    // Update components
    if (this.desktop && typeof this.desktop.render === 'function') {
      this.desktop.render();
    }
    
    if (this.taskbar && typeof this.taskbar.render === 'function') {
      this.taskbar.render();
    }
    
    if (this.appLauncher && typeof this.appLauncher.render === 'function') {
      this.appLauncher.render();
    }
    
    if (this.notificationCenter && typeof this.notificationCenter.render === 'function') {
      this.notificationCenter.render();
    }
    
    // Apply pending preferences if any
    this.applyPendingPreferences();
    
    // Start clock
    this.startClock();
  }
  
  /**
   * Apply any preferences that couldn't be applied earlier because DOM elements weren't ready
   * @private
   */
  applyPendingPreferences() {
    if (!this._pendingPreferences) return;
    
    try {
      // Apply taskbar position
      if (this._pendingPreferences.taskbarPosition) {
        const taskbar = document.getElementById('taskbar');
        if (taskbar) {
          taskbar.setAttribute('data-position', this._pendingPreferences.taskbarPosition);
          console.log('Applied pending taskbar position preference');
        }
      }
      
      // Clear pending preferences after applying
      this._pendingPreferences = null;
    } catch (error) {
      console.error('Error applying pending preferences:', error);
    }
  }
  
  /**
   * Create a minimal DOM structure for testing
   * @private
   */
  createTestShellDOM() {
    if (typeof document === 'undefined') return;
    
    // Create test container
    const testContainer = document.createElement('div');
    testContainer.id = 'test-shell-container';
    
    // Create minimal shell structure
    testContainer.innerHTML = `
      <div id="desktop" class="desktop"></div>
      <div id="taskbar" class="taskbar"></div>
      <div id="app-launcher" class="app-launcher hidden"></div>
      <div id="notification-center" class="notification-center hidden"></div>
    `;
    
    // Append to document body if available
    if (document.body) {
      document.body.appendChild(testContainer);
    }
    
    console.log('Created minimal test shell DOM');
  }
  
  /**
   * Initialize shell event listeners
   */
  initializeEventListeners() {
    try {
      // Start button - Direct implementation for reliability
      const startButton = document.getElementById('start-button');
      if (startButton) {
        console.log('Adding click handler to start button');
        startButton.addEventListener('click', (e) => {
          e.stopPropagation(); // Prevent event bubbling
          console.log('Start button clicked');
          
          // Direct toggle of app launcher visibility for reliability
          const appLauncher = document.getElementById('app-launcher');
          if (appLauncher) {
            const isHidden = appLauncher.classList.contains('hidden');
            console.log('App launcher visibility:', isHidden ? 'hidden -> visible' : 'visible -> hidden');
            
            if (isHidden) {
              appLauncher.classList.remove('hidden');
              // Update component state if available
              if (this.appLauncher && this.appLauncher.variant) {
                this.appLauncher.variant.visible = true;
              }
              
              // Force update the launcher to ensure apps are displayed
              this.updateAppLauncherContent();
            } else {
              appLauncher.classList.add('hidden');
              // Update component state if available
              if (this.appLauncher && this.appLauncher.variant) {
                this.appLauncher.variant.visible = false;
              }
            }
          } else {
            console.error('App launcher element not found in DOM');
          }
        });
      } else {
        console.error('Start button not found in DOM');
      }
      
      // Notification icon - Same direct approach
      const notificationIcon = document.getElementById('notification-icon');
      if (notificationIcon) {
        notificationIcon.addEventListener('click', (e) => {
          e.stopPropagation(); // Prevent event bubbling
          
          // Direct toggle of notification center visibility for reliability
          const notificationCenter = document.getElementById('notification-center');
          if (notificationCenter) {
            const isHidden = notificationCenter.classList.contains('hidden');
            
            if (isHidden) {
              notificationCenter.classList.remove('hidden');
              // Update component state if available
              if (this.notificationCenter && this.notificationCenter.variant) {
                this.notificationCenter.variant.visible = true;
              }
              
              // Force update to ensure notifications are displayed
              this.updateNotificationCenter();
            } else {
              notificationCenter.classList.add('hidden');
              // Update component state if available
              if (this.notificationCenter && this.notificationCenter.variant) {
                this.notificationCenter.variant.visible = false;
              }
            }
          } else {
            console.error('Notification center element not found in DOM');
          }
        });
      }
      
      // App search with direct DOM access
      const appSearch = document.getElementById('app-search');
      if (appSearch) {
        appSearch.addEventListener('input', (e) => {
          const searchQuery = e.target.value.trim().toLowerCase();
          console.log(`Search input: "${searchQuery}"`);
          
          if (this.appLauncher && this.appLauncher.variant) {
            // Set the search query in the component
            this.appLauncher.variant.searchQuery = searchQuery;
            
            // Filter apps directly
            if (Array.isArray(this.appLauncher.variant.apps)) {
              this.appLauncher.variant.filteredApps = this.appLauncher.variant.apps.filter(app => 
                (app.name?.toLowerCase().includes(searchQuery)) || 
                (app.description?.toLowerCase().includes(searchQuery))
              );
              
              console.log(`Filtered apps: ${this.appLauncher.variant.filteredApps.length} matches`);
              
              // Update the UI by updating the app launcher DOM directly
              this.updateAppLauncherContent();
            }
          }
        });
      }
      
      // Clear notifications
      const clearNotificationsBtn = document.getElementById('clear-notifications');
      if (clearNotificationsBtn) {
        clearNotificationsBtn.addEventListener('click', () => {
          this.clearAllNotifications();
        });
      }
      
      // Close app launcher when clicking outside
      document.addEventListener('click', (e) => {
        // Direct DOM element checks for reliability
        const appLauncher = document.getElementById('app-launcher');
        const startButton = document.getElementById('start-button');
        
        if (appLauncher && !appLauncher.classList.contains('hidden')) {
          if (!appLauncher.contains(e.target) && !startButton.contains(e.target)) {
            console.log('Click outside app launcher, hiding it');
            appLauncher.classList.add('hidden');
            
            // Update component state if available
            if (this.appLauncher && this.appLauncher.variant) {
              this.appLauncher.variant.visible = false;
            }
          }
        }
        
        // Same for notification center
        const notificationCenter = document.getElementById('notification-center');
        const notificationIcon = document.getElementById('notification-icon');
        
        if (notificationCenter && !notificationCenter.classList.contains('hidden')) {
          if (!notificationCenter.contains(e.target) && !notificationIcon.contains(e.target)) {
            notificationCenter.classList.add('hidden');
            
            // Update component state if available
            if (this.notificationCenter && this.notificationCenter.variant) {
              this.notificationCenter.variant.visible = false;
            }
          }
        }
      });
    } catch (error) {
      console.error('Error initializing event listeners:', error);
    }
  }
  
  /**
   * Update desktop component
   */
  updateDesktop() {
    const container = document.getElementById('windows-container');
    if (!container) return;
    
    // Get the current windows in the DOM
    const currentWindowEls = {};
    Array.from(container.querySelectorAll('.window')).forEach(el => {
      const windowId = el.getAttribute('data-window-id');
      if (windowId) {
        currentWindowEls[windowId] = el;
      }
    });
    
    // Clear container but don't destroy elements yet
    container.innerHTML = '';
    
    // Add windows in z-index order, reusing elements when possible
    this.windows.forEach(window => {
      // Check if we have an existing element for this window
      if (currentWindowEls[window.id]) {
        // Update the existing element
        const windowEl = currentWindowEls[window.id];
        
        // Update window classes for minimized/maximized state
        windowEl.className = 'window' + (window.minimized ? ' minimized' : '') + (window.maximized ? ' maximized' : '') + 
          (window.id === this.activeWindow?.id ? ' active' : '');
        
        // Set z-index based on window status
        windowEl.style.zIndex = window.id === this.activeWindow?.id ? '1000' : window.zIndex || '10';
        
        // Update maximize button text
        const maxButton = windowEl.querySelector('.window-maximize');
        if (maxButton) {
          maxButton.textContent = window.maximized ? '❐' : '□';
        }
        
        // Update position and size for non-maximized windows
        if (!window.maximized) {
          windowEl.style.width = `${window.width}px`;
          windowEl.style.height = `${window.height}px`;
          windowEl.style.left = `${window.x}px`;
          windowEl.style.top = `${window.y}px`;
        }
        
        container.appendChild(windowEl);
      } else {
        // Create a new window element
        const windowEl = this.createWindowElement(window);
        
        // Add active class and higher z-index if it's the active window
        if (window.id === this.activeWindow?.id) {
          windowEl.classList.add('active');
          windowEl.style.zIndex = '1000';
        }
        
        container.appendChild(windowEl);
      }
    });
  }
  
  /**
   * Update taskbar component
   */
  updateTaskbar() {
    try {
      const taskbarItems = document.getElementById('taskbar-items');
      if (!taskbarItems) return;
      
      // Clear existing items
      taskbarItems.innerHTML = '';
      
      // Add open windows to taskbar
      this.windows.forEach(window => {
        const item = document.createElement('div');
        item.className = 'taskbar-item' + (window.id === this.activeWindow?.id ? ' active' : '');
        item.setAttribute('data-window-id', window.id);
        
        // Find app info
        const app = this.apps.find(a => a.id === window.appId);
        
        item.innerHTML = `
          <span class="icon">${app?.icon || '📄'}</span>
          <span class="title">${window.title}</span>
        `;
        
        item.addEventListener('click', () => {
          if (window.id === this.activeWindow?.id && !window.minimized) {
            // If already active, minimize it
            this.minimizeWindow(window.id);
          } else {
            // Otherwise focus it (this will unminimize if needed)
            this.focusWindow(window.id);
          }
        });
        
        taskbarItems.appendChild(item);
      });
      
      // Update clock
      this.updateClock();
    } catch (error) {
      console.error('Error updating taskbar:', error);
    }
  }
  
  /**
   * Update app launcher component
   */
  updateAppLauncher() {
    const appGrid = document.getElementById('app-grid');
    const launcher = document.getElementById('app-launcher');
    
    if (!appGrid || !launcher) {
      console.warn('App launcher elements not found in DOM');
      return;
    }
    
    // Get the correct component and variant
    let appLauncher = this.appLauncher;
    if (!appLauncher || !appLauncher.variant) {
      console.warn('App launcher component not initialized properly');
      // Create variant object if it doesn't exist
      appLauncher = this.appLauncher = this.appLauncher || {};
      appLauncher.variant = appLauncher.variant || {};
      // Ensure launcher is initially hidden
      appLauncher.variant.visible = false;
    }
    
    // Update visibility
    if (appLauncher.variant.visible) {
      launcher.classList.remove('hidden');
    } else {
      launcher.classList.add('hidden');
    }
    
    // Clear existing apps
    appGrid.innerHTML = '';
    
    // Get apps to display (filtered or all)
    const appsToDisplay = appLauncher.variant.searchQuery ? 
      appLauncher.variant.filteredApps : 
      appLauncher.variant.apps;
    
    // Check if apps array exists
    if (!Array.isArray(appsToDisplay)) {
      console.warn('No apps to display');
      
      // Fallback to using the apps from the shell instance
      if (Array.isArray(this.apps) && this.apps.length > 0) {
        console.log('Using fallback apps array from shell instance');
        appLauncher.variant.apps = this.apps;
        appLauncher.variant.filteredApps = this.apps;
      } else {
        // Add default apps as last resort
        console.log('Using default apps as fallback');
        const defaultApps = [
          {
            id: 'calculator',
            name: 'Calculator',
            icon: '🧮',
            description: 'Perform calculations',
            path: '/apps/calculator/index.js'
          },
          {
            id: 'text-editor',
            name: 'Text Editor',
            icon: '📝',
            description: 'Create and edit documents',
            path: '/apps/text-editor/index.js'
          },
          {
            id: 'file-explorer',
            name: 'File Explorer',
            icon: '📁',
            description: 'Browse and manage your files',
            path: '/apps/file-explorer/index.js'
          }
        ];
        
        appLauncher.variant.apps = defaultApps;
        appLauncher.variant.filteredApps = defaultApps;
      }
      
      // Recursively call this function again with the updated apps array
      return this.updateAppLauncher();
    }
    
    // Filter out user preferences and other non-app entries
    const validApps = appsToDisplay.filter(app => {
      // Skip null or undefined apps
      if (!app || !app.id) return false;
      
      // Skip user preference entries
      if (app.id.startsWith('user_preferences_')) return false;
      
      // Skip app preference entries
      if (app.id.startsWith('app_preferences_')) return false;
      
      // Skip if name is missing (essential for display)
      if (!app.name) return false;
      
      // Valid app
      return true;
    });
    
    // Add apps to grid
    validApps.forEach(app => {
      const appItem = document.createElement('div');
      appItem.className = 'app-item';
      appItem.setAttribute('data-app-id', app.id);
      
      appItem.innerHTML = `
        <div class="app-icon">${app.icon || '📄'}</div>
        <div class="app-name">${app.name}</div>
      `;
      
      // Add debugging info to the console for this app
      console.log(`Adding app to launcher: ${app.name} (${app.id})`, app);
      
      // Make the app item clearly interactive with cursor styling
      appItem.style.cursor = 'pointer';
      
      // Add a hover effect to make it more obvious it's clickable
      appItem.addEventListener('mouseenter', () => {
        appItem.style.transform = 'scale(1.05)';
        appItem.style.transition = 'transform 0.2s';
      });
      
      appItem.addEventListener('mouseleave', () => {
        appItem.style.transform = 'scale(1)';
      });
      
      // Add click event with debugging
      appItem.addEventListener('click', () => {
        console.log(`App ${app.id} clicked, launching...`);
        this.launchApp({ appId: app.id });
        
        if (appLauncher.invariant && typeof appLauncher.invariant.toggleVisible === 'function') {
          appLauncher.invariant.toggleVisible.call(appLauncher);
        }
      });
      
      appGrid.appendChild(appItem);
    });
    
    // Log completion
    console.log(`Updated app launcher with ${validApps.length} valid apps`);
  }
  
  /**
   * Update notification center component
   */
  updateNotificationCenter() {
    const notificationsList = document.getElementById('notifications-list');
    const center = document.getElementById('notification-center');
    
    if (!notificationsList || !center) {
      console.warn('Notification center elements not found in DOM');
      return;
    }
    
    // Get the correct component and variant
    const notificationCenter = this.notificationCenter;
    if (!notificationCenter || !notificationCenter.variant) {
      console.warn('Notification center component not initialized properly');
      return;
    }
    
    // Update visibility
    if (notificationCenter.variant.visible) {
      center.classList.remove('hidden');
    } else {
      center.classList.add('hidden');
    }
    
    // Clear existing notifications
    notificationsList.innerHTML = '';
    
    // Check if notifications array exists
    if (!Array.isArray(notificationCenter.variant.notifications)) {
      notificationCenter.variant.notifications = [];
    }
    
    // Add notifications
    notificationCenter.variant.notifications.forEach(notification => {
      if (!notification || !notification.id) return;
      
      const notificationEl = document.createElement('div');
      notificationEl.className = `notification notification-${notification.type || 'info'}`;
      notificationEl.setAttribute('data-notification-id', notification.id);
      
      notificationEl.innerHTML = `
        <div class="notification-header">
          <h4>${notification.title || 'Notification'}</h4>
          <button class="close-notification">×</button>
        </div>
        <div class="notification-body">
          <p>${notification.message || ''}</p>
        </div>
        <div class="notification-timestamp">
          ${this.formatTimestamp(notification.timestamp || Date.now())}
        </div>
      `;
      
      notificationEl.querySelector('.close-notification').addEventListener('click', () => {
        if (notificationCenter.invariant && typeof notificationCenter.invariant.dismissNotification === 'function') {
          notificationCenter.invariant.dismissNotification.call(notificationCenter, notification.id);
        } else {
          this.dismissNotification({ notificationId: notification.id });
        }
      });
      
      notificationsList.appendChild(notificationEl);
    });
    
    // Show empty state if no notifications
    if (notificationCenter.variant.notifications.length === 0) {
      const emptyState = document.createElement('div');
      emptyState.className = 'empty-notifications';
      emptyState.innerHTML = '<p>No notifications</p>';
      notificationsList.appendChild(emptyState);
    }
    
    // Update notification badge
    const notificationIcon = document.getElementById('notification-icon');
    if (!notificationIcon) return;
    
    const badge = notificationIcon.querySelector('.badge');
    if (notificationCenter.variant.notifications.length > 0) {
      if (!badge) {
        const newBadge = document.createElement('span');
        newBadge.className = 'badge';
        newBadge.textContent = notificationCenter.variant.notifications.length;
        notificationIcon.appendChild(newBadge);
      } else {
        badge.textContent = notificationCenter.variant.notifications.length;
      }
    } else if (badge) {
      badge.remove();
    }
  }
  
  /**
   * Start the taskbar clock
   */
  startClock() {
    // First update immediately
    this.updateClock();
    
    // Don't create duplicate intervals
    if (this._clockInterval) {
      clearInterval(this._clockInterval);
    }
    
    // Update every second
    this._clockInterval = setInterval(() => this.updateClock(), 1000);
    
    // Store interval ID so it can be cleared if needed
    return this._clockInterval;
  }
  
  /**
   * Update the taskbar clock
   */
  updateClock() {
    try {
      const clock = document.getElementById('clock');
      if (clock) {
        const now = new Date();
        clock.textContent = now.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
      }
    } catch (error) {
      console.warn('Error updating clock:', error);
    }
  }
  
  /**
   * Format a timestamp for display
   * @param {number} timestamp - Unix timestamp
   * @returns {string} Formatted time
   */
  formatTimestamp(timestamp) {
    try {
      if (!timestamp) {
        timestamp = Date.now();
      }
      
      const date = new Date(timestamp);
      return date.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
    } catch (error) {
      console.warn('Error formatting timestamp:', error);
      return new Date().toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
    }
  }
  
  /**
   * Update app launcher content with current filtered apps
   * Ensures icons are visible and clickable during search
   */
  updateAppLauncherContent() {
    try {
      const appLauncherGrid = document.querySelector('#app-launcher .app-grid');
      if (!appLauncherGrid) return;
      
      // Store the scroll position
      const scrollTop = appLauncherGrid.scrollTop;
      
      // Clear existing apps
      appLauncherGrid.innerHTML = '';
      
      // Get the apps to display (filtered or all)
      let appsToDisplay = this.appLauncher?.variant?.filteredApps || 
                         this.appLauncher?.variant?.apps || 
                         [];
      
      // Ensure we only have valid apps with required properties
      appsToDisplay = appsToDisplay.filter(app => 
        app && app.id && app.name && 
        // Make sure this is a real app that can be launched
        (app.path || app.launch || typeof app.initialize === 'function')
      );
      
      console.log(`Updating app launcher with ${appsToDisplay.length} valid apps`);
      
      // Add each app to the grid
      appsToDisplay.forEach(app => {
        if (!app) return; // Skip undefined apps
        
        const appElement = document.createElement('div');
        appElement.className = 'app-item';
        appElement.setAttribute('data-app-id', app.id || app.name || 'unknown');
        
        // Use app.icon if available, otherwise a default icon
        let iconClass = 'fa-cube'; // Default icon
        
        if (app.icon) {
          // For emoji icons or raw icons, use them directly
          if (app.icon.includes('📁') || app.icon.includes('📝') || app.icon.includes('🧮')) {
            appElement.innerHTML = `
              <div class="app-icon">${app.icon}</div>
              <div class="app-name">${app.name || 'Unnamed App'}</div>
            `;
            appLauncherGrid.appendChild(appElement);
            
            // Add click event and continue to next app
            const self = this;
            appElement.addEventListener('click', function() {
              console.log(`Launching app: ${app.name}`);
              self.launchApp(app);
              
              const launcher = document.getElementById('app-launcher');
              if (launcher) launcher.classList.add('hidden');
              
              if (self.appLauncher && self.appLauncher.variant) {
                self.appLauncher.variant.visible = false;
              }
            });
            
            return; // Skip the rest of the current iteration
          }
          
          // For FontAwesome icons
          iconClass = app.icon.startsWith('fa-') ? app.icon : `fa-${app.icon}`;
        }
        
        appElement.innerHTML = `
          <div class="app-icon"><i class="fas ${iconClass}"></i></div>
          <div class="app-name">${app.name || 'Unnamed App'}</div>
        `;
        
        appLauncherGrid.appendChild(appElement);
        
        // Add click event with proper binding
        const self = this; // Preserve "this" context
        appElement.addEventListener('click', function() {
          console.log(`Launching app: ${app.name}`);
          self.launchApp(app);
          
          // Hide the launcher after clicking
          const launcher = document.getElementById('app-launcher');
          if (launcher) launcher.classList.add('hidden');
          
          if (self.appLauncher && self.appLauncher.variant) {
            self.appLauncher.variant.visible = false;
          }
        });
      });
      
      // If no apps match, show a message
      if (appsToDisplay.length === 0) {
        const noAppsMessage = document.createElement('div');
        noAppsMessage.className = 'no-apps-message';
        noAppsMessage.textContent = 'No matching apps found';
        noAppsMessage.style.gridColumn = '1 / span 4'; // Span all columns
        noAppsMessage.style.textAlign = 'center';
        noAppsMessage.style.padding = '20px';
        noAppsMessage.style.color = 'rgba(255, 255, 255, 0.7)';
        appLauncherGrid.appendChild(noAppsMessage);
      }
      
      // Restore scroll position
      appLauncherGrid.scrollTop = scrollTop;
    } catch (error) {
      console.error('Error updating app launcher content:', error);
    }
  }
  
  /**
   * Create a window element
   * @param {Object} window - Window configuration
   * @returns {HTMLElement} Window element
   */
  createWindowElement(window) {
    const windowEl = document.createElement('div');
    windowEl.className = 'window' + (window.minimized ? ' minimized' : '') + (window.maximized ? ' maximized' : '');
    windowEl.id = `window-${window.id}`;
    windowEl.setAttribute('data-window-id', window.id);
    
    // Set z-index to be visible
    windowEl.style.zIndex = window.zIndex || 10;
    
    // Set position and size for non-maximized windows
    if (!window.maximized) {
      windowEl.style.width = `${window.width}px`;
      windowEl.style.height = `${window.height}px`;
      windowEl.style.left = `${window.x}px`;
      windowEl.style.top = `${window.y}px`;
    }
    
    // Create the window elements
    const titlebar = document.createElement('div');
    titlebar.className = 'window-titlebar';
    titlebar.innerHTML = `
      <div class="window-title">${window.title}</div>
      <div class="window-controls">
        <button class="window-control window-minimize">_</button>
        <button class="window-control window-maximize">${window.maximized ? '❐' : '□'}</button>
        <button class="window-control window-close">×</button>
      </div>
    `;
    
    // Create window content separately to ensure it exists before app initialization
    const contentEl = document.createElement('div');
    contentEl.className = 'window-content';
    contentEl.id = `window-content-${window.id}`;
    
    // Create resize handle
    const resizeHandle = document.createElement('div');
    resizeHandle.className = 'window-resize-handle';
    
    // Append elements to window
    windowEl.appendChild(titlebar);
    windowEl.appendChild(contentEl);
    windowEl.appendChild(resizeHandle);
    
    // Debug output to confirm content element creation
    console.log(`Created window content element with ID: window-content-${window.id}`);
    
    // Add event listeners for window controls
    const self = this; // Store reference to this
    
    // Add minimize button handler
    const minimizeBtn = windowEl.querySelector('.window-minimize');
    if (minimizeBtn) {
      minimizeBtn.addEventListener('click', function(e) {
        e.stopPropagation(); // Prevent event bubbling
        console.log('Minimize button clicked for window:', window.id);
        self.minimizeWindow(window.id);
      });
    }
    
    // Add maximize button handler
    const maximizeBtn = windowEl.querySelector('.window-maximize');
    if (maximizeBtn) {
      maximizeBtn.addEventListener('click', function(e) {
        e.stopPropagation(); // Prevent event bubbling
        console.log('Maximize button clicked for window:', window.id);
        self.maximizeWindow(window.id);
      });
    }
    
    // Add close button handler
    const closeBtn = windowEl.querySelector('.window-close');
    if (closeBtn) {
      closeBtn.addEventListener('click', function(e) {
        e.stopPropagation(); // Prevent event bubbling
        console.log('Close button clicked for window:', window.id);
        self.closeWindow(window.id);
      });
    }
    
    // Make window draggable
    this.makeWindowDraggable(windowEl);
    
    // Make window resizable
    this.makeWindowResizable(windowEl);
    
    // Focus window on click
    windowEl.addEventListener('mousedown', () => {
      this.focusWindow(window.id);
    });
    
    return windowEl;
  }
  
  /**
   * Make a window draggable
   * @param {HTMLElement} windowEl - Window element
   */
  makeWindowDraggable(windowEl) {
    const titlebar = windowEl.querySelector('.window-titlebar');
    let isDragging = false;
    let offsetX, offsetY;
    const self = this; // Store reference to this
    
    titlebar.addEventListener('mousedown', function(e) {
      // Ignore if clicking on a control button
      if (e.target.closest('.window-control')) return;
      
      // Get the window ID
      const windowId = windowEl.getAttribute('data-window-id');
      
      // Focus window
      self.focusWindow(windowId);
      
      // Get window data
      const window = self.windows.find(w => w.id === windowId);
      
      // Don't drag if window not found or if maximized
      if (!window) return;
      if (window.maximized) return;
      
      isDragging = true;
      offsetX = e.clientX - windowEl.offsetLeft;
      offsetY = e.clientY - windowEl.offsetTop;
      
      // Add global event listeners
      document.addEventListener('mousemove', onMouseMove);
      document.addEventListener('mouseup', onMouseUp);
    });
    
    function onMouseMove(e) {
      if (!isDragging) return;
      
      windowEl.style.left = `${e.clientX - offsetX}px`;
      windowEl.style.top = `${e.clientY - offsetY}px`;
    }
    
    function onMouseUp() {
      isDragging = false;
      
      // Update window position in our state
      const windowId = windowEl.getAttribute('data-window-id');
      
      // Only update if windowEl still exists and has valid style properties
      if (windowEl && windowEl.style && windowEl.style.left && windowEl.style.top) {
        const window = self.windows.find(w => w.id === windowId);
        
        if (window) {
          window.x = parseInt(windowEl.style.left) || 0;
          window.y = parseInt(windowEl.style.top) || 0;
        }
      }
      
      // Remove global event listeners
      document.removeEventListener('mousemove', onMouseMove);
      document.removeEventListener('mouseup', onMouseUp);
    }
  }
  
  /**
   * Make a window resizable
   * @param {HTMLElement} windowEl - Window element
   */
  makeWindowResizable(windowEl) {
    const resizeHandle = windowEl.querySelector('.window-resize-handle');
    let isResizing = false;
    let startWidth, startHeight, startX, startY;
    const self = this; // Store reference to this
    
    resizeHandle.addEventListener('mousedown', function(e) {
      // Get the window ID
      const windowId = windowEl.getAttribute('data-window-id');
      
      // Get window data
      const window = self.windows.find(w => w.id === windowId);
      
      // Don't resize if window not found or if maximized
      if (!window) return;
      if (window.maximized) return;
      
      isResizing = true;
      startWidth = windowEl.offsetWidth;
      startHeight = windowEl.offsetHeight;
      startX = e.clientX;
      startY = e.clientY;
      
      // Add global event listeners
      document.addEventListener('mousemove', onMouseMove);
      document.addEventListener('mouseup', onMouseUp);
      
      // Prevent default to avoid text selection
      e.preventDefault();
    });
    
    function onMouseMove(e) {
      if (!isResizing) return;
      
      const newWidth = startWidth + (e.clientX - startX);
      const newHeight = startHeight + (e.clientY - startY);
      
      // Set minimum dimensions
      const width = Math.max(newWidth, 300);
      const height = Math.max(newHeight, 200);
      
      windowEl.style.width = `${width}px`;
      windowEl.style.height = `${height}px`;
    }
    
    function onMouseUp() {
      if (!isResizing) return;
      
      isResizing = false;
      
      // Update window dimensions in our state
      const windowId = windowEl.getAttribute('data-window-id');
      
      // Only update if windowEl still exists and has valid style properties
      if (windowEl && windowEl.style && windowEl.style.width && windowEl.style.height) {
        const window = self.windows.find(w => w.id === windowId);
        
        if (window) {
          window.width = parseInt(windowEl.style.width) || 300;
          window.height = parseInt(windowEl.style.height) || 200;
        }
      }
      
      // Remove global event listeners
      document.removeEventListener('mousemove', onMouseMove);
      document.removeEventListener('mouseup', onMouseUp);
    }
  }
  
  /**
   * Launch an application
   * @param {Object|string} params - Launch parameters or app ID
   * @param {string} [params.appId] - Application ID
   * @param {Object} [params.fileToOpen] - File to open with the application
   * @param {Object} [params.options] - Additional launch options
   * @returns {Promise<void>}
   */
  async launchApp(params) {
    try {
      // Support both object params and direct app object
      let app;
      let appId;
      let fileToOpen;
      let options = {};
      
      if (typeof params === 'string') {
        // If params is a string, treat it as an appId
        appId = params;
        app = this.apps.find(a => a.id === appId);
      } else if (params.id) {
        // If params has an id property, it might be an app object directly
        app = params;
        appId = app.id;
      } else {
        // Regular object with appId, fileToOpen, options
        appId = params.appId;
        fileToOpen = params.fileToOpen;
        options = params.options || {};
        app = this.apps.find(a => a.id === appId);
      }
      
      if (!app) {
        console.error(`Application not found:`, params);
        throw new Error(`Application ${appId || 'unknown'} not found`);
      }
      
      console.log(`Attempting to launch app:`, app);
      
      // Check if app is already running and we're not force-launching a new instance
      if (!options.forceNewInstance) {
        const existingWindow = this.windows.find(w => w.appId === appId);
        if (existingWindow) {
          // Focus existing window instead of launching a new instance
          this.focusWindow(existingWindow.id);
          
          // If there's a file to open, send it to the existing application
          if (fileToOpen) {
            this.eventBus.publish(`app:${appId}:open-file`, {
              windowId: existingWindow.id,
              file: fileToOpen
            });
          }
          
          return;
        }
      }
      
      console.log(`Launching application: ${app.name}`);
      
      // Load application module - use a more reliable approach
      // First check if the app is already available in window.PrimeOS namespace
      let appModule;
      
      if (window.PrimeOS && window.PrimeOS[app.name]) {
        console.log(`Using globally registered app: ${app.name}`);
        appModule = { default: window.PrimeOS[app.name] };
      } else {
        // Try to load the app from its path
        try {
          // For GitHub Pages, we need to add the PrimeOS prefix to the path
          const isGithubPages = location.hostname.includes('github.io');
          const basePath = isGithubPages ? '/PrimeOS' : '';
          const scriptPath = `${basePath}/reference-implementation/apps/${appId}/index.js`;
          console.log(`Loading app from path: ${scriptPath}`);
          
          // First check if we already have this script in the document to avoid duplicates
          const existingScript = document.querySelector(`script[src="${scriptPath}"]`);
          if (existingScript) {
            console.log(`Script for ${appId} already loaded`);
            // Script already exists, no need to load again
            // Wait a moment to ensure it's initialized
            await new Promise(resolve => setTimeout(resolve, 100));
          } else {
            // For demo, use a more reliable direct script loading approach
            const appScript = document.createElement('script');
            
            // Use the same scriptPath we already calculated
            appScript.src = scriptPath;
            console.log(`Loading app script from: ${appScript.src}`);
            appScript.type = 'text/javascript';
            
            // Safety timeout in case the load event doesn't fire
            const timeoutPromise = new Promise((_, reject) => {
              setTimeout(() => reject(new Error(`Timed out loading ${appId}`)), 5000);
            });
            
            // Script load promise
            const loadPromise = new Promise((resolve, reject) => {
              appScript.onload = resolve;
              appScript.onerror = reject;
              document.head.appendChild(appScript);
            });
            
            // Wait for script to load or timeout
            await Promise.race([loadPromise, timeoutPromise]);
            
            // Add a small delay to ensure script is processed
            await new Promise(resolve => setTimeout(resolve, 200));
          }
          
          // After script is loaded, look for the app constructor in window.PrimeOS
          // Try the app name, app ID, or capitalized app ID
          const capitalizedAppId = appId.charAt(0).toUpperCase() + appId.slice(1);
          
          // For FileExplorer and TextEditor, use their direct class references
          if (appId === 'file-explorer' && window.PrimeOS && window.PrimeOS.FileExplorer) {
            console.log('Found File Explorer app directly');
            appModule = { default: window.PrimeOS.FileExplorer };
          } else if (appId === 'text-editor' && window.PrimeOS && window.PrimeOS.TextEditor) {
            console.log('Found Text Editor app directly');
            appModule = { default: window.PrimeOS.TextEditor };
          } else if (window.PrimeOS && window.PrimeOS[app.name]) {
            console.log(`Found app constructor using app.name: ${app.name}`);
            appModule = { default: window.PrimeOS[app.name] };
          } else if (window.PrimeOS && window.PrimeOS[capitalizedAppId]) {
            console.log(`Found app constructor using capitalized appId: ${capitalizedAppId}`);
            appModule = { default: window.PrimeOS[capitalizedAppId] };
          } else if (window.PrimeOS && window.PrimeOS[appId]) {
            console.log(`Found app constructor using appId: ${appId}`);
            appModule = { default: window.PrimeOS[appId] };
          } else {
            // Create a generic app on-the-fly as fallback
            console.warn(`App ${app.name} (${appId}) not found in global PrimeOS object - creating generic app`);
            
            // Define a minimal demo application
            window.PrimeOS = window.PrimeOS || {};
            window.PrimeOS[appId] = class GenericApp {
              static async initialize(container, options) {
                const app = new GenericApp(container, options);
                await app.init();
                return app;
              }
              
              constructor(container, options) {
                this.container = container;
                this.options = options;
                this.title = app.name || "Application";
              }
              
              async init() {
                this.container.innerHTML = `
                  <div style="padding: 20px; text-align: center;">
                    <h2>${app.name || 'Application'}</h2>
                    <p>This is a placeholder for ${app.name || 'the application'}.</p>
                    <p>The actual application module could not be loaded.</p>
                  </div>
                `;
                return this;
              }
              
              getTitle() {
                return this.title;
              }
            };
            
            appModule = { default: window.PrimeOS[appId] };
          }
        } catch (error) {
          console.error(`Failed to load application module: ${error.message}`);
          
          // Create a fallback app for the demo
          console.warn(`Creating fallback app for ${app.name}`);
          
          // Define a fallback application class
          class FallbackApp {
            static async initialize(container, options) {
              const app = new FallbackApp(container, options);
              await app.init();
              return app;
            }
            
            constructor(container, options) {
              this.container = container;
              this.options = options;
              this.title = `${app.name || 'Application'} (Fallback)`;
            }
            
            async init() {
              this.container.innerHTML = `
                <div style="padding: 20px; text-align: center; color: #333; font-family: sans-serif;">
                  <h2>${app.name || 'Application'}</h2>
                  <p style="color: #e74c3c;">Error loading application: ${error.message}</p>
                  <div style="margin: 20px 0; padding: 15px; background: #f8f9fa; border-radius: 5px; border: 1px solid #ddd;">
                    <p>This is a fallback interface for demonstration purposes.</p>
                    <p>In a production environment, this would provide more robust error recovery options.</p>
                  </div>
                  <button id="retry-btn" style="padding: 8px 16px; background: #3498db; color: white; border: none; border-radius: 4px; cursor: pointer;">
                    Retry
                  </button>
                </div>
              `;
              
              // Add retry button functionality
              const retryBtn = this.container.querySelector('#retry-btn');
              if (retryBtn) {
                retryBtn.addEventListener('click', () => {
                  retryBtn.textContent = 'Retrying...';
                  retryBtn.disabled = true;
                  
                  setTimeout(() => {
                    // This is just for demo - in reality, we would implement proper retry logic
                    retryBtn.textContent = 'Retry Failed';
                    retryBtn.disabled = false;
                  }, 1500);
                });
              }
              
              return this;
            }
            
            getTitle() {
              return this.title;
            }
          }
          
          appModule = { default: FallbackApp };
        }
      }
      
      // Set window position with some randomness to avoid stacking
      const randomOffset = Math.floor(Math.random() * 50);
      const docWidth = document.documentElement.clientWidth || 1024;
      const docHeight = document.documentElement.clientHeight || 768;
      
      // Create window for the application - DON'T use variable name 'window' as it conflicts with global window
      const windowId = `${appId}-${Date.now()}`;
      const appWindow = {
        id: windowId,
        appId,
        title: app.name || 'Application',
        minimized: false,
        maximized: false,
        x: Math.max(50, Math.round((docWidth / 2 - 400) + randomOffset)),
        y: Math.max(50, Math.round((docHeight / 2 - 300) + randomOffset)),
        width: 800,
        height: 600,
        zIndex: this.windows.length + 1,
        appInstance: null, // Will hold a reference to the app instance
        state: {
          isSuspended: false,
          isInitialized: false
        }
      };
      
      // CRITICAL: Create the window DOM element first!
      // Create window element directly (don't wait for desktop render which might be async)
      const windowEl = this.createWindowElement(appWindow);
      
      // Add the window element to the DOM immediately
      const windowsContainer = document.getElementById('windows-container');
      if (windowsContainer) {
        windowsContainer.appendChild(windowEl);
        console.log(`Window element created and added to DOM with id: window-${windowId}`);
      } else {
        console.error("Windows container not found in DOM, creating it");
        // If windows container doesn't exist, create it
        const desktop = document.getElementById('desktop') || document.querySelector('.desktop');
        if (desktop) {
          const newContainer = document.createElement('div');
          newContainer.id = 'windows-container';
          newContainer.className = 'windows-container';
          desktop.appendChild(newContainer);
          newContainer.appendChild(windowEl);
          console.log("Created windows container and added window");
        } else {
          console.error("Desktop element not found, cannot create window");
        }
      }
      
      // Add to windows array
      this.windows.push(appWindow);
      
      // Set as active window
      this.activeWindow = appWindow;
      
      // Update desktop model
      this.desktop.variant.windows = [...this.windows];
      this.desktop.variant.activeWindowId = windowId;
      
      // Now get content element directly from the element we just created
      // This is more reliable than querying the DOM after a render
      let contentEl = windowEl.querySelector('.window-content');
      console.log('Content element found directly from window element:', !!contentEl);
      
      // For good measure, update the desktop UI
      this.desktop.render();
      
      // Update taskbar
      this.taskbar.variant.openWindows = this.windows.map(w => ({
        id: w.id,
        appId: w.appId,
        title: w.title,
        isActive: w.id === this.activeWindow?.id
      }));
      this.taskbar.render();
      
      if (contentEl && appModule.default) {
        // Pass file to open and other options to the application
        const appParams = {
          windowId,
          eventBus: this.eventBus,
          store: this.store,
          identity: this.identity,
          fileToOpen,
          ...options
        };
        
        // Ensure the AppAPI is available globally for apps to use
        if (typeof window !== 'undefined') {
          // Make sure PrimeOS namespace exists
          if (!window.PrimeOS) {
            window.PrimeOS = {};
          }
          
          // Import AppAPI if not already available
          if (!window.PrimeOS.AppAPI) {
            try {
              // Load AppAPI from the core apps directory
              const appApiScript = document.createElement('script');
              appApiScript.src = '/reference-implementation/core/apps/app-api.js';
              appApiScript.type = 'text/javascript';
              
              // Wait for the script to load
              await new Promise((resolve, reject) => {
                appApiScript.onload = resolve;
                appApiScript.onerror = reject;
                document.head.appendChild(appApiScript);
              });
              
              console.log('AppAPI loaded successfully for app:', appId);
            } catch (apiError) {
              console.error('Failed to load AppAPI:', apiError);
            }
          }
        }
        
        const appInstance = await appModule.default.initialize(contentEl, appParams);
        
        // Store app instance for lifecycle management
        appWindow.appInstance = appInstance;
        appWindow.state.isInitialized = true;
        
        // Set window title to app-provided title if available
        if (appInstance && appInstance.getTitle) {
          const appTitle = appInstance.getTitle();
          if (appTitle) {
            appWindow.title = appTitle;
            
            // Update window UI
            const windowTitleEl = document.querySelector(`#window-${windowId} .window-title`);
            if (windowTitleEl) {
              windowTitleEl.textContent = appTitle;
            }
            
            // Update taskbar
            this.updateTaskbar();
          }
        }
      } else {
        console.error('Could not initialize application: Either content element or app module not found', {
          contentEl: !!contentEl,
          appModuleDefault: !!appModule?.default
        });
      }
      
      // Publish event that app has launched
      this.eventBus.publish('shell:app-launched', { appId, windowId });
      
    } catch (error) {
      console.error(`Failed to launch application: ${error.message}`, error);
      this.showNotification({
        type: 'error',
        title: 'Application Error',
        message: `Failed to launch application: ${error.message}`,
        timeout: 5000
      });
    }
  }
  
  /**
   * Suspend an application to conserve resources
   * @param {string} windowId - Window ID
   */
  suspendApp(windowId) {
    const window = this.windows.find(w => w.id === windowId);
    if (!window || window.state.isSuspended) return;
    
    const appInstance = window.appInstance;
    if (appInstance && typeof appInstance.onSuspend === 'function') {
      try {
        appInstance.onSuspend();
        window.state.isSuspended = true;
        
        console.log(`Application ${window.appId} suspended`);
        this.eventBus.publish('shell:app-suspended', { windowId, appId: window.appId });
      } catch (error) {
        console.error(`Error suspending application: ${error.message}`, error);
      }
    }
  }
  
  /**
   * Resume a suspended application
   * @param {string} windowId - Window ID
   */
  resumeApp(windowId) {
    const window = this.windows.find(w => w.id === windowId);
    if (!window || !window.state.isSuspended) return;
    
    const appInstance = window.appInstance;
    if (appInstance && typeof appInstance.onResume === 'function') {
      try {
        appInstance.onResume();
        window.state.isSuspended = false;
        
        console.log(`Application ${window.appId} resumed`);
        this.eventBus.publish('shell:app-resumed', { windowId, appId: window.appId });
      } catch (error) {
        console.error(`Error resuming application: ${error.message}`, error);
      }
    }
  }
  
  /**
   * Suspend all applications except the active one
   */
  suspendBackgroundApps() {
    this.windows.forEach(window => {
      // Skip the active window
      if (window.id === this.activeWindow?.id) return;
      
      // Skip already suspended windows
      if (window.state.isSuspended) return;
      
      // Suspend the application
      this.suspendApp(window.id);
    });
  }
  
  /**
   * Close a window
   * @param {string} windowId - Window ID
   */
  async closeWindow(windowId) {
    console.log('Closing window:', windowId);
    const windowIndex = this.windows.findIndex(w => w.id === windowId);
    if (windowIndex === -1) return;
    
    const window = this.windows[windowIndex];
    
    // Direct DOM manipulation - remove the window element
    const windowEl = document.querySelector(`#window-${windowId}`);
    
    // Notify application it's about to be closed
    if (window.appInstance) {
      try {
        // Call application's lifecycle method if available
        if (typeof window.appInstance.onBeforeClose === 'function') {
          await window.appInstance.onBeforeClose();
        }
      } catch (error) {
        console.error(`Error calling onBeforeClose for application: ${error.message}`, error);
      }
    }
    
    // Publish window closing event
    this.eventBus.publish('shell:window-closing', { windowId, appId: window.appId });
    
    // Remove window from array
    this.windows.splice(windowIndex, 1);
    
    // Update active window if needed
    if (this.activeWindow?.id === windowId) {
      this.activeWindow = this.windows.length > 0 ? this.windows[this.windows.length - 1] : null;
      
      // Resume the newly active window if it was suspended
      if (this.activeWindow && this.activeWindow.state.isSuspended) {
        this.resumeApp(this.activeWindow.id);
      }
    }
    
    // Direct DOM manipulation - remove the window element
    if (windowEl) {
      windowEl.remove();
    }
    
    // Update desktop state without full rerender
    this.desktop.variant.windows = [...this.windows];
    this.desktop.variant.activeWindowId = this.activeWindow?.id || null;
    
    // Update active window in DOM
    if (this.activeWindow) {
      const activeWindowEl = document.querySelector(`#window-${this.activeWindow.id}`);
      if (activeWindowEl) {
        document.querySelectorAll('.window').forEach(el => {
          if (el === activeWindowEl) {
            el.classList.add('active');
            el.style.zIndex = '10'; // Bring to front
          } else {
            el.classList.remove('active');
            el.style.zIndex = '1';
          }
        });
      }
    }
    
    // Directly update the taskbar first for immediate feedback
    this.updateTaskbarDirectly();
    
    // Update taskbar through component system as backup
    this.taskbar.variant.openWindows = this.windows.map(w => ({
      id: w.id,
      appId: w.appId,
      title: w.title,
      isActive: w.id === this.activeWindow?.id
    }));
    this.taskbar.render();
    
    // Cleanup application instance
    if (window.appInstance) {
      try {
        // Call application's lifecycle method if available
        if (typeof window.appInstance.onClose === 'function') {
          await window.appInstance.onClose();
        }
      } catch (error) {
        console.error(`Error calling onClose for application: ${error.message}`, error);
      }
    }
    
    // Publish window closed event
    this.eventBus.publish('shell:window-closed', { windowId, appId: window.appId });
  }
  
  /**
   * Minimize a window
   * @param {string} windowId - Window ID
   */
  minimizeWindow(windowId) {
    console.log('Minimizing window:', windowId);
    const window = this.windows.find(w => w.id === windowId);
    if (!window) return;
    
    // Toggle minimized state
    window.minimized = !window.minimized;
    
    // Direct DOM manipulation - find and update the window element
    const windowEl = document.querySelector(`#window-${windowId}`);
    if (windowEl) {
      if (window.minimized) {
        windowEl.classList.add('minimized');
      } else {
        windowEl.classList.remove('minimized');
      }
    }
    
    // If minimizing, set a different active window and suspend the app
    if (window.minimized && this.activeWindow?.id === windowId) {
      // Suspend the minimized application
      this.suspendApp(windowId);
      
      // Find a new active window
      const visibleWindows = this.windows.filter(w => !w.minimized);
      this.activeWindow = visibleWindows.length > 0 ? visibleWindows[visibleWindows.length - 1] : null;
      
      // Resume the newly active window if needed
      if (this.activeWindow && this.activeWindow.state.isSuspended) {
        this.resumeApp(this.activeWindow.id);
      }
    } else if (!window.minimized) {
      // If restoring from minimized, make it active and resume it
      this.activeWindow = window;
      
      // Resume the application if it was suspended
      if (window.state.isSuspended) {
        this.resumeApp(windowId);
      }
    }
    
    // Update desktop state without full rerender
    this.desktop.variant.windows = [...this.windows];
    this.desktop.variant.activeWindowId = this.activeWindow?.id || null;
    
    // Update active window in DOM
    document.querySelectorAll('.window').forEach(el => {
      const wId = el.getAttribute('data-window-id');
      if (wId === this.activeWindow?.id) {
        el.classList.add('active');
        el.style.zIndex = '10'; // Bring to front
      } else {
        el.classList.remove('active');
        el.style.zIndex = '1';
      }
    });
    
    // Directly update the taskbar first for immediate feedback
    this.updateTaskbarDirectly();
    
    // Update taskbar through component system as backup
    this.taskbar.variant.openWindows = this.windows.map(w => ({
      id: w.id,
      appId: w.appId,
      title: w.title,
      isActive: w.id === this.activeWindow?.id
    }));
    this.taskbar.render();
    
    // Publish event
    this.eventBus.publish('shell:window-minimized', { 
      windowId, 
      minimized: window.minimized 
    });
  }
  
  /**
   * Update taskbar directly with DOM manipulation for immediate feedback
   * This ensures minimized windows show up in the taskbar without delay
   */
  updateTaskbarDirectly() {
    try {
      const taskbarItems = document.getElementById('taskbar-items');
      if (!taskbarItems) return;
      
      console.log('Directly updating taskbar for immediate feedback');
      
      // Clear existing items
      taskbarItems.innerHTML = '';
      
      // Add all windows to taskbar
      this.windows.forEach(window => {
        const item = document.createElement('div');
        item.className = 'taskbar-item' + (window.id === this.activeWindow?.id ? ' active' : '');
        if (window.minimized) {
          item.classList.add('minimized-window');
        }
        item.setAttribute('data-window-id', window.id);
        
        // Find app info
        const app = this.apps.find(a => a.id === window.appId);
        
        item.innerHTML = `
          <span class="icon">${app?.icon || '📄'}</span>
          <span class="title">${window.title}</span>
        `;
        
        // Use self to maintain context in the event listener
        const self = this;
        item.addEventListener('click', function() {
          const windowId = this.getAttribute('data-window-id');
          const window = self.windows.find(w => w.id === windowId);
          
          if (!window) return;
          
          if (window.id === self.activeWindow?.id && !window.minimized) {
            // If already active, minimize it
            self.minimizeWindow(window.id);
          } else {
            // Otherwise focus it (this will unminimize if needed)
            self.focusWindow(window.id);
          }
        });
        
        taskbarItems.appendChild(item);
      });
    } catch (error) {
      console.error('Error directly updating taskbar:', error);
    }
  }
  
  /**
   * Maximize a window
   * @param {string} windowId - Window ID
   */
  maximizeWindow(windowId) {
    console.log('Maximizing window:', windowId);
    const window = this.windows.find(w => w.id === windowId);
    if (!window) return;
    
    // Toggle maximized state
    window.maximized = !window.maximized;
    
    // Ensure window is not minimized
    window.minimized = false;
    
    // Make this the active window
    this.activeWindow = window;
    
    // Direct DOM manipulation - find and update the window element
    const windowEl = document.querySelector(`#window-${windowId}`);
    if (windowEl) {
      // Toggle maximized class
      if (window.maximized) {
        windowEl.classList.add('maximized');
      } else {
        windowEl.classList.remove('maximized');
      }
      
      // Remove minimized class if present
      windowEl.classList.remove('minimized');
      
      // Update maximize button text
      const maxButton = windowEl.querySelector('.window-maximize');
      if (maxButton) {
        maxButton.textContent = window.maximized ? '❐' : '□';
      }
      
      // Update position and size for non-maximized windows
      if (!window.maximized) {
        windowEl.style.width = `${window.width}px`;
        windowEl.style.height = `${window.height}px`;
        windowEl.style.left = `${window.x}px`;
        windowEl.style.top = `${window.y}px`;
      }
      
      // Set active state and z-index
      document.querySelectorAll('.window').forEach(el => {
        if (el === windowEl) {
          el.classList.add('active');
          el.style.zIndex = '10'; // Bring to front
        } else {
          el.classList.remove('active');
          el.style.zIndex = '1';
        }
      });
    }
    
    // Update desktop state without full rerender
    this.desktop.variant.windows = [...this.windows];
    this.desktop.variant.activeWindowId = windowId;
    
    // Directly update the taskbar first for immediate feedback
    this.updateTaskbarDirectly();
    
    // Update taskbar through component system as backup
    this.taskbar.variant.openWindows = this.windows.map(w => ({
      id: w.id,
      appId: w.appId,
      title: w.title,
      isActive: w.id === windowId
    }));
    this.taskbar.render();
    
    // Publish event
    this.eventBus.publish('shell:window-maximized', { 
      windowId, 
      maximized: window.maximized 
    });
  }
  
  /**
   * Focus a window
   * @param {string} windowId - Window ID
   */
  focusWindow(windowId) {
    console.log('Focusing window:', windowId);
    const window = this.windows.find(w => w.id === windowId);
    if (!window) return;
    
    // If this is already the active window, do nothing
    if (this.activeWindow?.id === windowId && !window.minimized) return;
    
    // Direct DOM manipulation - find window element
    const windowEl = document.querySelector(`#window-${windowId}`);
    if (!windowEl) {
      console.warn(`Window element not found for ID: ${windowId}`);
      return;
    }
    
    // If window is minimized, restore it
    if (window.minimized) {
      window.minimized = false;
      
      // Update DOM to show window
      windowEl.classList.remove('minimized');
      console.log('Restoring minimized window:', windowId);
    }
    
    // Get the previously active window
    const previousActiveWindow = this.activeWindow;
    
    // Move window to front by updating z-index
    this.windows.forEach(w => {
      w.zIndex = w.id === windowId ? this.windows.length : w.zIndex;
    });
    
    // Sort windows by z-index
    this.windows.sort((a, b) => a.zIndex - b.zIndex);
    
    // Set as active window
    this.activeWindow = window;
    
    // Direct DOM manipulation - update active window
    document.querySelectorAll('.window').forEach(el => {
      if (el === windowEl) {
        el.classList.add('active');
        el.style.zIndex = '10'; // Bring to front
      } else {
        el.classList.remove('active');
        el.style.zIndex = '1';
      }
    });
    
    // Resume the application if it was suspended
    if (window.state && window.state.isSuspended) {
      this.resumeApp(windowId);
    }
    
    // Update desktop state without full rerender
    this.desktop.variant.windows = [...this.windows];
    this.desktop.variant.activeWindowId = windowId;
    
    // Update taskbar to show active window and restore minimized windows
    this.updateTaskbar();
    
    // Suspend previous window (if exists and different from current)
    if (previousActiveWindow && previousActiveWindow.id !== windowId) {
      this.suspendApp(previousActiveWindow.id);
    }
    
    // Resume newly focused window if it was suspended
    if (window.state.isSuspended) {
      this.resumeApp(windowId);
    }
    
    // Call application's focus handler if available
    if (window.appInstance && typeof window.appInstance.onFocus === 'function') {
      try {
        window.appInstance.onFocus();
      } catch (error) {
        console.error(`Error calling onFocus for application: ${error.message}`, error);
      }
    }
    
    // Publish event
    this.eventBus.publish('shell:window-focused', { windowId });
  }
  
  /**
   * Show a notification
   * @param {Object} notification - Notification data
   * @param {string} notification.type - Notification type (info, warning, error, success)
   * @param {string} notification.title - Notification title
   * @param {string} notification.message - Notification message
   * @param {number} [notification.timeout] - Auto-dismiss timeout in ms
   */
  showNotification(notification) {
    // Generate ID if not provided
    const notificationWithId = {
      id: `notification-${Date.now()}-${Math.floor(Math.random() * 1000)}`,
      timestamp: Date.now(),
      ...notification
    };
    
    // Add to notifications array
    this.notifications.push(notificationWithId);
    
    // Update notification center
    this.notificationCenter.variant.notifications = [...this.notifications];
    this.notificationCenter.render();
    
    // Create toast notification
    this.showToastNotification(notificationWithId);
    
    // Auto-dismiss if timeout is set
    if (notification.timeout) {
      setTimeout(() => {
        this.dismissNotification({ notificationId: notificationWithId.id });
      }, notification.timeout);
    }
    
    // Publish event
    this.eventBus.publish('shell:notification-shown', { 
      notificationId: notificationWithId.id,
      type: notification.type
    });
  }
  
  /**
   * Show a toast notification
   * @param {Object} notification - Notification object
   */
  showToastNotification(notification) {
    // Create toast container if it doesn't exist
    let toastContainer = document.getElementById('toast-container');
    if (!toastContainer) {
      toastContainer = document.createElement('div');
      toastContainer.id = 'toast-container';
      document.body.appendChild(toastContainer);
    }
    
    // Create toast element
    const toast = document.createElement('div');
    toast.className = `toast toast-${notification.type}`;
    toast.setAttribute('data-notification-id', notification.id);
    
    toast.innerHTML = `
      <div class="toast-header">
        <h4>${notification.title}</h4>
        <button class="close-toast">×</button>
      </div>
      <div class="toast-body">
        <p>${notification.message}</p>
      </div>
    `;
    
    // Add dismiss handler
    toast.querySelector('.close-toast').addEventListener('click', () => {
      this.dismissNotification({ notificationId: notification.id });
    });
    
    // Add to container
    toastContainer.appendChild(toast);
    
    // Animate in
    setTimeout(() => {
      toast.classList.add('show');
    }, 10);
    
    // Auto-remove from DOM after animation completes
    if (notification.timeout) {
      setTimeout(() => {
        toast.classList.remove('show');
        setTimeout(() => {
          toast.remove();
        }, 300); // Match CSS transition time
      }, notification.timeout - 300);
    }
  }
  
  /**
   * Dismiss a notification
   * @param {Object} params - Parameters
   * @param {string} params.notificationId - Notification ID
   */
  dismissNotification(params) {
    const { notificationId } = params;
    
    // Remove from notifications array
    const index = this.notifications.findIndex(n => n.id === notificationId);
    if (index !== -1) {
      this.notifications.splice(index, 1);
    }
    
    // Update notification center
    this.notificationCenter.variant.notifications = [...this.notifications];
    this.notificationCenter.render();
    
    // Remove toast if it exists
    const toast = document.querySelector(`.toast[data-notification-id="${notificationId}"]`);
    if (toast) {
      toast.classList.remove('show');
      setTimeout(() => {
        toast.remove();
      }, 300); // Match CSS transition time
    }
    
    // Publish event
    this.eventBus.publish('shell:notification-dismissed', { notificationId });
  }
  
  /**
   * Clear all notifications
   */
  clearAllNotifications() {
    // Clear notifications array
    this.notifications = [];
    
    // Update notification center
    this.notificationCenter.variant.notifications = [];
    this.notificationCenter.render();
    
    // Remove all toasts
    const toasts = document.querySelectorAll('.toast');
    toasts.forEach(toast => {
      toast.classList.remove('show');
      setTimeout(() => {
        toast.remove();
      }, 300);
    });
    
    // Publish event
    this.eventBus.publish('shell:notifications-cleared');
  }
  
  /**
   * Update a window's title
   * @param {Object} params - Parameters
   * @param {string} params.windowId - Window ID
   * @param {string} params.title - New window title
   */
  updateWindowTitle(params) {
    const { windowId, title } = params;
    
    // Find the window
    const window = this.windows.find(w => w.id === windowId);
    if (!window) return;
    
    // Update window title
    window.title = title;
    
    // Update window titlebar
    const windowTitleEl = document.querySelector(`#window-${windowId} .window-title`);
    if (windowTitleEl) {
      windowTitleEl.textContent = title;
    }
    
    // Update taskbar
    this.updateTaskbar();
  }
  
  /**
   * Show the login screen
   */
  showLoginScreen() {
    // Create login container
    const loginContainer = document.createElement('div');
    loginContainer.className = 'login-screen';
    loginContainer.innerHTML = `
      <div class="login-card">
        <div class="login-header">
          <h2>Welcome to PrimeOS</h2>
          <p>Please sign in to continue</p>
        </div>
        <div class="login-form">
          <div class="form-group">
            <label for="username">Username</label>
            <input type="text" id="username" placeholder="Username">
          </div>
          <div class="form-group">
            <label for="password">Password</label>
            <input type="password" id="password" placeholder="Password">
          </div>
          <div class="form-actions">
            <button id="login-button" class="btn-primary">Sign In</button>
            <button id="create-account-button" class="btn-secondary">Create Account</button>
          </div>
        </div>
        <div class="login-footer">
          <p>PrimeOS Reference Implementation</p>
        </div>
      </div>
    `;
    
    document.body.appendChild(loginContainer);
    
    // Add event listeners
    document.getElementById('login-button').addEventListener('click', async () => {
      const username = document.getElementById('username').value;
      const password = document.getElementById('password').value;
      
      if (!username || !password) {
        this.showNotification({
          type: 'error',
          title: 'Login Error',
          message: 'Please enter both username and password',
          timeout: 3000
        });
        return;
      }
      
      try {
        const success = await this.identity.login(username, password);
        if (success) {
          loginContainer.remove();
          this.initialize();
        } else {
          this.showNotification({
            type: 'error',
            title: 'Login Failed',
            message: 'Invalid username or password',
            timeout: 3000
          });
        }
      } catch (error) {
        this.showNotification({
          type: 'error',
          title: 'Login Error',
          message: error.message,
          timeout: 3000
        });
      }
    });
    
    document.getElementById('create-account-button').addEventListener('click', () => {
      this.showCreateAccountScreen();
      loginContainer.remove();
    });
  }
  
  /**
   * Show the create account screen
   */
  showCreateAccountScreen() {
    // Create account container
    const createAccountContainer = document.createElement('div');
    createAccountContainer.className = 'login-screen';
    createAccountContainer.innerHTML = `
      <div class="login-card">
        <div class="login-header">
          <h2>Create PrimeOS Account</h2>
          <p>Enter your details to create an account</p>
        </div>
        <div class="login-form">
          <div class="form-group">
            <label for="new-username">Username</label>
            <input type="text" id="new-username" placeholder="Choose a username">
          </div>
          <div class="form-group">
            <label for="new-password">Password</label>
            <input type="password" id="new-password" placeholder="Create a password">
          </div>
          <div class="form-group">
            <label for="confirm-password">Confirm Password</label>
            <input type="password" id="confirm-password" placeholder="Confirm your password">
          </div>
          <div class="form-actions">
            <button id="create-button" class="btn-primary">Create Account</button>
            <button id="back-to-login-button" class="btn-secondary">Back to Login</button>
          </div>
        </div>
        <div class="login-footer">
          <p>PrimeOS Reference Implementation</p>
        </div>
      </div>
    `;
    
    document.body.appendChild(createAccountContainer);
    
    // Add event listeners
    document.getElementById('create-button').addEventListener('click', async () => {
      const username = document.getElementById('new-username').value;
      const password = document.getElementById('new-password').value;
      const confirmPassword = document.getElementById('confirm-password').value;
      
      if (!username || !password) {
        this.showNotification({
          type: 'error',
          title: 'Account Creation Error',
          message: 'Please fill in all fields',
          timeout: 3000
        });
        return;
      }
      
      if (password !== confirmPassword) {
        this.showNotification({
          type: 'error',
          title: 'Account Creation Error',
          message: 'Passwords do not match',
          timeout: 3000
        });
        return;
      }
      
      try {
        const success = await this.identity.createUser(username, password);
        if (success) {
          this.showNotification({
            type: 'success',
            title: 'Account Created',
            message: 'Your account has been created successfully',
            timeout: 3000
          });
          
          createAccountContainer.remove();
          this.showLoginScreen();
        }
      } catch (error) {
        this.showNotification({
          type: 'error',
          title: 'Account Creation Error',
          message: error.message,
          timeout: 3000
        });
      }
    });
    
    document.getElementById('back-to-login-button').addEventListener('click', () => {
      createAccountContainer.remove();
      this.showLoginScreen();
    });
  }
}

// Export as ES module
export { Shell };

// Make available on window for browser usage
if (typeof window !== 'undefined') {
  window.Shell = Shell;
}