/**
 * PrimeOS Shell Environment
 * 
 * The Shell forms the primary user interface for PrimeOS, providing
 * window management, application launching, and system interaction.
 * It implements the four-tier architecture using the PrimeOS framework.
 */

// Import from global modules if available, otherwise attempt to require the modules
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
    
    // Use global PrimeStore or create a simple mock
    PrimeStore = window.PrimeStore || require('../storage/primestore').PrimeStore;
    PrimeIdentity = window.PrimeIdentity || require('../identity/identity-provider').PrimeIdentity;
  } else {
    // Node.js environment, import with require
    const framework = require('../../js/framework');
    EventBus = framework.EventBus;
    createComponent = framework.createComponent;
    PrimeStore = require('../storage/primestore').PrimeStore;
    PrimeIdentity = require('../identity/identity-provider').PrimeIdentity;
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
    this.storeName = storeName;
    this.data = {};
    
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
    this.store = new PrimeStore('shell');
    this.identity = new PrimeIdentity();
    
    // Register shell events
    this.eventBus.subscribe('shell:launch-app', this.launchApp.bind(this));
    this.eventBus.subscribe('shell:close-window', this.closeWindow.bind(this));
    this.eventBus.subscribe('shell:minimize-window', this.minimizeWindow.bind(this));
    this.eventBus.subscribe('shell:maximize-window', this.maximizeWindow.bind(this));
    this.eventBus.subscribe('shell:focus-window', this.focusWindow.bind(this));
    this.eventBus.subscribe('shell:show-notification', this.showNotification.bind(this));
    this.eventBus.subscribe('shell:dismiss-notification', this.dismissNotification.bind(this));
    
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
    
    // Initialize app launcher
    this.appLauncher = createComponent({
      id: 'app-launcher',
      variant: {
        visible: false,
        apps: [],
        searchQuery: ''
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
    // Load available applications
    await this.loadApplications();
    
    // Load user preferences
    await this.loadPreferences();
    
    // Render shell components
    this.renderShell();
    
    // Check user authentication
    const isAuthenticated = await this.identity.checkSession();
    if (!isAuthenticated) {
      this.showLoginScreen();
    }
    
    console.log('PrimeOS Shell initialized');
    
    // Publish shell ready event
    this.eventBus.publish('shell:ready', { timestamp: Date.now() });
  }
  
  /**
   * Load available applications
   * @returns {Promise<void>}
   */
  async loadApplications() {
    try {
      // Fetch installed apps from storage
      const apps = await this.store.query('applications');
      if (apps && apps.length > 0) {
        this.apps = apps;
      } else {
        // Load default applications if none are found
        this.apps = [
          {
            id: 'file-manager',
            name: 'File Manager',
            icon: 'folder',
            description: 'Browse and manage your files',
            path: '/apps/file-manager/index.js'
          },
          {
            id: 'terminal',
            name: 'Terminal',
            icon: 'terminal',
            description: 'Command-line interface',
            path: '/apps/terminal/index.js'
          },
          {
            id: 'settings',
            name: 'Settings',
            icon: 'cog',
            description: 'System configuration',
            path: '/apps/settings/index.js'
          },
          {
            id: 'text-editor',
            name: 'Text Editor',
            icon: 'edit',
            description: 'Create and edit documents',
            path: '/apps/text-editor/index.js'
          }
        ];
        
        // Store default apps
        await this.store.saveAll('applications', this.apps);
      }
      
      // Update app launcher component
      this.appLauncher.variant.apps = this.apps;
      this.taskbar.variant.apps = this.apps;
      
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
      
      const preferences = await this.store.get('user_preferences', currentUser.id);
      if (preferences) {
        // Apply user preferences (theme, layout, etc.)
        if (preferences.theme) {
          document.documentElement.setAttribute('data-theme', preferences.theme);
        }
        
        if (preferences.fontSize) {
          document.documentElement.style.setProperty('--font-size-base', preferences.fontSize);
        }
        
        if (preferences.taskbarPosition) {
          document.getElementById('taskbar').setAttribute('data-position', preferences.taskbarPosition);
        }
        
        console.log('Applied user preferences');
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
    
    // Start clock
    this.startClock();
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
      // Start button
      const startButton = document.getElementById('start-button');
      if (startButton) {
        startButton.addEventListener('click', () => {
          if (this.appLauncher && this.appLauncher.invariant && 
              typeof this.appLauncher.invariant.toggleVisible === 'function') {
            this.appLauncher.invariant.toggleVisible.call(this.appLauncher);
          }
        });
      }
      
      // Notification icon
      const notificationIcon = document.getElementById('notification-icon');
      if (notificationIcon) {
        notificationIcon.addEventListener('click', () => {
          if (this.notificationCenter && this.notificationCenter.invariant && 
              typeof this.notificationCenter.invariant.toggleVisible === 'function') {
            this.notificationCenter.invariant.toggleVisible.call(this.notificationCenter);
          }
        });
      }
      
      // App search
      const appSearch = document.getElementById('app-search');
      if (appSearch) {
        appSearch.addEventListener('input', (e) => {
          if (this.appLauncher && this.appLauncher.invariant && 
              typeof this.appLauncher.invariant.search === 'function') {
            this.appLauncher.invariant.search.call(this.appLauncher, e.target.value);
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
      if (document && this.appLauncher && this.notificationCenter) {
        document.addEventListener('click', (e) => {
          // Only handle app launcher if it exists with proper structure
          if (this.appLauncher && this.appLauncher.variant && 
              this.appLauncher.variant.visible && 
              this.appLauncher.invariant && 
              typeof this.appLauncher.invariant.toggleVisible === 'function') {
              
            if (!e.target.closest('#app-launcher') && !e.target.closest('#start-button')) {
              this.appLauncher.invariant.toggleVisible.call(this.appLauncher);
            }
          }
          
          // Only handle notification center if it exists with proper structure
          if (this.notificationCenter && this.notificationCenter.variant && 
              this.notificationCenter.variant.visible && 
              this.notificationCenter.invariant && 
              typeof this.notificationCenter.invariant.toggleVisible === 'function') {
              
            if (!e.target.closest('#notification-center') && !e.target.closest('#notification-icon')) {
              this.notificationCenter.invariant.toggleVisible.call(this.notificationCenter);
            }
          }
        });
      }
    } catch (error) {
      console.error('Error initializing event listeners:', error);
    }
  }
  
  /**
   * Update desktop component
   */
  updateDesktop() {
    const container = document.getElementById('windows-container');
    
    // Clear existing windows
    container.innerHTML = '';
    
    // Add windows in z-index order
    this.windows.forEach(window => {
      const windowEl = this.createWindowElement(window);
      container.appendChild(windowEl);
    });
  }
  
  /**
   * Update taskbar component
   */
  updateTaskbar() {
    const taskbarItems = document.getElementById('taskbar-items');
    
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
        this.focusWindow(window.id);
      });
      
      taskbarItems.appendChild(item);
    });
    
    // Update clock
    this.updateClock();
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
    const appLauncher = this.appLauncher;
    if (!appLauncher || !appLauncher.variant) {
      console.warn('App launcher component not initialized properly');
      return;
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
      return;
    }
    
    // Add apps to grid
    appsToDisplay.forEach(app => {
      if (!app || !app.id) return;
      
      const appItem = document.createElement('div');
      appItem.className = 'app-item';
      appItem.setAttribute('data-app-id', app.id);
      
      appItem.innerHTML = `
        <div class="app-icon">${app.icon || '📄'}</div>
        <div class="app-name">${app.name}</div>
      `;
      
      appItem.addEventListener('click', () => {
        this.launchApp({ appId: app.id });
        if (appLauncher.invariant && typeof appLauncher.invariant.toggleVisible === 'function') {
          appLauncher.invariant.toggleVisible.call(appLauncher);
        }
      });
      
      appGrid.appendChild(appItem);
    });
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
   * Create a window element
   * @param {Object} window - Window configuration
   * @returns {HTMLElement} Window element
   */
  createWindowElement(window) {
    const windowEl = document.createElement('div');
    windowEl.className = 'window' + (window.minimized ? ' minimized' : '') + (window.maximized ? ' maximized' : '');
    windowEl.id = `window-${window.id}`;
    windowEl.setAttribute('data-window-id', window.id);
    
    // Set position and size for non-maximized windows
    if (!window.maximized) {
      windowEl.style.width = `${window.width}px`;
      windowEl.style.height = `${window.height}px`;
      windowEl.style.left = `${window.x}px`;
      windowEl.style.top = `${window.y}px`;
    }
    
    windowEl.innerHTML = `
      <div class="window-titlebar">
        <div class="window-title">${window.title}</div>
        <div class="window-controls">
          <button class="window-control window-minimize">_</button>
          <button class="window-control window-maximize">${window.maximized ? '❐' : '□'}</button>
          <button class="window-control window-close">×</button>
        </div>
      </div>
      <div class="window-content" id="window-content-${window.id}"></div>
      <div class="window-resize-handle"></div>
    `;
    
    // Add event listeners for window controls
    windowEl.querySelector('.window-minimize').addEventListener('click', () => {
      this.minimizeWindow(window.id);
    });
    
    windowEl.querySelector('.window-maximize').addEventListener('click', () => {
      this.maximizeWindow(window.id);
    });
    
    windowEl.querySelector('.window-close').addEventListener('click', () => {
      this.closeWindow(window.id);
    });
    
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
    
    titlebar.addEventListener('mousedown', (e) => {
      // Ignore if clicking on a control button
      if (e.target.closest('.window-control')) return;
      
      // Get the window ID
      const windowId = windowEl.getAttribute('data-window-id');
      
      // Focus window
      this.focusWindow(windowId);
      
      // Get window data
      const window = this.windows.find(w => w.id === windowId);
      
      // Don't drag if maximized
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
      const window = this.windows.find(w => w.id === windowId);
      
      if (window) {
        window.x = parseInt(windowEl.style.left);
        window.y = parseInt(windowEl.style.top);
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
    
    resizeHandle.addEventListener('mousedown', (e) => {
      // Get the window ID
      const windowId = windowEl.getAttribute('data-window-id');
      
      // Get window data
      const window = this.windows.find(w => w.id === windowId);
      
      // Don't resize if maximized
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
      const window = this.windows.find(w => w.id === windowId);
      
      if (window) {
        window.width = parseInt(windowEl.style.width);
        window.height = parseInt(windowEl.style.height);
      }
      
      // Remove global event listeners
      document.removeEventListener('mousemove', onMouseMove);
      document.removeEventListener('mouseup', onMouseUp);
    }
  }
  
  /**
   * Launch an application
   * @param {Object} params - Launch parameters
   * @param {string} params.appId - Application ID
   * @returns {Promise<void>}
   */
  async launchApp(params) {
    try {
      const { appId } = params;
      
      // Find app in registry
      const app = this.apps.find(a => a.id === appId);
      if (!app) {
        throw new Error(`Application ${appId} not found`);
      }
      
      // Check if app is already running
      const existingWindow = this.windows.find(w => w.appId === appId);
      if (existingWindow) {
        // Focus existing window instead of launching a new instance
        this.focusWindow(existingWindow.id);
        return;
      }
      
      console.log(`Launching application: ${app.name}`);
      
      // Load application module
      const appModule = await import(app.path);
      
      // Create window for the application
      const windowId = `${appId}-${Date.now()}`;
      const window = {
        id: windowId,
        appId,
        title: app.name,
        minimized: false,
        maximized: false,
        x: Math.round(window.innerWidth / 2 - 400),
        y: Math.round(window.innerHeight / 2 - 300),
        width: 800,
        height: 600,
        zIndex: this.windows.length + 1
      };
      
      // Add to windows array
      this.windows.push(window);
      
      // Set as active window
      this.activeWindow = window;
      
      // Update desktop to show the new window
      this.desktop.variant.windows = [...this.windows];
      this.desktop.variant.activeWindowId = windowId;
      this.desktop.render();
      
      // Update taskbar
      this.taskbar.variant.openWindows = this.windows.map(w => ({
        id: w.id,
        appId: w.appId,
        title: w.title,
        isActive: w.id === this.activeWindow?.id
      }));
      this.taskbar.render();
      
      // Initialize application within the window
      const contentEl = document.getElementById(`window-content-${windowId}`);
      if (contentEl && appModule.default) {
        await appModule.default.initialize(contentEl, {
          windowId,
          eventBus: this.eventBus,
          store: this.store,
          identity: this.identity
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
   * Close a window
   * @param {string} windowId - Window ID
   */
  closeWindow(windowId) {
    const windowIndex = this.windows.findIndex(w => w.id === windowId);
    if (windowIndex === -1) return;
    
    const window = this.windows[windowIndex];
    
    // Publish window closing event
    this.eventBus.publish('shell:window-closing', { windowId, appId: window.appId });
    
    // Remove window from array
    this.windows.splice(windowIndex, 1);
    
    // Update active window if needed
    if (this.activeWindow?.id === windowId) {
      this.activeWindow = this.windows.length > 0 ? this.windows[this.windows.length - 1] : null;
    }
    
    // Update desktop
    this.desktop.variant.windows = [...this.windows];
    this.desktop.variant.activeWindowId = this.activeWindow?.id || null;
    this.desktop.render();
    
    // Update taskbar
    this.taskbar.variant.openWindows = this.windows.map(w => ({
      id: w.id,
      appId: w.appId,
      title: w.title,
      isActive: w.id === this.activeWindow?.id
    }));
    this.taskbar.render();
    
    // Publish window closed event
    this.eventBus.publish('shell:window-closed', { windowId, appId: window.appId });
  }
  
  /**
   * Minimize a window
   * @param {string} windowId - Window ID
   */
  minimizeWindow(windowId) {
    const window = this.windows.find(w => w.id === windowId);
    if (!window) return;
    
    // Toggle minimized state
    window.minimized = !window.minimized;
    
    // If minimizing, set a different active window
    if (window.minimized && this.activeWindow?.id === windowId) {
      const visibleWindows = this.windows.filter(w => !w.minimized);
      this.activeWindow = visibleWindows.length > 0 ? visibleWindows[visibleWindows.length - 1] : null;
    }
    
    // Update desktop
    this.desktop.variant.windows = [...this.windows];
    this.desktop.variant.activeWindowId = this.activeWindow?.id || null;
    this.desktop.render();
    
    // Update taskbar
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
   * Maximize a window
   * @param {string} windowId - Window ID
   */
  maximizeWindow(windowId) {
    const window = this.windows.find(w => w.id === windowId);
    if (!window) return;
    
    // Toggle maximized state
    window.maximized = !window.maximized;
    
    // Ensure window is not minimized
    window.minimized = false;
    
    // Make this the active window
    this.activeWindow = window;
    
    // Update desktop
    this.desktop.variant.windows = [...this.windows];
    this.desktop.variant.activeWindowId = windowId;
    this.desktop.render();
    
    // Update taskbar
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
    const window = this.windows.find(w => w.id === windowId);
    if (!window) return;
    
    // If window is minimized, restore it
    if (window.minimized) {
      window.minimized = false;
    }
    
    // Move window to front by updating z-index
    this.windows.forEach(w => {
      w.zIndex = w.id === windowId ? this.windows.length : w.zIndex;
    });
    
    // Sort windows by z-index
    this.windows.sort((a, b) => a.zIndex - b.zIndex);
    
    // Set as active window
    this.activeWindow = window;
    
    // Update desktop
    this.desktop.variant.windows = [...this.windows];
    this.desktop.variant.activeWindowId = windowId;
    this.desktop.render();
    
    // Update taskbar
    this.taskbar.variant.openWindows = this.windows.map(w => ({
      id: w.id,
      appId: w.appId,
      title: w.title,
      isActive: w.id === windowId
    }));
    this.taskbar.render();
    
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

module.exports = { Shell };