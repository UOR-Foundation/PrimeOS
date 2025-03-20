// PrimeOS Settings Application
import { SettingsStore } from './models/settings-store.js';
import { SettingsPanel } from './components/settings-panel.js';
import { SecretsManager } from './components/secrets-manager.js';

// Create the Settings App class
class SettingsApp {
  /**
   * Create a new Settings App
   * @param {Object} shell - Shell instance
   */
  constructor(shell) {
    this.shell = shell || {};
    this.name = 'settings';
    this.title = 'Settings';
    this.container = null;
    this.activeView = null;
    this.navigation = [];
    
    // Will be initialized later
    this.settingsStore = null;
    this.settingsPanel = null;
    this.secretsManager = null;
    this.eventBus = null;
    this.storage = null;
  }
  
  /**
   * Initialize the application
   * @param {HTMLElement} container - Container element
   * @param {Object} options - Options
   * @returns {Promise<Object>} App interface
   */
  async initialize(container, options = {}) {
    try {
      // Store references
      this.container = container;
      this.options = options || {};
      
      // Get services from options or shell
      this.eventBus = options.eventBus || 
                      (this.shell.getComponent ? this.shell.getComponent('eventBus') : null) || 
                      { publish: () => {}, subscribe: () => {} };
      
      this.storage = options.store || options.storage || 
                    (this.shell.getComponent ? this.shell.getComponent('storage') : null) || 
                    this._createInMemoryStorage();
      
      const secureVault = options.secureVault || 
                          (this.shell.getComponent ? this.shell.getComponent('secureVault') : null);
      
      // Initialize SettingsStore
      this.settingsStore = new SettingsStore({
        storage: this.storage,
        eventBus: this.eventBus,
        secureVault: secureVault
      });
      
      await this.settingsStore.initialize();
      
      // Initialize SettingsPanel
      this.settingsPanel = new SettingsPanel({
        container: document.createElement('div'),
        store: this.settingsStore,
        eventBus: this.eventBus
      });
      
      await this.settingsPanel.initialize();
      
      // Initialize SecretsManager
      this.secretsManager = new SecretsManager({
        container: document.createElement('div'),
        settingsStore: this.settingsStore,
        secureVault: secureVault,
        eventBus: this.eventBus
      });
      
      await this.secretsManager.initialize();
      
      // Subscribe to settings events
      this.eventBus.subscribe('settings:changed', this.handleSettingsEvents.bind(this));
      
      // Subscribe to app lifecycle events
      this.eventBus.subscribe('app:settings:start', this.start.bind(this));
      this.eventBus.subscribe('app:settings:stop', this.stop.bind(this));
      
      // Register app with shell if available
      if (this.shell.registerApp) {
        this.shell.registerApp('settings', {
          name: this.name,
          title: this.title,
          start: this.start.bind(this),
          stop: this.stop.bind(this)
        });
      }
      
      // Return app interface
      return {
        name: this.name,
        title: this.title,
        render: () => this.render(),
        stop: () => this.stop()
      };
    } catch (error) {
      console.error('Failed to initialize settings app:', error);
      
      // Create error UI
      this._renderError(container, error);
      
      // Return minimal app interface
      return {
        name: this.name,
        title: 'Settings (Error)',
        render: () => false,
        stop: () => true
      };
    }
  }
  
  /**
   * Start the app
   * @returns {Promise<boolean>} Success flag
   */
  async start() {
    try {
      if (!this.container) {
        this.container = this.shell.getAppContainer ? 
                        this.shell.getAppContainer('settings') : 
                        document.createElement('div');
      }
      
      // Clear the container
      this.container.innerHTML = '';
      
      // Setup navigation
      this.setupNavigation();
      
      // Set active view
      await this.setActiveView('settings');
      
      return true;
    } catch (error) {
      console.error('Failed to start settings app:', error);
      this._renderError(this.container, error);
      return false;
    }
  }
  
  /**
   * Stop the app
   * @returns {Promise<boolean>} Success flag
   */
  async stop() {
    try {
      // Clean up
      this.container.innerHTML = '';
      this.activeView = null;
      
      return true;
    } catch (error) {
      console.error('Failed to stop settings app:', error);
      return false;
    }
  }
  
  /**
   * Render the app
   * @returns {boolean} Success flag
   */
  render() {
    // Return to the active view
    if (this.activeView) {
      this.setActiveView(this.activeView);
    } else {
      this.setActiveView('settings');
    }
    
    return true;
  }
  
  /**
   * Setup navigation
   */
  setupNavigation() {
    // Define available views
    this.navigation = [
      { view: 'settings', label: 'Settings', icon: '⚙️' },
      { view: 'secrets', label: 'API Keys', icon: '🔑' },
      { view: 'about', label: 'About', icon: 'ℹ️' }
    ];
    
    // Create navigation UI
    const navContainer = document.createElement('div');
    navContainer.className = 'settings-nav-container';
    
    // Create navigation header
    const navHeader = document.createElement('h2');
    navHeader.textContent = 'Settings';
    navContainer.appendChild(navHeader);
    
    // Create navigation list
    const navList = document.createElement('ul');
    navList.className = 'settings-nav-list';
    
    // Add navigation items
    for (const item of this.navigation) {
      const navItem = document.createElement('li');
      navItem.className = 'settings-nav-item';
      
      const navLink = document.createElement('a');
      navLink.href = '#';
      navLink.className = 'settings-nav-link';
      navLink.dataset.view = item.view;
      navLink.innerHTML = `<span class="settings-nav-icon">${item.icon}</span> ${item.label}`;
      
      // Add click handler
      navLink.addEventListener('click', this.handleNavigation.bind(this));
      
      navItem.appendChild(navLink);
      navList.appendChild(navItem);
    }
    
    navContainer.appendChild(navList);
    
    // Add styles
    const style = document.createElement('style');
    style.textContent = `
      .settings-app {
        display: flex;
        height: 100%;
        font-family: system-ui, sans-serif;
      }
      
      .settings-nav-container {
        width: 200px;
        background: #f5f5f5;
        border-right: 1px solid #ddd;
        padding: 20px;
      }
      
      .settings-nav-list {
        list-style: none;
        padding: 0;
        margin: 0;
      }
      
      .settings-nav-item {
        margin-bottom: 8px;
      }
      
      .settings-nav-link {
        display: flex;
        align-items: center;
        padding: 8px 12px;
        color: #333;
        text-decoration: none;
        border-radius: 4px;
      }
      
      .settings-nav-link:hover {
        background: #e0e0e0;
      }
      
      .settings-nav-link.active {
        background: #0066cc;
        color: white;
      }
      
      .settings-nav-icon {
        margin-right: 8px;
      }
      
      .settings-content {
        flex: 1;
        padding: 20px;
        overflow-y: auto;
      }
      
      .settings-error {
        background: #ffebee;
        color: #c62828;
        padding: 20px;
        border-radius: 4px;
        margin: 20px;
      }
    `;
    
    // Create main app container
    const appContainer = document.createElement('div');
    appContainer.className = 'settings-app';
    
    // Create content container
    const contentContainer = document.createElement('div');
    contentContainer.className = 'settings-content';
    contentContainer.id = 'settings-content';
    
    // Assemble UI
    appContainer.appendChild(style);
    appContainer.appendChild(navContainer);
    appContainer.appendChild(contentContainer);
    
    // Add to container
    this.container.appendChild(appContainer);
  }
  
  /**
   * Handle navigation clicks
   * @param {Event} event - Click event
   */
  async handleNavigation(event) {
    event.preventDefault();
    const view = event.target.dataset.view || event.target.parentElement.dataset.view;
    
    if (view) {
      // Update active state
      const navLinks = this.container.querySelectorAll('.settings-nav-link');
      navLinks.forEach(link => {
        if (link.dataset.view === view || link.parentElement.dataset.view === view) {
          link.classList.add('active');
        } else {
          link.classList.remove('active');
        }
      });
      
      // Set active view
      await this.setActiveView(view);
    }
  }
  
  /**
   * Set active view
   * @param {string} view - View name
   * @returns {Promise<boolean>} Success flag
   */
  async setActiveView(view) {
    try {
      // Update active view
      this.activeView = view;
      
      // Get content container
      const contentContainer = this.container.querySelector('#settings-content');
      if (!contentContainer) {
        return false;
      }
      
      // Clear content
      contentContainer.innerHTML = '';
      
      // Render selected view
      if (view === 'settings') {
        contentContainer.appendChild(this.settingsPanel.render());
      } else if (view === 'secrets') {
        // Ensure initialized
        if (!this.secretsManager.initialized) {
          await this.secretsManager.initialize();
        }
        this.secretsManager.render();
        contentContainer.appendChild(this.secretsManager.container);
      } else if (view === 'about') {
        this.renderAboutView(contentContainer);
      }
      
      return true;
    } catch (error) {
      console.error(`Failed to set active view to ${view}:`, error);
      this._renderError(this.container.querySelector('#settings-content'), error);
      return false;
    }
  }
  
  /**
   * Render the about view
   * @param {HTMLElement} container - Container element
   */
  renderAboutView(container) {
    container.innerHTML = `
      <div class="about-view">
        <h2>About PrimeOS</h2>
        <div class="about-logo">π</div>
        <p>PrimeOS Reference Implementation</p>
        <p>Version: 1.0.0</p>
        <p>A mathematically sound operating system with manifold-based architecture.</p>
        
        <h3>System Information</h3>
        <ul class="about-info">
          <li><strong>Core:</strong> PrimeOS Kernel</li>
          <li><strong>Architecture:</strong> Manifold-based</li>
          <li><strong>UI Framework:</strong> Web Components</li>
          <li><strong>Apps:</strong> 5 (Calculator, Text Editor, File Explorer, Settings, App Factory)</li>
        </ul>
        
        <p class="about-footer">© 2025 Prime Research Team</p>
      </div>
    `;
    
    // Add styles
    const style = document.createElement('style');
    style.textContent = `
      .about-view {
        max-width: 600px;
        margin: 0 auto;
        text-align: center;
      }
      
      .about-logo {
        font-size: 72px;
        margin: 20px 0;
        color: #0066cc;
      }
      
      .about-info {
        text-align: left;
        list-style: none;
        padding: 0;
        margin: 20px auto;
        max-width: 400px;
      }
      
      .about-info li {
        padding: 8px 0;
        border-bottom: 1px solid #eee;
      }
      
      .about-footer {
        margin-top: 40px;
        font-size: 0.9em;
        color: #666;
      }
    `;
    
    container.appendChild(style);
  }
  
  /**
   * Handle settings events
   * @param {Object} event - Settings change event
   */
  async handleSettingsEvents(event) {
    // Only handle specific events
    if (event.category === 'appearance' && event.key === 'theme') {
      // Notify system about theme change
      this.eventBus.publish('system:theme-changed', {
        theme: event.value,
        source: 'settings',
        timestamp: new Date().toISOString()
      });
    } else if (event.category === 'general' && event.key === 'language') {
      // Notify system about language change
      this.eventBus.publish('system:language-changed', {
        language: event.value,
        source: 'settings',
        timestamp: new Date().toISOString()
      });
    }
  }
  
  /**
   * Get system settings
   * @returns {Promise<Object>} System settings
   */
  async getSystemSettings() {
    const settings = {};
    
    // Get theme
    if (this.shell.getTheme) {
      settings.theme = this.shell.getTheme();
    } else {
      // Default to light theme
      settings.theme = 'light';
    }
    
    return settings;
  }
  
  /**
   * Render error message
   * @private
   * @param {HTMLElement} container - Container element
   * @param {Error} error - Error object
   */
  _renderError(container, error) {
    container.innerHTML = `
      <div class="settings-error">
        <h3>Settings App Error</h3>
        <p>${error.message || 'Failed to initialize settings application'}</p>
        <p>Please try again or contact system administrator.</p>
      </div>
    `;
  }
  
  /**
   * Create in-memory storage
   * @private
   * @returns {Object} Storage object
   */
  _createInMemoryStorage() {
    const storage = new Map();
    
    return {
      getItem: (key) => Promise.resolve(storage.get(key) || null),
      setItem: (key, value) => {
        storage.set(key, value);
        return Promise.resolve(true);
      },
      removeItem: (key) => {
        storage.delete(key);
        return Promise.resolve(true);
      }
    };
  }
}

// Export for module system
export default {
  initialize: function(container, options) {
    const app = new SettingsApp(options?.shell || null);
    return app.initialize(container, options);
  }
};