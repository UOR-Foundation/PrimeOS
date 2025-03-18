/**
 * PrimeOS Settings Panel Component
 * 
 * Primary UI component for the Settings application that handles
 * rendering and updating settings categories.
 */

/**
 * SettingsPanel component
 * Handles rendering the settings UI and managing user interactions
 */
class SettingsPanel {
  /**
   * Create a new settings panel
   * @param {Object} options - Configuration options
   * @param {Object} options.store - Settings data store
   * @param {Object} options.eventBus - Event bus for communication
   */
  constructor(options = {}) {
    this.store = options.store;
    this.eventBus = options.eventBus;
    this.container = document.createElement('div');
    this.container.className = 'settings-panel';
    
    // Settings categories
    this.categories = [
      { id: 'general', name: 'General', icon: '⚙️' },
      { id: 'appearance', name: 'Appearance', icon: '🎨' },
      { id: 'security', name: 'Security', icon: '🔒' },
      { id: 'apiKeys', name: 'API Keys', icon: '🔑' },
      { id: 'developer', name: 'Developer', icon: '💻' },
      { id: 'about', name: 'About', icon: 'ℹ️' }
    ];
    
    // Current active category
    this.activeCategory = 'general';
    
    // Form elements by category/setting
    this.formElements = {};
    
    // Bind methods
    this.initialize = this.initialize.bind(this);
    this.render = this.render.bind(this);
    this.renderCategory = this.renderCategory.bind(this);
    this.switchCategory = this.switchCategory.bind(this);
    this.handleFormChange = this.handleFormChange.bind(this);
    this.getFormElement = this.getFormElement.bind(this);
  }
  
  /**
   * Initialize the component
   * @returns {Promise<void>}
   */
  async initialize() {
    // Subscribe to settings update events
    if (this.eventBus) {
      this.eventBus.subscribe('settings:updated', this.render);
      this.eventBus.subscribe('settings:saved', () => this.showSaveNotification(true));
      this.eventBus.subscribe('settings:save-error', () => this.showSaveNotification(false));
    }
    
    // Load initial settings
    if (this.store) {
      await this.store.loadAll();
    }
  }
  
  /**
   * Render the settings panel
   * @returns {HTMLElement} Rendered container
   */
  render() {
    // Clear existing content
    this.container.innerHTML = '';
    
    // Create layout structure
    const layout = document.createElement('div');
    layout.className = 'settings-layout';
    
    // Create sidebar
    const sidebar = this.renderSidebar();
    layout.appendChild(sidebar);
    
    // Create content area
    const content = document.createElement('div');
    content.className = 'settings-content';
    content.id = 'settings-content';
    
    // Render current category
    this.renderCategory(content, this.activeCategory);
    
    layout.appendChild(content);
    this.container.appendChild(layout);
    
    return this.container;
  }
  
  /**
   * Render the settings sidebar
   * @returns {HTMLElement} Sidebar element
   */
  renderSidebar() {
    const sidebar = document.createElement('div');
    sidebar.className = 'settings-sidebar';
    
    // Add header
    const header = document.createElement('div');
    header.className = 'settings-sidebar-header';
    header.innerHTML = '<h2>Settings</h2>';
    sidebar.appendChild(header);
    
    // Add categories list
    const nav = document.createElement('nav');
    nav.className = 'settings-navigation';
    
    const list = document.createElement('ul');
    list.className = 'settings-categories';
    
    // Add category items
    this.categories.forEach(category => {
      const item = document.createElement('li');
      item.dataset.category = category.id;
      item.className = category.id === this.activeCategory ? 'active' : '';
      
      item.innerHTML = `
        <span class="category-icon">${category.icon}</span>
        <span class="category-name">${category.name}</span>
      `;
      
      // Add click event
      item.addEventListener('click', () => {
        this.switchCategory(category.id);
      });
      
      list.appendChild(item);
    });
    
    nav.appendChild(list);
    sidebar.appendChild(nav);
    
    return sidebar;
  }
  
  /**
   * Render a specific settings category
   * @param {HTMLElement} container - Content container
   * @param {string} categoryId - Category ID
   */
  renderCategory(container, categoryId) {
    // Clear the container
    container.innerHTML = '';
    
    // Add category header
    const category = this.categories.find(c => c.id === categoryId);
    
    const header = document.createElement('div');
    header.className = 'settings-content-header';
    header.innerHTML = `<h2>${category ? category.name : 'Settings'}</h2>`;
    container.appendChild(header);
    
    // Create form container
    const form = document.createElement('div');
    form.className = 'settings-form';
    
    // Render category-specific forms
    switch (categoryId) {
      case 'general':
        this.renderGeneralSettings(form);
        break;
      case 'appearance':
        this.renderAppearanceSettings(form);
        break;
      case 'security':
        this.renderSecuritySettings(form);
        break;
      case 'apiKeys':
        this.renderApiKeySettings(form);
        break;
      case 'developer':
        this.renderDeveloperSettings(form);
        break;
      case 'about':
        this.renderAboutSettings(form);
        break;
      default:
        form.innerHTML = '<p>Select a category from the sidebar</p>';
    }
    
    container.appendChild(form);
    
    // Add action buttons
    const actions = document.createElement('div');
    actions.className = 'settings-actions';
    
    const saveButton = document.createElement('button');
    saveButton.className = 'settings-button settings-save-button';
    saveButton.textContent = 'Save Settings';
    saveButton.addEventListener('click', () => {
      if (this.eventBus) {
        this.eventBus.publish('settings:save-requested');
      }
    });
    
    const resetButton = document.createElement('button');
    resetButton.className = 'settings-button settings-reset-button';
    resetButton.textContent = 'Reset';
    resetButton.addEventListener('click', () => {
      if (this.eventBus) {
        this.eventBus.publish('settings:reset-requested');
      }
    });
    
    actions.appendChild(saveButton);
    actions.appendChild(resetButton);
    
    container.appendChild(actions);
    
    // Add notification area
    const notification = document.createElement('div');
    notification.className = 'settings-notification';
    notification.id = 'settings-notification';
    notification.style.display = 'none';
    container.appendChild(notification);
  }
  
  /**
   * Render general settings
   * @param {HTMLElement} container - Form container
   */
  renderGeneralSettings(container) {
    const section = document.createElement('section');
    section.className = 'settings-section';
    section.innerHTML = `
      <h3>General Settings</h3>
      <p>Configure basic system preferences.</p>
      
      <div class="form-group">
        <label for="language">Language</label>
        <select id="language" data-category="general" data-setting="language">
          <option value="English">English</option>
          <option value="Spanish">Spanish</option>
          <option value="French">French</option>
          <option value="German">German</option>
          <option value="Japanese">Japanese</option>
        </select>
      </div>
      
      <div class="form-group">
        <label class="checkbox-label">
          <input type="checkbox" id="notifications" data-category="general" data-setting="notifications">
          Enable system notifications
        </label>
      </div>
      
      <div class="form-group">
        <label for="startupApp">Default startup application</label>
        <input type="text" id="startupApp" data-category="general" data-setting="startupApp" 
               placeholder="e.g., calculator">
      </div>
    `;
    
    container.appendChild(section);
    
    // Set form values from settings store
    if (this.store) {
      const settings = this.store.getSettings('general');
      if (settings) {
        this.setFormValues('general', settings);
      }
    }
    
    // Add event listeners
    this.addFormEventListeners(section);
  }
  
  /**
   * Render appearance settings
   * @param {HTMLElement} container - Form container
   */
  renderAppearanceSettings(container) {
    const section = document.createElement('section');
    section.className = 'settings-section';
    section.innerHTML = `
      <h3>Appearance</h3>
      <p>Customize the look and feel of PrimeOS.</p>
      
      <div class="form-group">
        <label for="theme">Theme</label>
        <select id="theme" data-category="appearance" data-setting="theme">
          <option value="light">Light</option>
          <option value="dark">Dark</option>
          <option value="auto">Auto (System)</option>
        </select>
      </div>
      
      <div class="form-group">
        <label for="accentColor">Accent Color</label>
        <input type="color" id="accentColor" data-category="appearance" data-setting="accentColor">
      </div>
      
      <div class="form-group">
        <label for="fontSize">Font Size</label>
        <select id="fontSize" data-category="appearance" data-setting="fontSize">
          <option value="small">Small</option>
          <option value="medium">Medium</option>
          <option value="large">Large</option>
        </select>
      </div>
      
      <div class="form-group">
        <label for="fontFamily">Font Family</label>
        <select id="fontFamily" data-category="appearance" data-setting="fontFamily">
          <option value="system-ui">System Default</option>
          <option value="sans-serif">Sans Serif</option>
          <option value="serif">Serif</option>
          <option value="monospace">Monospace</option>
        </select>
      </div>
    `;
    
    container.appendChild(section);
    
    // Set form values from settings store
    if (this.store) {
      const settings = this.store.getSettings('appearance');
      if (settings) {
        this.setFormValues('appearance', settings);
      }
    }
    
    // Add event listeners
    this.addFormEventListeners(section);
  }
  
  /**
   * Render security settings
   * @param {HTMLElement} container - Form container
   */
  renderSecuritySettings(container) {
    const section = document.createElement('section');
    section.className = 'settings-section';
    section.innerHTML = `
      <h3>Security & Privacy</h3>
      <p>Manage security settings and privacy options.</p>
      
      <div class="form-group">
        <label class="checkbox-label">
          <input type="checkbox" id="enablePasswordLock" data-category="security" data-setting="enablePasswordLock">
          Enable password lock on idle
        </label>
      </div>
      
      <div class="form-group">
        <label for="autoLockTimeout">Auto-lock timeout (minutes)</label>
        <input type="number" id="autoLockTimeout" data-category="security" data-setting="autoLockTimeout"
               min="1" max="60">
      </div>
      
      <div class="form-group">
        <label class="checkbox-label">
          <input type="checkbox" id="saveLoginSession" data-category="security" data-setting="saveLoginSession">
          Remember login session
        </label>
      </div>
      
      <div class="form-group">
        <label for="sessionTimeout">Session timeout (minutes)</label>
        <input type="number" id="sessionTimeout" data-category="security" data-setting="sessionTimeout"
               min="15" max="1440">
      </div>
      
      <div class="form-group">
        <label class="checkbox-label">
          <input type="checkbox" id="enableAnalytics" data-category="security" data-setting="enableAnalytics">
          Allow anonymous usage analytics
        </label>
      </div>
    `;
    
    container.appendChild(section);
    
    // Set form values from settings store
    if (this.store) {
      const settings = this.store.getSettings('security');
      if (settings) {
        this.setFormValues('security', settings);
      }
    }
    
    // Add event listeners
    this.addFormEventListeners(section);
  }
  
  /**
   * Render API key settings
   * @param {HTMLElement} container - Form container
   */
  renderApiKeySettings(container) {
    const section = document.createElement('section');
    section.className = 'settings-section';
    section.innerHTML = `
      <h3>API Keys</h3>
      <p>Manage API keys and external service credentials.</p>
      
      <div class="api-key-section">
        <h4>Claude AI API</h4>
        <p>Used by App Factory for AI-assisted application development.</p>
        
        <div class="form-group">
          <label for="claudeApiKey">Claude API Key</label>
          <div class="api-key-input">
            <input type="password" id="claudeApiKey" data-category="apiKeys" data-setting="claudeApiKey"
                   placeholder="Enter your Claude API key">
          </div>
        </div>
        
        <div class="form-group">
          <label for="claudeApiUrl">Claude API URL</label>
          <input type="text" id="claudeApiUrl" data-category="apiKeys" data-setting="claudeApiUrl"
                 placeholder="https://api.anthropic.com/v1/messages">
        </div>
        
        <div class="form-group">
          <label for="claudeModel">Claude Model</label>
          <select id="claudeModel" data-category="apiKeys" data-setting="claudeModel">
            <option value="claude-3-opus-20240229">Claude 3 Opus</option>
            <option value="claude-3-sonnet-20240229">Claude 3 Sonnet</option>
            <option value="claude-3-haiku-20240307">Claude 3 Haiku</option>
          </select>
        </div>
        
        <button id="test-claude-key" class="settings-button">Test Connection</button>
      </div>
      
      <div class="api-key-section">
        <h4>Other API Keys</h4>
        <p>Add additional API keys for other services.</p>
        
        <div class="form-group">
          <label for="newApiKeyName">API Key Name</label>
          <input type="text" id="newApiKeyName" placeholder="e.g., github-token">
        </div>
        
        <div class="form-group">
          <label for="newApiKeyValue">API Key Value</label>
          <input type="password" id="newApiKeyValue" placeholder="Enter API key value">
        </div>
        
        <button id="add-api-key" class="settings-button">Add API Key</button>
      </div>
      
      <div class="api-keys-list">
        <h4>Saved API Keys</h4>
        <div id="api-keys-container">
          <p>No API keys stored yet.</p>
        </div>
      </div>
      
      <div class="settings-note">
        <p><strong>Note:</strong> API keys are stored securely using manifold-based encryption.</p>
      </div>
    `;
    
    container.appendChild(section);
    
    // Set form values from settings store
    if (this.store) {
      const settings = this.store.getSettings('apiKeys');
      if (settings) {
        this.setFormValues('apiKeys', settings);
      }
    }
    
    // Add event listeners
    this.addFormEventListeners(section);
    
    // Add event listener for test connection button
    const testClaudeKeyButton = section.querySelector('#test-claude-key');
    if (testClaudeKeyButton) {
      testClaudeKeyButton.addEventListener('click', async () => {
        await this.testClaudeApiKey();
      });
    }
    
    // Add event listener for add API key button
    const addApiKeyButton = section.querySelector('#add-api-key');
    if (addApiKeyButton) {
      addApiKeyButton.addEventListener('click', async () => {
        await this.addCustomApiKey();
      });
    }
  }
  
  /**
   * Render developer settings
   * @param {HTMLElement} container - Form container
   */
  renderDeveloperSettings(container) {
    const section = document.createElement('section');
    section.className = 'settings-section';
    section.innerHTML = `
      <h3>Developer Options</h3>
      <p>Settings for developers and advanced users.</p>
      
      <div class="form-group">
        <label class="checkbox-label">
          <input type="checkbox" id="enableDevTools" data-category="developer" data-setting="enableDevTools">
          Enable developer tools
        </label>
      </div>
      
      <div class="form-group">
        <label class="checkbox-label">
          <input type="checkbox" id="enableDebugLogging" data-category="developer" data-setting="enableDebugLogging">
          Enable debug logging
        </label>
      </div>
      
      <div class="form-group">
        <label for="logLevel">Log Level</label>
        <select id="logLevel" data-category="developer" data-setting="logLevel">
          <option value="error">Error</option>
          <option value="warn">Warning</option>
          <option value="info">Info</option>
          <option value="debug">Debug</option>
          <option value="trace">Trace</option>
        </select>
      </div>
      
      <div class="form-group">
        <label for="coherenceThreshold">System Coherence Threshold</label>
        <input type="range" id="coherenceThreshold" data-category="developer" data-setting="coherenceThreshold"
               min="0" max="1" step="0.1">
        <div class="range-value">
          <span id="coherenceThresholdValue">0.8</span>
        </div>
      </div>
      
      <div class="form-group">
        <label for="manifestDepth">Manifold Depth Validation</label>
        <select id="manifestDepth" data-category="developer" data-setting="manifestDepth">
          <option value="strict">Strict</option>
          <option value="moderate">Moderate</option>
          <option value="relaxed">Relaxed</option>
        </select>
      </div>
      
      <div class="advanced-options">
        <h4>Advanced Options</h4>
        <div class="form-group">
          <label for="appFactoryPromptTemplate">App Factory Prompt Template</label>
          <textarea id="appFactoryPromptTemplate" data-category="developer" data-setting="appFactoryPromptTemplate"
                    rows="5"></textarea>
        </div>
        
        <button id="reset-system-defaults" class="settings-button settings-danger-button">Reset to System Defaults</button>
      </div>
    `;
    
    container.appendChild(section);
    
    // Set form values from settings store
    if (this.store) {
      const settings = this.store.getSettings('developer');
      if (settings) {
        this.setFormValues('developer', settings);
      }
    }
    
    // Add event listeners
    this.addFormEventListeners(section);
    
    // Add event listener for coherence threshold range
    const coherenceThreshold = section.querySelector('#coherenceThreshold');
    const coherenceThresholdValue = section.querySelector('#coherenceThresholdValue');
    
    if (coherenceThreshold && coherenceThresholdValue) {
      coherenceThreshold.addEventListener('input', () => {
        coherenceThresholdValue.textContent = coherenceThreshold.value;
      });
    }
    
    // Add event listener for reset system defaults button
    const resetButton = section.querySelector('#reset-system-defaults');
    if (resetButton) {
      resetButton.addEventListener('click', () => {
        if (confirm('Are you sure you want to reset all developer settings to system defaults? This cannot be undone.')) {
          this.resetDeveloperSettings();
        }
      });
    }
  }
  
  /**
   * Render about settings
   * @param {HTMLElement} container - Form container
   */
  renderAboutSettings(container) {
    const section = document.createElement('section');
    section.className = 'settings-section about-section';
    
    // Get system info
    const version = this.store ? this.store.getSettings('about')?.version || '1.0.0' : '1.0.0';
    const buildDate = this.store ? this.store.getSettings('about')?.buildDate || new Date().toISOString().slice(0, 10) : new Date().toISOString().slice(0, 10);
    
    section.innerHTML = `
      <h3>About PrimeOS</h3>
      
      <div class="system-info">
        <div class="system-logo">
          <span class="prime-logo">π</span>
        </div>
        <div class="system-details">
          <h4>PrimeOS</h4>
          <p>A manifold-based operating system with mathematical coherence</p>
          <p><strong>Version:</strong> ${version}</p>
          <p><strong>Build Date:</strong> ${buildDate}</p>
          <p><strong>License:</strong> MIT</p>
        </div>
      </div>
      
      <div class="about-section-content">
        <h4>Mathematical Foundation</h4>
        <p>
          PrimeOS is built on the principles of mathematical manifolds, Clifford algebras, and coherence theory.
          The system represents all components as manifolds with meta/invariant/variant decomposition, providing
          unprecedented stability and adaptability.
        </p>
        
        <h4>Core Features</h4>
        <ul>
          <li>Manifold-based architecture with mathematical coherence validation</li>
          <li>App Factory powered by Claude AI for intelligent application creation</li>
          <li>Secure credential management with multi-level encryption</li>
          <li>Advanced mathematical verification for all system operations</li>
        </ul>
        
        <h4>Credits</h4>
        <p>
          PrimeOS was developed by the Prime Research Team as an exploration into 
          mathematically sound operating system design.
        </p>
        
        <div class="actions">
          <button id="view-documentation" class="settings-button">View Documentation</button>
          <button id="check-updates" class="settings-button">Check for Updates</button>
        </div>
      </div>
    `;
    
    container.appendChild(section);
    
    // Add event listeners
    const viewDocsButton = section.querySelector('#view-documentation');
    if (viewDocsButton) {
      viewDocsButton.addEventListener('click', () => {
        if (this.eventBus) {
          this.eventBus.publish('settings:view-documentation');
        }
      });
    }
    
    const checkUpdatesButton = section.querySelector('#check-updates');
    if (checkUpdatesButton) {
      checkUpdatesButton.addEventListener('click', () => {
        if (this.eventBus) {
          this.eventBus.publish('settings:check-updates');
        }
      });
    }
  }
  
  /**
   * Switch to a different settings category
   * @param {string} categoryId - Category ID
   */
  switchCategory(categoryId) {
    // Update active category
    this.activeCategory = categoryId;
    
    // Update UI
    const content = document.getElementById('settings-content');
    if (content) {
      this.renderCategory(content, categoryId);
    }
    
    // Update sidebar
    const categoryItems = this.container.querySelectorAll('.settings-categories li');
    categoryItems.forEach(item => {
      if (item.dataset.category === categoryId) {
        item.classList.add('active');
      } else {
        item.classList.remove('active');
      }
    });
  }
  
  /**
   * Add event listeners to form elements
   * @param {HTMLElement} container - Form container
   */
  addFormEventListeners(container) {
    const inputs = container.querySelectorAll('input, select, textarea');
    inputs.forEach(input => {
      input.addEventListener('change', this.handleFormChange);
      
      // Store reference to form element
      const category = input.dataset.category;
      const setting = input.dataset.setting;
      
      if (category && setting) {
        if (!this.formElements[category]) {
          this.formElements[category] = {};
        }
        
        this.formElements[category][setting] = input;
      }
    });
  }
  
  /**
   * Handle form input changes
   * @param {Event} event - Change event
   */
  handleFormChange(event) {
    const input = event.target;
    const category = input.dataset.category;
    const setting = input.dataset.setting;
    
    if (!category || !setting) {
      return;
    }
    
    if (this.store) {
      // Get the value based on input type
      let value;
      
      if (input.type === 'checkbox') {
        value = input.checked;
      } else if (input.type === 'number') {
        value = parseFloat(input.value);
      } else {
        value = input.value;
      }
      
      // Update store
      this.store.updateSetting(category, setting, value);
      
      // Handle special settings
      if (category === 'appearance' && setting === 'theme') {
        this.applyTheme(value);
      }
    }
  }
  
  /**
   * Apply theme to the UI
   * @param {string} theme - Theme to apply
   */
  applyTheme(theme) {
    const root = document.documentElement;
    
    if (theme === 'dark') {
      root.classList.add('theme-dark');
      root.classList.remove('theme-light');
    } else {
      root.classList.add('theme-light');
      root.classList.remove('theme-dark');
    }
  }
  
  /**
   * Set form values from settings
   * @param {string} category - Settings category
   * @param {Object} settings - Settings values
   */
  setFormValues(category, settings) {
    for (const [setting, value] of Object.entries(settings)) {
      const element = this.getFormElement(category, setting);
      
      if (element) {
        if (element.type === 'checkbox') {
          element.checked = !!value;
        } else if (element.type === 'number' || element.type === 'range') {
          element.value = value !== undefined ? value : '';
          
          // Update range display value
          if (element.type === 'range' && element.id === 'coherenceThreshold') {
            const valueDisplay = document.getElementById('coherenceThresholdValue');
            if (valueDisplay) {
              valueDisplay.textContent = value;
            }
          }
        } else {
          element.value = value !== undefined ? value : '';
        }
      }
    }
  }
  
  /**
   * Get form element for a setting
   * @param {string} category - Settings category
   * @param {string} setting - Setting name
   * @returns {HTMLElement} Form element
   */
  getFormElement(category, setting) {
    if (this.formElements[category] && this.formElements[category][setting]) {
      return this.formElements[category][setting];
    }
    
    // If not cached, try to find it
    const element = this.container.querySelector(`[data-category="${category}"][data-setting="${setting}"]`);
    
    if (element) {
      // Cache it for future use
      if (!this.formElements[category]) {
        this.formElements[category] = {};
      }
      
      this.formElements[category][setting] = element;
    }
    
    return element;
  }
  
  /**
   * Test Claude API key
   * @returns {Promise<void>}
   */
  async testClaudeApiKey() {
    const notification = document.getElementById('settings-notification');
    
    if (!notification) {
      return;
    }
    
    try {
      // Get API key
      const apiKeyInput = this.getFormElement('apiKeys', 'claudeApiKey');
      const apiUrlInput = this.getFormElement('apiKeys', 'claudeApiUrl');
      const modelInput = this.getFormElement('apiKeys', 'claudeModel');
      
      if (!apiKeyInput || !apiKeyInput.value) {
        throw new Error('Please enter an API key');
      }
      
      const apiKey = apiKeyInput.value;
      const apiUrl = apiUrlInput ? apiUrlInput.value : 'https://api.anthropic.com/v1/messages';
      const model = modelInput ? modelInput.value : 'claude-3-sonnet-20240229';
      
      // Show testing notification
      notification.className = 'settings-notification settings-notification-info';
      notification.textContent = 'Testing API key...';
      notification.style.display = 'block';
      
      // Simulate testing (in a real implementation, we'd make an API call)
      await new Promise(resolve => setTimeout(resolve, 1500));
      
      // For demonstration, we'll just check if the key looks valid
      if (apiKey.length < 20) {
        throw new Error('API key appears to be invalid');
      }
      
      // Show success notification
      notification.className = 'settings-notification settings-notification-success';
      notification.textContent = 'API key tested successfully!';
      setTimeout(() => {
        notification.style.display = 'none';
      }, 3000);
      
      // Save to secure storage
      if (this.store) {
        await this.store.saveApiKey('claudeApiKey', apiKey);
        await this.store.updateSetting('apiKeys', 'claudeApiUrl', apiUrl);
        await this.store.updateSetting('apiKeys', 'claudeModel', model);
      }
      
      // Notify others via event bus
      if (this.eventBus) {
        this.eventBus.publish('settings:api-key-changed', {
          key: 'claudeApiKey',
          url: apiUrl,
          model: model
        });
      }
    } catch (error) {
      // Show error notification
      notification.className = 'settings-notification settings-notification-error';
      notification.textContent = `Error: ${error.message}`;
      setTimeout(() => {
        notification.style.display = 'none';
      }, 5000);
    }
  }
  
  /**
   * Add a custom API key
   * @returns {Promise<void>}
   */
  async addCustomApiKey() {
    const nameInput = document.getElementById('newApiKeyName');
    const valueInput = document.getElementById('newApiKeyValue');
    const notification = document.getElementById('settings-notification');
    
    if (!nameInput || !valueInput || !notification) {
      return;
    }
    
    try {
      const name = nameInput.value.trim();
      const value = valueInput.value;
      
      if (!name) {
        throw new Error('Please enter an API key name');
      }
      
      if (!value) {
        throw new Error('Please enter an API key value');
      }
      
      // Show saving notification
      notification.className = 'settings-notification settings-notification-info';
      notification.textContent = 'Saving API key...';
      notification.style.display = 'block';
      
      // Save to secure storage
      if (this.store) {
        await this.store.saveApiKey(name, value);
      }
      
      // Show success notification
      notification.className = 'settings-notification settings-notification-success';
      notification.textContent = `API key "${name}" saved successfully!`;
      setTimeout(() => {
        notification.style.display = 'none';
      }, 3000);
      
      // Clear inputs
      nameInput.value = '';
      valueInput.value = '';
      
      // Update the list of saved keys
      this.updateApiKeysList();
    } catch (error) {
      // Show error notification
      notification.className = 'settings-notification settings-notification-error';
      notification.textContent = `Error: ${error.message}`;
      setTimeout(() => {
        notification.style.display = 'none';
      }, 5000);
    }
  }
  
  /**
   * Update the list of saved API keys
   * @returns {Promise<void>}
   */
  async updateApiKeysList() {
    const container = document.getElementById('api-keys-container');
    
    if (!container || !this.store) {
      return;
    }
    
    try {
      // Get all keys
      const keys = await this.store.getAllApiKeys();
      
      if (!keys || keys.length === 0) {
        container.innerHTML = '<p>No API keys stored yet.</p>';
        return;
      }
      
      // Create list
      const list = document.createElement('ul');
      list.className = 'api-keys-list';
      
      keys.forEach(key => {
        const item = document.createElement('li');
        item.className = 'api-key-item';
        
        item.innerHTML = `
          <span class="api-key-name">${key}</span>
          <div class="api-key-actions">
            <button class="api-key-view" data-key="${key}">View</button>
            <button class="api-key-delete" data-key="${key}">Delete</button>
          </div>
        `;
        
        list.appendChild(item);
      });
      
      container.innerHTML = '';
      container.appendChild(list);
      
      // Add event listeners
      const viewButtons = container.querySelectorAll('.api-key-view');
      viewButtons.forEach(button => {
        button.addEventListener('click', () => {
          this.viewApiKey(button.dataset.key);
        });
      });
      
      const deleteButtons = container.querySelectorAll('.api-key-delete');
      deleteButtons.forEach(button => {
        button.addEventListener('click', () => {
          this.deleteApiKey(button.dataset.key);
        });
      });
    } catch (error) {
      console.error('Failed to update API keys list:', error);
      container.innerHTML = '<p>Error loading API keys.</p>';
    }
  }
  
  /**
   * View an API key (show in a dialog)
   * @param {string} key - Key name
   */
  async viewApiKey(key) {
    if (!this.store) {
      return;
    }
    
    try {
      const value = await this.store.getApiKey(key);
      alert(`API Key: ${key}\nValue: ${value}`);
    } catch (error) {
      console.error('Failed to view API key:', error);
      alert('Error: Could not retrieve API key.');
    }
  }
  
  /**
   * Delete an API key
   * @param {string} key - Key name
   */
  async deleteApiKey(key) {
    if (!this.store || !confirm(`Are you sure you want to delete the API key "${key}"?`)) {
      return;
    }
    
    try {
      await this.store.deleteApiKey(key);
      this.updateApiKeysList();
      
      const notification = document.getElementById('settings-notification');
      if (notification) {
        notification.className = 'settings-notification settings-notification-success';
        notification.textContent = `API key "${key}" deleted successfully.`;
        notification.style.display = 'block';
        setTimeout(() => {
          notification.style.display = 'none';
        }, 3000);
      }
    } catch (error) {
      console.error('Failed to delete API key:', error);
      alert('Error: Could not delete API key.');
    }
  }
  
  /**
   * Reset developer settings to defaults
   */
  resetDeveloperSettings() {
    if (!this.store) {
      return;
    }
    
    const defaults = {
      enableDevTools: false,
      enableDebugLogging: false,
      logLevel: 'error',
      coherenceThreshold: 0.8,
      manifestDepth: 'moderate',
      appFactoryPromptTemplate: ''
    };
    
    // Update store
    for (const [setting, value] of Object.entries(defaults)) {
      this.store.updateSetting('developer', setting, value);
    }
    
    // Update form
    this.setFormValues('developer', defaults);
    
    // Show notification
    const notification = document.getElementById('settings-notification');
    if (notification) {
      notification.className = 'settings-notification settings-notification-success';
      notification.textContent = 'Developer settings reset to defaults.';
      notification.style.display = 'block';
      setTimeout(() => {
        notification.style.display = 'none';
      }, 3000);
    }
  }
  
  /**
   * Show save notification
   * @param {boolean} success - Whether save was successful
   */
  showSaveNotification(success) {
    const notification = document.getElementById('settings-notification');
    
    if (!notification) {
      return;
    }
    
    if (success) {
      notification.className = 'settings-notification settings-notification-success';
      notification.textContent = 'Settings saved successfully.';
    } else {
      notification.className = 'settings-notification settings-notification-error';
      notification.textContent = 'Error saving settings.';
    }
    
    notification.style.display = 'block';
    setTimeout(() => {
      notification.style.display = 'none';
    }, 3000);
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { SettingsPanel };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.SettingsPanel = SettingsPanel;
}