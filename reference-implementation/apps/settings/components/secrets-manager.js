/**
 * PrimeOS Secrets Manager Component
 * 
 * User interface for managing API keys and other secrets
 * in a secure, manifold-based vault.
 */

/**
 * SecretsManager component
 * Manages secure storage and retrieval of sensitive credentials
 */
class SecretsManager {
  /**
   * Create a new secrets manager
   * @param {Object} options - Configuration options
   * @param {Object} options.secureVault - Secure vault for secrets storage
   * @param {Object} options.eventBus - Event bus for messaging
   * @param {Object} options.store - Settings store reference
   */
  constructor(options = {}) {
    this.secureVault = options.secureVault;
    this.eventBus = options.eventBus;
    this.store = options.store;
    
    this.container = document.createElement('div');
    this.container.className = 'secrets-manager';
    
    // Track secret keys
    this.secretKeys = new Set();
    
    // Track active section
    this.activeSection = 'api-keys';
    
    // Bind methods
    this.initialize = this.initialize.bind(this);
    this.render = this.render.bind(this);
    this.saveSecret = this.saveSecret.bind(this);
    this.getSecret = this.getSecret.bind(this);
    this.deleteSecret = this.deleteSecret.bind(this);
    this.getAllSecrets = this.getAllSecrets.bind(this);
  }
  
  /**
   * Initialize the component
   * @returns {Promise<void>}
   */
  async initialize() {
    // Load available secrets if vault is available
    if (this.secureVault) {
      try {
        const keys = await this.secureVault.getAllKeys();
        keys.forEach(key => this.secretKeys.add(key));
        
        console.log(`Loaded ${this.secretKeys.size} secrets from vault`);
      } catch (error) {
        console.error('Failed to load secrets:', error);
      }
    }
    
    // Subscribe to events if event bus is available
    if (this.eventBus) {
      this.eventBus.subscribe('secrets:save-requested', this.saveSecret);
      this.eventBus.subscribe('secrets:get-requested', this.getSecret);
      this.eventBus.subscribe('secrets:delete-requested', this.deleteSecret);
    }
  }
  
  /**
   * Render the secrets manager
   * @returns {HTMLElement} Rendered container
   */
  render() {
    // Clear container
    this.container.innerHTML = '';
    
    // Create main structure
    const secretsPanel = document.createElement('div');
    secretsPanel.className = 'secrets-panel';
    
    // Add header
    const header = document.createElement('div');
    header.className = 'secrets-header';
    header.innerHTML = `
      <h3>Secure Credentials Manager</h3>
      <p>Securely store and manage API keys and other sensitive credentials.</p>
    `;
    secretsPanel.appendChild(header);
    
    // Add tabs for different secret types
    const tabs = document.createElement('div');
    tabs.className = 'secrets-tabs';
    
    tabs.innerHTML = `
      <button class="tab-button ${this.activeSection === 'api-keys' ? 'active' : ''}" data-section="api-keys">
        <span class="tab-icon">🔑</span>
        <span class="tab-name">API Keys</span>
      </button>
      <button class="tab-button ${this.activeSection === 'credentials' ? 'active' : ''}" data-section="credentials">
        <span class="tab-icon">🔒</span>
        <span class="tab-name">Credentials</span>
      </button>
      <button class="tab-button ${this.activeSection === 'certificates' ? 'active' : ''}" data-section="certificates">
        <span class="tab-icon">📜</span>
        <span class="tab-name">Certificates</span>
      </button>
      <button class="tab-button ${this.activeSection === 'audit' ? 'active' : ''}" data-section="audit">
        <span class="tab-icon">📋</span>
        <span class="tab-name">Audit Log</span>
      </button>
    `;
    
    // Add tab event listeners
    tabs.querySelectorAll('.tab-button').forEach(button => {
      button.addEventListener('click', () => {
        this.activeSection = button.dataset.section;
        this.render();
      });
    });
    
    secretsPanel.appendChild(tabs);
    
    // Add content area
    const content = document.createElement('div');
    content.className = 'secrets-content';
    
    // Render the active section
    switch (this.activeSection) {
      case 'api-keys':
        this.renderApiKeysSection(content);
        break;
      case 'credentials':
        this.renderCredentialsSection(content);
        break;
      case 'certificates':
        this.renderCertificatesSection(content);
        break;
      case 'audit':
        this.renderAuditSection(content);
        break;
      default:
        this.renderApiKeysSection(content);
    }
    
    secretsPanel.appendChild(content);
    
    // Add status indicator
    const status = document.createElement('div');
    status.className = 'vault-status';
    status.innerHTML = `
      <div class="status-icon ${this.secureVault ? 'status-secure' : 'status-warning'}">
        ${this.secureVault ? '🔒' : '⚠️'}
      </div>
      <div class="status-text">
        <p><strong>Vault Status:</strong> ${this.secureVault ? 'Secure' : 'Not Available'}</p>
        <p class="status-details">${this.secureVault ? 
          'Using manifold-based encryption with depth-aware validation' : 
          'Secure vault is not available. Some features may be limited.'}</p>
      </div>
    `;
    
    secretsPanel.appendChild(status);
    
    this.container.appendChild(secretsPanel);
    
    return this.container;
  }
  
  /**
   * Render API Keys section
   * @param {HTMLElement} container - Content container
   */
  renderApiKeysSection(container) {
    const section = document.createElement('div');
    section.className = 'secrets-section';
    
    section.innerHTML = `
      <h4>API Keys</h4>
      <p>Manage API keys for external services.</p>
      
      <div class="secrets-form">
        <div class="form-group">
          <label for="apiKeyName">Key Name</label>
          <input type="text" id="apiKeyName" placeholder="e.g., claude-api-key">
        </div>
        
        <div class="form-group">
          <label for="apiKeyValue">Key Value</label>
          <div class="secret-input-group">
            <input type="password" id="apiKeyValue" placeholder="Enter API key value">
            <button id="toggle-key-visibility" class="visibility-toggle">👁️</button>
          </div>
        </div>
        
        <div class="form-group">
          <label for="apiKeyDescription">Description (Optional)</label>
          <input type="text" id="apiKeyDescription" placeholder="What this API key is used for">
        </div>
        
        <div class="form-group">
          <label>Security Level</label>
          <div class="radio-group">
            <label class="radio-label">
              <input type="radio" name="apiKeySecurity" value="high" checked>
              High (Encrypted)
            </label>
            <label class="radio-label">
              <input type="radio" name="apiKeySecurity" value="critical">
              Critical (Hardware-backed)
            </label>
          </div>
        </div>
        
        <div class="actions">
          <button id="save-api-key" class="secret-button save-button">Save API Key</button>
        </div>
      </div>
      
      <div class="stored-secrets">
        <h4>Stored API Keys</h4>
        <div id="stored-api-keys" class="stored-keys-list">
          <p>Loading stored API keys...</p>
        </div>
      </div>
    `;
    
    container.appendChild(section);
    
    // Add event listeners
    const saveButton = section.querySelector('#save-api-key');
    if (saveButton) {
      saveButton.addEventListener('click', () => {
        this.handleSaveApiKey();
      });
    }
    
    // Toggle password visibility
    const toggleButton = section.querySelector('#toggle-key-visibility');
    const keyInput = section.querySelector('#apiKeyValue');
    
    if (toggleButton && keyInput) {
      toggleButton.addEventListener('click', () => {
        const isPassword = keyInput.type === 'password';
        keyInput.type = isPassword ? 'text' : 'password';
        toggleButton.textContent = isPassword ? '🔒' : '👁️';
      });
    }
    
    // Load stored API keys
    this.loadStoredApiKeys();
  }
  
  /**
   * Render Credentials section
   * @param {HTMLElement} container - Content container
   */
  renderCredentialsSection(container) {
    const section = document.createElement('div');
    section.className = 'secrets-section';
    
    section.innerHTML = `
      <h4>Login Credentials</h4>
      <p>Securely store usernames and passwords for various services.</p>
      
      <div class="secrets-form">
        <div class="form-group">
          <label for="credentialName">Service Name</label>
          <input type="text" id="credentialName" placeholder="e.g., GitHub">
        </div>
        
        <div class="form-group">
          <label for="credentialUsername">Username/Email</label>
          <input type="text" id="credentialUsername" placeholder="Enter username or email">
        </div>
        
        <div class="form-group">
          <label for="credentialPassword">Password</label>
          <div class="secret-input-group">
            <input type="password" id="credentialPassword" placeholder="Enter password">
            <button id="toggle-password-visibility" class="visibility-toggle">👁️</button>
          </div>
        </div>
        
        <div class="form-group">
          <label for="credentialUrl">Service URL (Optional)</label>
          <input type="text" id="credentialUrl" placeholder="https://example.com">
        </div>
        
        <div class="form-group">
          <label>Security Level</label>
          <div class="radio-group">
            <label class="radio-label">
              <input type="radio" name="credentialSecurity" value="high" checked>
              High (Encrypted)
            </label>
            <label class="radio-label">
              <input type="radio" name="credentialSecurity" value="critical">
              Critical (Hardware-backed)
            </label>
          </div>
        </div>
        
        <div class="actions">
          <button id="save-credential" class="secret-button save-button">Save Credential</button>
          <button id="generate-password" class="secret-button">Generate Strong Password</button>
        </div>
      </div>
      
      <div class="stored-secrets">
        <h4>Stored Credentials</h4>
        <div id="stored-credentials" class="stored-credentials-list">
          <p>Credentials securely stored in the vault. Select to manage.</p>
          <ul class="credentials-list">
            <li class="credential-placeholder">No credentials stored yet.</li>
          </ul>
        </div>
      </div>
    `;
    
    container.appendChild(section);
    
    // Add event listeners
    const saveButton = section.querySelector('#save-credential');
    if (saveButton) {
      saveButton.addEventListener('click', () => {
        this.handleSaveCredential();
      });
    }
    
    // Toggle password visibility
    const toggleButton = section.querySelector('#toggle-password-visibility');
    const passwordInput = section.querySelector('#credentialPassword');
    
    if (toggleButton && passwordInput) {
      toggleButton.addEventListener('click', () => {
        const isPassword = passwordInput.type === 'password';
        passwordInput.type = isPassword ? 'text' : 'password';
        toggleButton.textContent = isPassword ? '🔒' : '👁️';
      });
    }
    
    // Generate password
    const generateButton = section.querySelector('#generate-password');
    if (generateButton) {
      generateButton.addEventListener('click', () => {
        this.generatePassword();
      });
    }
  }
  
  /**
   * Render Certificates section
   * @param {HTMLElement} container - Content container
   */
  renderCertificatesSection(container) {
    const section = document.createElement('div');
    section.className = 'secrets-section';
    
    section.innerHTML = `
      <h4>Certificates & Keys</h4>
      <p>Manage SSL certificates, SSH keys, and other cryptographic credentials.</p>
      
      <div class="certificates-actions">
        <button class="secret-button">Generate New Key Pair</button>
        <button class="secret-button">Import Certificate</button>
        <button class="secret-button">Export Public Key</button>
      </div>
      
      <div class="stored-secrets">
        <h4>Stored Certificates & Keys</h4>
        <div class="stored-certificates">
          <p class="placeholder-text">This feature is not yet implemented in the reference implementation.</p>
          <p class="placeholder-text">Certificate management will be added in a future update.</p>
        </div>
      </div>
      
      <div class="certificate-info">
        <div class="info-box">
          <h4>About Secure Storage</h4>
          <p>Certificates and keys are stored using manifold-based encryption with mathematical coherence validation.</p>
          <p>This ensures that cryptographic material is protected from unauthorized access or tampering.</p>
        </div>
      </div>
    `;
    
    container.appendChild(section);
  }
  
  /**
   * Render Audit section
   * @param {HTMLElement} container - Content container
   */
  renderAuditSection(container) {
    const section = document.createElement('div');
    section.className = 'secrets-section audit-section';
    
    section.innerHTML = `
      <h4>Security Audit Log</h4>
      <p>Review access and modification history for secrets.</p>
      
      <div class="audit-controls">
        <div class="form-group">
          <label for="auditFilter">Filter by:</label>
          <select id="auditFilter">
            <option value="all">All Events</option>
            <option value="access">Access Events</option>
            <option value="modification">Modification Events</option>
            <option value="failed">Failed Access Attempts</option>
          </select>
        </div>
        
        <div class="audit-timeframe">
          <button class="time-button active">Today</button>
          <button class="time-button">Week</button>
          <button class="time-button">Month</button>
          <button class="time-button">All Time</button>
        </div>
        
        <button id="export-audit-log" class="secret-button">Export Log</button>
      </div>
      
      <div class="audit-log">
        <table class="audit-table">
          <thead>
            <tr>
              <th>Timestamp</th>
              <th>Event</th>
              <th>Resource</th>
              <th>Result</th>
              <th>Details</th>
            </tr>
          </thead>
          <tbody id="audit-log-entries">
            <!-- Audit log entries will be inserted here -->
          </tbody>
        </table>
      </div>
    `;
    
    container.appendChild(section);
    
    // Load audit log entries
    this.loadAuditLog();
  }
  
  /**
   * Handle saving an API key
   */
  async handleSaveApiKey() {
    const nameInput = document.getElementById('apiKeyName');
    const valueInput = document.getElementById('apiKeyValue');
    const descriptionInput = document.getElementById('apiKeyDescription');
    const securityLevel = document.querySelector('input[name="apiKeySecurity"]:checked');
    
    if (!nameInput || !valueInput) {
      this.showNotification('Missing required fields', 'error');
      return;
    }
    
    const name = nameInput.value.trim();
    const value = valueInput.value;
    const description = descriptionInput ? descriptionInput.value : '';
    const security = securityLevel ? securityLevel.value : 'high';
    
    if (!name) {
      this.showNotification('Key name is required', 'error');
      return;
    }
    
    if (!value) {
      this.showNotification('Key value is required', 'error');
      return;
    }
    
    try {
      await this.saveSecret({
        key: name,
        value,
        metadata: {
          type: 'api_key',
          description,
          securityLevel: security,
          created: new Date().toISOString()
        }
      });
      
      // Clear inputs
      nameInput.value = '';
      valueInput.value = '';
      if (descriptionInput) descriptionInput.value = '';
      
      // Show success notification
      this.showNotification(`API key "${name}" saved successfully`, 'success');
      
      // Refresh the list
      this.loadStoredApiKeys();
    } catch (error) {
      this.showNotification(`Failed to save API key: ${error.message}`, 'error');
    }
  }
  
  /**
   * Handle saving a credential
   */
  async handleSaveCredential() {
    const serviceInput = document.getElementById('credentialName');
    const usernameInput = document.getElementById('credentialUsername');
    const passwordInput = document.getElementById('credentialPassword');
    const urlInput = document.getElementById('credentialUrl');
    const securityLevel = document.querySelector('input[name="credentialSecurity"]:checked');
    
    if (!serviceInput || !usernameInput || !passwordInput) {
      this.showNotification('Missing required fields', 'error');
      return;
    }
    
    const service = serviceInput.value.trim();
    const username = usernameInput.value.trim();
    const password = passwordInput.value;
    const url = urlInput ? urlInput.value : '';
    const security = securityLevel ? securityLevel.value : 'high';
    
    if (!service) {
      this.showNotification('Service name is required', 'error');
      return;
    }
    
    if (!username) {
      this.showNotification('Username is required', 'error');
      return;
    }
    
    if (!password) {
      this.showNotification('Password is required', 'error');
      return;
    }
    
    try {
      // Create credential key in format service:username
      const key = `credential_${service}_${username}`;
      
      // Store as JSON string
      const credentialData = JSON.stringify({
        service,
        username,
        password,
        url,
        createdAt: new Date().toISOString(),
        lastModified: new Date().toISOString()
      });
      
      await this.saveSecret({
        key,
        value: credentialData,
        metadata: {
          type: 'credential',
          service,
          username,
          securityLevel: security,
          created: new Date().toISOString()
        }
      });
      
      // Clear inputs
      serviceInput.value = '';
      usernameInput.value = '';
      passwordInput.value = '';
      if (urlInput) urlInput.value = '';
      
      // Show success notification
      this.showNotification(`Credential for "${service}" saved successfully`, 'success');
    } catch (error) {
      this.showNotification(`Failed to save credential: ${error.message}`, 'error');
    }
  }
  
  /**
   * Generate a random strong password
   */
  generatePassword() {
    const passwordInput = document.getElementById('credentialPassword');
    if (!passwordInput) return;
    
    // Generate a random password with 16-24 characters
    const length = 16 + Math.floor(Math.random() * 9);
    const charset = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@#$%^&*()_+~`|}{[]:;?><,./-=';
    
    let password = '';
    let hasLower = false;
    let hasUpper = false;
    let hasNumber = false;
    let hasSpecial = false;
    
    // Ensure at least one of each character type
    password += 'a'; // lowercase
    password += 'A'; // uppercase
    password += '1'; // number
    password += '#'; // special
    
    // Fill the rest randomly
    for (let i = 4; i < length; i++) {
      const randomIndex = Math.floor(Math.random() * charset.length);
      password += charset[randomIndex];
    }
    
    // Shuffle the password
    password = password.split('').sort(() => 0.5 - Math.random()).join('');
    
    // Set the password in the input
    passwordInput.value = password;
    passwordInput.type = 'text';
    
    // Show a notification
    this.showNotification('Strong password generated', 'success');
    
    // After 5 seconds, hide the password again
    setTimeout(() => {
      if (passwordInput) {
        passwordInput.type = 'password';
        
        // Also update the toggle button
        const toggleButton = document.getElementById('toggle-password-visibility');
        if (toggleButton) {
          toggleButton.textContent = '👁️';
        }
      }
    }, 5000);
  }
  
  /**
   * Load and display stored API keys
   */
  async loadStoredApiKeys() {
    const container = document.getElementById('stored-api-keys');
    if (!container) return;
    
    try {
      if (!this.secureVault) {
        container.innerHTML = '<p class="error-message">Secure vault is not available</p>';
        return;
      }
      
      // Get all keys from vault
      const allKeys = await this.secureVault.getAllKeys();
      
      // Filter for API keys only
      const apiKeys = allKeys.filter(key => !key.startsWith('credential_'));
      
      if (apiKeys.length === 0) {
        container.innerHTML = '<p class="empty-list">No API keys stored yet.</p>';
        return;
      }
      
      // Create list
      const list = document.createElement('ul');
      list.className = 'api-keys-list';
      
      // Sort keys alphabetically
      apiKeys.sort().forEach(key => {
        const item = document.createElement('li');
        item.className = 'api-key-item';
        
        // We'll mask the actual key value for security
        item.innerHTML = `
          <div class="api-key-info">
            <span class="api-key-name">${key}</span>
            <span class="api-key-type">API Key</span>
          </div>
          <div class="api-key-actions">
            <button class="action-button view-button" data-key="${key}">View</button>
            <button class="action-button copy-button" data-key="${key}">Copy</button>
            <button class="action-button delete-button" data-key="${key}">Delete</button>
          </div>
        `;
        
        list.appendChild(item);
      });
      
      container.innerHTML = '';
      container.appendChild(list);
      
      // Add event listeners
      container.querySelectorAll('.view-button').forEach(button => {
        button.addEventListener('click', () => {
          this.viewSecret(button.dataset.key);
        });
      });
      
      container.querySelectorAll('.copy-button').forEach(button => {
        button.addEventListener('click', () => {
          this.copySecret(button.dataset.key);
        });
      });
      
      container.querySelectorAll('.delete-button').forEach(button => {
        button.addEventListener('click', () => {
          this.confirmDeleteSecret(button.dataset.key);
        });
      });
    } catch (error) {
      console.error('Failed to load API keys:', error);
      container.innerHTML = `<p class="error-message">Error loading API keys: ${error.message}</p>`;
    }
  }
  
  /**
   * Load and display audit log entries
   */
  async loadAuditLog() {
    const container = document.getElementById('audit-log-entries');
    if (!container) return;
    
    try {
      if (!this.secureVault) {
        container.innerHTML = `
          <tr>
            <td colspan="5" class="centered-message">Secure vault is not available</td>
          </tr>
        `;
        return;
      }
      
      // Get log entries from vault
      let logEntries = [];
      
      if (typeof this.secureVault.getAccessLog === 'function') {
        logEntries = await this.secureVault.getAccessLog(50); // Get last 50 entries
      }
      
      if (logEntries.length === 0) {
        container.innerHTML = `
          <tr>
            <td colspan="5" class="centered-message">No audit log entries available</td>
          </tr>
        `;
        return;
      }
      
      // Create log entries
      let html = '';
      
      // Sort by timestamp (newest first)
      logEntries.sort((a, b) => new Date(b.timestamp) - new Date(a.timestamp));
      
      logEntries.forEach(entry => {
        const timestamp = new Date(entry.timestamp).toLocaleString();
        
        html += `
          <tr class="${entry.success ? 'success-row' : 'error-row'}">
            <td>${timestamp}</td>
            <td>${entry.action}</td>
            <td>${entry.key}</td>
            <td>${entry.success ? 'Success' : 'Failed'}</td>
            <td>${entry.details || '-'}</td>
          </tr>
        `;
      });
      
      container.innerHTML = html;
    } catch (error) {
      console.error('Failed to load audit log:', error);
      container.innerHTML = `
        <tr>
          <td colspan="5" class="centered-message">Error loading audit log: ${error.message}</td>
        </tr>
      `;
    }
  }
  
  /**
   * View a secret value
   * @param {string} key - Secret key
   */
  async viewSecret(key) {
    try {
      if (!this.secureVault) {
        this.showNotification('Secure vault is not available', 'error');
        return;
      }
      
      const value = await this.secureVault.getSecret(key);
      
      if (value === null) {
        this.showNotification(`Secret "${key}" not found`, 'error');
        return;
      }
      
      // Check if the value is a JSON string (for credentials)
      let displayValue = value;
      let isCredential = false;
      
      try {
        const parsed = JSON.parse(value);
        if (parsed.service && parsed.username && parsed.password) {
          displayValue = `Service: ${parsed.service}\nUsername: ${parsed.username}\nPassword: ${parsed.password}`;
          if (parsed.url) {
            displayValue += `\nURL: ${parsed.url}`;
          }
          isCredential = true;
        }
      } catch (e) {
        // Not a JSON string, use as is
      }
      
      // Show in a modal
      this.showSecretModal(key, displayValue, isCredential);
    } catch (error) {
      console.error('Failed to view secret:', error);
      this.showNotification(`Error retrieving secret: ${error.message}`, 'error');
    }
  }
  
  /**
   * Copy a secret value to clipboard
   * @param {string} key - Secret key
   */
  async copySecret(key) {
    try {
      if (!this.secureVault) {
        this.showNotification('Secure vault is not available', 'error');
        return;
      }
      
      const value = await this.secureVault.getSecret(key);
      
      if (value === null) {
        this.showNotification(`Secret "${key}" not found`, 'error');
        return;
      }
      
      // Check if the value is a JSON string (for credentials)
      let copyValue = value;
      
      try {
        const parsed = JSON.parse(value);
        if (parsed.password) {
          // If it's a credential, just copy the password
          copyValue = parsed.password;
        }
      } catch (e) {
        // Not a JSON string, use as is
      }
      
      // Copy to clipboard
      await navigator.clipboard.writeText(copyValue);
      
      this.showNotification('Copied to clipboard!', 'success');
    } catch (error) {
      console.error('Failed to copy secret:', error);
      this.showNotification(`Error copying secret: ${error.message}`, 'error');
    }
  }
  
  /**
   * Confirm deletion of a secret
   * @param {string} key - Secret key
   */
  confirmDeleteSecret(key) {
    if (confirm(`Are you sure you want to delete the secret "${key}"? This cannot be undone.`)) {
      this.deleteSecret({ key });
    }
  }
  
  /**
   * Show a modal with the secret value
   * @param {string} key - Secret key
   * @param {string} value - Secret value
   * @param {boolean} isCredential - Whether this is a credential
   */
  showSecretModal(key, value, isCredential = false) {
    // Create modal container
    const modal = document.createElement('div');
    modal.className = 'secret-modal';
    
    // Create modal content
    const modalContent = document.createElement('div');
    modalContent.className = 'secret-modal-content';
    
    modalContent.innerHTML = `
      <div class="secret-modal-header">
        <h3>${isCredential ? 'Credential Details' : 'Secret Value'}</h3>
        <button class="close-modal">&times;</button>
      </div>
      <div class="secret-modal-body">
        <div class="secret-key">
          <strong>Key:</strong> ${key}
        </div>
        <div class="secret-value">
          <strong>Value:</strong>
          <pre>${value}</pre>
        </div>
      </div>
      <div class="secret-modal-footer">
        <button class="secret-button copy-button">Copy Value</button>
        <button class="secret-button close-button">Close</button>
      </div>
    `;
    
    modal.appendChild(modalContent);
    document.body.appendChild(modal);
    
    // Add event listeners
    const closeButtons = modal.querySelectorAll('.close-modal, .close-button');
    closeButtons.forEach(button => {
      button.addEventListener('click', () => {
        document.body.removeChild(modal);
      });
    });
    
    const copyButton = modal.querySelector('.copy-button');
    if (copyButton) {
      copyButton.addEventListener('click', async () => {
        // Copy the value to clipboard
        try {
          await navigator.clipboard.writeText(value);
          this.showNotification('Copied to clipboard!', 'success');
        } catch (error) {
          this.showNotification('Failed to copy to clipboard', 'error');
        }
      });
    }
    
    // Close modal when clicking outside
    modal.addEventListener('click', event => {
      if (event.target === modal) {
        document.body.removeChild(modal);
      }
    });
  }
  
  /**
   * Show a notification
   * @param {string} message - Notification message
   * @param {string} type - Notification type (success, error, info)
   */
  showNotification(message, type = 'info') {
    // Check if there's already a notification
    let notification = document.querySelector('.secrets-notification');
    
    if (!notification) {
      // Create new notification
      notification = document.createElement('div');
      notification.className = `secrets-notification notification-${type}`;
      document.body.appendChild(notification);
    } else {
      // Update existing notification
      notification.className = `secrets-notification notification-${type}`;
    }
    
    // Set content and show
    notification.textContent = message;
    notification.style.display = 'block';
    
    // Clear previous timeout
    if (this._notificationTimeout) {
      clearTimeout(this._notificationTimeout);
    }
    
    // Hide after delay
    this._notificationTimeout = setTimeout(() => {
      notification.style.display = 'none';
    }, 5000);
  }
  
  /**
   * Save a secret to the vault
   * @param {Object} event - Event data
   * @param {string} event.key - Secret key
   * @param {string} event.value - Secret value
   * @param {Object} event.metadata - Additional metadata
   * @returns {Promise<boolean>} Success indicator
   */
  async saveSecret(event) {
    if (!event || !event.key || !event.value) {
      throw new Error('Key and value are required');
    }
    
    try {
      if (!this.secureVault) {
        throw new Error('Secure vault is not available');
      }
      
      // Save to vault
      await this.secureVault.setSecret(event.key, event.value, event.metadata || {});
      
      // Add to known keys
      this.secretKeys.add(event.key);
      
      // Notify via event bus
      if (this.eventBus) {
        this.eventBus.publish('secrets:saved', {
          key: event.key,
          timestamp: new Date().toISOString()
        });
      }
      
      return true;
    } catch (error) {
      console.error('Failed to save secret:', error);
      
      // Notify via event bus
      if (this.eventBus) {
        this.eventBus.publish('secrets:save-error', {
          key: event.key,
          error: error.message,
          timestamp: new Date().toISOString()
        });
      }
      
      throw error;
    }
  }
  
  /**
   * Get a secret from the vault
   * @param {Object} event - Event data
   * @param {string} event.key - Secret key
   * @returns {Promise<string|null>} Secret value
   */
  async getSecret(event) {
    if (!event || !event.key) {
      throw new Error('Key is required');
    }
    
    try {
      if (!this.secureVault) {
        throw new Error('Secure vault is not available');
      }
      
      // Get from vault
      return await this.secureVault.getSecret(event.key);
    } catch (error) {
      console.error('Failed to get secret:', error);
      throw error;
    }
  }
  
  /**
   * Delete a secret from the vault
   * @param {Object} event - Event data
   * @param {string} event.key - Secret key
   * @returns {Promise<boolean>} Success indicator
   */
  async deleteSecret(event) {
    if (!event || !event.key) {
      throw new Error('Key is required');
    }
    
    try {
      if (!this.secureVault) {
        throw new Error('Secure vault is not available');
      }
      
      // Delete from vault
      await this.secureVault.removeSecret(event.key);
      
      // Remove from known keys
      this.secretKeys.delete(event.key);
      
      // Notify via event bus
      if (this.eventBus) {
        this.eventBus.publish('secrets:deleted', {
          key: event.key,
          timestamp: new Date().toISOString()
        });
      }
      
      // Show notification
      this.showNotification(`Secret "${event.key}" deleted successfully`, 'success');
      
      // Refresh API keys list
      this.loadStoredApiKeys();
      
      return true;
    } catch (error) {
      console.error('Failed to delete secret:', error);
      
      // Show notification
      this.showNotification(`Failed to delete secret: ${error.message}`, 'error');
      
      throw error;
    }
  }
  
  /**
   * Get all secrets from the vault
   * @returns {Promise<Array<string>>} Array of secret keys
   */
  async getAllSecrets() {
    try {
      if (!this.secureVault) {
        throw new Error('Secure vault is not available');
      }
      
      // Get all keys from vault
      const keys = await this.secureVault.getAllKeys();
      
      // Update known keys
      keys.forEach(key => this.secretKeys.add(key));
      
      return keys;
    } catch (error) {
      console.error('Failed to get all secrets:', error);
      throw error;
    }
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { SecretsManager };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.SecretsManager = SecretsManager;
}