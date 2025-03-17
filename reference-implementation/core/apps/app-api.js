/**
 * PrimeOS Application API
 * 
 * Provides a standardized interface for applications to interact with the PrimeOS shell
 * and utilize system services. This API enables applications to:
 * 
 * 1. Manage their lifecycle (init, suspend, resume, close)
 * 2. Interact with the shell UI
 * 3. Use system services like storage and identity
 * 4. Communicate with other applications
 */

class AppAPI {
  /**
   * Create a new Application API instance
   * @param {Object} options - Configuration options
   * @param {string} options.appId - Application ID
   * @param {HTMLElement} options.containerElement - The DOM element where the app should render
   * @param {Object} options.eventBus - Event bus for inter-component communication
   * @param {Object} options.store - Storage interface
   * @param {Object} options.identity - Identity service
   */
  constructor(options) {
    // Validate required parameters
    if (!options.appId) {
      throw new Error('AppAPI requires an appId');
    }
    
    if (!options.containerElement || !(options.containerElement instanceof HTMLElement)) {
      throw new Error('AppAPI requires a valid containerElement');
    }
    
    if (!options.eventBus) {
      throw new Error('AppAPI requires an eventBus');
    }
    
    // Store references to dependencies
    this.appId = options.appId;
    this.container = options.containerElement;
    this.eventBus = options.eventBus;
    this.store = options.store || null;
    this.identity = options.identity || null;
    this.windowId = options.windowId || null;
    
    // Initialize state
    this.state = {
      isActive: true,
      isSuspended: false,
      isFullscreen: false,
      preferences: {}
    };
    
    // Bind event handlers
    this._handleWindowEvents = this._handleWindowEvents.bind(this);
    
    // Subscribe to relevant events
    this._subscribeToEvents();
    
    // Log application initialization
    console.log(`AppAPI initialized for ${this.appId}`);
  }
  
  /**
   * Subscribe to system events relevant to this application
   * @private
   */
  _subscribeToEvents() {
    // Window focus events
    this.eventBus.subscribe('shell:window-focused', this._handleWindowEvents);
    
    // Window state events
    this.eventBus.subscribe('shell:window-minimized', this._handleWindowEvents);
    this.eventBus.subscribe('shell:window-maximized', this._handleWindowEvents);
    this.eventBus.subscribe('shell:window-closing', this._handleWindowEvents);
    this.eventBus.subscribe('shell:window-closed', this._handleWindowEvents);
    
    // System events
    this.eventBus.subscribe('system:low-memory', () => {
      if (this.state.isActive && !this.state.isSuspended) {
        this.suspend();
      }
    });
    
    this.eventBus.subscribe('system:power-saving', () => {
      if (this.state.isActive && !this.state.isSuspended) {
        this.suspend();
      }
    });
  }
  
  /**
   * Handle window-related events
   * @private
   * @param {Object} eventData - Event data
   */
  _handleWindowEvents(eventData) {
    // Only handle events for this window
    if (eventData.windowId !== this.windowId) {
      return;
    }
    
    switch (eventData.event) {
      case 'shell:window-focused':
        this.state.isActive = true;
        if (this.state.isSuspended) {
          this.resume();
        }
        this.onFocus();
        break;
        
      case 'shell:window-minimized':
        this.state.isActive = !eventData.minimized;
        if (eventData.minimized && !this.state.isSuspended) {
          this.suspend();
        }
        break;
        
      case 'shell:window-maximized':
        this.state.isFullscreen = eventData.maximized;
        this.onResize();
        break;
        
      case 'shell:window-closing':
        this.onBeforeClose();
        break;
        
      case 'shell:window-closed':
        this.onClose();
        // Unsubscribe from events
        this._unsubscribeFromEvents();
        break;
    }
  }
  
  /**
   * Unsubscribe from all events
   * @private
   */
  _unsubscribeFromEvents() {
    // Window focus events
    this.eventBus.unsubscribe('shell:window-focused', this._handleWindowEvents);
    
    // Window state events
    this.eventBus.unsubscribe('shell:window-minimized', this._handleWindowEvents);
    this.eventBus.unsubscribe('shell:window-maximized', this._handleWindowEvents);
    this.eventBus.unsubscribe('shell:window-closing', this._handleWindowEvents);
    this.eventBus.unsubscribe('shell:window-closed', this._handleWindowEvents);
    
    // System events
    this.eventBus.unsubscribe('system:low-memory', this.suspend);
    this.eventBus.unsubscribe('system:power-saving', this.suspend);
  }
  
  /**
   * Load application preferences from storage
   * @returns {Promise<Object>} Application preferences
   */
  async loadPreferences() {
    if (!this.store) {
      console.warn('Storage not available, unable to load preferences');
      return {};
    }
    
    try {
      const record = await this.store.get(`app_preferences_${this.appId}`);
      
      if (record) {
        // Extract only the preference fields, not id or type
        const { id, type, ...preferences } = record;
        this.state.preferences = preferences || {};
      } else {
        this.state.preferences = {};
      }
      
      return this.state.preferences;
    } catch (error) {
      console.error('Failed to load preferences:', error);
      return {};
    }
  }
  
  /**
   * Save application preferences to storage
   * @param {Object} preferences - Preferences to save
   * @returns {Promise<void>}
   */
  async savePreferences(preferences) {
    if (!this.store) {
      console.warn('Storage not available, unable to save preferences');
      return;
    }
    
    try {
      // Merge with existing preferences
      this.state.preferences = { ...this.state.preferences, ...preferences };
      
      // Ensure we have an id field for PrimeStore coherence checks
      const recordToSave = {
        id: `app_preferences_${this.appId}`,
        type: 'preferences',
        ...this.state.preferences
      };
      
      // Save to storage
      await this.store.put(recordToSave);
      
      console.log('Preferences saved successfully');
    } catch (error) {
      console.error('Failed to save preferences:', error);
    }
  }
  
  /**
   * Show a notification from this application
   * @param {Object} notification - Notification data
   * @param {string} notification.title - Notification title
   * @param {string} notification.message - Notification message
   * @param {string} [notification.type='info'] - Notification type (info, success, warning, error)
   * @param {number} [notification.timeout=5000] - Auto-dismiss timeout in ms (0 for no auto-dismiss)
   */
  showNotification(notification) {
    this.eventBus.publish('shell:show-notification', {
      appId: this.appId,
      title: notification.title,
      message: notification.message,
      type: notification.type || 'info',
      timeout: notification.timeout || 5000
    });
  }
  
  /**
   * Request data from another application
   * @param {string} targetAppId - Target application ID
   * @param {Object} request - Request data
   * @param {Object} options - Additional options
   * @param {number} options.timeout - Timeout in milliseconds (default: 30000)
   * @param {boolean} options.retry - Whether to retry on timeout (default: true)
   * @param {number} options.retryCount - Number of retries (default: 2)
   * @returns {Promise<any>} Response data
   */
  async requestAppData(targetAppId, request, options = {}) {
    // Default options
    const timeout = options.timeout || 30000;
    const retry = options.retry !== false;
    const maxRetries = options.retryCount || 2;
    
    // Internal function to handle a single request attempt
    const attemptRequest = (retryCount = 0) => {
      return new Promise((resolve, reject) => {
        // Generate unique request ID
        const requestId = `req_${Date.now()}_${Math.floor(Math.random() * 10000)}`;
        
        // Set up one-time response handler
        const responseHandler = (response) => {
          if (response.requestId === requestId) {
            // Success! Remove listener and clear timeout
            this.eventBus.unsubscribe(`app:response:${this.appId}`, responseHandler);
            clearTimeout(timeoutId);
            
            if (response.error) {
              reject(new Error(response.error));
            } else {
              resolve(response.data);
            }
          }
        };
        
        // Subscribe to response
        this.eventBus.subscribe(`app:response:${this.appId}`, responseHandler);
        
        // Send request
        this.eventBus.publish(`app:request:${targetAppId}`, {
          requestId,
          sourceAppId: this.appId,
          request
        });
        
        // Set timeout to prevent hanging
        const timeoutId = setTimeout(() => {
          // Unsubscribe to prevent memory leaks
          this.eventBus.unsubscribe(`app:response:${this.appId}`, responseHandler);
          
          if (retry && retryCount < maxRetries) {
            // Retry the request
            console.log(`Request to ${targetAppId} timed out, retrying (${retryCount + 1}/${maxRetries})...`);
            resolveWithRetry(retryCount + 1);
          } else {
            // No more retries, reject with timeout error
            reject(new Error(`Request to ${targetAppId} timed out after ${retryCount} retries`));
          }
        }, timeout);
      });
    };
    
    // Function to handle retry logic
    const resolveWithRetry = async (retryCount) => {
      try {
        // Add a small delay before retrying to allow system to stabilize
        await new Promise(resolve => setTimeout(resolve, 500));
        return await attemptRequest(retryCount);
      } catch (error) {
        // If we've hit max retries or this isn't a timeout error, rethrow
        if (!retry || retryCount >= maxRetries || !error.message.includes('timed out')) {
          throw error;
        }
        // Otherwise retry again
        return resolveWithRetry(retryCount + 1);
      }
    };
    
    // Start first attempt
    return resolveWithRetry(0);
  }
  
  /**
   * Send response to an application request
   * @param {string} targetAppId - Target application ID
   * @param {string} requestId - Original request ID
   * @param {any} data - Response data
   * @param {string} [error] - Error message if request failed
   */
  sendAppResponse(targetAppId, requestId, data, error = null) {
    this.eventBus.publish(`app:response:${targetAppId}`, {
      requestId,
      sourceAppId: this.appId,
      data,
      error
    });
  }
  
  /**
   * Register a request handler for this application
   * @param {Function} handler - Request handler function
   * @returns {Function} Unsubscribe function
   */
  registerRequestHandler(handler) {
    return this.eventBus.subscribe(`app:request:${this.appId}`, async (requestData) => {
      try {
        const { requestId, sourceAppId, request } = requestData;
        const response = await handler(request, sourceAppId);
        
        this.sendAppResponse(sourceAppId, requestId, response);
      } catch (error) {
        // Make sure sourceAppId is available even if there was an error in the earlier destructuring
        const sourceAppId = requestData.sourceAppId;
        this.sendAppResponse(sourceAppId, requestData.requestId, null, error.message);
      }
    });
  }
  
  /**
   * Suspend the application to conserve resources
   * Applications should pause CPU/memory intensive operations
   */
  suspend() {
    if (this.state.isSuspended) return;
    
    this.state.isSuspended = true;
    this.onSuspend();
    
    console.log(`Application ${this.appId} suspended`);
  }
  
  /**
   * Resume a suspended application
   */
  resume() {
    if (!this.state.isSuspended) return;
    
    this.state.isSuspended = false;
    this.onResume();
    
    console.log(`Application ${this.appId} resumed`);
  }
  
  /**
   * Request to close this application's window
   */
  close() {
    this.eventBus.publish('shell:close-window', { windowId: this.windowId });
  }
  
  // Lifecycle hooks - to be overridden by applications
  
  /**
   * Called when the application gains focus
   * @virtual
   */
  onFocus() {
    // To be implemented by application
  }
  
  /**
   * Called when the application window is resized
   * @virtual
   */
  onResize() {
    // To be implemented by application
  }
  
  /**
   * Called before the application is closed
   * @virtual
   */
  onBeforeClose() {
    // To be implemented by application
  }
  
  /**
   * Called when the application is closed
   * @virtual
   */
  onClose() {
    // To be implemented by application
    this._unsubscribeFromEvents();
  }
  
  /**
   * Called when the application is suspended
   * @virtual
   */
  onSuspend() {
    // To be implemented by application
  }
  
  /**
   * Called when the application is resumed from suspension
   * @virtual
   */
  onResume() {
    // To be implemented by application
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { AppAPI };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.AppAPI = AppAPI;
}