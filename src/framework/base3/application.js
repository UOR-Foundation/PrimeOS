/**
 * Base3 - Application Module
 * 
 * Provides core application functionality including:
 * - State management with immutable updates and coherence checking
 * - Action dispatching with middleware support
 * - Lifecycle hooks and event handling
 * - Component tree management
 */

const Prime = require('../../core');
const { Utils } = Prime;

/**
 * Create a new application instance
 * @param {Object} options - Application options
 * @returns {Object} Application instance
 */
function createApplication(options = {}) {
  // Validate required options
  if (!options.id) {
    throw new Prime.ValidationError('Application id is required', {
      context: { options }
    });
  }

  // Default values with proper type checking
  const initialState = Prime.Utils.isObject(options.initialState) ? options.initialState : {};
  const componentRegistry = new Map();
  const middlewares = [];
  const subscriptions = [];

  // Setup action history with configurable size limit
  const actionHistoryLimit = options.actionHistoryLimit || 100;
  const actionHistory = [];

  // Initialize application instance
  const app = {
    id: options.id,
    type: 'application',
    name: options.name || options.id,
    version: options.version || '1.0.0',
    state: Prime.Utils.deepClone(initialState),
    _isRunning: false,
    
    /**
     * Start the application
     * @returns {Object} Application instance
     */
    start: function() {
      if (this._isRunning) {
        return this;
      }
      
      this._isRunning = true;
      
      // Call initialization hook if available
      if (options.onStart && typeof options.onStart === 'function') {
        options.onStart.call(this);
      }
      
      // Publish start event
      Prime.EventBus.publish('application:start', {
        id: this.id,
        name: this.name,
        timestamp: Date.now()
      });
      
      return this;
    },
    
    /**
     * Stop the application
     * @returns {Object} Application instance
     */
    stop: function() {
      if (!this._isRunning) {
        return this;
      }
      
      this._isRunning = false;
      
      // Call cleanup hook if available
      if (options.onStop && typeof options.onStop === 'function') {
        options.onStop.call(this);
      }
      
      // Publish stop event
      Prime.EventBus.publish('application:stop', {
        id: this.id,
        name: this.name,
        timestamp: Date.now()
      });
      
      return this;
    },
    
    /**
     * Mount the application to a container
     * @param {Object} container - Container element
     * @returns {Object} Application instance
     */
    mount: function(container) {
      this._container = container;
      
      // Call mount hook if available
      if (options.onMount && typeof options.onMount === 'function') {
        options.onMount.call(this, container);
      }
      
      return this;
    },
    
    /**
     * Unmount the application from its container
     * @returns {Object} Application instance
     */
    unmount: function() {
      // Call unmount hook if available
      if (options.onUnmount && typeof options.onUnmount === 'function') {
        options.onUnmount.call(this);
      }
      
      this._container = null;
      return this;
    },
    
    /**
     * Update the application
     * @returns {Object} Application instance
     */
    update: function() {
      // Call update hook if available
      if (options.onUpdate && typeof options.onUpdate === 'function') {
        options.onUpdate.call(this);
      }
      
      return this;
    },
    
    /**
     * Use a kernel service
     * @param {string} service - Service name
     * @param {...any} args - Service arguments
     * @returns {*} Service result
     */
    useKernel: function(service, ...args) {
      if (!this._kernel) {
        throw new Prime.InvalidOperationError('Application is not connected to kernel');
      }
      
      if (!this._kernelActions || !this._kernelActions[service]) {
        throw new Prime.InvalidOperationError(`Service '${service}' not found`);
      }
      
      return this._kernelActions[service](...args);
    },
    
    /**
     * Register a component with the application
     * @param {Object} component - Component to register
     * @returns {string} Component ID
     */
    registerComponent: function(component) {
      if (!component || !component.id) {
        throw new Prime.ValidationError('Component must have an id', {
          context: { component }
        });
      }
      
      if (componentRegistry.has(component.id)) {
        throw new Prime.InvalidOperationError(`Component ${component.id} is already registered`);
      }
      
      // Store component with enhanced metadata
      componentRegistry.set(component.id, {
        component,
        registeredAt: Date.now(),
        lastUpdated: Date.now(),
        updateCount: 0
      });
      
      return component.id;
    },
    
    /**
     * Unregister a component from the application
     * @param {string} componentId - Component ID
     * @returns {boolean} Success
     */
    unregisterComponent: function(componentId) {
      if (!componentRegistry.has(componentId)) {
        return false;
      }
      
      componentRegistry.delete(componentId);
      return true;
    },
    
    /**
     * Get a registered component by ID
     * @param {string} componentId - Component ID
     * @returns {Object} Component instance
     */
    getComponent: function(componentId) {
      const registration = componentRegistry.get(componentId);
      
      if (!registration) {
        throw new Prime.InvalidOperationError(`Component ${componentId} not found`, {
          context: { 
            availableComponents: Array.from(componentRegistry.keys())
          }
        });
      }
      
      return registration.component;
    },
    
    /**
     * Get all registered components
     * @returns {Array} Array of components
     */
    getComponents: function() {
      return Array.from(componentRegistry.values()).map(reg => reg.component);
    },
    
    /**
     * Add middleware to the action pipeline
     * @param {Function} middleware - Middleware function
     * @returns {Function} Function to remove the middleware
     */
    use: function(middleware) {
      if (!Prime.Utils.isFunction(middleware)) {
        throw new Prime.ValidationError('Middleware must be a function', {
          context: { middleware }
        });
      }
      
      middlewares.push(middleware);
      
      // Return function to remove this middleware
      return () => {
        const index = middlewares.indexOf(middleware);
        if (index !== -1) {
          middlewares.splice(index, 1);
          return true;
        }
        return false;
      };
    },
    
    /**
     * Dispatch an action to update application state
     * @param {Object} action - Action to dispatch
     * @returns {Object} Updated state
     */
    dispatch: function(action) {
      if (!action || !action.type) {
        throw new Prime.ValidationError('Action must have a type property', {
          context: { action }
        });
      }
      
      // Record action in history
      if (actionHistory.length >= actionHistoryLimit) {
        actionHistory.shift();
      }
      
      const actionMeta = {
        id: Prime.Utils.uuid(),
        timestamp: Date.now(),
        action: Prime.Utils.deepClone(action)
      };
      
      actionHistory.push(actionMeta);
      
      // Run action through middleware chain
      let processedAction = action;
      let prevented = false;
      
      for (const middleware of middlewares) {
        const result = middleware(processedAction, this.getState.bind(this));
        
        if (result === false) {
          prevented = true;
          break;
        } else if (result && typeof result === 'object') {
          processedAction = result;
        }
      }
      
      if (prevented) {
        // Action was prevented by middleware
        actionMeta.prevented = true;
        return this.state;
      }
      
      // Process the action
      const prevState = Prime.Utils.deepClone(this.state);
      
      // Apply the action to update state
      const nextState = this._processAction(processedAction, prevState);
      
      // Update the state with coherence validation
      if (nextState !== prevState) {
        // Check coherence if specified in options
        if (options.checkCoherence !== false) {
          const coherenceResult = Prime.checkCoherence(prevState, nextState);
          
          if (!coherenceResult.isCoherent) {
            throw new Prime.CoherenceError('State update failed coherence check', {
              context: {
                action: processedAction,
                issues: coherenceResult.issues
              }
            });
          }
        }
        
        // Apply state update with Kahan summation for any numerical values
        this.state = this._applyPreciseUpdate(prevState, nextState);
        
        // Update action metadata
        actionMeta.stateChanged = true;
        
        // Notify subscribers of state change
        this._notifySubscribers(processedAction, prevState, this.state);
      } else {
        actionMeta.stateChanged = false;
      }
      
      return this.state;
    },
    
    /**
     * Apply a state update with precise numerical handling
     * @private
     * @param {Object} prevState - Previous state
     * @param {Object} nextState - Next state
     * @returns {Object} Updated state with precise numerical values
     */
    _applyPreciseUpdate: function(prevState, nextState) {
      // For primitive values, just return nextState
      if (!Prime.Utils.isObject(prevState) || !Prime.Utils.isObject(nextState)) {
        // If they're numbers, use precise math
        if (typeof prevState === 'number' && typeof nextState === 'number') {
          const delta = nextState - prevState;
          return Prime.KahanSum(prevState, delta);
        }
        return nextState;
      }
      
      // For arrays, create a new array with precise updates
      if (Array.isArray(prevState) && Array.isArray(nextState)) {
        return nextState.map((item, i) => {
          if (i < prevState.length) {
            return this._applyPreciseUpdate(prevState[i], item);
          }
          return item;
        });
      }
      
      // For objects, recursively apply precise updates
      const result = {};
      const allKeys = new Set([
        ...Object.keys(prevState),
        ...Object.keys(nextState)
      ]);
      
      for (const key of allKeys) {
        if (key in nextState) {
          if (key in prevState) {
            result[key] = this._applyPreciseUpdate(prevState[key], nextState[key]);
          } else {
            result[key] = nextState[key];
          }
        }
      }
      
      return result;
    },
    
    /**
     * Process an action to produce the next state
     * @private
     * @param {Object} action - Action to process
     * @param {Object} state - Current state
     * @returns {Object} Updated state
     */
    _processAction: function(action, state) {
      // Call reducer if specified in options
      if (options.reducer && Prime.Utils.isFunction(options.reducer)) {
        return options.reducer(state, action);
      }
      
      // Default processing based on action type
      switch (action.type) {
        case 'SET_STATE':
          if (action.path && action.value !== undefined) {
            return this._setStateValue(state, action.path, action.value);
          } else if (action.state && Prime.Utils.isObject(action.state)) {
            return { ...action.state };
          }
          break;
          
        case 'UPDATE_STATE':
          if (Prime.Utils.isObject(action.updates)) {
            return { ...state, ...action.updates };
          }
          break;
          
        case 'MERGE_STATE':
          if (Prime.Utils.isObject(action.updates)) {
            return Prime.Utils.deepMerge(state, action.updates);
          }
          break;
          
        default:
          // For unknown actions, call the handler if defined
          if (options.actionHandlers && 
              options.actionHandlers[action.type] && 
              Prime.Utils.isFunction(options.actionHandlers[action.type])) {
            return options.actionHandlers[action.type](state, action);
          }
          break;
      }
      
      // If no processing was done, return the original state
      return state;
    },
    
    /**
     * Set a value at a specific path in the state
     * @private
     * @param {Object} state - Current state
     * @param {string|Array} path - Path to set value at
     * @param {*} value - Value to set
     * @returns {Object} Updated state
     */
    _setStateValue: function(state, path, value) {
      const pathArray = Array.isArray(path) ? path : path.split('.');
      const result = Prime.Utils.deepClone(state);
      
      let current = result;
      for (let i = 0; i < pathArray.length - 1; i++) {
        const key = pathArray[i];
        // Create objects along the path if they don't exist
        if (current[key] === undefined || current[key] === null || 
            typeof current[key] !== 'object') {
          current[key] = {};
        }
        current = current[key];
      }
      
      // Set the value at the final path segment
      const lastKey = pathArray[pathArray.length - 1];
      
      // If both current and new values are numbers, use Kahan summation for the difference
      if (typeof current[lastKey] === 'number' && typeof value === 'number') {
        const delta = value - current[lastKey];
        current[lastKey] = Prime.KahanSum(current[lastKey], delta);
      } else {
        current[lastKey] = value;
      }
      
      return result;
    },
    
    /**
     * Subscribe to state changes
     * @param {Function} subscriber - Subscriber function
     * @returns {Function} Unsubscribe function
     */
    subscribe: function(subscriber) {
      if (!Prime.Utils.isFunction(subscriber)) {
        throw new Prime.ValidationError('Subscriber must be a function', {
          context: { subscriber }
        });
      }
      
      subscriptions.push(subscriber);
      
      // Return function to unsubscribe
      return () => {
        const index = subscriptions.indexOf(subscriber);
        if (index !== -1) {
          subscriptions.splice(index, 1);
          return true;
        }
        return false;
      };
    },
    
    /**
     * Notify subscribers of state change
     * @private
     * @param {Object} action - Action that caused the change
     * @param {Object} prevState - Previous state
     * @param {Object} newState - New state
     */
    _notifySubscribers: function(action, prevState, newState) {
      const changeInfo = {
        action,
        prevState: Prime.Utils.deepClone(prevState),
        newState: Prime.Utils.deepClone(newState),
        timestamp: Date.now()
      };
      
      // Calculate delta paths for more efficient updates
      changeInfo.changedPaths = this._calculateChangedPaths(prevState, newState);
      
      // Notify subscribers
      for (const subscriber of subscriptions) {
        try {
          subscriber(changeInfo);
        } catch (error) {
          Prime.Logger.error('Error in state change subscriber:', error);
        }
      }
    },
    
    /**
     * Calculate paths that changed between two states
     * @private
     * @param {Object} prevState - Previous state
     * @param {Object} newState - New state
     * @param {string} [basePath=''] - Base path
     * @returns {Array} Array of changed paths
     */
    _calculateChangedPaths: function(prevState, newState, basePath = '') {
      const paths = [];
      
      // Handle non-object cases
      if (!Prime.Utils.isObject(prevState) || !Prime.Utils.isObject(newState)) {
        if (prevState !== newState) {
          paths.push(basePath);
        }
        return paths;
      }
      
      // Get all keys from both objects
      const allKeys = new Set([
        ...Object.keys(prevState),
        ...Object.keys(newState)
      ]);
      
      for (const key of allKeys) {
        const currentPath = basePath ? `${basePath}.${key}` : key;
        
        if (!(key in prevState)) {
          // Key was added
          paths.push(currentPath);
        } else if (!(key in newState)) {
          // Key was removed
          paths.push(currentPath);
        } else if (Prime.Utils.isObject(prevState[key]) && Prime.Utils.isObject(newState[key])) {
          // Recursively check objects
          const nestedPaths = this._calculateChangedPaths(
            prevState[key], 
            newState[key], 
            currentPath
          );
          paths.push(...nestedPaths);
        } else if (prevState[key] !== newState[key]) {
          // Leaf values differ
          paths.push(currentPath);
        }
      }
      
      return paths;
    },
    
    /**
     * Get current application state
     * @returns {Object} Current state
     */
    getState: function() {
      return Prime.Utils.deepClone(this.state);
    },
    
    /**
     * Get state change history
     * @param {Object} [options] - History options
     * @returns {Array} Action history
     */
    getHistory: function(options = {}) {
      let history = [...actionHistory];
      
      // Apply filters if specified
      if (options.actionTypes && Array.isArray(options.actionTypes)) {
        history = history.filter(entry => 
          options.actionTypes.includes(entry.action.type)
        );
      }
      
      // Apply limit if specified
      if (Prime.Utils.isNumber(options.limit) && options.limit > 0) {
        history = history.slice(-options.limit);
      }
      
      return history;
    },
    
    /**
     * Reset application state to initial state
     * @returns {Object} New state
     */
    resetState: function() {
      const prevState = this.state;
      this.state = Prime.Utils.deepClone(initialState);
      
      // Create and record reset action
      const resetAction = { type: 'RESET_STATE' };
      
      // Add to history
      if (actionHistory.length >= actionHistoryLimit) {
        actionHistory.shift();
      }
      
      actionHistory.push({
        id: Prime.Utils.uuid(),
        timestamp: Date.now(),
        action: resetAction,
        stateChanged: true
      });
      
      // Notify subscribers
      this._notifySubscribers(resetAction, prevState, this.state);
      
      return this.state;
    },
    
    /**
     * Get application metrics
     * @returns {Object} Application metrics
     */
    getMetrics: function() {
      return {
        id: this.id,
        startTime: options.startTime || Date.now(),
        componentCount: componentRegistry.size,
        stateSize: JSON.stringify(this.state).length,
        actionCount: actionHistory.length,
        subscriberCount: subscriptions.length,
        middlewareCount: middlewares.length
      };
    }
  };
  
  // Initialize additional aspects
  if (options.initialize && Prime.Utils.isFunction(options.initialize)) {
    options.initialize(app);
  }
  
  return app;
}

module.exports = createApplication;