/**
 * PrimeOS JavaScript Library - Core
 * Foundation utilities, error classes, version management, and the central Prime object
 * Version 1.0.0
 */

// Use module pattern for encapsulation
const Prime = (function() {
    'use strict';
  
    /**
     * Library version with semantic validation support
     */
    const VERSION = '1.0.0';
    
    const validateVersion = (minVersion) => {
      if (!minVersion) return true;
      
      const [majorReq, minorReq, patchReq] = minVersion.split('.').map(Number);
      const [major, minor, patch] = VERSION.split('.').map(Number);
      
      if (major < majorReq) return false;
      if (major === majorReq && minor < minorReq) return false;
      if (major === majorReq && minor === minorReq && patch < patchReq) return false;
      
      return true;
    };
  
    /**
     * Enhanced utilities with robust error checking
     */
    const Utils = {
      isObject: function(obj) {
        return obj !== null && typeof obj === 'object' && !Array.isArray(obj);
      },
      
      isFunction: function(fn) {
        return typeof fn === 'function';
      },
      
      isArray: function(arr) {
        return Array.isArray(arr);
      },
      
      isNumber: function(num) {
        return typeof num === 'number' && !isNaN(num) && isFinite(num);
      },
      
      isString: function(str) {
        return typeof str === 'string';
      },
      
      isBoolean: function(bool) {
        return typeof bool === 'boolean';
      },
      
      isUndefined: function(val) {
        return typeof val === 'undefined';
      },
      
      isNull: function(val) {
        return val === null;
      },
      
      isNullOrUndefined: function(val) {
        return val === null || typeof val === 'undefined';
      },
      
      isPrimitive: function(val) {
        const type = typeof val;
        return val === null || (type !== 'object' && type !== 'function');
      },
      
      /**
       * Deep clone an object with circular reference handling
       */
      deepClone: function(obj) {
        if (this.isPrimitive(obj)) return obj;
        
        const cache = new WeakMap();
        
        const clone = (item) => {
          if (this.isObject(item) || this.isArray(item)) {
            if (cache.has(item)) {
              return cache.get(item);
            }
            
            let copy;
            
            if (this.isArray(item)) {
              copy = [];
              cache.set(item, copy);
              item.forEach((val, i) => {
                copy[i] = clone(val);
              });
            } else if (item instanceof Date) {
              copy = new Date(item);
            } else if (item instanceof RegExp) {
              copy = new RegExp(item.source, item.flags);
            } else if (item instanceof Map) {
              copy = new Map();
              cache.set(item, copy);
              item.forEach((val, key) => {
                copy.set(clone(key), clone(val));
              });
            } else if (item instanceof Set) {
              copy = new Set();
              cache.set(item, copy);
              item.forEach(val => {
                copy.add(clone(val));
              });
            } else {
              copy = Object.create(Object.getPrototypeOf(item));
              cache.set(item, copy);
              Object.getOwnPropertyNames(item).forEach(key => {
                const descriptor = Object.getOwnPropertyDescriptor(item, key);
                if (descriptor.value) {
                  descriptor.value = clone(descriptor.value);
                }
                Object.defineProperty(copy, key, descriptor);
              });
            }
            
            return copy;
          }
          
          return item;
        };
        
        return clone(obj);
      },
      
      /**
       * Memoize a function with configurable cache size limit
       */
      memoize: function(fn, options = {}) {
        const cache = new Map();
        const maxSize = options.maxSize || 100;
        
        return function(...args) {
          const key = JSON.stringify(args);
          
          if (cache.has(key)) {
            // Move this key to the front of the LRU cache
            const value = cache.get(key);
            cache.delete(key);
            cache.set(key, value);
            return value;
          }
          
          const result = fn.apply(this, args);
          
          // Maintain cache size limit (LRU eviction)
          if (cache.size >= maxSize) {
            const firstKey = cache.keys().next().value;
            cache.delete(firstKey);
          }
          
          cache.set(key, result);
          return result;
        };
      },
      
      /**
       * Safely get a deeply nested property with a default value
       */
      get: function(obj, path, defaultValue) {
        if (!obj || !path) return defaultValue;
        
        const keys = this.isArray(path) ? path : path.split('.');
        let result = obj;
        
        for (const key of keys) {
          if (result === null || result === undefined) {
            return defaultValue;
          }
          result = result[key];
        }
        
        return result === undefined ? defaultValue : result;
      },
      
      /**
       * Safely set a deeply nested property
       */
      set: function(obj, path, value) {
        if (!obj || !path) return obj;
        
        const keys = this.isArray(path) ? path : path.split('.');
        let current = obj;
        
        for (let i = 0; i < keys.length - 1; i++) {
          const key = keys[i];
          if (current[key] === undefined) {
            current[key] = {};
          }
          current = current[key];
        }
        
        current[keys[keys.length - 1]] = value;
        return obj;
      },
      
      /**
       * Throttle a function to limit execution frequency
       */
      throttle: function(fn, delay) {
        let lastCall = 0;
        
        return function(...args) {
          const now = Date.now();
          
          if (now - lastCall >= delay) {
            lastCall = now;
            return fn.apply(this, args);
          }
        };
      },
      
      /**
       * Debounce a function to delay execution until input stops
       */
      debounce: function(fn, delay) {
        let timeoutId;
        
        return function(...args) {
          clearTimeout(timeoutId);
          
          timeoutId = setTimeout(() => {
            fn.apply(this, args);
          }, delay);
        };
      },
      
      /**
       * Create a UUID for unique identification
       */
      uuid: function() {
        return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, function(c) {
          const r = (Math.random() * 16) | 0;
          const v = c === 'x' ? r : (r & 0x3) | 0x8;
          return v.toString(16);
        });
      }
    };
  
    /**
     * Comprehensive error hierarchy
     */
    class PrimeError extends Error {
      constructor(message, options = {}) {
        super(message);
        this.name = 'PrimeError';
        this.timestamp = new Date();
        this.code = options.code || 'GENERIC_ERROR';
        
        // Capture stack trace
        if (Error.captureStackTrace) {
          Error.captureStackTrace(this, this.constructor);
        }
        
        // Additional context if provided
        if (options.context) {
          this.context = options.context;
        }
      }
      
      toString() {
        let result = `${this.name}: ${this.message}`;
        if (this.code) {
          result += ` [${this.code}]`;
        }
        if (this.context) {
          result += `\nContext: ${JSON.stringify(this.context)}`;
        }
        return result;
      }
    }
  
    class CoherenceViolationError extends PrimeError {
      constructor(message, constraint, magnitude, options = {}) {
        super(message, { 
          code: options.code || 'COHERENCE_VIOLATION',
          context: { ...options.context, constraint, magnitude }
        });
        this.name = 'CoherenceViolationError';
        this.constraint = constraint;
        this.magnitude = magnitude;
      }
    }
  
    class MathematicalError extends PrimeError {
      constructor(message, options = {}) {
        super(message, { 
          code: options.code || 'MATHEMATICAL_ERROR', 
          context: options.context 
        });
        this.name = 'MathematicalError';
      }
    }
  
    class InvalidOperationError extends PrimeError {
      constructor(message, options = {}) {
        super(message, { 
          code: options.code || 'INVALID_OPERATION', 
          context: options.context 
        });
        this.name = 'InvalidOperationError';
      }
    }
  
    class ConfigurationError extends PrimeError {
      constructor(message, options = {}) {
        super(message, { 
          code: options.code || 'CONFIGURATION_ERROR', 
          context: options.context 
        });
        this.name = 'ConfigurationError';
      }
    }
  
    class ValidationError extends PrimeError {
      constructor(message, options = {}) {
        super(message, { 
          code: options.code || 'VALIDATION_ERROR', 
          context: options.context 
        });
        this.name = 'ValidationError';
      }
    }
  
    /**
     * Global event bus for framework communication
     */
    const EventBus = {
      events: {},
      
      /**
       * Subscribe to an event with a callback
       * @param {string} event - Event name
       * @param {Function} callback - Callback function
       * @returns {Function} Unsubscribe function
       */
      subscribe: function(event, callback) {
        if (!Utils.isString(event)) {
          throw new ValidationError('Event name must be a string', { 
            context: { providedType: typeof event } 
          });
        }
        
        if (!Utils.isFunction(callback)) {
          throw new ValidationError('Callback must be a function', { 
            context: { providedType: typeof callback } 
          });
        }
        
        if (!this.events[event]) {
          this.events[event] = [];
        }
        
        this.events[event].push(callback);
        
        // Return unsubscribe function
        return () => this.unsubscribe(event, callback);
      },
      
      /**
       * Publish an event with data
       * @param {string} event - Event name
       * @param {*} data - Event data
       */
      publish: function(event, data) {
        if (!this.events[event]) {
          return;
        }
        
        this.events[event].forEach(callback => {
          try {
            callback(data);
          } catch (error) {
            console.error(`Error in event handler for ${event}:`, error);
          }
        });
      },
      
      /**
       * Unsubscribe from an event
       * @param {string} event - Event name
       * @param {Function} callback - Callback function
       * @returns {boolean} Success
       */
      unsubscribe: function(event, callback) {
        if (!this.events[event]) {
          return false;
        }
        
        const index = this.events[event].indexOf(callback);
        if (index !== -1) {
          this.events[event].splice(index, 1);
          
          // Clean up empty event arrays
          if (this.events[event].length === 0) {
            delete this.events[event];
          }
          
          return true;
        }
        
        return false;
      },
      
      /**
       * Clear all event subscriptions or for a specific event
       * @param {string} [event] - Optional event name
       */
      clear: function(event) {
        if (event) {
          delete this.events[event];
        } else {
          this.events = {};
        }
      }
    };
  
    /**
     * Module loader with environment detection
     */
    const ModuleLoader = {
      /**
       * Check the current JavaScript environment
       * @returns {string} Environment type: 'browser', 'node', 'worker', or 'unknown'
       */
      detectEnvironment: function() {
        if (typeof window !== 'undefined' && typeof document !== 'undefined') {
          return 'browser';
        }
        
        if (typeof process !== 'undefined' && 
            process.versions && 
            process.versions.node) {
          return 'node';
        }
        
        if (typeof self !== 'undefined' && 
            typeof WorkerGlobalScope !== 'undefined' && 
            self instanceof WorkerGlobalScope) {
          return 'worker';
        }
        
        return 'unknown';
      },
      
      /**
       * Load a module dynamically
       * @param {string} modulePath - Path to module
       * @returns {Promise} Promise that resolves with the loaded module
       */
      load: async function(modulePath) {
        const env = this.detectEnvironment();
        
        if (env === 'browser' || env === 'worker') {
          try {
            return await import(modulePath);
          } catch (error) {
            throw new InvalidOperationError(`Failed to load module: ${modulePath}`, {
              context: { error: error.message }
            });
          }
        } else if (env === 'node') {
          try {
            // Use dynamic import for Node.js ESM compatibility
            return await import(modulePath);
          } catch (error) {
            throw new InvalidOperationError(`Failed to load module: ${modulePath}`, {
              context: { error: error.message }
            });
          }
        } else {
          throw new InvalidOperationError('Module loading not supported in this environment');
        }
      },
      
      /**
       * Register a module in the Prime namespace
       * @param {string} name - Module name
       * @param {Object} module - Module object
       */
      register: function(name, module) {
        if (!Utils.isString(name)) {
          throw new ValidationError('Module name must be a string');
        }
        
        if (!Utils.isObject(module)) {
          throw new ValidationError('Module must be an object');
        }
        
        // Extend Prime with the module
        Prime[name] = module;
        
        EventBus.publish('module:loaded', { name, module });
        
        return true;
      }
    };
  
    /**
     * Testing utilities for the Prime framework
     */
    const Testing = {
      /**
       * Assert that a condition is true
       * @param {boolean} condition - Condition to check
       * @param {string} message - Error message if condition is false
       */
      assert: function(condition, message = 'Assertion failed') {
        if (!condition) {
          throw new ValidationError(message);
        }
      },
      
      /**
       * Create a mock object for testing
       * @param {Object} template - Template object to mock
       * @returns {Object} Mock object
       */
      createMock: function(template = {}) {
        const mock = {
          calls: {},
          results: {},
          ...Utils.deepClone(template)
        };
        
        // Track calls to all methods
        Object.keys(mock).forEach(key => {
          if (Utils.isFunction(mock[key]) && key !== 'calls' && key !== 'results') {
            const originalFn = mock[key];
            
            mock[key] = function(...args) {
              // Record call
              if (!mock.calls[key]) {
                mock.calls[key] = [];
              }
              mock.calls[key].push(args);
              
              // Return predefined result if available
              if (mock.results[key]) {
                if (Utils.isFunction(mock.results[key])) {
                  return mock.results[key](...args);
                }
                return mock.results[key];
              }
              
              // Otherwise call original function
              return originalFn.apply(this, args);
            };
          }
        });
        
        return mock;
      },
      
      /**
       * Create a spy function that tracks calls
       * @param {Function} [fn] - Original function to spy on
       * @returns {Function} Spy function
       */
      createSpy: function(fn = () => {}) {
        const calls = [];
        
        const spy = function(...args) {
          calls.push(args);
          return fn.apply(this, args);
        };
        
        spy.calls = calls;
        spy.getCallCount = () => calls.length;
        spy.reset = () => { calls.length = 0; };
        
        return spy;
      }
    };
  
    /**
     * Internal logger with configurable levels
     */
    const Logger = {
      levels: {
        DEBUG: 0,
        INFO: 1,
        WARN: 2,
        ERROR: 3,
        NONE: 4
      },
      
      currentLevel: 1, // Default to INFO
      
      setLevel: function(level) {
        if (Utils.isString(level)) {
          if (this.levels[level.toUpperCase()] !== undefined) {
            this.currentLevel = this.levels[level.toUpperCase()];
          } else {
            throw new ValidationError(`Invalid log level: ${level}`);
          }
        } else if (Utils.isNumber(level) && level >= 0 && level <= 4) {
          this.currentLevel = level;
        } else {
          throw new ValidationError('Log level must be a valid string or number');
        }
      },
      
      shouldLog: function(level) {
        return this.levels[level] >= this.currentLevel;
      },
      
      format: function(level, message, context) {
        let output = `[Prime] [${level}] ${message}`;
        if (context) {
          output += `\nContext: ${JSON.stringify(context)}`;
        }
        return output;
      },
      
      debug: function(message, context) {
        if (this.shouldLog('DEBUG')) {
          console.debug(this.format('DEBUG', message, context));
        }
      },
      
      info: function(message, context) {
        if (this.shouldLog('INFO')) {
          console.info(this.format('INFO', message, context));
        }
      },
      
      warn: function(message, context) {
        if (this.shouldLog('WARN')) {
          console.warn(this.format('WARN', message, context));
        }
      },
      
      error: function(message, context) {
        if (this.shouldLog('ERROR')) {
          console.error(this.format('ERROR', message, context));
        }
      }
    };
  
    /**
     * Return core Prime object (to be extended by other modules)
     */
    return {
      // Version information
      version: VERSION,
      validateVersion,
      
      // Core utilities
      Utils,
      EventBus,
      ModuleLoader,
      Testing,
      Logger,
      
      // Error classes
      PrimeError,
      CoherenceViolationError,
      MathematicalError,
      InvalidOperationError,
      ConfigurationError,
      ValidationError,
      
      // Version compatibility system
      isCompatible: function(requirements) {
        const features = requirements.features || [];
        const minVersion = requirements.minVersion || '0.0.0';
        
        // Check version compatibility
        if (!validateVersion(minVersion)) {
          return false;
        }
        
        // Check feature availability
        for (const feature of features) {
          if (feature === 'coherence' && !this.coherence) return false;
          if (feature === 'spectral' && !this.spectral) return false;
          if (feature === 'lie' && !this.Lie) return false;
        }
        
        return true;
      },
      
      // Deprecation warning system
      deprecationWarnings: [],
      
      addDeprecationWarning: function(warning) {
        this.deprecationWarnings.push(warning);
      },
      
      getDeprecationWarnings: function() {
        return [...this.deprecationWarnings];
      }
    };
  })();
  
  // Export for different module systems
  export { Prime };
  
  // For CommonJS compatibility
  if (typeof module !== 'undefined' && module.exports) {
    module.exports = Prime;
  }
  
  // For browser global scope
  if (typeof window !== 'undefined') {
    window.Prime = Prime;
  }