/**
 * PrimeOS Test Utilities - Mocking
 * 
 * Standardized mocking helpers for PrimeOS tests.
 * These utilities provide consistent mocking patterns across all test files.
 */

/**
 * Mocking utilities for standardized test mocks
 */
const Mocking = {
  /**
   * Create a mock object based on the original object
   * 
   * @param {Object} original - Object to mock
   * @param {Object} [options] - Mocking options
   * @param {boolean} [options.preserveNonFunctions=false] - Whether to preserve non-function properties
   * @param {boolean} [options.callThrough=false] - Whether to call through to original methods
   * @returns {Object} - Mock object
   */
  createMock: (original, options = {}) => {
    const mock = {};
    const calls = {};
    const results = {};
    
    // Process options
    const preserveNonFunctions = options.preserveNonFunctions || false;
    const callThrough = options.callThrough || false;
    
    // Copy all methods from original to mock
    Object.getOwnPropertyNames(original).forEach(key => {
      const value = original[key];
      
      if (typeof value === 'function') {
        // Track calls to this method
        calls[key] = [];
        
        // Create mock method
        mock[key] = function(...args) {
          // Track call arguments
          calls[key].push(args);
          
          // Return predefined result or call through
          if (results[key] !== undefined) {
            return typeof results[key] === 'function' 
              ? results[key](...args) 
              : results[key];
          } else if (callThrough) {
            return value.apply(original, args);
          }
          
          // Default return is undefined
        };
      } else if (preserveNonFunctions) {
        // Preserve non-function properties
        mock[key] = value;
      }
    });
    
    // Attach call tracking and result overrides
    mock.calls = calls;
    mock.results = results;
    
    // Add utility methods
    mock.resetCalls = function() {
      Object.keys(calls).forEach(key => {
        calls[key] = [];
      });
    };
    
    mock.resetResults = function() {
      Object.keys(results).forEach(key => {
        delete results[key];
      });
    };
    
    return mock;
  },
  
  /**
   * Create a spy that wraps the original function
   * 
   * @param {Function} originalFunction - Function to spy on
   * @returns {Function} - Spy function
   */
  createSpy: (originalFunction) => {
    const calls = [];
    
    // Create spy function
    const spy = function(...args) {
      // Track call
      calls.push(args);
      
      // Call original function
      return originalFunction.apply(this, args);
    };
    
    // Add tracking info
    spy.calls = calls;
    spy.getCallCount = () => calls.length;
    spy.reset = () => { 
      calls.length = 0;
    };
    
    return spy;
  },
  
  /**
   * Create a mock component with coherence constraints
   * 
   * @param {Object} options - Component options
   * @param {string} options.name - Component name
   * @param {Object} [options.state] - Initial state
   * @param {Array} [options.constraints] - Coherence constraints
   * @returns {Object} - Mock component
   */
  createMockComponent: (options) => {
    const { name, state = {}, constraints = [] } = options;
    
    const component = {
      name,
      state: { ...state },
      methods: {
        updateState: function(newState) {
          // Check constraints before updating
          for (const constraint of constraints) {
            if (constraint.check && !constraint.check({...component.state, ...newState})) {
              const weight = constraint.weight || 1;
              throw new Error(`Coherence violation: ${constraint.name || 'unnamed'} (weight: ${weight})`);
            }
          }
          
          // Update state if all constraints pass
          component.state = {...component.state, ...newState};
        }
      }
    };
    
    // Add variant getter for compatibility
    Object.defineProperty(component, 'variant', {
      get: function() {
        return this.state;
      }
    });
    
    // Add setState method for compatibility
    component.setState = function(newState) {
      this.methods.updateState(newState);
      return this;
    };
    
    // Add coherenceNorm method
    component.coherenceNorm = function() {
      // Check constraints and calculate norm
      let normSquared = 0;
      
      for (const constraint of constraints) {
        if (constraint.check && !constraint.check(this.state)) {
          const weight = constraint.weight || 1;
          normSquared += weight * weight;
        }
      }
      
      return Math.sqrt(normSquared);
    };
    
    return component;
  },
  
  /**
   * Create a mock event bus
   * 
   * @returns {Object} - Mock event bus
   */
  createMockEventBus: () => {
    const handlers = {};
    const calls = {
      subscribe: [],
      publish: [],
      unsubscribe: [],
      clear: []
    };
    
    return {
      subscribe: function(event, handler) {
        calls.subscribe.push([event, handler]);
        
        if (!handlers[event]) {
          handlers[event] = [];
        }
        
        handlers[event].push(handler);
        
        return () => this.unsubscribe(event, handler);
      },
      
      publish: function(event, data) {
        calls.publish.push([event, data]);
        
        if (handlers[event]) {
          handlers[event].forEach(handler => {
            try {
              handler(data);
            } catch (e) {
              // Swallow errors in handlers to mimic EventBus behavior
              console.error(`Error in event handler for ${event}:`, e);
            }
          });
        }
      },
      
      unsubscribe: function(event, handler) {
        calls.unsubscribe.push([event, handler]);
        
        if (handlers[event]) {
          const index = handlers[event].indexOf(handler);
          if (index !== -1) {
            handlers[event].splice(index, 1);
            return true;
          }
        }
        
        return false;
      },
      
      clear: function(event) {
        calls.clear.push([event]);
        
        if (event) {
          delete handlers[event];
        } else {
          Object.keys(handlers).forEach(key => {
            delete handlers[key];
          });
        }
      },
      
      // For compatibility with different implementations
      on: function(event, handler) {
        return this.subscribe(event, handler);
      },
      
      emit: function(event, data) {
        return this.publish(event, data);
      },
      
      off: function(event, handler) {
        return this.unsubscribe(event, handler);
      },
      
      // Tracking
      _handlers: handlers,
      calls
    };
  }
};

module.exports = Mocking;