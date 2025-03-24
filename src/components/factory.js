/**
 * PrimeOS JavaScript Library - Component Factory
 * Factory for creating specialized components
 * Version 1.0.0
 */

// Import Prime using CommonJS to avoid circular dependency
const Prime = require("../core.js");
// Ensure all modules are loaded in correct order
require("../mathematics.js");
require("../coherence.js");
require("../framework/index.js");
require("./base.js");

(function (Prime) {
  /**
   * Component Factory for creating specialized components
   */
  const ComponentFactory = {
    /**
     * Map of registered component types
     */
    types: new Map(),

    /**
     * Registered lifecycle hooks
     */
    lifecycleHooks: {
      beforeRegister: [],
      afterRegister: [],
      beforeUnregister: [],
      afterUnregister: []
    },
    
    /**
     * Add a lifecycle hook
     * @param {string} hook - Hook name (beforeRegister, afterRegister, beforeUnregister, afterUnregister)
     * @param {Function} callback - Hook callback
     * @returns {Function} Function to remove the hook
     */
    addHook: function(hook, callback) {
      if (!this.lifecycleHooks[hook]) {
        throw new Prime.ValidationError(`Invalid hook name: ${hook}`);
      }
      
      if (!Prime.Utils.isFunction(callback)) {
        throw new Prime.ValidationError("Hook callback must be a function");
      }
      
      this.lifecycleHooks[hook].push(callback);
      
      // Return function to remove the hook
      return () => {
        const index = this.lifecycleHooks[hook].indexOf(callback);
        if (index !== -1) {
          this.lifecycleHooks[hook].splice(index, 1);
        }
      };
    },
    
    /**
     * Register a component type
     * @param {string} type - Component type name
     * @param {Function} factory - Factory function
     * @returns {boolean} Success
     */
    register: function (type, factory) {
      if (!Prime.Utils.isString(type)) {
        throw new Prime.ValidationError("Type must be a string");
      }

      if (!Prime.Utils.isFunction(factory)) {
        throw new Prime.ValidationError("Factory must be a function");
      }
      
      // Run beforeRegister hooks
      for (const hook of this.lifecycleHooks.beforeRegister) {
        try {
          hook(type, factory);
        } catch (error) {
          Prime.Logger.error(`Error in beforeRegister hook for type ${type}`, {
            error: error.message,
            stack: error.stack
          });
        }
      }
      
      // Check if type is already registered
      const isUpdate = this.types.has(type);
      
      // Register the factory
      this.types.set(type, factory);
      
      // Run afterRegister hooks
      for (const hook of this.lifecycleHooks.afterRegister) {
        try {
          hook(type, factory, isUpdate);
        } catch (error) {
          Prime.Logger.error(`Error in afterRegister hook for type ${type}`, {
            error: error.message,
            stack: error.stack
          });
        }
      }
      
      // Publish event for component type registration
      Prime.EventBus.publish("component:typeRegistered", {
        type,
        isUpdate
      });
      
      return true;
    },

    /**
     * Create a component of the specified type
     * @param {string} type - Component type name
     * @param {Object} [config={}] - Component configuration
     * @returns {Object} New component
     * @throws {InvalidOperationError} If type is not registered
     * @throws {ValidationError} If factory returns invalid component
     */
    create: function (type, config = {}) {
      if (!this.types.has(type)) {
        throw new Prime.InvalidOperationError(
          `Component type ${type} is not registered`,
        );
      }

      try {
        // Get the factory function
        const factory = this.types.get(type);
        
        // Create the component
        const component = factory(config);
        
        // Validate the component
        if (!component || typeof component !== 'object') {
          throw new Prime.ValidationError(
            `Factory for component type ${type} returned invalid component`
          );
        }
        
        // Validate that the component has the required properties
        if (!component.meta || !component.variant || !component.invariant || !component.lifecycle) {
          throw new Prime.ValidationError(
            `Factory for component type ${type} returned incomplete component (missing required properties)`
          );
        }
        
        // Set the component type if not already set
        if (!component.meta.type) {
          component.meta.type = type;
        }
        
        // Add component version for tracking
        component.meta.version = component.meta.version || Prime.Components.version;
        
        // Add creation timestamp
        component.meta.created = component.meta.created || new Date().toISOString();
        
        // Validate coherence if applicable
        if (Prime.coherence && Prime.coherence.validate) {
          try {
            Prime.coherence.validate(component);
          } catch (coherenceError) {
            Prime.Logger.warn(`Component ${component.meta.id} failed coherence validation`, {
              error: coherenceError.message,
              component: component.meta.id,
            });
            
            // Add coherence warning to component
            component.meta.coherenceWarning = coherenceError.message;
          }
        }
        
        return component;
      } catch (error) {
        // Catch all errors from the factory function and wrap them
        Prime.Logger.error(`Failed to create component of type ${type}`, {
          error: error.message,
          stack: error.stack,
        });
        
        // Re-throw with additional context
        throw new Prime.InvalidOperationError(
          `Failed to create component of type ${type}: ${error.message}`,
          { cause: error }
        );
      }
    },

    /**
     * Check if a component type is registered
     * @param {string} type - Component type name
     * @returns {boolean} True if type is registered
     */
    hasType: function (type) {
      return this.types.has(type);
    },

    /**
     * Get all registered component types
     * @returns {Array} Registered type names
     */
    getTypes: function () {
      return Array.from(this.types.keys());
    },

    /**
     * Unregister a component type
     * @param {string} type - Component type name
     * @returns {boolean} Success
     */
    unregister: function (type) {
      if (!this.types.has(type)) {
        return false;
      }
      
      const factory = this.types.get(type);
      
      // Run beforeUnregister hooks
      for (const hook of this.lifecycleHooks.beforeUnregister) {
        try {
          hook(type, factory);
        } catch (error) {
          Prime.Logger.error(`Error in beforeUnregister hook for type ${type}`, {
            error: error.message,
            stack: error.stack
          });
        }
      }
      
      // Unregister the type
      const success = this.types.delete(type);
      
      if (success) {
        // Run afterUnregister hooks
        for (const hook of this.lifecycleHooks.afterUnregister) {
          try {
            hook(type);
          } catch (error) {
            Prime.Logger.error(`Error in afterUnregister hook for type ${type}`, {
              error: error.message,
              stack: error.stack
            });
          }
        }
        
        // Publish event for component type unregistration
        Prime.EventBus.publish("component:typeUnregistered", {
          type
        });
      }
      
      return success;
    },
  };

  // Register common component types
  ComponentFactory.register("container", (config) => {
    const defaults = {
      meta: {
        name: "Container",
        type: "container",
      },
      invariant: {
        // Container-specific methods
        addComponent: function (component) {
          return this.addChild(component);
        },
        removeComponent: function (component) {
          return this.removeChild(component);
        },
        getComponents: function () {
          return this.getChildren();
        },
      },
      variant: {
        layout: "default",
      },
    };

    return Prime.createComponent(
      Prime.Utils.deepClone({ ...defaults, ...config }),
    );
  });

  ComponentFactory.register("data", (config) => {
    const defaults = {
      meta: {
        name: "DataComponent",
        type: "data",
      },
      invariant: {
        // Data component specific methods
        getData: function () {
          return this.variant.data;
        },
        setData: function (data) {
          this.lifecycle.update({ data });
          return true;
        },
        transform: function (transformFn) {
          if (!Prime.Utils.isFunction(transformFn)) {
            throw new Prime.ValidationError("Transform must be a function");
          }

          const currentData = this.variant.data;
          const newData = transformFn(currentData);

          this.lifecycle.update({ data: newData });
          return true;
        },
      },
      variant: {
        data: null,
      },
    };

    return Prime.createComponent(
      Prime.Utils.deepClone({ ...defaults, ...config }),
    );
  });

  ComponentFactory.register("stateful", (config) => {
    const defaults = {
      meta: {
        name: "StatefulComponent",
        type: "stateful",
      },
      invariant: {
        // Stateful component specific methods
        getState: function () {
          return this.variant.state;
        },
        setState: function (state) {
          const newState = { ...this.variant.state, ...state };
          this.lifecycle.update({ state: newState });
          return true;
        },
        resetState: function () {
          this.lifecycle.update({ state: this.variant.initialState });
          return true;
        },
      },
      variant: {
        initialState: {},
        state: {},
      },
    };

    // Ensure initialState is copied to state
    const merged = Prime.Utils.deepClone({ ...defaults, ...config });
    if (
      !merged.variant.state ||
      Object.keys(merged.variant.state).length === 0
    ) {
      merged.variant.state = Prime.Utils.deepClone(merged.variant.initialState);
    }

    return Prime.createComponent(merged);
  });

  // Export ComponentFactory to Prime
  Prime.ComponentFactory = ComponentFactory;

  // Publish component module loaded event
  Prime.EventBus.publish("module:loaded", { name: "component-factory" });
})(Prime);

// CommonJS export (no ES module export to avoid circular dependency)
if (typeof module !== "undefined" && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== "undefined") {
  window.Prime = Prime;
}
