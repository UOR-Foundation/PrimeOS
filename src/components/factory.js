/**
 * PrimeOS JavaScript Library - Component Factory
 * Factory for creating specialized components
 * Version 1.0.0
 */

// Import Prime using CommonJS to avoid circular dependency
const Prime = require('../core.js');
// Ensure all modules are loaded in correct order
require('../mathematics.js');
require('../coherence.js');
require('../framework/index.js');
require('./base.js');

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
     * Register a component type
     * @param {string} type - Component type name
     * @param {Function} factory - Factory function
     * @returns {boolean} Success
     */
    register: function (type, factory) {
      if (!Prime.Utils.isString(type)) {
        throw new Prime.ValidationError('Type must be a string');
      }

      if (!Prime.Utils.isFunction(factory)) {
        throw new Prime.ValidationError('Factory must be a function');
      }

      this.types.set(type, factory);
      return true;
    },

    /**
     * Create a component of the specified type
     * @param {string} type - Component type name
     * @param {Object} [config={}] - Component configuration
     * @returns {Object} New component
     * @throws {InvalidOperationError} If type is not registered
     */
    create: function (type, config = {}) {
      if (!this.types.has(type)) {
        throw new Prime.InvalidOperationError(
          `Component type ${type} is not registered`,
        );
      }

      const factory = this.types.get(type);
      return factory(config);
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
      return this.types.delete(type);
    },
  };

  // Register common component types
  ComponentFactory.register('container', (config) => {
    const defaults = {
      meta: {
        name: 'Container',
        type: 'container',
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
        layout: 'default',
      },
    };

    return Prime.createComponent(
      Prime.Utils.deepClone({ ...defaults, ...config }),
    );
  });

  ComponentFactory.register('data', (config) => {
    const defaults = {
      meta: {
        name: 'DataComponent',
        type: 'data',
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
            throw new Prime.ValidationError('Transform must be a function');
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

  ComponentFactory.register('stateful', (config) => {
    const defaults = {
      meta: {
        name: 'StatefulComponent',
        type: 'stateful',
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
  Prime.EventBus.publish('module:loaded', { name: 'component-factory' });
})(Prime);

// CommonJS export (no ES module export to avoid circular dependency)
if (typeof module !== 'undefined' && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== 'undefined') {
  window.Prime = Prime;
}
