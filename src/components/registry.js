/**
 * PrimeOS JavaScript Library - Component Registry
 * Registry for tracking and managing components
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
   * Component Registry for tracking and managing components
   */
  const ComponentRegistry = {
    /**
     * Map of registered components by ID
     */
    components: new Map(),

    /**
     * Register a component
     * @param {Object} component - Component to register
     * @returns {boolean} Success
     */
    register: function (component) {
      if (!component || !component.meta || !component.meta.id) {
        throw new Prime.ValidationError(
          'Component must have a meta.id property',
        );
      }

      const id = component.meta.id;

      if (this.components.has(id)) {
        throw new Prime.InvalidOperationError(
          `Component with ID ${id} is already registered`,
        );
      }

      this.components.set(id, component);

      // Publish registration event
      Prime.EventBus.publish('component:registered', { component });

      return true;
    },

    /**
     * Unregister a component
     * @param {Object|string} component - Component or component ID
     * @returns {boolean} Success
     */
    unregister: function (component) {
      const id = Prime.Utils.isString(component)
        ? component
        : component.meta.id;

      if (!this.components.has(id)) {
        return false;
      }

      const removedComponent = this.components.get(id);
      this.components.delete(id);

      // Publish unregistration event
      Prime.EventBus.publish('component:unregistered', {
        component: removedComponent,
      });

      return true;
    },

    /**
     * Get a component by ID
     * @param {string} id - Component ID
     * @returns {Object|undefined} Component
     */
    get: function (id) {
      return this.components.get(id);
    },

    /**
     * Check if a component is registered
     * @param {Object|string} component - Component or component ID
     * @returns {boolean} True if component is registered
     */
    has: function (component) {
      const id = Prime.Utils.isString(component)
        ? component
        : component.meta.id;
      return this.components.has(id);
    },

    /**
     * Get all registered components
     * @returns {Array} All components
     */
    getAll: function () {
      return Array.from(this.components.values());
    },

    /**
     * Find components by criteria
     * @param {Function} predicate - Filter function
     * @returns {Array} Matching components
     */
    find: function (predicate) {
      return this.getAll().filter(predicate);
    },

    /**
     * Count registered components
     * @returns {number} Component count
     */
    count: function () {
      return this.components.size;
    },

    /**
     * Clear all registered components
     * @returns {number} Number of components cleared
     */
    clear: function () {
      const count = this.components.size;
      this.components.clear();
      return count;
    },
  };

  // Export ComponentRegistry to Prime
  Prime.ComponentRegistry = ComponentRegistry;

  // Publish component module loaded event
  Prime.EventBus.publish('module:loaded', { name: 'component-registry' });
})(Prime);

// CommonJS export (no ES module export to avoid circular dependency)
if (typeof module !== 'undefined' && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== 'undefined') {
  window.Prime = Prime;
}
