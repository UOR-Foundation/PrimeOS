/**
 * PrimeOS JavaScript Library - Components Part 1
 * Component model and lifecycle management
 * Version 1.0.0
 */

// Import extended Prime
import { Prime } from './framework.js';

(function(Prime) {
  'use strict';
  
  /**
   * Enhanced component creation with proper lifecycle management
   * @param {Object} config - Component configuration
   * @returns {Object} New component
   */
  function createComponent(config) {
    if (!config) {
      throw new Prime.ValidationError('Component configuration is required');
    }
    
    // Validate required sections
    if (!config.meta) {
      config.meta = {};
    }
    
    if (!config.meta.name) {
      config.meta.name = 'UnnamedComponent';
    }
    
    // Generate component ID if not provided
    if (!config.meta.id) {
      config.meta.id = `${config.meta.name.toLowerCase()}-${Prime.Utils.uuid().substring(0, 8)}`;
    }
    
    // Ensure invariant and variant sections exist
    if (!config.invariant) {
      config.invariant = {};
    }
    
    // Create a coherence-aware component
    const component = {
      // Meta: contextual information and metadata
      meta: Prime.Utils.deepClone(config.meta),
      
      // Invariant: static assets and code
      invariant: Prime.Utils.deepClone(config.invariant),
      
      // Variant: dynamic data and state
      variant: Prime.Utils.deepClone(config.variant || {}),
      
      // Component interface - methods from invariant that can be called
      invocable: {},
      
      // Component references and relationships
      _parent: null,
      _children: [],
      
      // Event listeners
      _listeners: {},
      
      // Enhanced lifecycle with proper event handling
      lifecycle: {
        /**
         * Initialize component
         * @returns {boolean} Success
         */
        initialize: function() {
          try {
            // Run user-provided initializer if available
            if (component.invariant.initialize && typeof component.invariant.initialize === 'function') {
              component.invariant.initialize.call(component);
            }
            
            // Set initial state
            component.setState(component.variant);
            
            // Trigger initialization event
            component.emit('initialize');
            
            // Register with coherence system if available
            if (Prime.coherence && Prime.coherence.systemCoherence) {
              Prime.coherence.systemCoherence.register(component);
            }
            
            // Component is now initialized
            component.meta.initialized = true;
            
            return true;
          } catch (error) {
            Prime.Logger.error(`Failed to initialize component ${component.meta.id}`, {
              error: error.message,
              stack: error.stack
            });
            
            return false;
          }
        },
        
        /**
         * Mount component to parent
         * @param {Object} parent - Parent component or container
         * @returns {boolean} Success
         */
        mount: function(parent) {
          if (!component.meta.initialized) {
            this.initialize();
          }
          
          try {
            // Set parent reference
            component._parent = parent;
            
            // Add to parent's children if parent is a component
            if (parent && parent._children) {
              parent._children.push(component);
            }
            
            // Run user-provided mount handler if available
            if (component.invariant.mount && typeof component.invariant.mount === 'function') {
              component.invariant.mount.call(component, parent);
            }
            
            // Trigger mount event
            component.emit('mount', { parent });
            
            // Component is now mounted
            component.meta.mounted = true;
            
            return true;
          } catch (error) {
            Prime.Logger.error(`Failed to mount component ${component.meta.id}`, {
              error: error.message,
              stack: error.stack
            });
            
            return false;
          }
        },
        
        /**
         * Update component state
         * @param {Object} newState - New state
         * @returns {boolean} Success
         */
        update: function(newState) {
          try {
            // Calculate previous state for comparison
            const prevState = Prime.Utils.deepClone(component.variant);
            
            // Update the variant with new state
            component.setState(newState);
            
            // Run user-provided update handler if available
            if (component.invariant.update && typeof component.invariant.update === 'function') {
              component.invariant.update.call(component, newState, prevState);
            }
            
            // Trigger update event
            component.emit('update', { 
              newState, 
              prevState 
            });
            
            // Update event in global bus
            Prime.EventBus.publish('component:updated', {
              component,
              newState,
              prevState
            });
            
            return true;
          } catch (error) {
            Prime.Logger.error(`Failed to update component ${component.meta.id}`, {
              error: error.message,
              stack: error.stack
            });
            
            return false;
          }
        },
        
        /**
         * Unmount component
         * @returns {boolean} Success
         */
        unmount: function() {
          try {
            // Run user-provided unmount handler if available
            if (component.invariant.unmount && typeof component.invariant.unmount === 'function') {
              component.invariant.unmount.call(component);
            }
            
            // Remove from parent's children
            if (component._parent && component._parent._children) {
              const index = component._parent._children.indexOf(component);
              
              if (index !== -1) {
                component._parent._children.splice(index, 1);
              }
            }
            
            // Trigger unmount event
            component.emit('unmount');
            
            // Unmount all children
            for (const child of component._children.slice()) {
              child.lifecycle.unmount();
            }
            
            // Clear parent reference
            component._parent = null;
            component._children = [];
            
            // Unregister from coherence system
            if (Prime.coherence && Prime.coherence.systemCoherence) {
              Prime.coherence.systemCoherence.unregister(component);
            }
            
            // Component is now unmounted
            component.meta.mounted = false;
            
            return true;
          } catch (error) {
            Prime.Logger.error(`Failed to unmount component ${component.meta.id}`, {
              error: error.message,
              stack: error.stack
            });
            
            return false;
          }
        },
        
        /**
         * Destroy component and clean up resources
         * @returns {boolean} Success
         */
        destroy: function() {
          try {
            // Unmount if mounted
            if (component.meta.mounted) {
              this.unmount();
            }
            
            // Run user-provided destroy handler if available
            if (component.invariant.destroy && typeof component.invariant.destroy === 'function') {
              component.invariant.destroy.call(component);
            }
            
            // Trigger destroy event
            component.emit('destroy');
            
            // Clear all references
            component._parent = null;
            component._children = [];
            component._listeners = {};
            
            // Component is now destroyed
            component.meta.destroyed = true;
            
            return true;
          } catch (error) {
            Prime.Logger.error(`Failed to destroy component ${component.meta.id}`, {
              error: error.message,
              stack: error.stack
            });
            
            return false;
          }
        }
      },
      
      /**
       * Update component state with coherence validation
       * @param {Object} newState - New state to apply
       * @returns {Object} Updated component
       */
      setState: function(newState) {
        if (!newState) {
          return this;
        }
        
        // Check if using coherence constraints
        if (this.invariant.constraints && this.invariant.constraints.length > 0) {
          const constraints = this.invariant.constraints;
          const proposed = { ...this.variant, ...newState };
          
          // Check all constraints
          for (const constraint of constraints) {
            if (!constraint.check(proposed)) {
              if (constraint.type === 'hard') {
                throw new Prime.CoherenceViolationError(
                  `State update violates hard constraint "${constraint.name}"`,
                  constraint,
                  1.0,
                  { object: proposed }
                );
              }
              
              // For soft constraints, we'll just log a warning
              Prime.Logger.warn(`State update violates soft constraint "${constraint.name}"`, {
                component: this.meta.id,
                constraint: constraint.name
              });
            }
          }
        }
        
        // Update variant with new state
        this.variant = { ...this.variant, ...newState };
        
        return this;
      },
      
      /**
       * Get component state
       * @returns {Object} Component state
       */
      getState: function() {
        return Prime.Utils.deepClone(this.variant);
      },
      
      /**
       * Add event listener
       * @param {string} event - Event name
       * @param {Function} callback - Event callback
       * @returns {Function} Unsubscribe function
       */
      on: function(event, callback) {
        if (!Prime.Utils.isString(event)) {
          throw new Prime.ValidationError('Event name must be a string');
        }
        
        if (!Prime.Utils.isFunction(callback)) {
          throw new Prime.ValidationError('Callback must be a function');
        }
        
        // Create event array if it doesn't exist
        if (!this._listeners[event]) {
          this._listeners[event] = [];
        }
        
        // Add callback to listeners
        this._listeners[event].push(callback);
        
        // Return unsubscribe function
        return () => {
          const index = this._listeners[event].indexOf(callback);
          
          if (index !== -1) {
            this._listeners[event].splice(index, 1);
          }
        };
      },
      
      /**
       * Remove event listener
       * @param {string} event - Event name
       * @param {Function} callback - Event callback
       * @returns {boolean} Success
       */
      off: function(event, callback) {
        if (!this._listeners[event]) {
          return false;
        }
        
        const index = this._listeners[event].indexOf(callback);
        
        if (index !== -1) {
          this._listeners[event].splice(index, 1);
          return true;
        }
        
        return false;
      },
      
      /**
       * Emit event
       * @param {string} event - Event name
       * @param {Object} [data={}] - Event data
       * @returns {boolean} Success
       */
      emit: function(event, data = {}) {
        if (!this._listeners[event]) {
          return false;
        }
        
        // Clone listeners array to avoid issues if handlers modify the array
        const listeners = [...this._listeners[event]];
        
        for (const callback of listeners) {
          try {
            callback.call(this, { ...data, component: this });
          } catch (error) {
            Prime.Logger.error(`Error in event handler for ${event}`, {
              error: error.message,
              stack: error.stack,
              component: this.meta.id
            });
          }
        }
        
        return true;
      },
      
      /**
       * Add a child component
       * @param {Object} child - Child component
       * @returns {Object} Child component
       */
      addChild: function(child) {
        if (!child || !child.lifecycle) {
          throw new Prime.ValidationError('Child must be a valid component');
        }
        
        // Mount child to this component
        child.lifecycle.mount(this);
        
        return child;
      },
      
      /**
       * Remove a child component
       * @param {Object|string} child - Child component or ID
       * @returns {boolean} Success
       */
      removeChild: function(child) {
        let childComponent;
        
        if (Prime.Utils.isString(child)) {
          // Find child by ID
          childComponent = this._children.find(c => c.meta.id === child);
        } else {
          childComponent = child;
        }
        
        if (!childComponent) {
          return false;
        }
        
        // Unmount child
        return childComponent.lifecycle.unmount();
      },
      
      /**
       * Find a child component by ID
       * @param {string} id - Child ID
       * @param {boolean} [deep=false] - Search deeply through component tree
       * @returns {Object|null} Found component or null
       */
      findChild: function(id, deep = false) {
        // Direct children search
        const directChild = this._children.find(c => c.meta.id === id);
        
        if (directChild) {
          return directChild;
        }
        
        // Deep search if requested
        if (deep) {
          for (const child of this._children) {
            const found = child.findChild(id, true);
            
            if (found) {
              return found;
            }
          }
        }
        
        return null;
      },
      
      /**
       * Get all children
       * @returns {Array} Child components
       */
      getChildren: function() {
        return [...this._children];
      },
      
      /**
       * Get parent component
       * @returns {Object|null} Parent component
       */
      getParent: function() {
        return this._parent;
      },
      
      /**
       * Calculate coherence norm
       * @returns {number} Coherence norm
       */
      coherenceNorm: function() {
        // If there are constraints, calculate coherence based on them
        if (this.invariant.constraints && this.invariant.constraints.length > 0) {
          let normSquared = 0;
          
          for (const constraint of this.invariant.constraints) {
            if (!constraint.check(this.variant)) {
              const weight = constraint.weight || 1;
              normSquared += weight * weight;
            }
          }
          
          return Math.sqrt(normSquared);
        }
        
        // If no constraints, delegate to coherence system
        if (Prime.coherence) {
          return Prime.coherence.norm(this.variant);
        }
        
        // Default to 0 (perfectly coherent)
        return 0;
      },
      
      /**
       * Check if component is coherent
       * @param {number} [tolerance=1e-6] - Tolerance for coherence check
       * @returns {boolean} True if component is coherent
       */
      isCoherent: function(tolerance = 1e-6) {
        return this.coherenceNorm() <= tolerance;
      },
      
      /**
       * Clone this component
       * @param {Object} [overrides={}] - Configuration overrides
       * @returns {Object} Cloned component
       */
      clone: function(overrides = {}) {
        const config = {
          meta: { ...this.meta, id: undefined }, // Generate new ID
          invariant: this.invariant,
          variant: this.variant
        };
        
        // Apply overrides
        if (overrides.meta) {
          config.meta = { ...config.meta, ...overrides.meta };
        }
        
        if (overrides.variant) {
          config.variant = { ...config.variant, ...overrides.variant };
        }
        
        return createComponent(config);
      },
      
      /**
       * Convert component to string
       * @returns {string} String representation
       */
      toString: function() {
        return `Component(${this.meta.id})`;
      },
      
      /**
       * Serialize component to JSON
       * @returns {Object} Serialized component
       */
      toJSON: function() {
        return {
          meta: this.meta,
          variant: this.variant
        };
      }
    };
    
    // Create the invocable interface from invariant methods
    for (const key in config.invariant) {
      if (Prime.Utils.isFunction(config.invariant[key])) {
        component.invocable[key] = function(...args) {
          return config.invariant[key].apply(component, args);
        };
      }
    }
    
    return component;
  }
  
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
    register: function(component) {
      if (!component || !component.meta || !component.meta.id) {
        throw new Prime.ValidationError('Component must have a meta.id property');
      }
      
      const id = component.meta.id;
      
      if (this.components.has(id)) {
        throw new Prime.InvalidOperationError(`Component with ID ${id} is already registered`);
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
    unregister: function(component) {
      const id = Prime.Utils.isString(component) ? component : component.meta.id;
      
      if (!this.components.has(id)) {
        return false;
      }
      
      const removedComponent = this.components.get(id);
      this.components.delete(id);
      
      // Publish unregistration event
      Prime.EventBus.publish('component:unregistered', { component: removedComponent });
      
      return true;
    },
    
    /**
     * Get a component by ID
     * @param {string} id - Component ID
     * @returns {Object|undefined} Component
     */
    get: function(id) {
      return this.components.get(id);
    },
    
    /**
     * Check if a component is registered
     * @param {Object|string} component - Component or component ID
     * @returns {boolean} True if component is registered
     */
    has: function(component) {
      const id = Prime.Utils.isString(component) ? component : component.meta.id;
      return this.components.has(id);
    },
    
    /**
     * Get all registered components
     * @returns {Array} All components
     */
    getAll: function() {
      return Array.from(this.components.values());
    },
    
    /**
     * Find components by criteria
     * @param {Function} predicate - Filter function
     * @returns {Array} Matching components
     */
    find: function(predicate) {
      return this.getAll().filter(predicate);
    },
    
    /**
     * Count registered components
     * @returns {number} Component count
     */
    count: function() {
      return this.components.size;
    },
    
    /**
     * Clear all registered components
     * @returns {number} Number of components cleared
     */
    clear: function() {
      const count = this.components.size;
      this.components.clear();
      return count;
    }
  };
  
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
    register: function(type, factory) {
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
    create: function(type, config = {}) {
      if (!this.types.has(type)) {
        throw new Prime.InvalidOperationError(`Component type ${type} is not registered`);
      }
      
      const factory = this.types.get(type);
      return factory(config);
    },
    
    /**
     * Check if a component type is registered
     * @param {string} type - Component type name
     * @returns {boolean} True if type is registered
     */
    hasType: function(type) {
      return this.types.has(type);
    },
    
    /**
     * Get all registered component types
     * @returns {Array} Registered type names
     */
    getTypes: function() {
      return Array.from(this.types.keys());
    },
    
    /**
     * Unregister a component type
     * @param {string} type - Component type name
     * @returns {boolean} Success
     */
    unregister: function(type) {
      return this.types.delete(type);
    }
  };
  
  /**
   * Component Template for creating reusable component templates
   */
  class ComponentTemplate {
    /**
     * Create a new component template
     * @param {Object} template - Template configuration
     */
    constructor(template) {
      this.template = Prime.Utils.deepClone(template);
      this.validators = [];
      
      // Add name validation by default
      this.addValidator(config => {
        if (!config.meta || !config.meta.name) {
          throw new Prime.ValidationError('Component must have a meta.name property');
        }
        return true;
      });
    }
    
    /**
     * Add a validator function
     * @param {Function} validator - Validator function
     * @returns {ComponentTemplate} This template for chaining
     */
    addValidator(validator) {
      if (!Prime.Utils.isFunction(validator)) {
        throw new Prime.ValidationError('Validator must be a function');
      }
      
      this.validators.push(validator);
      return this;
    }
    
    /**
     * Create a component from this template
     * @param {Object} config - Component configuration
     * @returns {Object} New component
     */
    create(config) {
      // Merge template with provided config
      const mergedConfig = this._mergeConfigs(this.template, config);
      
      // Run all validators
      for (const validator of this.validators) {
        validator(mergedConfig);
      }
      
      // Create the component
      return createComponent(mergedConfig);
    }
    
    /**
     * Create multiple components from this template
     * @param {Array} configs - Array of component configurations
     * @returns {Array} New components
     */
    createBatch(configs) {
      return configs.map(config => this.create(config));
    }
    
    /**
     * Extend this template with additional properties
     * @param {Object} extension - Template extension
     * @returns {ComponentTemplate} New template
     */
    extend(extension) {
      const extendedTemplate = new ComponentTemplate(this._mergeConfigs(this.template, extension));
      
      // Copy validators
      for (const validator of this.validators) {
        extendedTemplate.addValidator(validator);
      }
      
      return extendedTemplate;
    }
    
    /**
     * Register this template as a component type
     * @param {string} typeName - Type name to register
     * @returns {ComponentTemplate} This template for chaining
     */
    registerType(typeName) {
      if (!Prime.Utils.isString(typeName)) {
        throw new Prime.ValidationError('Type name must be a string');
      }
      
      // Register with component factory
      ComponentFactory.register(typeName, config => this.create(config));
      
      return this;
    }
    
    /**
     * Helper to deeply merge configurations
     * @private
     * @param {Object} base - Base configuration
     * @param {Object} override - Configuration override
     * @returns {Object} Merged configuration
     */
    _mergeConfigs(base, override) {
      const result = Prime.Utils.deepClone(base);
      
      // Special handling for different sections
      for (const section of ['meta', 'invariant', 'variant']) {
        if (override[section]) {
          result[section] = result[section] || {};
          result[section] = { ...result[section], ...override[section] };
        }
      }
      
      // Handle other properties
      for (const key in override) {
        if (!['meta', 'invariant', 'variant'].includes(key)) {
          result[key] = override[key];
        }
      }
      
      return result;
    }
  }
  
  // Register common component types
  ComponentFactory.register('container', config => {
    const defaults = {
      meta: {
        name: 'Container',
        type: 'container'
      },
      invariant: {
        // Container-specific methods
        addComponent: function(component) {
          return this.addChild(component);
        },
        removeComponent: function(component) {
          return this.removeChild(component);
        },
        getComponents: function() {
          return this.getChildren();
        }
      },
      variant: {
        layout: 'default'
      }
    };
    
    return createComponent(Prime.Utils.deepClone({...defaults, ...config}));
  });
  
  ComponentFactory.register('data', config => {
    const defaults = {
      meta: {
        name: 'DataComponent',
        type: 'data'
      },
      invariant: {
        // Data component specific methods
        getData: function() {
          return this.variant.data;
        },
        setData: function(data) {
          this.lifecycle.update({ data });
          return true;
        },
        transform: function(transformFn) {
          if (!Prime.Utils.isFunction(transformFn)) {
            throw new Prime.ValidationError('Transform must be a function');
          }
          
          const currentData = this.variant.data;
          const newData = transformFn(currentData);
          
          this.lifecycle.update({ data: newData });
          return true;
        }
      },
      variant: {
        data: null
      }
    };
    
    return createComponent(Prime.Utils.deepClone({...defaults, ...config}));
  });
  
  ComponentFactory.register('stateful', config => {
    const defaults = {
      meta: {
        name: 'StatefulComponent',
        type: 'stateful'
      },
      invariant: {
        // Stateful component specific methods
        getState: function() {
          return this.variant.state;
        },
        setState: function(state) {
          const newState = { ...this.variant.state, ...state };
          this.lifecycle.update({ state: newState });
          return true;
        },
        resetState: function() {
          this.lifecycle.update({ state: this.variant.initialState });
          return true;
        }
      },
      variant: {
        initialState: {},
        state: {}
      }
    };
    
    // Ensure initialState is copied to state
    const merged = Prime.Utils.deepClone({...defaults, ...config});
    if (!merged.variant.state || Object.keys(merged.variant.state).length === 0) {
      merged.variant.state = Prime.Utils.deepClone(merged.variant.initialState);
    }
    
    return createComponent(merged);
  });
  
  // Extend Prime with component capabilities
  Prime.createComponent = createComponent;
  Prime.ComponentRegistry = ComponentRegistry;
  Prime.ComponentFactory = ComponentFactory;
  Prime.ComponentTemplate = ComponentTemplate;
  
  // Publish component module loaded event
  Prime.EventBus.publish('module:loaded', { name: 'components-1' });
  
})(Prime);

// Export extended Prime
export { Prime };

// For CommonJS compatibility
if (typeof module !== 'undefined' && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== 'undefined') {
  window.Prime = Prime;
}
