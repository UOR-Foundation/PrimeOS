/**
 * PrimeOS JavaScript Library - Component Base
 * Core component creation and lifecycle management
 * Version 1.0.0
 */

// Import Prime using CommonJS to avoid circular dependency
const Prime = require("../core.js");
// Ensure all modules are loaded in correct order
require("../mathematics.js");
require("../coherence.js");
require("../framework/index.js");
// Load component utilities with optimized clone methods
require("./componentUtils.js");

(function (Prime) {
  /**
   * Enhanced component creation with proper lifecycle management
   * @param {Object} config - Component configuration
   * @returns {Object} New component
   */
  function createComponent(config) {
    if (!config) {
      throw new Prime.ValidationError("Component configuration is required");
    }

    // Validate required sections
    if (!config.meta) {
      config.meta = {};
    }

    if (!config.meta.name) {
      config.meta.name = "UnnamedComponent";
    }

    // Generate component ID if not provided
    if (!config.meta.id) {
      config.meta.id = `${config.meta.name.toLowerCase()}-${Prime.Utils.uuid().substring(0, 8)}`;
    }

    // Ensure invariant and variant sections exist
    if (!config.invariant) {
      config.invariant = {};
    }

    // Log the createComponent call for debugging with safe access
    try {
      if (Prime.Logger && typeof Prime.Logger.debug === 'function') {
        Prime.Logger.debug("Creating component", { name: config.meta.name });
      }
    } catch (err) {
      console.log("Creating component:", config.meta.name);
    }

    // Create a coherence-aware component
    const component = {
      // Meta: contextual information and metadata
      meta: Prime.Components.Utils.fastClone(config.meta),

      // Invariant: static assets and code
      invariant: Prime.Components.Utils.fastClone(config.invariant),

      // Variant: dynamic data and state
      variant: Prime.Components.Utils.fastClone(config.variant || {}),

      // For compatibility with integration tests
      _initialized: false,
      _events: [],

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
        initialize: function () {
          // Don't re-initialize if already done
          if (component._initialized && component.meta.initialized) {
            return true;
          }
          
          try {
            // Create a safe initialization function that works with both patterns
            const initMethod = component.invariant.initialize || component.invariant.init;
            
            // Call the initialization method if available
            if (initMethod && typeof initMethod === "function") {
              initMethod.call(component);
            }

            // Set initial state
            component.setState(component.variant);

            // Register with coherence system if available
            if (Prime.coherence && Prime.coherence.systemCoherence) {
              Prime.coherence.systemCoherence.register(component);
            }

            // Component is now initialized - set both flags for compatibility
            component.meta.initialized = true;
            component._initialized = true;

            // Ensure events array exists
            if (!component._events) {
              component._events = [];
            }
            component._events.push("initialize");
            
            // Trigger initialization event after everything is set up
            component.emit("initialize");

            return true;
          } catch (error) {
            try {
              if (Prime.Logger && typeof Prime.Logger.error === 'function') {
                Prime.Logger.error(
                  `Failed to initialize component ${component.meta.id}`,
                  {
                    error: error.message,
                    stack: error.stack,
                    component: component.meta.id,
                  }
                );
              } else {
                console.error(`Failed to initialize component ${component.meta.id}`, error);
              }
            } catch (logErr) {
              console.error(`Failed to initialize component ${component.meta.id}`, error);
            }
            
            // Emit error event for better error recovery
            if (component._listeners && component._listeners['error']) {
              try {
                component.emit('error', {
                  phase: 'initialization',
                  error: error
                });
              } catch (emitError) {
                // Just log if error event handler fails
                try {
                  if (Prime.Logger && typeof Prime.Logger.error === 'function') {
                    Prime.Logger.error(`Failed to emit error event during initialization`, {
                      error: emitError.message,
                      component: component.meta.id,
                    });
                  } else {
                    console.error(`Failed to emit error event during initialization for ${component.meta.id}`, emitError);
                  }
                } catch (logErr) {
                  console.error(`Failed to emit error event during initialization for ${component.meta.id}`, emitError);
                }
              }
            }

            return false;
          }
        },

        /**
         * Mount component to parent
         * @param {Object} parent - Parent component or container
         * @returns {boolean} Success
         */
        mount: function (parent) {
          if (!component.meta.initialized || !component._initialized) {
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
            if (
              component.invariant.mount &&
              typeof component.invariant.mount === "function"
            ) {
              component.invariant.mount.call(component, parent);
            }

            // Trigger mount event
            component.emit("mount", { parent });

            // Component is now mounted
            component.meta.mounted = true;

            return true;
          } catch (error) {
            try {
              if (Prime.Logger && typeof Prime.Logger.error === 'function') {
                Prime.Logger.error(
                  `Failed to mount component ${component.meta.id}`,
                  {
                    error: error.message,
                    stack: error.stack,
                  }
                );
              } else {
                console.error(`Failed to mount component ${component.meta.id}`, error);
              }
            } catch (logErr) {
              console.error(`Failed to mount component ${component.meta.id}`, error);
            }

            return false;
          }
        },

        /**
         * Update component state
         * @param {Object} newState - New state
         * @returns {boolean} Success
         */
        update: function (newState) {
          try {
            // Calculate previous state for comparison - use fast clone for performance
            const prevState = Prime.Components.Utils.fastClone(component.variant);

            // Update the variant with new state
            component.setState(newState);

            // Run user-provided update handler if available
            if (
              component.invariant.update &&
              typeof component.invariant.update === "function"
            ) {
              component.invariant.update.call(component, newState, prevState);
            }

            // Trigger update event
            component.emit("update", {
              newState,
              prevState,
            });

            // Update event in global bus
            Prime.EventBus.publish("component:updated", {
              component,
              newState,
              prevState,
            });

            return true;
          } catch (error) {
            try {
              if (Prime.Logger && typeof Prime.Logger.error === 'function') {
                Prime.Logger.error(
                  `Failed to update component ${component.meta.id}`,
                  {
                    error: error.message,
                    stack: error.stack,
                  }
                );
              } else {
                console.error(`Failed to update component ${component.meta.id}`, error);
              }
            } catch (logErr) {
              console.error(`Failed to update component ${component.meta.id}`, error);
            }

            return false;
          }
        },

        /**
         * Unmount component
         * @returns {boolean} Success
         */
        unmount: function () {
          try {
            // Run user-provided unmount handler if available
            if (
              component.invariant.unmount &&
              typeof component.invariant.unmount === "function"
            ) {
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
            component.emit("unmount");

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
            try {
              if (Prime.Logger && typeof Prime.Logger.error === 'function') {
                Prime.Logger.error(
                  `Failed to unmount component ${component.meta.id}`,
                  {
                    error: error.message,
                    stack: error.stack,
                  }
                );
              } else {
                console.error(`Failed to unmount component ${component.meta.id}`, error);
              }
            } catch (logErr) {
              console.error(`Failed to unmount component ${component.meta.id}`, error);
            }

            return false;
          }
        },

        /**
         * Destroy component and clean up resources
         * @returns {boolean} Success
         */
        destroy: function () {
          try {
            // Unmount if mounted
            if (component.meta.mounted) {
              this.unmount();
            }

            // Run user-provided destroy handler if available
            if (
              component.invariant.destroy &&
              typeof component.invariant.destroy === "function"
            ) {
              component.invariant.destroy.call(component);
            }

            // Trigger destroy event
            component.emit("destroy");

            // Clear all references
            component._parent = null;
            component._children = [];
            component._listeners = {};

            // Component is now destroyed
            component.meta.destroyed = true;

            return true;
          } catch (error) {
            try {
              if (Prime.Logger && typeof Prime.Logger.error === 'function') {
                Prime.Logger.error(
                  `Failed to destroy component ${component.meta.id}`,
                  {
                    error: error.message,
                    stack: error.stack,
                  }
                );
              } else {
                console.error(`Failed to destroy component ${component.meta.id}`, error);
              }
            } catch (logErr) {
              console.error(`Failed to destroy component ${component.meta.id}`, error);
            }

            return false;
          }
        },
      },

      /**
       * Update component state with coherence validation
       * @param {Object} newState - New state to apply
       * @returns {Object} Updated component
       */
      setState: function (newState) {
        if (!newState) {
          return this;
        }

        // Skip update if nothing has changed (performance optimization)
        if (Object.keys(newState).length === 0) {
          return this;
        }

        // Check if using coherence constraints
        if (
          this.invariant.constraints &&
          this.invariant.constraints.length > 0
        ) {
          const constraints = this.invariant.constraints;
          // Create proposed state with efficient merge
          const proposed = Prime.Components.Utils.shallowMerge(this.variant, newState);

          // Check all constraints
          for (const constraint of constraints) {
            if (!constraint.check(proposed)) {
              if (constraint.type === "hard") {
                throw new Prime.CoherenceViolationError(
                  `State update violates hard constraint "${constraint.name}"`,
                  constraint,
                  1.0,
                  { object: proposed },
                );
              }

              // For soft constraints, we'll just log a warning
              try {
                if (Prime.Logger && typeof Prime.Logger.warn === 'function') {
                  Prime.Logger.warn(
                    `State update violates soft constraint "${constraint.name}"`,
                    {
                      component: this.meta.id,
                      constraint: constraint.name,
                    }
                  );
                } else {
                  console.warn(`State update violates soft constraint "${constraint.name}" for component ${this.meta.id}`);
                }
              } catch (logErr) {
                console.warn(`State update violates soft constraint "${constraint.name}" for component ${this.meta.id}`);
              }
            }
          }
        }

        // Optimize: Skip deep merging for top-level primitive values
        const hasNestedObjects = Object.values(newState).some(v => 
          v !== null && typeof v === 'object'
        );

        if (hasNestedObjects) {
          // For complex nested updates, use efficient merging
          this.variant = Prime.Components.Utils.efficientMerge(this.variant, newState);
        } else {
          // For simple updates, shallow merge is faster
          this.variant = Prime.Components.Utils.shallowMerge(this.variant, newState);
        }

        return this;
      },

      /**
       * Get component state
       * @returns {Object} Component state
       */
      getState: function () {
        return Prime.Components.Utils.fastClone(this.variant);
      },

      /**
       * Add event listener
       * @param {string} event - Event name
       * @param {Function} callback - Event callback
       * @returns {Function} Unsubscribe function
       */
      on: function (event, callback) {
        if (!Prime.Utils.isString(event)) {
          throw new Prime.ValidationError("Event name must be a string");
        }

        if (!Prime.Utils.isFunction(callback)) {
          throw new Prime.ValidationError("Callback must be a function");
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
      off: function (event, callback) {
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
      emit: function (event, data = {}) {
        if (!this._listeners[event]) {
          return false;
        }

        // Clone listeners array to avoid issues if handlers modify the array
        const listeners = [...this._listeners[event]];
        let hasErrors = false;
        let successCount = 0;

        for (const callback of listeners) {
          try {
            callback.call(this, { ...data, component: this });
            successCount++;
          } catch (error) {
            hasErrors = true;
            try {
              if (Prime.Logger && typeof Prime.Logger.error === 'function') {
                Prime.Logger.error(`Error in event handler for ${event}`, {
                  error: error.message,
                  stack: error.stack,
                  component: this.meta.id,
                });
              } else {
                console.error(`Error in event handler for ${event} in component ${this.meta.id}`, error);
              }
            } catch (logErr) {
              console.error(`Error in event handler for ${event} in component ${this.meta.id}`, error);
            }
            
            // Emit an error event so the error can be handled by the component
            if (this._listeners['error'] && event !== 'error') {
              try {
                this.emit('error', {
                  originalEvent: event,
                  originalData: data,
                  error: error
                });
              } catch (emitError) {
                // Prevent infinite loops with error events
                try {
                  if (Prime.Logger && typeof Prime.Logger.error === 'function') {
                    Prime.Logger.error(`Failed to emit error event`, {
                      error: emitError.message,
                      component: this.meta.id,
                    });
                  } else {
                    console.error(`Failed to emit error event for component ${this.meta.id}`, emitError);
                  }
                } catch (logErr) {
                  console.error(`Failed to emit error event for component ${this.meta.id}`, emitError);
                }
              }
            }
          }
        }

        // Return true only if all handlers succeeded
        return !hasErrors && successCount > 0;
      },

      /**
       * Add a child component
       * @param {Object} child - Child component
       * @returns {Object} Child component
       */
      addChild: function (child) {
        if (!child || !child.lifecycle) {
          throw new Prime.ValidationError("Child must be a valid component");
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
      removeChild: function (child) {
        let childComponent;

        if (Prime.Utils.isString(child)) {
          // Find child by ID
          childComponent = this._children.find((c) => c.meta.id === child);
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
      findChild: function (id, deep = false) {
        // Direct children search
        const directChild = this._children.find((c) => c.meta.id === id);

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
      getChildren: function () {
        return [...this._children];
      },

      /**
       * Get parent component
       * @returns {Object|null} Parent component
       */
      getParent: function () {
        return this._parent;
      },

      /**
       * Calculate coherence norm
       * @returns {number} Coherence norm
       */
      coherenceNorm: function () {
        // If there are constraints, calculate coherence based on them
        if (
          this.invariant.constraints &&
          this.invariant.constraints.length > 0
        ) {
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
        if (Prime.coherence && Prime.coherence.norm) {
          return Prime.coherence.norm(this.variant);
        }

        // Default to 0 (perfectly coherent)
        return 0;
      },

      /**
       * Check if component is coherent
       * @param {number} [tolerance=1e-6] - Tolerance for coherence check
       * @param {Object} [options] - Additional coherence check options
       * @returns {boolean} True if component is coherent
       */
      isCoherent: function (tolerance = 1e-6, options = {}) {
        // Basic coherence check based on constraints
        const basicCoherent = this.coherenceNorm() <= tolerance;
        
        // If basic check fails, return false immediately
        if (!basicCoherent) {
          return false;
        }
        
        // Enhanced mathematical coherence checks if requested
        if (options.checkMathematical !== false) {
          // Perform mathematical coherence checks on variant data
          return Prime.Components.CoherenceCheck.isCoherent(this.variant, options);
        }
        
        return true;
      },

      /**
       * Add mathematical coherence constraints
       * @param {string} path - Path to property to constrain
       * @param {Object} [options] - Constraint options
       * @returns {Object} Component instance for chaining
       */
      addMathConstraint: function (path, options = {}) {
        // Initialize constraints array if not present
        if (!this.invariant.constraints) {
          this.invariant.constraints = [];
        }
        
        // Create appropriate constraint type based on property type
        let value;
        try {
          if (Prime.Utils && typeof Prime.Utils.getPath === 'function') {
            value = Prime.Utils.getPath(this.variant, path);
          } else {
            // Simple fallback path traversal
            value = path.split('.').reduce((o, p) => o && o[p], this.variant);
          }
        } catch (err) {
          console.error(`Error getting path ${path} in addMathConstraint`, err);
          // Continue with undefined value
        }
        
        let constraint;
        
        if (Array.isArray(value)) {
          // Array constraint
          constraint = Prime.Components.CoherenceCheck.createUniformArrayConstraint(
            path, 
            options.name || `Array coherence (${path})`
          );
        } else if (Prime.Math && Prime.Math.Matrix && value instanceof Prime.Math.Matrix) {
          // Matrix constraint
          constraint = Prime.Components.CoherenceCheck.createMatrixConstraint(
            path,
            options,
            options.name || `Matrix coherence (${path})`
          );
        } else {
          // Generic constraint
          constraint = Prime.Components.CoherenceCheck.createMathConstraint(
            (obj) => {
              let val;
              try {
                if (Prime.Utils && typeof Prime.Utils.getPath === 'function') {
                  val = Prime.Utils.getPath(obj, path);
                } else {
                  // Simple fallback path traversal
                  val = path.split('.').reduce((o, p) => o && o[p], obj);
                }
              } catch (err) {
                console.error(`Error getting path ${path}`, err);
                return false;
              }
              
              try {
                if (Prime.Components && Prime.Components.CoherenceCheck && 
                    typeof Prime.Components.CoherenceCheck.isCoherent === 'function') {
                  return Prime.Components.CoherenceCheck.isCoherent(val, options);
                }
                // If CoherenceCheck not available, consider it valid
                return true;
              } catch (err) {
                console.error(`Error checking coherence for ${path}`, err);
                return false;
              }
            },
            options.name || `Math coherence (${path})`,
            { type: options.type || 'hard' }
          );
        }
        
        // Add constraint
        this.invariant.constraints.push(constraint);
        
        return this;
      },
      
      /**
       * Clone this component
       * @param {Object} [overrides={}] - Configuration overrides
       * @returns {Object} Cloned component
       */
      clone: function (overrides = {}) {
        const config = {
          meta: { ...this.meta, id: undefined }, // Generate new ID
          invariant: this.invariant,
          variant: this.variant,
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
      toString: function () {
        return `Component(${this.meta.id})`;
      },

      /**
       * Serialize component to JSON
       * @returns {Object} Serialized component
       */
      toJSON: function () {
        return {
          meta: this.meta,
          variant: this.variant,
        };
      },
    };

    // Create the invocable interface from invariant methods
    for (const key in config.invariant) {
      if (Prime.Utils.isFunction(config.invariant[key])) {
        component.invocable[key] = function (...args) {
          return config.invariant[key].apply(component, args);
        };
      }
    }

    // Call lifecycle.initialize() which will handle both init and initialize methods
    component.lifecycle.initialize();

    // coherenceNorm method is already defined on the component

    return component;
  }

  // Export createComponent to Prime
  Prime.createComponent = createComponent;

  // Add event publishing wrapped in a try-catch to handle potential initialization issues
  try {
    if (Prime.EventBus && typeof Prime.EventBus.publish === 'function') {
      Prime.EventBus.publish("module:loaded", { name: "component-base" });
    }
  } catch (err) {
    console.error('Error publishing module:loaded event for component-base:', err);
  }
})(Prime);

// CommonJS export (no ES module export to avoid circular dependency)
if (typeof module !== "undefined" && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== "undefined") {
  window.Prime = Prime;
}
