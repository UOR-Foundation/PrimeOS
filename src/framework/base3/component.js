/**
 * Base3 - Component Module
 *
 * Provides the component model for the application layer:
 * - Lifecycle management (mount, update, unmount)
 * - Prop validation and coherence checking
 * - Event handling with precise timing
 * - Rendering with various representation formats
 */

const Prime = require("../../core/prime.js");
const { Utils } = Prime;

/**
 * Create a component
 * @param {Object} options - Component options
 * @returns {Object} Component instance
 */
function createComponent(options = {}) {
  // Validate required options
  if (!options.id) {
    throw new Prime.ValidationError("Component id is required", {
      context: { options },
    });
  }

  // Default options with secure type checking
  const props = Prime.Utils.isObject(options.props)
    ? Prime.Utils.deepClone(options.props)
    : {};
  const children = Array.isArray(options.children) ? [...options.children] : [];
  const eventHandlers = new Map();

  // Setup lifecycle hooks
  const hooks = {
    beforeMount: options.beforeMount,
    mounted: options.mounted,
    beforeUpdate: options.beforeUpdate,
    updated: options.updated,
    beforeUnmount: options.beforeUnmount,
    unmounted: options.unmounted,
    errorCaught: options.errorCaught,
  };

  // Performance metrics
  const metrics = {
    renderCount: 0,
    lastRenderDuration: 0,
    totalRenderTime: 0,
    mountTime: null,
    updateTimes: [],
  };

  // Core component instance
  const component = {
    id: options.id,
    type: "component",
    name: options.name || options.id,
    state: Prime.Utils.deepClone(options.state || {}),
    props,
    children,
    isMounted: false,

    /**
     * Mount the component
     * @param {Object} mountOptions - Mount options
     * @returns {boolean} Success
     */
    mount: function (mountOptions = {}) {
      if (this.isMounted) {
        return false;
      }

      try {
        // Call before mount hook
        if (Prime.Utils.isFunction(hooks.beforeMount)) {
          hooks.beforeMount.call(this, mountOptions);
        }

        // Set mounted flag
        this.isMounted = true;
        metrics.mountTime = Date.now();

        // Call mounted hook
        if (Prime.Utils.isFunction(hooks.mounted)) {
          hooks.mounted.call(this, mountOptions);
        }

        return true;
      } catch (error) {
        // Handle mount errors
        this.isMounted = false;

        if (Prime.Utils.isFunction(hooks.errorCaught)) {
          hooks.errorCaught.call(this, error, "mount");
        } else {
          throw error;
        }

        return false;
      }
    },

    /**
     * Unmount the component
     * @param {Object} unmountOptions - Unmount options
     * @returns {boolean} Success
     */
    unmount: function (unmountOptions = {}) {
      if (!this.isMounted) {
        return false;
      }

      try {
        // Call before unmount hook
        if (Prime.Utils.isFunction(hooks.beforeUnmount)) {
          hooks.beforeUnmount.call(this, unmountOptions);
        }

        // Set mounted flag
        this.isMounted = false;

        // Call unmounted hook
        if (Prime.Utils.isFunction(hooks.unmounted)) {
          hooks.unmounted.call(this, unmountOptions);
        }

        return true;
      } catch (error) {
        // Handle unmount errors, but still consider unmounted
        this.isMounted = false;

        if (Prime.Utils.isFunction(hooks.errorCaught)) {
          hooks.errorCaught.call(this, error, "unmount");
        } else {
          throw error;
        }

        return true;
      }
    },

    /**
     * Update component props with validation
     * @param {Object} newProps - New props
     * @returns {boolean} Success
     */
    updateProps: function (newProps) {
      if (!Prime.Utils.isObject(newProps)) {
        throw new Prime.ValidationError("Props must be an object", {
          context: { newProps },
        });
      }

      try {
        // Validate prop types if specified
        if (options.propTypes) {
          for (const propName in newProps) {
            if (options.propTypes[propName]) {
              const validator = options.propTypes[propName];
              const value = newProps[propName];

              if (Prime.Utils.isFunction(validator)) {
                const validationResult = validator(value, propName, this.id);

                if (validationResult !== true) {
                  throw new Prime.ValidationError(
                    `Invalid prop '${propName}'`,
                    {
                      context: {
                        componentId: this.id,
                        propName,
                        value,
                        validationMessage:
                          validationResult || "Failed type validation",
                      },
                    },
                  );
                }
              }
            }
          }
        }

        // Call before update hook if mounted
        if (this.isMounted && Prime.Utils.isFunction(hooks.beforeUpdate)) {
          hooks.beforeUpdate.call(this, { props: newProps, type: "props" });
        }

        // Update props with deep merging and precise numerical handling
        this.props = this._applyPreciseUpdate(this.props, newProps);

        // Record update time
        const updateTime = Date.now();
        metrics.updateTimes.push(updateTime);

        // Keep only the last 10 update times
        if (metrics.updateTimes.length > 10) {
          metrics.updateTimes.shift();
        }

        // Call updated hook if mounted
        if (this.isMounted && Prime.Utils.isFunction(hooks.updated)) {
          hooks.updated.call(this, { props: newProps, type: "props" });
        }

        return true;
      } catch (error) {
        // Handle update errors
        if (Prime.Utils.isFunction(hooks.errorCaught)) {
          hooks.errorCaught.call(this, error, "updateProps");
          return false;
        } else {
          throw error;
        }
      }
    },

    /**
     * Apply a precise update to props or state
     * @private
     * @param {Object} current - Current object
     * @param {Object} updates - Updates to apply
     * @returns {Object} Updated object
     */
    _applyPreciseUpdate: function (current, updates) {
      // Handle non-object cases
      if (!Prime.Utils.isObject(current) || !Prime.Utils.isObject(updates)) {
        return updates;
      }

      const result = Prime.Utils.deepClone(current);

      for (const key in updates) {
        if (Object.prototype.hasOwnProperty.call(updates, key)) {
          const updateValue = updates[key];
          const currentValue = current[key];

          // For numerical values, use Kahan summation for the difference
          if (
            typeof currentValue === "number" &&
            typeof updateValue === "number"
          ) {
            const delta = updateValue - currentValue;
            result[key] = Prime.KahanSum(currentValue, delta);
          }
          // For nested objects, recursively apply precise update
          else if (
            Prime.Utils.isObject(currentValue) &&
            Prime.Utils.isObject(updateValue)
          ) {
            result[key] = this._applyPreciseUpdate(currentValue, updateValue);
          }
          // For arrays with numerical values, apply precise updates to each element
          else if (
            Array.isArray(currentValue) &&
            Array.isArray(updateValue) &&
            updateValue.length === currentValue.length &&
            currentValue.every((item) => typeof item === "number") &&
            updateValue.every((item) => typeof item === "number")
          ) {
            result[key] = updateValue.map((newVal, i) => {
              const delta = newVal - currentValue[i];
              return Prime.KahanSum(currentValue[i], delta);
            });
          }
          // For all other cases, use the update value directly
          else {
            result[key] = updateValue;
          }
        }
      }

      return result;
    },

    /**
     * Update component state with validation
     * @param {Object} updates - State updates
     * @returns {boolean} Success
     */
    updateState: function (updates) {
      if (!Prime.Utils.isObject(updates)) {
        throw new Prime.ValidationError("State updates must be an object", {
          context: { updates },
        });
      }

      try {
        // Call before update hook if mounted
        if (this.isMounted && Prime.Utils.isFunction(hooks.beforeUpdate)) {
          hooks.beforeUpdate.call(this, { state: updates, type: "state" });
        }

        // Check if update would create coherent state if specified
        if (options.checkStateCoherence !== false) {
          const nextState = { ...this.state, ...updates };
          const coherenceResult = Prime.checkCoherence(this.state, nextState);

          if (!coherenceResult.isCoherent) {
            throw new Prime.CoherenceError(
              "State update failed coherence check",
              {
                context: {
                  componentId: this.id,
                  currentState: this.state,
                  updates,
                  issues: coherenceResult.issues,
                },
              },
            );
          }
        }

        // Update state with precise numerical handling
        this.state = this._applyPreciseUpdate(this.state, updates);

        // Record update time
        const updateTime = Date.now();
        metrics.updateTimes.push(updateTime);

        // Keep only the last 10 update times
        if (metrics.updateTimes.length > 10) {
          metrics.updateTimes.shift();
        }

        // Call updated hook if mounted
        if (this.isMounted && Prime.Utils.isFunction(hooks.updated)) {
          hooks.updated.call(this, { state: updates, type: "state" });
        }

        return true;
      } catch (error) {
        // Handle update errors
        if (Prime.Utils.isFunction(hooks.errorCaught)) {
          hooks.errorCaught.call(this, error, "updateState");
          return false;
        } else {
          throw error;
        }
      }
    },

    /**
     * Add a child component
     * @param {Object} child - Child component
     * @param {number} [index] - Index to insert at
     * @returns {boolean} Success
     */
    addChild: function (child, index) {
      if (!child || !child.id) {
        throw new Prime.ValidationError(
          "Child must be a valid component with an id",
          {
            context: { child },
          },
        );
      }

      // Check if child already exists
      const existingIndex = this.children.findIndex((c) => c.id === child.id);
      if (existingIndex !== -1) {
        return false;
      }

      // Insert child at specified index or append
      if (
        Prime.Utils.isNumber(index) &&
        index >= 0 &&
        index <= this.children.length
      ) {
        this.children.splice(index, 0, child);
      } else {
        this.children.push(child);
      }

      return true;
    },

    /**
     * Remove a child component
     * @param {string|Object} childId - Child ID or component
     * @returns {boolean} Success
     */
    removeChild: function (childId) {
      const id =
        typeof childId === "string"
          ? childId
          : childId && childId.id
            ? childId.id
            : null;

      if (!id) {
        return false;
      }

      const index = this.children.findIndex((c) => c.id === id);

      if (index === -1) {
        return false;
      }

      this.children.splice(index, 1);
      return true;
    },

    /**
     * Add an event handler
     * @param {string} eventType - Event type
     * @param {Function} handler - Event handler
     * @returns {Function} Function to remove the handler
     */
    on: function (eventType, handler) {
      if (!eventType || !Prime.Utils.isFunction(handler)) {
        throw new Prime.ValidationError(
          "Event type and handler function are required",
          {
            context: { eventType, handler },
          },
        );
      }

      // Initialize handlers array for this event type
      if (!eventHandlers.has(eventType)) {
        eventHandlers.set(eventType, []);
      }

      const handlers = eventHandlers.get(eventType);
      handlers.push(handler);

      // Return function to remove this handler
      return () => {
        const index = handlers.indexOf(handler);
        if (index !== -1) {
          handlers.splice(index, 1);
          return true;
        }
        return false;
      };
    },

    /**
     * Remove an event handler
     * @param {string} eventType - Event type
     * @param {Function} handler - Event handler
     * @returns {boolean} Success
     */
    off: function (eventType, handler) {
      if (!eventHandlers.has(eventType)) {
        return false;
      }

      const handlers = eventHandlers.get(eventType);
      const index = handlers.indexOf(handler);

      if (index === -1) {
        return false;
      }

      handlers.splice(index, 1);
      return true;
    },

    /**
     * Trigger an event
     * @param {string} eventType - Event type
     * @param {Object} eventData - Event data
     * @returns {Array} Handler results
     */
    trigger: function (eventType, eventData = {}) {
      if (!eventHandlers.has(eventType)) {
        return [];
      }

      const handlers = eventHandlers.get(eventType);
      const event = {
        type: eventType,
        timestamp: Date.now(),
        target: this,
        data: eventData,
      };

      const results = [];

      for (const handler of handlers) {
        try {
          results.push(handler.call(this, event));
        } catch (error) {
          if (Prime.Utils.isFunction(hooks.errorCaught)) {
            hooks.errorCaught.call(this, error, "eventHandler", {
              eventType,
              event,
            });
          } else {
            Prime.Logger.error(
              `Error in ${this.id} '${eventType}' event handler:`,
              error,
            );
          }
          results.push(null);
        }
      }

      return results;
    },

    /**
     * Render the component
     * @param {Object} [options] - Render options
     * @returns {Object|string} Rendered output
     */
    render: function (options = {}) {
      if (
        !Prime.Utils.isFunction(options.renderer) &&
        !Prime.Utils.isFunction(this.renderer)
      ) {
        throw new Prime.InvalidOperationError(
          `No renderer available for component ${this.id}`,
        );
      }

      const startTime = Date.now();

      try {
        const renderer = options.renderer || this.renderer;
        const format = options.format || "default";

        const renderCtx = {
          component: this,
          props: this.props,
          state: this.state,
          children: this.children,
          format,
          options,
        };

        const result = renderer.call(this, renderCtx);

        // Update metrics
        const endTime = Date.now();
        const duration = endTime - startTime;

        metrics.renderCount++;
        metrics.lastRenderDuration = duration;
        metrics.totalRenderTime = Prime.KahanSum(
          metrics.totalRenderTime,
          duration,
        );

        return result;
      } catch (error) {
        if (Prime.Utils.isFunction(hooks.errorCaught)) {
          hooks.errorCaught.call(this, error, "render", options);
          return null;
        } else {
          throw new Prime.RenderError(`Error rendering component ${this.id}`, {
            context: {
              componentId: this.id,
              options,
              error: error.message,
              stack: error.stack,
            },
            cause: error,
          });
        }
      }
    },

    /**
     * Get the component's metrics
     * @returns {Object} Component metrics
     */
    getMetrics: function () {
      return {
        id: this.id,
        renderCount: metrics.renderCount,
        lastRenderDuration: metrics.lastRenderDuration,
        averageRenderDuration:
          metrics.renderCount > 0
            ? metrics.totalRenderTime / metrics.renderCount
            : 0,
        mountTime: metrics.mountTime,
        childrenCount: this.children.length,
        eventTypes: Array.from(eventHandlers.keys()),
        totalEventHandlers: Array.from(eventHandlers.values()).reduce(
          (sum, handlers) => sum + handlers.length,
          0,
        ),
        updateCount: metrics.updateTimes.length,
      };
    },
  };

  // Set up custom renderer if provided
  if (Prime.Utils.isFunction(options.renderer)) {
    component.renderer = options.renderer;
  }

  return component;
}

module.exports = createComponent;
