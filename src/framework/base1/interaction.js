/**
 * PrimeOS JavaScript Library - Framework
 * Base 1 Interaction Model
 */

// Import core
const Prime = require('../../core.js');
const MathUtils = require('../math');

/**
 * Interaction Model - Manages state changes and data persistence
 */
const InteractionModel = {
  /**
   * Create an interaction model
   * @param {Object} config - Configuration object
   * @returns {Object} Interaction model
   */
  create: function (config = {}) {
    return {
      type: 'interaction',
      mutations: config.mutations || [],
      validators: config.validators || [],
      name: config.name || 'InteractionModel',

      /**
       * Apply a mutation to an object
       * @param {*} object - Object to mutate
       * @param {string} mutation - Mutation name
       * @param {*} [payload] - Mutation payload
       * @returns {*} Mutated object
       */
      mutate: function (object, mutation, payload) {
        const mutator = this.mutations.find((m) => m.name === mutation);

        if (!mutator) {
          throw new Prime.InvalidOperationError(
            `Mutation ${mutation} not found`,
            {
              context: {
                availableMutations: this.mutations.map((m) => m.name),
              },
            },
          );
        }

        let result;

        if (typeof mutator.apply === 'function') {
          result = mutator.apply(object, payload);
        } else if (typeof mutator === 'function') {
          result = mutator(object, payload);
        } else {
          throw new Prime.InvalidOperationError(`Invalid mutation ${mutation}`);
        }

        // Validate the result
        this.validate(result);

        // Publish event
        Prime.EventBus.publish('object:mutated', {
          original: object,
          mutation,
          payload,
          result,
        });

        return result;
      },

      /**
       * Save an object with improved state validation
       * @param {*} object - Object to save
       * @param {Object} [options] - Save options
       * @returns {boolean} Success
       */
      save: function (object, options = {}) {
        // Enhanced validation with detailed reporting
        const validationResult = this._validateWithDetails(object);

        // If validation fails and strict option is enabled (default), throw error
        if (!validationResult.valid && options.strict !== false) {
          throw new Prime.ValidationError('Object validation failed', {
            context: {
              failures: validationResult.failures,
              details: validationResult.details,
            },
          });
        }

        // Persist the object using configurable storage strategy
        const storage = options.storage || this._storage || {
          type: 'memory',
          data: this._storageData = (this._storageData || new Map())
        };

        // Additional metadata for the save operation
        const metadata = {
          timestamp: Date.now(),
          version: options.version || (object.version ? object.version + 1 : 1),
          validationResult: {
            valid: validationResult.valid,
            failures: validationResult.failures.length
          }
        };

        // Execute appropriate storage strategy
        if (storage.type === 'memory') {
          // In-memory storage implementation
          const id = options.id || object.id || Prime.Utils.uuid();

          // Create a versioned deep copy to prevent accidental mutations
          const storedObject = JSON.parse(JSON.stringify({
            ...object,
            id,
            _metadata: metadata
          }));

          // Store in the memory map
          storage.data.set(id, storedObject);

          // Update object with ID if it doesn't have one
          if (!object.id) {
            object.id = id;
          }

          Prime.Logger.info(`Object ${id} saved to memory storage`, {
            version: metadata.version,
            valid: validationResult.valid
          });
        } else if (storage.type === 'localStorage' && typeof window !== 'undefined') {
          // Browser localStorage implementation
          const id = options.id || object.id || Prime.Utils.uuid();

          try {
            const storageKey = `${this.name}_${id}`;
            const storedObject = {
              ...object,
              id,
              _metadata: metadata
            };

            window.localStorage.setItem(storageKey, JSON.stringify(storedObject));

            // Update object with ID if it doesn't have one
            if (!object.id) {
              object.id = id;
            }

            Prime.Logger.info(`Object ${id} saved to localStorage`, {
              key: storageKey,
              version: metadata.version
            });
          } catch (error) {
            Prime.Logger.error(`Failed to save object to localStorage: ${error.message}`);
            throw new Prime.StorageError('Failed to save to localStorage', {
              context: { error: error.message }
            });
          }
        } else if (storage.type === 'custom' && typeof storage.save === 'function') {
          // Custom storage implementation
          try {
            storage.save(object, metadata, options);
            Prime.Logger.info('Object saved to custom storage', {
              storageId: storage.id || 'unknown',
              valid: validationResult.valid
            });
          } catch (error) {
            Prime.Logger.error(`Failed to save object to custom storage: ${error.message}`);
            throw new Prime.StorageError('Failed to save to custom storage', {
              context: { error: error.message, storage: storage.id || 'unknown' }
            });
          }
        } else {
          Prime.Logger.warn(`Unsupported storage type: ${storage.type}`, {
            fallback: 'event-only'
          });
        }

        // Publish event with storage information
        Prime.EventBus.publish('object:saved', {
          object,
          id: object.id,
          validationResult,
          storage: storage.type,
          metadata
        });

        return validationResult.valid;
      },

      /**
       * Validate an object with enhanced error reporting
       * @param {*} object - Object to validate
       * @returns {boolean} Validation result
       * @throws {ValidationError} If validation fails
       */
      validate: function (object) {
        const validationResult = this._validateWithDetails(object);

        if (!validationResult.valid) {
          throw new Prime.ValidationError('Object validation failed', {
            context: {
              failures: validationResult.failures,
              details: validationResult.details,
            },
          });
        }

        return true;
      },

      /**
       * Enhanced validation with detailed reporting
       * @private
       * @param {*} object - Object to validate
       * @returns {Object} Detailed validation result
       */
      _validateWithDetails: function (object) {
        const failures = [];
        const details = {};

        for (const validator of this.validators) {
          try {
            let valid = false;
            const validatorName = validator.name || 'anonymous validator';

            if (typeof validator === 'function') {
              valid = validator(object);
            } else if (validator && typeof validator.validate === 'function') {
              valid = validator.validate(object);
            } else {
              throw new Prime.InvalidOperationError('Invalid validator');
            }

            if (!valid) {
              failures.push(validatorName);

              // Capture additional context if available
              if (
                validator.getDetails &&
                typeof validator.getDetails === 'function'
              ) {
                details[validatorName] = validator.getDetails(object);
              }
            }
          } catch (error) {
            const validatorName = validator.name || 'anonymous validator';
            failures.push(`Error in ${validatorName}: ${error.message}`);
            details[validatorName] = {
              error: error.message,
              stack: error.stack,
            };
          }
        }

        return {
          valid: failures.length === 0,
          failures,
          details,
        };
      },

      /**
       * Add a mutation
       * @param {Object|Function} mutation - Mutation to add
       * @returns {Object} Updated interaction model
       */
      addMutation: function (mutation) {
        if (!mutation.name && typeof mutation !== 'function') {
          throw new Prime.ValidationError(
            'Mutation must have a name property or be a function',
          );
        }

        this.mutations.push(mutation);
        return this;
      },

      /**
       * Add a validator
       * @param {Object|Function} validator - Validator to add
       * @returns {Object} Updated interaction model
       */
      addValidator: function (validator) {
        this.validators.push(validator);
        return this;
      },

      /**
       * Perform deep merge of objects with enhanced numerical handling
       * @param {Object} target - Target object
       * @param {Object} source - Source object
       * @param {Object} [options] - Merge options
       * @returns {Object} Merged result
       */
      deepMerge: function (target, source, options = {}) {
        // Set default options
        const mergeArrays = options.mergeArrays !== false;
        const maxDepth = options.maxDepth || 10;

        // Helper function to check if a value is a plain object
        const isPlainObject = (value) => {
          return (
            value !== null &&
            typeof value === 'object' &&
            Object.prototype.toString.call(value) === '[object Object]'
          );
        };

        // Track visited objects to avoid circular references
        const visited = new WeakMap();

        // Recursive deep merge with depth tracking
        const merge = (target, source, depth = 0) => {
          // Check for circular references
          if (visited.has(source)) {
            return visited.get(source);
          }

          // Create fresh copy of target to avoid modifying the original
          const result = Array.isArray(target) ? [...target] : { ...target };

          // Store result to handle circular references
          visited.set(source, result);

          // Skip further merging if max depth is reached
          if (depth >= maxDepth) {
            return result;
          }

          // Define property merging behavior for different types
          if (Array.isArray(result) && Array.isArray(source)) {
            if (mergeArrays) {
              // Merge arrays by extending and overwriting existing elements
              source.forEach((item, index) => {
                if (index < result.length) {
                  // For existing positions, recursively merge objects
                  if (isPlainObject(item) && isPlainObject(result[index])) {
                    result[index] = merge(result[index], item, depth + 1);
                  } else {
                    // For non-objects, simply overwrite
                    result[index] = item;
                  }
                } else {
                  // For new positions, append
                  result.push(item);
                }
              });
            } else {
              // Replace entire array
              return source;
            }
          } else if (isPlainObject(result) && isPlainObject(source)) {
            // Process each property in source
            for (const key in source) {
              // Skip if property doesn't exist in source
              if (!Object.prototype.hasOwnProperty.call(source, key)) {
                continue;
              }

              const sourceValue = source[key];

              // Handle special numerical values with extra precision
              if (typeof sourceValue === 'number') {
                if (!Number.isFinite(sourceValue)) {
                  Prime.Logger.warn(
                    `Non-finite number detected during merge: ${key}=${sourceValue}`,
                  );
                }

                // Always overwrite numerical values
                result[key] = sourceValue;
                continue;
              }

              // For nested objects, merge recursively
              if (isPlainObject(sourceValue)) {
                if (isPlainObject(result[key])) {
                  result[key] = merge(result[key], sourceValue, depth + 1);
                } else {
                  // If target property is not an object, replace with source value
                  result[key] = merge({}, sourceValue, depth + 1);
                }
              }
              // For arrays, handle according to mergeArrays option
              else if (Array.isArray(sourceValue)) {
                if (Array.isArray(result[key]) && mergeArrays) {
                  result[key] = merge(result[key], sourceValue, depth + 1);
                } else {
                  // Create a deep copy of the array to avoid reference issues
                  result[key] = Array.isArray(sourceValue)
                    ? sourceValue.map((item) =>
                      isPlainObject(item) ? merge({}, item, depth + 1) : item,
                    )
                    : sourceValue;
                }
              }
              // For primitive values, simply copy
              else {
                result[key] = sourceValue;
              }
            }
          }

          return result;
        };

        return merge(target, source);
      },

      /**
       * Connect to Base 0 components
       * @param {Object} base0 - Base 0 components
       * @returns {Object} Connected interaction model
       */
      connectToBase0: function (base0) {
        this._base0 = base0;
        return this;
      },
    };
  },
};

module.exports = InteractionModel;
