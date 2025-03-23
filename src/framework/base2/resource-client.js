/**
 * PrimeOS JavaScript Library - Framework
 * Base 2 Resource Client
 */

// Import core
const Prime = require("../../core/prime.js");
const MathUtils = require("../math");

/**
 * Resource Client - Interface to Base 1 Resources
 */
const ResourceClient = {
  /**
   * Create a resource client
   * @param {Object} config - Configuration object
   * @returns {Object} Resource client
   */
  create: function (config = {}) {
    return {
      type: "resourceClient",
      runtime: config.runtime,
      observation: config.observation,
      interaction: config.interaction,
      representation: config.representation,
      name: config.name || "ResourceClient",

      // Cache for performance optimization
      _cache: {
        fetchResults: new Map(),
        presentationResults: new Map(),
      },

      // Performance metrics
      _metrics: {
        startCalls: 0,
        runCalls: 0,
        stopCalls: 0,
        fetchCalls: 0,
        mutateCalls: 0,
        saveCalls: 0,
        presentCalls: 0,
        renderCalls: 0,
        cacheHits: 0,
        cacheMisses: 0,
        errors: 0,
      },

      /**
       * Get the runtime model
       * @returns {Object} Runtime model
       */
      getRuntime: function () {
        return this.runtime;
      },

      /**
       * Get the observation model
       * @returns {Object} Observation model
       */
      getObservation: function () {
        return this.observation;
      },

      /**
       * Get the interaction model
       * @returns {Object} Interaction model
       */
      getInteraction: function () {
        return this.interaction;
      },

      /**
       * Get the representation model
       * @returns {Object} Representation model
       */
      getRepresentation: function () {
        return this.representation;
      },

      /**
       * Start a model with enhanced error handling
       * @param {Object} model - Model to start
       * @returns {Object} Started model
       */
      startModel: function (model) {
        try {
          this._metrics.startCalls++;
          return this.runtime.start(model);
        } catch (error) {
          this._metrics.errors++;
          Prime.Logger.error(`Error starting model:`, error);
          throw error;
        }
      },

      /**
       * Run a model with enhanced validation and caching
       * @param {Object} model - Model to run
       * @param {*} input - Input data
       * @param {Object} [options] - Run options
       * @returns {*} Model output
       */
      runModel: function (model, input, options = {}) {
        // Input validation with detailed error messages
        if (!model) {
          throw new Prime.ValidationError(
            "Model is required for runModel operation",
          );
        }

        // Record metrics
        this._metrics.runCalls++;

        // Check if caching is enabled and if we have a cached result
        const enableCaching =
          options.cache !== false && model.cacheable !== false;
        const cacheKey = enableCaching ? this._getCacheKey(model, input) : null;

        if (
          enableCaching &&
          this._cache.modelRuns &&
          this._cache.modelRuns.has(cacheKey)
        ) {
          this._metrics.cacheHits++;
          return this._cache.modelRuns.get(cacheKey);
        }

        this._metrics.cacheMisses++;

        try {
          // Run the model through the runtime
          const result = this.runtime.run(model, input);

          // Cache the result if caching is enabled
          if (enableCaching) {
            // Initialize cache if needed
            this._cache.modelRuns = this._cache.modelRuns || new Map();
            this._cache.modelRuns.set(cacheKey, result);

            // Set expiration if TTL is specified
            if (options.cacheTtl) {
              setTimeout(() => {
                this._cache.modelRuns.delete(cacheKey);
              }, options.cacheTtl);
            }
          }

          return result;
        } catch (error) {
          this._metrics.errors++;
          Prime.Logger.error(`Error running model:`, error);
          throw error;
        }
      },

      /**
       * Stop a model
       * @param {Object} model - Model to stop
       * @returns {boolean} Success
       */
      stopModel: function (model) {
        try {
          this._metrics.stopCalls++;
          return this.runtime.stop(model);
        } catch (error) {
          this._metrics.errors++;
          Prime.Logger.error(`Error stopping model:`, error);
          throw error;
        }
      },

      /**
       * Fetch data with caching and enhanced error handling
       * @param {Object} query - Query to execute
       * @param {Object} [options] - Fetch options
       * @returns {Array} Matching data
       */
      fetchData: function (query, options = {}) {
        // Input validation
        if (!query) {
          return [];
        }

        // Record metrics
        this._metrics.fetchCalls++;

        // Check if caching is enabled and if we have a cached result
        const enableCaching = options.cache !== false;
        const cacheKey = enableCaching
          ? JSON.stringify({
              query,
              options: {
                limit: options.limit,
                offset: options.offset,
                sort: options.sort,
              },
            })
          : null;

        if (enableCaching && this._cache.fetchResults.has(cacheKey)) {
          const cached = this._cache.fetchResults.get(cacheKey);
          // Check if cached result is still valid
          if (!cached.expiry || cached.expiry > Date.now()) {
            this._metrics.cacheHits++;
            return cached.data;
          }
          // Remove expired entry
          this._cache.fetchResults.delete(cacheKey);
        }

        this._metrics.cacheMisses++;

        try {
          // Fetch from observation model
          const result = this.observation.fetch(query, options);

          // Cache the result if caching is enabled
          if (enableCaching) {
            const expiry = options.cacheTtl
              ? Date.now() + options.cacheTtl
              : null;
            this._cache.fetchResults.set(cacheKey, {
              data: result,
              expiry,
            });
          }

          return result;
        } catch (error) {
          this._metrics.errors++;
          Prime.Logger.error(`Error fetching data:`, error);
          throw error;
        }
      },

      /**
       * Mutate an object
       * @param {*} object - Object to mutate
       * @param {string} mutation - Mutation name
       * @param {*} [payload] - Mutation payload
       * @returns {*} Mutated object
       */
      mutateObject: function (object, mutation, payload) {
        try {
          this._metrics.mutateCalls++;
          const result = this.interaction.mutate(object, mutation, payload);
          // Invalidate cache entries that might depend on this object
          this._invalidateRelatedCache(object);
          return result;
        } catch (error) {
          this._metrics.errors++;
          Prime.Logger.error(`Error mutating object:`, error);
          throw error;
        }
      },

      /**
       * Save an object
       * @param {*} object - Object to save
       * @param {Object} [options] - Save options
       * @returns {boolean} Success
       */
      saveObject: function (object, options = {}) {
        try {
          this._metrics.saveCalls++;
          const result = this.interaction.save(object, options);
          // Invalidate cache entries that might depend on this object
          this._invalidateRelatedCache(object);
          return result;
        } catch (error) {
          this._metrics.errors++;
          Prime.Logger.error(`Error saving object:`, error);
          throw error;
        }
      },

      /**
       * Present an object with caching
       * @param {*} object - Object to present
       * @param {string} format - Format name
       * @param {Object} [options] - Presentation options
       * @returns {*} Presented object
       */
      presentObject: function (object, format, options = {}) {
        // Record metrics
        this._metrics.presentCalls++;

        // Check if caching is enabled and if we have a cached result
        const enableCaching = options.cache !== false;
        let cacheKey = null;

        if (enableCaching) {
          try {
            // For primitives and simple objects, we can create a cache key
            if (
              object === null ||
              object === undefined ||
              typeof object !== "object" ||
              (Array.isArray(object) && object.length < 100)
            ) {
              cacheKey = JSON.stringify({
                object,
                format,
                options: { maxDepth: options.maxDepth },
              });

              if (this._cache.presentationResults.has(cacheKey)) {
                this._metrics.cacheHits++;
                return this._cache.presentationResults.get(cacheKey);
              }
            }
          } catch (e) {
            // If stringification fails, we can't cache this object
            cacheKey = null;
          }
        }

        this._metrics.cacheMisses++;

        try {
          // Present using representation model
          const result = this.representation.present(object, format, options);

          // Cache the result if possible
          if (cacheKey) {
            this._cache.presentationResults.set(cacheKey, result);

            // Set expiration if TTL is specified
            if (options.cacheTtl) {
              setTimeout(() => {
                this._cache.presentationResults.delete(cacheKey);
              }, options.cacheTtl);
            }
          }

          return result;
        } catch (error) {
          this._metrics.errors++;
          Prime.Logger.error(`Error presenting object:`, error);
          throw error;
        }
      },

      /**
       * Render an object
       * @param {*} object - Object to render
       * @param {*} target - Render target
       * @returns {*} Render result
       */
      renderObject: function (object, target) {
        try {
          this._metrics.renderCalls++;
          return this.representation.render(object, target);
        } catch (error) {
          this._metrics.errors++;
          Prime.Logger.error(`Error rendering object:`, error);
          throw error;
        }
      },

      /**
       * Clear all caches
       */
      clearCache: function () {
        this._cache.fetchResults.clear();
        this._cache.presentationResults.clear();
        if (this._cache.modelRuns) {
          this._cache.modelRuns.clear();
        }

        Prime.Logger.info("Resource client cache cleared");
      },

      /**
       * Get performance metrics
       * @returns {Object} Performance metrics
       */
      getMetrics: function () {
        return { ...this._metrics };
      },

      /**
       * Generate cache key for model runs
       * @private
       * @param {Object} model - Model being run
       * @param {*} input - Model input
       * @returns {string} Cache key
       */
      _getCacheKey: function (model, input) {
        try {
          const modelId = model.id || model.name || JSON.stringify(model);
          return `${modelId}:${JSON.stringify(input)}`;
        } catch (e) {
          // If JSON stringify fails, use a fallback approach
          return `${model.id || model.name || "model"}:${typeof input}:${Date.now()}`;
        }
      },

      /**
       * Invalidate cache entries related to an object
       * @private
       * @param {Object} object - Object that was changed
       */
      _invalidateRelatedCache: function (object) {
        // Simple implementation - clear fetch cache
        // In a more sophisticated implementation, would only clear related entries
        this._cache.fetchResults.clear();

        // If the object has an ID, try to selectively invalidate presentation cache
        if (object && object.id) {
          for (const [
            key,
            value,
          ] of this._cache.presentationResults.entries()) {
            if (
              key.includes(`"id":"${object.id}"`) ||
              key.includes(`"_id":"${object.id}"`)
            ) {
              this._cache.presentationResults.delete(key);
            }
          }
        }
      },
    };
  },
};

module.exports = ResourceClient;
