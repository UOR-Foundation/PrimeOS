/**
 * PrimeOS JavaScript Library - Framework
 * Base 1 Runtime Model
 */

// Import core
const Prime = require("../../core/prime.js");
const MathUtils = require("../math");

/**
 * Runtime Model - Manages model execution lifecycle
 */
const RuntimeModel = {
  /**
   * Create a runtime model
   * @param {Object} config - Configuration object
   * @returns {Object} Runtime model
   */
  create: function (config = {}) {
    return {
      type: "runtime",
      embedding: config.embedding,
      logic: config.logic,
      representation: config.representation,
      processor: config.processor,
      name: config.name || "RuntimeModel",

      // Track performance and resource statistics
      _stats: {
        modelStarts: 0,
        modelRuns: 0,
        modelStops: 0,
        avgRunTime: 0,
        peakMemoryUsage: 0,
        errorCount: 0,
      },

      /**
       * Start a model
       * @param {Object} model - Model to start
       * @returns {Object} Started model
       */
      start: function (model) {
        if (!model) {
          throw new Prime.ValidationError("Model is required");
        }

        // Initialize the model
        if (typeof model.initialize === "function") {
          model.initialize();
        }

        // Set the model's status to running
        model._running = true;
        model._startTime = Date.now();

        // Track statistics
        this._stats.modelStarts++;

        // Publish event
        Prime.EventBus.publish("model:started", { model });

        return model;
      },

      /**
       * Run a model with input
       * @param {Object} model - Model to run
       * @param {*} input - Input data
       * @returns {*} Model output
       */
      run: function (model, input) {
        if (!model) {
          throw new Prime.ValidationError("Model is required");
        }

        if (!model._running) {
          throw new Prime.InvalidOperationError("Model is not running", {
            context: { model: model.name || "unnamed" },
          });
        }

        // Track performance
        const startTime = performance.now();
        let error = null;

        try {
          // Process input through the model's pipeline
          let data = input;

          // 1. Embed the input if embedding is available
          if (this.embedding && model.useEmbedding !== false) {
            data = this.embedding.embed(data);
          }

          // 2. Apply logic if available
          if (this.logic && model.useLogic !== false) {
            data = this.logic.apply(data);
          }

          // 3. Process with the model's own function
          if (typeof model.process === "function") {
            data = model.process(data);
          } else if (typeof model === "function") {
            data = model(data);
          }

          // 4. Represent the output if representation is available
          if (
            this.representation &&
            model.useRepresentation !== false &&
            model.outputFormat
          ) {
            data = this.representation.represent(data, model.outputFormat);
          }

          // Track run time with exponential moving average
          const runTime = performance.now() - startTime;
          this._updateRunningStats(runTime);

          // Publish event
          Prime.EventBus.publish("model:ran", {
            model,
            input,
            output: data,
            runTime,
          });

          return data;
        } catch (err) {
          // Track error
          this._stats.errorCount++;
          error = err;

          // Log error and rethrow
          Prime.Logger.error("Error running model:", err);
          throw err;
        } finally {
          // Calculate memory usage for statistics (if available)
          if (typeof process !== "undefined" && process.memoryUsage) {
            const memUsage = process.memoryUsage().heapUsed;
            this._stats.peakMemoryUsage = Math.max(
              this._stats.peakMemoryUsage,
              memUsage,
            );
          }

          // Always publish completion event for monitoring purposes
          Prime.EventBus.publish("model:completed", {
            model,
            success: !error,
            runTime: performance.now() - startTime,
            error: error ? error.message : null,
          });
        }
      },

      /**
       * Stop a model
       * @param {Object} model - Model to stop
       * @returns {boolean} Success
       */
      stop: function (model) {
        if (!model) {
          throw new Prime.ValidationError("Model is required");
        }

        // Set the model's status to not running
        model._running = false;

        // Calculate total run time if possible
        if (model._startTime) {
          model._totalRunTime = Date.now() - model._startTime;
        }

        // Track statistics
        this._stats.modelStops++;

        // Clean up resources if necessary
        if (typeof model.cleanup === "function") {
          model.cleanup();
        }

        // Publish event
        Prime.EventBus.publish("model:stopped", { model });

        return true;
      },

      /**
       * Update running statistics with new performance data
       * Uses exponential moving average for stable tracking
       * @private
       * @param {number} runTime - Time taken to run the model
       */
      _updateRunningStats: function (runTime) {
        this._stats.modelRuns++;

        // Use exponential moving average with alpha=0.1
        const alpha = 0.1;
        this._stats.avgRunTime =
          alpha * runTime + (1 - alpha) * (this._stats.avgRunTime || runTime);
      },

      /**
       * Get runtime statistics
       * @returns {Object} Runtime statistics
       */
      getStats: function () {
        return {
          ...this._stats,
          uptime: model._startTime ? Date.now() - model._startTime : 0,
        };
      },

      /**
       * Connect to Base 0 components
       * @param {Object} base0 - Base 0 components
       * @returns {Object} Connected runtime model
       */
      connectToBase0: function (base0) {
        this.embedding = base0.embedding;
        this.logic = base0.logic;
        this.representation = base0.representation;
        this.processor = base0.processor;

        return this;
      },
    };
  },
};

module.exports = RuntimeModel;
