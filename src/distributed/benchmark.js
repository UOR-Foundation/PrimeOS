/**
 * PrimeOS JavaScript Library - Distributed Computation Benchmarking
 * Performance measurement for distributed neural networks
 */

// Import the Prime object from core
const Prime = require('../core');
const EventBus = require('./event-bus');

// Create the Benchmark module using IIFE
(function () {
  /**
   * Benchmark types for distributed computation
   * @enum {string}
   */
  const BenchmarkType = {
    /** Network communication benchmarks */
    COMMUNICATION: 'communication',
    /** Neural computation benchmarks */
    COMPUTATION: 'computation',
    /** Cluster operation benchmarks */
    CLUSTER: 'cluster',
    /** Data partitioning benchmarks */
    PARTITIONING: 'partitioning',
    /** End-to-end system benchmarks */
    SYSTEM: 'system',
  };

  /**
   * Benchmarking suite for distributed computation
   * Measures performance of distributed neural network operations
   */
  class BenchmarkSuite {
    /**
     * Create a new benchmark suite
     * @param {Object} config - Benchmark configuration
     * @param {string} config.id - Unique identifier
     * @param {Object} [config.options={}] - Benchmark options
     */
    constructor(config) {
      if (!Prime.Utils.isObject(config)) {
        throw new Prime.ValidationError(
          'Benchmark configuration must be an object',
        );
      }

      if (!config.id) {
        throw new Prime.ValidationError('Benchmark ID is required');
      }

      this.id = config.id;
      this.options = {
        iterations: config.options?.iterations || 10,
        warmupIterations: config.options?.warmupIterations || 2,
        reportProgress: config.options?.reportProgress !== false,
        captureMemory: config.options?.captureMemory !== false,
        saveResults: config.options?.saveResults !== false,
        nodeCounts: config.options?.nodeCounts || [1, 2, 4, 8],
      };

      // Benchmark registrations
      this.benchmarks = new Map();

      // Results
      this.results = new Map();

      // Event bus for benchmark events
      this.eventBus = new EventBus();

      Prime.Logger.info(`Created benchmark suite ${this.id}`);
    }

    /**
     * Register a benchmark test
     * @param {string} name - Benchmark name
     * @param {Function} benchmarkFn - Benchmark function to run
     * @param {Object} [metadata={}] - Benchmark metadata
     * @returns {BenchmarkSuite} this (for chaining)
     */
    register(name, benchmarkFn, metadata = {}) {
      if (typeof benchmarkFn !== 'function') {
        throw new Prime.ValidationError('Benchmark function is required');
      }

      this.benchmarks.set(name, {
        name,
        fn: benchmarkFn,
        type: metadata.type || BenchmarkType.COMPUTATION,
        description: metadata.description || '',
        tags: metadata.tags || [],
      });

      return this;
    }

    /**
     * Run a specific benchmark
     * @param {string} name - Benchmark name to run
     * @param {Object} [options={}] - Run options (overrides suite options)
     * @returns {Promise<Object>} Benchmark results
     */
    async runBenchmark(name, options = {}) {
      const benchmark = this.benchmarks.get(name);

      if (!benchmark) {
        throw new Prime.ValidationError(`Benchmark ${name} not found`);
      }

      // Merge options
      const runOptions = { ...this.options, ...options };

      Prime.Logger.info(`Running benchmark ${name}`, {
        iterations: runOptions.iterations,
        warmup: runOptions.warmupIterations,
      });

      // Emit start event
      this.eventBus.emit('benchmark:start', {
        name,
        options: runOptions,
        timestamp: Date.now(),
      });

      // Run warmup iterations
      if (runOptions.warmupIterations > 0) {
        for (let i = 0; i < runOptions.warmupIterations; i++) {
          await benchmark.fn({ iteration: i, warmup: true });
        }
      }

      // Run actual benchmark iterations
      const iterationResults = [];
      const startTime = performance.now();

      for (let i = 0; i < runOptions.iterations; i++) {
        // Capture memory before run if requested
        const memoryBefore = runOptions.captureMemory
          ? process.memoryUsage()
          : null;

        // Run benchmark iteration
        const iterStartTime = performance.now();
        const iterationResult = await benchmark.fn({
          iteration: i,
          warmup: false,
          options: runOptions,
        });
        const iterEndTime = performance.now();

        // Capture memory after run
        const memoryAfter = runOptions.captureMemory
          ? process.memoryUsage()
          : null;

        // Calculate metrics
        const duration = iterEndTime - iterStartTime;
        let memoryDelta = null;

        if (memoryBefore && memoryAfter) {
          memoryDelta = {
            rss: memoryAfter.rss - memoryBefore.rss,
            heapTotal: memoryAfter.heapTotal - memoryBefore.heapTotal,
            heapUsed: memoryAfter.heapUsed - memoryBefore.heapUsed,
            external: memoryAfter.external - memoryBefore.external,
          };
        }

        // Store iteration result
        iterationResults.push({
          iteration: i,
          duration,
          timestamp: Date.now(),
          memory: memoryDelta,
          result: iterationResult,
        });

        // Report progress if requested
        if (runOptions.reportProgress) {
          this.eventBus.emit('benchmark:progress', {
            name,
            iteration: i,
            totalIterations: runOptions.iterations,
            duration,
            result: iterationResult,
          });

          if (i > 0 && i % 5 === 0) {
            Prime.Logger.info(
              `Benchmark ${name} progress: ${i}/${runOptions.iterations}`,
            );
          }
        }
      }

      const endTime = performance.now();

      // Calculate benchmark statistics
      const totalDuration = endTime - startTime;
      const durations = iterationResults.map((r) => r.duration);

      const stats = {
        mean: this._calculateMean(durations),
        median: this._calculateMedian(durations),
        min: Math.min(...durations),
        max: Math.max(...durations),
        stdDev: this._calculateStdDev(durations),
        total: totalDuration,
        iterations: runOptions.iterations,
        opsPerSecond: (runOptions.iterations / totalDuration) * 1000,
      };

      // Memory statistics if available
      if (runOptions.captureMemory) {
        const rssDeltas = iterationResults
          .filter((r) => r.memory)
          .map((r) => r.memory.rss);

        const heapUsedDeltas = iterationResults
          .filter((r) => r.memory)
          .map((r) => r.memory.heapUsed);

        stats.memory = {
          meanRss: this._calculateMean(rssDeltas),
          medianRss: this._calculateMedian(rssDeltas),
          meanHeapUsed: this._calculateMean(heapUsedDeltas),
          medianHeapUsed: this._calculateMedian(heapUsedDeltas),
        };
      }

      // Create result object
      const result = {
        name,
        type: benchmark.type,
        description: benchmark.description,
        options: runOptions,
        stats,
        iterationResults,
        timestamp: Date.now(),
      };

      // Store results
      this.results.set(name, result);

      // Emit completion event
      this.eventBus.emit('benchmark:complete', {
        name,
        stats,
        timestamp: Date.now(),
      });

      Prime.Logger.info(`Benchmark ${name} completed`, {
        mean: stats.mean.toFixed(2) + 'ms',
        median: stats.median.toFixed(2) + 'ms',
        opsPerSecond: stats.opsPerSecond.toFixed(2),
      });

      // Save results if requested
      if (runOptions.saveResults) {
        this._saveResults(name, result);
      }

      return result;
    }

    /**
     * Run all registered benchmarks
     * @param {Object} [options={}] - Run options (overrides suite options)
     * @returns {Promise<Map<string, Object>>} All benchmark results
     */
    async runAll(options = {}) {
      const benchmarkNames = Array.from(this.benchmarks.keys());

      if (benchmarkNames.length === 0) {
        Prime.Logger.warn('No benchmarks registered');
        return new Map();
      }

      Prime.Logger.info(`Running all ${benchmarkNames.length} benchmarks`);

      // Emit start all event
      this.eventBus.emit('benchmarks:start', {
        count: benchmarkNames.length,
        names: benchmarkNames,
        timestamp: Date.now(),
      });

      // Run all benchmarks sequentially
      for (const name of benchmarkNames) {
        await this.runBenchmark(name, options);
      }

      // Emit completion event
      this.eventBus.emit('benchmarks:complete', {
        count: benchmarkNames.length,
        timestamp: Date.now(),
      });

      return this.results;
    }

    /**
     * Calculate scaling performance across different node counts
     * @param {string} benchmarkName - Base benchmark name
     * @param {Object} [options={}] - Scaling options
     * @returns {Promise<Object>} Scaling benchmark results
     */
    async measureScaling(benchmarkName, options = {}) {
      const benchmark = this.benchmarks.get(benchmarkName);

      if (!benchmark) {
        throw new Prime.ValidationError(`Benchmark ${benchmarkName} not found`);
      }

      // Merge options
      const scalingOptions = {
        ...this.options,
        ...options,
        nodeCounts: options.nodeCounts || this.options.nodeCounts,
      };

      Prime.Logger.info(`Measuring scaling for ${benchmarkName}`, {
        nodeCounts: scalingOptions.nodeCounts,
      });

      // Results for each node count
      const nodeResults = [];

      // Run benchmark for each node count
      for (const nodeCount of scalingOptions.nodeCounts) {
        const nodeOptions = {
          ...scalingOptions,
          nodeCount,
        };

        // Create unique name for this run
        const runName = `${benchmarkName}_nodes${nodeCount}`;

        // Register temporary benchmark for this run
        this.register(
          runName,
          async (runContext) => {
            // Call original benchmark with node count
            return benchmark.fn({
              ...runContext,
              nodeCount,
            });
          },
          {
            type: benchmark.type,
            description: `${benchmark.description} with ${nodeCount} nodes`,
            tags: [...benchmark.tags, 'scaling', `nodes-${nodeCount}`],
          },
        );

        // Run the benchmark
        const result = await this.runBenchmark(runName, nodeOptions);

        // Store result
        nodeResults.push({
          nodeCount,
          result,
        });

        // Unregister temporary benchmark
        this.benchmarks.delete(runName);
      }

      // Calculate scaling efficiency
      const baseResult = nodeResults.find(
        (r) => r.nodeCount === Math.min(...scalingOptions.nodeCounts),
      );

      if (!baseResult) {
        throw new Error('No base result found for scaling calculation');
      }

      const baseMean = baseResult.result.stats.mean;
      const baseNodeCount = baseResult.nodeCount;

      for (const nodeResult of nodeResults) {
        const scalingEfficiency =
          (baseMean * baseNodeCount) /
          (nodeResult.result.stats.mean * nodeResult.nodeCount);

        nodeResult.scalingEfficiency = scalingEfficiency;
        nodeResult.speedup = baseMean / nodeResult.result.stats.mean;
      }

      // Create scaling result
      const scalingResult = {
        name: `${benchmarkName}_scaling`,
        type: BenchmarkType.SYSTEM,
        description: `Scaling measurements for ${benchmarkName}`,
        nodeCounts: scalingOptions.nodeCounts,
        results: nodeResults,
        optimalNodeCount: this._findOptimalNodeCount(nodeResults),
        timestamp: Date.now(),
      };

      // Store result
      this.results.set(`${benchmarkName}_scaling`, scalingResult);

      Prime.Logger.info(`Scaling measurement for ${benchmarkName} completed`, {
        nodeCounts: scalingOptions.nodeCounts,
        optimalNodeCount: scalingResult.optimalNodeCount,
      });

      return scalingResult;
    }

    /**
     * Find the optimal node count based on efficiency
     * @private
     * @param {Array<Object>} nodeResults - Results for each node count
     * @returns {number} Optimal node count
     */
    _findOptimalNodeCount(nodeResults) {
      if (!nodeResults || nodeResults.length === 0) {
        return 1;
      }

      // Find node count with best efficiency vs performance tradeoff
      // We use a combined metric of speedup * efficiency^2
      let bestNodeCount = 1;
      let bestMetric = 0;

      for (const result of nodeResults) {
        const metric = result.speedup * Math.pow(result.scalingEfficiency, 2);

        if (metric > bestMetric) {
          bestMetric = metric;
          bestNodeCount = result.nodeCount;
        }
      }

      return bestNodeCount;
    }

    /**
     * Save benchmark results
     * @private
     * @param {string} name - Benchmark name
     * @param {Object} result - Benchmark result
     */
    _saveResults(name, result) {
      // Save results to persistent storage
      try {
        // Create results storage object if doesn't exist
        this._resultsStorage = this._resultsStorage || {};

        // Ensure we have an entry for this benchmark
        this._resultsStorage[name] = this._resultsStorage[name] || [];

        // Add result with timestamp
        const storageResult = {
          ...result,
          saved: true,
          saveTimestamp: Date.now()
        };

        // Limit to last 100 results per benchmark to avoid memory issues
        this._resultsStorage[name].push(storageResult);
        if (this._resultsStorage[name].length > 100) {
          this._resultsStorage[name].shift();
        }

        // Log success
        Prime.Logger.debug(`Benchmark results for ${name} saved to storage`);

        // Emit storage event
        this.eventBus.emit('benchmark:stored', {
          name,
          timestamp: Date.now(),
          resultCount: this._resultsStorage[name].length
        });

        // For a proper implementation with file storage, we would do:
        // 1. Convert result to string (JSON.stringify)
        // 2. Write to file system using Node's fs module
        // 3. Implement file rotation and compression for large benchmarks
        // 4. Support optional database backends (SQLite, etc.)
      } catch (error) {
        Prime.Logger.error(`Error saving benchmark results for ${name}`, {
          error: error.message
        });
      }
    }

    /**
     * Calculate mean of an array of numbers
     * @private
     * @param {Array<number>} values - Values to calculate mean for
     * @returns {number} Mean value
     */
    _calculateMean(values) {
      if (!values || values.length === 0) {
        return 0;
      }
      return values.reduce((sum, val) => sum + val, 0) / values.length;
    }

    /**
     * Calculate median of an array of numbers
     * @private
     * @param {Array<number>} values - Values to calculate median for
     * @returns {number} Median value
     */
    _calculateMedian(values) {
      if (!values || values.length === 0) {
        return 0;
      }

      const sorted = [...values].sort((a, b) => a - b);
      const middle = Math.floor(sorted.length / 2);

      if (sorted.length % 2 === 0) {
        return (sorted[middle - 1] + sorted[middle]) / 2;
      }

      return sorted[middle];
    }

    /**
     * Calculate standard deviation of an array of numbers
     * @private
     * @param {Array<number>} values - Values to calculate std dev for
     * @returns {number} Standard deviation
     */
    _calculateStdDev(values) {
      if (!values || values.length <= 1) {
        return 0;
      }

      const mean = this._calculateMean(values);
      const variance =
        values.reduce((sum, val) => {
          return sum + Math.pow(val - mean, 2);
        }, 0) /
        (values.length - 1);

      return Math.sqrt(variance);
    }

    /**
     * Generate benchmark report
     * @param {Object} [options={}] - Report options
     * @returns {Object} Benchmark report
     */
    generateReport(options = {}) {
      const reportOptions = {
        format: options.format || 'json',
        includeIterations: options.includeIterations !== false,
        sortBy: options.sortBy || 'name',
      };

      // Prepare result data
      const resultEntries = Array.from(this.results.entries());

      // Sort results
      if (reportOptions.sortBy === 'name') {
        resultEntries.sort((a, b) => a[0].localeCompare(b[0]));
      } else if (reportOptions.sortBy === 'duration') {
        resultEntries.sort((a, b) => a[1].stats.mean - b[1].stats.mean);
      } else if (reportOptions.sortBy === 'type') {
        resultEntries.sort((a, b) => a[1].type.localeCompare(b[1].type));
      }

      // Create report data
      const reportData = {
        suiteId: this.id,
        timestamp: Date.now(),
        benchmarkCount: this.results.size,
        results: resultEntries.map(([name, result]) => {
          const reportResult = {
            name,
            type: result.type,
            description: result.description,
            stats: result.stats,
          };

          // Include iteration data if requested
          if (reportOptions.includeIterations && result.iterationResults) {
            reportResult.iterations = result.iterationResults;
          }

          return reportResult;
        }),
      };

      // Add summary statistics
      reportData.summary = {
        averageDuration: this._calculateMean(
          reportData.results.map((r) => r.stats.mean),
        ),
        fastestBenchmark: reportData.results.reduce(
          (fastest, result) => {
            return result.stats.mean < fastest.stats.mean ? result : fastest;
          },
          { stats: { mean: Infinity }, name: 'none' },
        ).name,
        slowestBenchmark: reportData.results.reduce(
          (slowest, result) => {
            return result.stats.mean > slowest.stats.mean ? result : slowest;
          },
          { stats: { mean: -Infinity }, name: 'none' },
        ).name,
      };

      // Format output
      if (reportOptions.format === 'json') {
        return reportData;
      } else if (reportOptions.format === 'text') {
        // Simple text format
        return this._formatReportAsText(reportData);
      } else if (reportOptions.format === 'csv') {
        // CSV format
        return this._formatReportAsCsv(reportData);
      }

      return reportData;
    }

    /**
     * Format report as plain text
     * @private
     * @param {Object} reportData - Report data
     * @returns {string} Formatted text report
     */
    _formatReportAsText(reportData) {
      // Build report header
      let report = `Benchmark Report for ${reportData.suiteId}\n`;
      report += `Timestamp: ${new Date(reportData.timestamp).toISOString()}\n`;
      report += `Number of Benchmarks: ${reportData.benchmarkCount}\n\n`;

      // Add summary
      report += 'Summary:\n';
      report += `  Average Duration: ${reportData.summary.averageDuration.toFixed(2)}ms\n`;
      report += `  Fastest Benchmark: ${reportData.summary.fastestBenchmark}\n`;
      report += `  Slowest Benchmark: ${reportData.summary.slowestBenchmark}\n\n`;

      // Add individual results
      report += 'Benchmark Results:\n';

      for (const result of reportData.results) {
        report += `  ${result.name} (${result.type}):\n`;
        report += `    Description: ${result.description || 'N/A'}\n`;
        report += `    Mean: ${result.stats.mean.toFixed(2)}ms\n`;
        report += `    Median: ${result.stats.median.toFixed(2)}ms\n`;
        report += `    Min: ${result.stats.min.toFixed(2)}ms\n`;
        report += `    Max: ${result.stats.max.toFixed(2)}ms\n`;
        report += `    Std Dev: ${result.stats.stdDev.toFixed(2)}ms\n`;
        report += `    Ops/Second: ${result.stats.opsPerSecond.toFixed(2)}\n`;

        if (result.stats.memory) {
          report += `    Mean RSS Delta: ${(result.stats.memory.meanRss / 1024 / 1024).toFixed(2)}MB\n`;
          report += `    Mean Heap Used Delta: ${(result.stats.memory.meanHeapUsed / 1024 / 1024).toFixed(2)}MB\n`;
        }

        report += '\n';
      }

      return report;
    }

    /**
     * Format report as CSV
     * @private
     * @param {Object} reportData - Report data
     * @returns {string} Formatted CSV report
     */
    _formatReportAsCsv(reportData) {
      // CSV header
      let csv =
        'Name,Type,Description,Mean (ms),Median (ms),Min (ms),Max (ms),StdDev (ms),Ops/Second\n';

      // Add rows
      for (const result of reportData.results) {
        const row = [
          `"${result.name}"`,
          `"${result.type}"`,
          `"${result.description || ''}"`,
          result.stats.mean.toFixed(2),
          result.stats.median.toFixed(2),
          result.stats.min.toFixed(2),
          result.stats.max.toFixed(2),
          result.stats.stdDev.toFixed(2),
          result.stats.opsPerSecond.toFixed(2),
        ];

        csv += row.join(',') + '\n';
      }

      return csv;
    }

    /**
     * Get results for a specific benchmark
     * @param {string} name - Benchmark name
     * @returns {Object|null} Benchmark result or null if not found
     */
    getResult(name) {
      return this.results.get(name) || null;
    }

    /**
     * Get all benchmark results
     * @returns {Map<string, Object>} All benchmark results
     */
    getAllResults() {
      return new Map(this.results);
    }

    /**
     * Clear all benchmark results
     * @returns {BenchmarkSuite} this (for chaining)
     */
    clearResults() {
      this.results.clear();
      return this;
    }

    /**
     * Subscribe to benchmark events
     * @param {string} event - Event name
     * @param {Function} callback - Event callback
     * @returns {Function} Unsubscribe function
     */
    subscribe(event, callback) {
      return this.eventBus.on(event, callback);
    }
  }

  /**
   * Neural network performance benchmarks
   */
  class NeuralBenchmarks {
    /**
     * Create pre-configured neural network benchmarks
     * @param {BenchmarkSuite} suite - Benchmark suite to add to
     * @param {Object} [options={}] - Benchmark options
     * @returns {BenchmarkSuite} Enhanced benchmark suite
     */
    static registerTo(suite, options = {}) {
      if (!(suite instanceof BenchmarkSuite)) {
        throw new Prime.ValidationError('Invalid benchmark suite');
      }

      const neurOptions = {
        layerSizes: options.layerSizes || [784, 256, 128, 64, 10],
        batchSizes: options.batchSizes || [1, 16, 64, 256],
        ...options,
      };

      // Register forward pass benchmark
      suite.register(
        'neural_forward_pass',
        async (context) => {
          const nodeCount = context.nodeCount || 1;
          const batchSize =
            neurOptions.batchSizes[
              context.iteration % neurOptions.batchSizes.length
            ];

          // Create a distributed layer for benchmark
          const layer = new Prime.Distributed.Partition.DistributedLayer({
            id: 'bench_layer',
            layerConfig: {
              inputSize: neurOptions.layerSizes[0],
              outputSize: neurOptions.layerSizes[1],
              activation: 'relu',
            },
            nodeIds: Array.from({ length: nodeCount }, (_, i) => `node_${i}`),
            partitionScheme: new Prime.Distributed.Partition.PartitionScheme({
              type: Prime.Distributed.Partition.PartitionType.INTRA_LAYER,
              nodeCount,
              layerConfig: {
                bench_layer: {
                  inputSize: neurOptions.layerSizes[0],
                  outputSize: neurOptions.layerSizes[1],
                },
              },
            }),
          });

          // Create random input batch
          const inputBatch = [];
          for (let i = 0; i < batchSize; i++) {
            const input = new Array(neurOptions.layerSizes[0])
              .fill(0)
              .map(() => Math.random());
            inputBatch.push(input);
          }

          // Run forward pass for each input
          const results = [];
          for (let i = 0; i < inputBatch.length; i++) {
            const result = await layer.forward(inputBatch[i]);
            results.push(result);
          }

          return {
            batchSize,
            nodeCount,
            results: results.length,
          };
        },
        {
          type: BenchmarkType.COMPUTATION,
          description: 'Benchmark forward pass across distributed layers',
          tags: ['neural', 'forward-pass'],
        },
      );

      // Register backward pass benchmark
      suite.register(
        'neural_backward_pass',
        async (context) => {
          const nodeCount = context.nodeCount || 1;
          const batchSize =
            neurOptions.batchSizes[
              context.iteration % neurOptions.batchSizes.length
            ];

          // Create a distributed layer for benchmark
          const layer = new Prime.Distributed.Partition.DistributedLayer({
            id: 'bench_layer',
            layerConfig: {
              inputSize: neurOptions.layerSizes[0],
              outputSize: neurOptions.layerSizes[1],
              activation: 'relu',
            },
            nodeIds: Array.from({ length: nodeCount }, (_, i) => `node_${i}`),
            partitionScheme: new Prime.Distributed.Partition.PartitionScheme({
              type: Prime.Distributed.Partition.PartitionType.INTRA_LAYER,
              nodeCount,
              layerConfig: {
                bench_layer: {
                  inputSize: neurOptions.layerSizes[0],
                  outputSize: neurOptions.layerSizes[1],
                },
              },
            }),
          });

          const results = [];

          for (let i = 0; i < batchSize; i++) {
            // Create random input
            const input = new Array(neurOptions.layerSizes[0])
              .fill(0)
              .map(() => Math.random());

            // Forward pass to get cache for backward pass
            const forward = await layer.forward(input);

            // Create random gradient
            const gradient = new Array(neurOptions.layerSizes[1])
              .fill(0)
              .map(() => Math.random() - 0.5);

            // Run backward pass
            const backResult = await layer.backward(gradient, forward.cache);
            results.push(backResult);
          }

          return {
            batchSize,
            nodeCount,
            results: results.length,
          };
        },
        {
          type: BenchmarkType.COMPUTATION,
          description: 'Benchmark backward pass across distributed layers',
          tags: ['neural', 'backward-pass'],
        },
      );

      // Register full network training benchmark
      suite.register(
        'neural_network_training',
        async (context) => {
          const nodeCount = context.nodeCount || 1;
          const batchSize = Math.min(
            16,
            neurOptions.batchSizes[
              context.iteration % neurOptions.batchSizes.length
            ],
          );

          // Create a simple multi-layer network
          const layers = [];

          for (let i = 0; i < neurOptions.layerSizes.length - 1; i++) {
            layers.push(
              new Prime.Distributed.Partition.DistributedLayer({
                id: `bench_layer_${i}`,
                layerConfig: {
                  inputSize: neurOptions.layerSizes[i],
                  outputSize: neurOptions.layerSizes[i + 1],
                  activation:
                    i === neurOptions.layerSizes.length - 2
                      ? 'sigmoid'
                      : 'relu',
                },
                nodeIds: Array.from(
                  { length: nodeCount },
                  (_, j) => `node_${j}`,
                ),
                partitionScheme:
                  new Prime.Distributed.Partition.PartitionScheme({
                    type:
                      i % 2 === 0
                        ? Prime.Distributed.Partition.PartitionType.INTRA_LAYER
                        : Prime.Distributed.Partition.PartitionType
                          .DATA_PARALLEL,
                    nodeCount,
                    layerConfig: {
                      [`bench_layer_${i}`]: {
                        inputSize: neurOptions.layerSizes[i],
                        outputSize: neurOptions.layerSizes[i + 1],
                      },
                    },
                  }),
              }),
            );
          }

          // Create training data batch
          const batch = [];
          for (let i = 0; i < batchSize; i++) {
            batch.push({
              input: new Array(neurOptions.layerSizes[0])
                .fill(0)
                .map(() => Math.random()),
              target: new Array(
                neurOptions.layerSizes[neurOptions.layerSizes.length - 1],
              )
                .fill(0)
                .map(() => Math.random()),
            });
          }

          // Train for one epoch
          const results = [];

          for (const sample of batch) {
            // Forward passes
            const activations = [];
            const caches = [];

            let layerInput = sample.input;

            for (const layer of layers) {
              const result = await layer.forward(layerInput);
              activations.push(result.activation);
              caches.push(result.cache);
              layerInput = result.activation;
            }

            // Compute output gradient (simplified loss)
            const output = activations[activations.length - 1];
            const outputGradient = output.map((o, i) => o - sample.target[i]);

            // Backward passes
            let gradOutput = outputGradient;

            for (let i = layers.length - 1; i >= 0; i--) {
              const gradResult = await layers[i].backward(
                gradOutput,
                caches[i],
              );
              gradOutput = gradResult.dX;

              // Apply weight updates
              await layers[i].update(
                {
                  dW: gradResult.dW,
                  dB: gradResult.dB,
                },
                0.01,
              );
            }

            results.push({
              sample: sample.input.length,
              layers: layers.length,
            });
          }

          return {
            batchSize,
            nodeCount,
            layers: layers.length,
            results: results.length,
          };
        },
        {
          type: BenchmarkType.SYSTEM,
          description: 'Benchmark full neural network training',
          tags: ['neural', 'training', 'end-to-end'],
        },
      );

      return suite;
    }
  }

  /**
   * Communication performance benchmarks
   */
  class CommunicationBenchmarks {
    /**
     * Create pre-configured communication benchmarks
     * @param {BenchmarkSuite} suite - Benchmark suite to add to
     * @param {Object} [options={}] - Benchmark options
     * @returns {BenchmarkSuite} Enhanced benchmark suite
     */
    static registerTo(suite, options = {}) {
      if (!(suite instanceof BenchmarkSuite)) {
        throw new Prime.ValidationError('Invalid benchmark suite');
      }

      const commOptions = {
        messageSizes: options.messageSizes || [1, 10, 100, 1000, 10000],
        ...options,
      };

      // Register message roundtrip benchmark
      suite.register(
        'communication_roundtrip',
        async (context) => {
          const nodeCount = context.nodeCount || 2;
          const messageSize =
            commOptions.messageSizes[
              context.iteration % commOptions.messageSizes.length
            ];

          // Create router for benchmark
          const router = new Prime.Distributed.Communication.MessageRouter({
            nodeId: 'bench_node',
          });

          // Create message payload
          const payload = new Array(messageSize).fill(0).map(() => ({
            value: Math.random(),
            timestamp: Date.now(),
          }));

          // Send messages to all nodes and measure roundtrip
          const promises = [];

          for (let i = 0; i < nodeCount; i++) {
            const promise = router.route(
              `node_${i}`,
              Prime.Distributed.Communication.MessageType.GRADIENT_SYNC,
              {
                gradients: payload,
                layerId: 'benchmark_layer',
                iteration: context.iteration,
              },
              {
                requireAck: true,
              },
            );

            promises.push(promise);
          }

          // Wait for all messages to complete roundtrip
          const results = await Promise.all(promises);

          // Clean up
          await router.shutdown();

          return {
            nodeCount,
            messageSize,
            successful: results.length,
          };
        },
        {
          type: BenchmarkType.COMMUNICATION,
          description: 'Benchmark message roundtrip time',
          tags: ['communication', 'roundtrip'],
        },
      );

      // Register broadcast benchmark
      suite.register(
        'communication_broadcast',
        async (context) => {
          const nodeCount = context.nodeCount || 5;
          const messageSize =
            commOptions.messageSizes[
              context.iteration % commOptions.messageSizes.length
            ];

          // Create router for benchmark
          const router = new Prime.Distributed.Communication.MessageRouter({
            nodeId: 'bench_node',
          });

          // Create message payload
          const payload = new Array(messageSize).fill(0).map(() => ({
            value: Math.random(),
            timestamp: Date.now(),
          }));

          // Broadcast to all nodes
          const result = await router.route(
            'broadcast',
            Prime.Distributed.Communication.MessageType.GRADIENT_SYNC,
            {
              gradients: payload,
              layerId: 'benchmark_layer',
              iteration: context.iteration,
            },
          );

          // Clean up
          await router.shutdown();

          return {
            nodeCount,
            messageSize,
            result,
          };
        },
        {
          type: BenchmarkType.COMMUNICATION,
          description: 'Benchmark broadcast performance',
          tags: ['communication', 'broadcast'],
        },
      );

      // Register gradient synchronization benchmark
      suite.register(
        'communication_gradient_sync',
        async (context) => {
          const nodeCount = context.nodeCount || 4;
          const rows =
            context.neurOptions && context.neurOptions.layerSizes
              ? context.neurOptions.layerSizes[0]
              : 100;
          const cols =
            context.neurOptions && context.neurOptions.layerSizes
              ? context.neurOptions.layerSizes[1]
              : 50;

          // Create router for benchmark
          const router = new Prime.Distributed.Communication.MessageRouter({
            nodeId: 'bench_node',
          });

          // Create fake gradients matrix
          const gradients = {
            weights: Array.from({ length: rows }, () =>
              Array.from({ length: cols }, () => Math.random() * 0.1),
            ),
            biases: Array.from({ length: cols }, () => Math.random() * 0.1),
          };

          // Sync gradients with all nodes
          const promises = [];

          for (let i = 0; i < nodeCount; i++) {
            const promise = router.syncGradients(`node_${i}`, gradients, {
              layerId: 'benchmark_layer',
              iteration: context.iteration,
            });

            promises.push(promise);
          }

          // Wait for all syncs to complete
          const results = await Promise.all(promises);

          // Clean up
          await router.shutdown();

          return {
            nodeCount,
            gradientSize: rows * cols + cols,
            successful: results.length,
          };
        },
        {
          type: BenchmarkType.COMMUNICATION,
          description: 'Benchmark gradient synchronization',
          tags: ['communication', 'gradient-sync'],
        },
      );

      return suite;
    }
  }

  /**
   * Coherence performance benchmarks
   */
  class CoherenceBenchmarks {
    /**
     * Create pre-configured coherence benchmarks
     * @param {BenchmarkSuite} suite - Benchmark suite to add to
     * @param {Object} [options={}] - Benchmark options
     * @returns {BenchmarkSuite} Enhanced benchmark suite
     */
    static registerTo(suite, options = {}) {
      if (!(suite instanceof BenchmarkSuite)) {
        throw new Prime.ValidationError('Invalid benchmark suite');
      }

      const cohOptions = {
        matrixSizes: options.matrixSizes || [10, 50, 100, 500],
        ...options,
      };

      // Register coherence calculation benchmark
      suite.register(
        'coherence_calculation',
        async (context) => {
          const nodeCount = context.nodeCount || 1;
          const matrixSize =
            cohOptions.matrixSizes[
              context.iteration % cohOptions.matrixSizes.length
            ];

          // Create layers for coherence check
          const layers = [];

          for (let i = 0; i < nodeCount; i++) {
            layers.push({
              id: `bench_layer_${i}`,
              config: {
                inputSize: matrixSize,
                outputSize: matrixSize,
                activation: 'relu',
              },
              weights: Array.from({ length: matrixSize }, () =>
                Array.from({ length: matrixSize }, () => Math.random() * 0.1),
              ),
              biases: Array.from(
                { length: matrixSize },
                () => Math.random() * 0.1,
              ),
            });
          }

          // Measure coherence
          const coherenceScores = [];

          for (const layer of layers) {
            // Simulate cluster node coherence check
            const node = new Prime.Distributed.Cluster.ClusterNode({
              id: `node_${layer.id}`,
              type: Prime.Distributed.Cluster.NodeType.WORKER,
            });

            // Create task for coherence check
            const task = {
              id: `coherence_check_${layer.id}`,
              type: 'coherence_check',
              data: {
                layerConfig: layer.config,
                parameters: {
                  weights: layer.weights,
                  biases: layer.biases,
                },
              },
            };

            // Use private method directly since we don't want to go through task queue
            const result = node._simulateCoherenceCheck(task.data);
            coherenceScores.push(result.score);

            // Clean up
            await node.terminate();
          }

          // Calculate global coherence
          const globalCoherence =
            coherenceScores.reduce((sum, score) => sum + score, 0) /
            coherenceScores.length;

          return {
            nodeCount,
            matrixSize,
            coherenceScores,
            globalCoherence,
          };
        },
        {
          type: BenchmarkType.COMPUTATION,
          description: 'Benchmark coherence calculation performance',
          tags: ['coherence', 'calculation'],
        },
      );

      // Register partition optimization benchmark
      suite.register(
        'coherence_partition_optimize',
        async (context) => {
          const nodeCount = Math.max(2, context.nodeCount || 4);
          const layerCount = context.iteration + 3; // At least 3 layers

          // Create layers for partitioning
          const layerConfig = {};

          for (let i = 0; i < layerCount; i++) {
            const size =
              cohOptions.matrixSizes[i % cohOptions.matrixSizes.length];
            const nextSize =
              cohOptions.matrixSizes[(i + 1) % cohOptions.matrixSizes.length];

            layerConfig[`layer_${i}`] = {
              inputSize: size,
              outputSize: nextSize,
              activation: i % 2 === 0 ? 'relu' : 'sigmoid',
            };
          }

          // Create and time partition schemes
          const schemes = [];

          for (const schemeType of Object.values(
            Prime.Distributed.Partition.PartitionType,
          )) {
            const startTime = performance.now();

            const scheme = new Prime.Distributed.Partition.PartitionScheme({
              type: schemeType,
              nodeCount,
              layerConfig,
              optimizeCoherence: true,
            });

            const endTime = performance.now();

            schemes.push({
              type: schemeType,
              time: endTime - startTime,
              coherenceScore: scheme.coherenceScore,
            });
          }

          return {
            nodeCount,
            layerCount,
            schemes,
          };
        },
        {
          type: BenchmarkType.PARTITIONING,
          description: 'Benchmark partition optimization performance',
          tags: ['coherence', 'partitioning'],
        },
      );

      return suite;
    }
  }

  // Add classes to Prime.Distributed namespace
  Prime.Distributed.Benchmark = {
    BenchmarkType,
    BenchmarkSuite,
    NeuralBenchmarks,
    CommunicationBenchmarks,
    CoherenceBenchmarks,
  };
})();

// Export the enhanced Prime object
module.exports = Prime;
