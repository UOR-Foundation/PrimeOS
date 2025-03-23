/**
 * Extreme Value Benchmarks for PrimeOS
 *
 * This module provides benchmarking utilities for testing operations with extreme values
 * to ensure numerical stability and performance under challenging conditions.
 */

const { performance } = require("perf_hooks");
const Prime = require("../mathematics.js");

/**
 * Benchmark class for numerical operations with extreme values
 */
class ExtremeValueBenchmark {
  /**
   * Create a new benchmark instance
   * @param {Object} options Configuration options
   * @param {boolean} [options.verbose=false] Whether to log detailed results
   * @param {number} [options.warmupRuns=3] Number of warmup runs before measuring
   * @param {number} [options.measureRuns=10] Number of measured runs
   */
  constructor(options = {}) {
    this.options = Object.assign(
      {
        verbose: false,
        warmupRuns: 3,
        measureRuns: 10,
      },
      options,
    );

    this.results = {};
  }

  /**
   * Run a benchmark for a function with given inputs
   * @param {string} name Benchmark name
   * @param {Function} fn Function to benchmark
   * @param {Array<Array<*>>} inputs Array of input sets (each set is an array of arguments)
   * @param {Function} [validator] Optional function to validate results
   * @returns {Object} Benchmark results
   */
  run(name, fn, inputs, validator) {
    if (this.options.verbose) {
      console.log(`Running benchmark: ${name}`);
    }

    // Warmup
    for (let i = 0; i < this.options.warmupRuns; i++) {
      for (const input of inputs) {
        fn(...input);
      }
    }

    const durations = [];
    const results = [];
    let validationErrors = 0;

    // Measurement runs
    for (let run = 0; run < this.options.measureRuns; run++) {
      const runResults = [];
      const startTime = performance.now();

      for (const input of inputs) {
        const result = fn(...input);
        runResults.push(result);

        // Validate if validator provided
        if (validator) {
          try {
            const valid = validator(result, input);
            if (!valid) validationErrors++;
          } catch (e) {
            validationErrors++;
            if (this.options.verbose) {
              console.error(`Validation error in ${name}:`, e.message);
            }
          }
        }
      }

      const endTime = performance.now();
      const duration = endTime - startTime;
      durations.push(duration);
      results.push(runResults);
    }

    // Calculate statistics
    durations.sort((a, b) => a - b);
    const totalDuration = durations.reduce((sum, d) => sum + d, 0);
    const avgDuration = totalDuration / durations.length;
    const medianDuration = durations[Math.floor(durations.length / 2)];
    const minDuration = durations[0];
    const maxDuration = durations[durations.length - 1];

    const benchmarkResult = {
      name,
      inputs: inputs.length,
      validationErrors,
      stats: {
        avg: avgDuration,
        median: medianDuration,
        min: minDuration,
        max: maxDuration,
        total: totalDuration,
      },
      opsPerSecond:
        (inputs.length * this.options.measureRuns) / (totalDuration / 1000),
    };

    this.results[name] = benchmarkResult;

    if (this.options.verbose) {
      console.log(`Benchmark ${name} completed`);
      console.log(
        `  Avg: ${avgDuration.toFixed(2)}ms, Median: ${medianDuration.toFixed(2)}ms`,
      );
      console.log(
        `  Min: ${minDuration.toFixed(2)}ms, Max: ${maxDuration.toFixed(2)}ms`,
      );
      console.log(`  Ops/sec: ${benchmarkResult.opsPerSecond.toFixed(2)}`);
      if (validationErrors > 0) {
        console.log(`  Validation errors: ${validationErrors}`);
      }
    }

    return benchmarkResult;
  }

  /**
   * Compare multiple implementations of the same operation
   * @param {string} name Benchmark name
   * @param {Object<string, Function>} implementations Map of implementation name to function
   * @param {Array<Array<*>>} inputs Array of input sets
   * @param {Function} [validator] Optional function to validate results
   * @returns {Object} Comparison results
   */
  compare(name, implementations, inputs, validator) {
    if (this.options.verbose) {
      console.log(`Running comparison benchmark: ${name}`);
    }

    const results = {};
    let baseline = null;

    // Run benchmark for each implementation
    for (const [implName, fn] of Object.entries(implementations)) {
      const result = this.run(`${name}_${implName}`, fn, inputs, validator);
      results[implName] = result;

      // First implementation is baseline
      if (baseline === null) {
        baseline = result;
      }
    }

    // Calculate relative performance
    for (const [implName, result] of Object.entries(results)) {
      if (implName !== Object.keys(implementations)[0]) {
        result.relativeThroughput = result.opsPerSecond / baseline.opsPerSecond;
      } else {
        result.relativeThroughput = 1;
      }
    }

    // Sort by performance
    const sortedResults = Object.entries(results)
      .sort((a, b) => b[1].opsPerSecond - a[1].opsPerSecond)
      .map(([implName, result]) => ({
        implementation: implName,
        opsPerSecond: result.opsPerSecond,
        relativeThroughput: result.relativeThroughput,
        validationErrors: result.validationErrors,
      }));

    const comparison = {
      name,
      results: sortedResults,
      fastest: sortedResults[0].implementation,
      slowest: sortedResults[sortedResults.length - 1].implementation,
      maxSpeedup:
        sortedResults[0].opsPerSecond /
        sortedResults[sortedResults.length - 1].opsPerSecond,
    };

    if (this.options.verbose) {
      console.log(`Comparison results for ${name}:`);
      console.table(sortedResults);
      console.log(
        `Fastest: ${comparison.fastest}, Slowest: ${comparison.slowest}`,
      );
      console.log(`Max speedup: ${comparison.maxSpeedup.toFixed(2)}x`);
    }

    return comparison;
  }

  /**
   * Generate extreme value test cases
   * @param {string} type Type of extreme values ('vector', 'matrix', 'mixed')
   * @param {Object} options Generation options
   * @returns {Array} Array of test cases
   */
  static generateExtremeValues(type, options = {}) {
    const defaults = {
      count: 10,
      dimension: 10,
      includeSmall: true,
      includeLarge: true,
      includeNormal: true,
      includeMixed: true,
    };

    const config = { ...defaults, ...options };
    const cases = [];

    switch (type) {
      case "vector":
        // Generate vectors with extreme values
        if (config.includeNormal) {
          cases.push(
            Array(config.dimension)
              .fill()
              .map(() => Math.random() * 2 - 1),
          );
        }

        if (config.includeSmall) {
          cases.push(
            Array(config.dimension)
              .fill()
              .map(() => (Math.random() * 2 - 1) * 1e-15),
          );
        }

        if (config.includeLarge) {
          cases.push(
            Array(config.dimension)
              .fill()
              .map(() => (Math.random() * 2 - 1) * 1e15),
          );
        }

        if (config.includeMixed) {
          cases.push(
            Array(config.dimension)
              .fill()
              .map((_, i) => {
                const magnitude = i % 3 === 0 ? 1e15 : i % 3 === 1 ? 1e-15 : 1;
                return (Math.random() * 2 - 1) * magnitude;
              }),
          );
        }
        break;

      case "matrix":
        // Generate matrices with extreme values
        if (config.includeNormal) {
          cases.push(
            Array(config.dimension)
              .fill()
              .map(() =>
                Array(config.dimension)
                  .fill()
                  .map(() => Math.random() * 2 - 1),
              ),
          );
        }

        if (config.includeSmall) {
          cases.push(
            Array(config.dimension)
              .fill()
              .map(() =>
                Array(config.dimension)
                  .fill()
                  .map(() => (Math.random() * 2 - 1) * 1e-15),
              ),
          );
        }

        if (config.includeLarge) {
          cases.push(
            Array(config.dimension)
              .fill()
              .map(() =>
                Array(config.dimension)
                  .fill()
                  .map(() => (Math.random() * 2 - 1) * 1e15),
              ),
          );
        }

        if (config.includeMixed) {
          cases.push(
            Array(config.dimension)
              .fill()
              .map((_, i) =>
                Array(config.dimension)
                  .fill()
                  .map((_, j) => {
                    const magnitude =
                      (i + j) % 3 === 0 ? 1e15 : (i + j) % 3 === 1 ? 1e-15 : 1;
                    return (Math.random() * 2 - 1) * magnitude;
                  }),
              ),
          );
        }
        break;

      case "mixed":
        // Generate mixed type test cases
        if (config.includeNormal) {
          cases.push([
            Array(config.dimension)
              .fill()
              .map(() => Math.random() * 2 - 1),
            Array(config.dimension)
              .fill()
              .map(() => Math.random() * 2 - 1),
          ]);
        }

        if (config.includeSmall) {
          cases.push([
            Array(config.dimension)
              .fill()
              .map(() => (Math.random() * 2 - 1) * 1e-15),
            Array(config.dimension)
              .fill()
              .map(() => Math.random() * 2 - 1),
          ]);
        }

        if (config.includeLarge) {
          cases.push([
            Array(config.dimension)
              .fill()
              .map(() => (Math.random() * 2 - 1) * 1e15),
            Array(config.dimension)
              .fill()
              .map(() => Math.random() * 2 - 1),
          ]);
        }

        if (config.includeMixed) {
          cases.push([
            Array(config.dimension)
              .fill()
              .map((_, i) => {
                const magnitude = i % 3 === 0 ? 1e15 : i % 3 === 1 ? 1e-15 : 1;
                return (Math.random() * 2 - 1) * magnitude;
              }),
            Array(config.dimension)
              .fill()
              .map((_, i) => {
                const magnitude = i % 3 === 2 ? 1e15 : i % 3 === 0 ? 1e-15 : 1;
                return (Math.random() * 2 - 1) * magnitude;
              }),
          ]);
        }
        break;

      default:
        throw new Error(`Unknown extreme value type: ${type}`);
    }

    // Fill to the requested count
    while (cases.length < config.count) {
      const baseCase = cases[cases.length % Math.max(1, cases.length)];
      const jitter = 0.01;

      if (Array.isArray(baseCase[0])) {
        // Matrix or mixed type
        const newCase = baseCase.map((arr) =>
          arr.map((val) => val * (1 + (Math.random() * jitter * 2 - jitter))),
        );
        cases.push(newCase);
      } else {
        // Vector type
        const newCase = baseCase.map(
          (val) => val * (1 + (Math.random() * jitter * 2 - jitter)),
        );
        cases.push(newCase);
      }
    }

    return cases;
  }
}

/**
 * Create standard benchmark suite for matrix operations
 * @param {Object} math Math module to benchmark
 * @param {Object} options Benchmark options
 * @returns {Object} Benchmark suite
 */
function createMatrixBenchmarkSuite(math, options = {}) {
  const benchmark = new ExtremeValueBenchmark(options);

  // Generate test matrices
  const normalMatrices = ExtremeValueBenchmark.generateExtremeValues("matrix", {
    count: 5,
    dimension: 10,
    includeSmall: false,
    includeLarge: false,
    includeMixed: false,
  });

  const extremeMatrices = ExtremeValueBenchmark.generateExtremeValues(
    "matrix",
    {
      count: 5,
      dimension: 10,
      includeNormal: false,
    },
  );

  const mixedMatrices = ExtremeValueBenchmark.generateExtremeValues("matrix", {
    count: 5,
    dimension: 10,
    includeNormal: false,
    includeSmall: false,
    includeLarge: false,
    includeMixed: true,
  });

  // Convert raw arrays to matrix objects if needed
  const prepareMatrix = (m) => {
    if (math.Matrix && math.Matrix.create) {
      return math.Matrix.create(m.length, m[0].length, 0);
    } else if (math.Matrix) {
      return new math.Matrix(m);
    } else {
      return m;
    }
  };

  const normalMatrixObjects = normalMatrices.map(prepareMatrix);
  const extremeMatrixObjects = extremeMatrices.map(prepareMatrix);
  const mixedMatrixObjects = mixedMatrices.map(prepareMatrix);

  // Create benchmark cases for different operations
  const suite = {
    // Run benchmarks
    runAll() {
      this.benchmarkInversion();
      this.benchmarkMultiplication();
      this.benchmarkDecomposition();
      this.benchmarkEigenvalues();

      return benchmark.results;
    },

    // Matrix inversion benchmark
    benchmarkInversion() {
      // Benchmark with normal matrices
      benchmark.run(
        "matrix_inversion_normal",
        (matrix) => {
          return math.Matrix
            ? math.Matrix.inverse(matrix)
            : math.inverse(matrix);
        },
        normalMatrixObjects.map((m) => [m]),
      );

      // Benchmark with extreme matrices
      benchmark.run(
        "matrix_inversion_extreme",
        (matrix) => {
          return math.Matrix
            ? math.Matrix.inverse(matrix)
            : math.inverse(matrix);
        },
        extremeMatrixObjects.map((m) => [m]),
      );

      // Benchmark with mixed matrices
      benchmark.run(
        "matrix_inversion_mixed",
        (matrix) => {
          return math.Matrix
            ? math.Matrix.inverse(matrix)
            : math.inverse(matrix);
        },
        mixedMatrixObjects.map((m) => [m]),
      );

      return benchmark.results;
    },

    // Matrix multiplication benchmark
    benchmarkMultiplication() {
      // Generate pairs of matrices for multiplication
      const normalPairs = [];
      const extremePairs = [];
      const mixedPairs = [];

      for (let i = 0; i < normalMatrixObjects.length; i++) {
        const j = (i + 1) % normalMatrixObjects.length;
        normalPairs.push([normalMatrixObjects[i], normalMatrixObjects[j]]);
        extremePairs.push([extremeMatrixObjects[i], extremeMatrixObjects[j]]);
        mixedPairs.push([mixedMatrixObjects[i], mixedMatrixObjects[j]]);
      }

      // Benchmark with normal matrices
      benchmark.run(
        "matrix_multiplication_normal",
        (a, b) => {
          return math.Matrix ? math.Matrix.multiply(a, b) : math.multiply(a, b);
        },
        normalPairs,
      );

      // Benchmark with extreme matrices
      benchmark.run(
        "matrix_multiplication_extreme",
        (a, b) => {
          return math.Matrix ? math.Matrix.multiply(a, b) : math.multiply(a, b);
        },
        extremePairs,
      );

      // Benchmark with mixed matrices
      benchmark.run(
        "matrix_multiplication_mixed",
        (a, b) => {
          return math.Matrix ? math.Matrix.multiply(a, b) : math.multiply(a, b);
        },
        mixedPairs,
      );

      return benchmark.results;
    },

    // Matrix decomposition benchmark
    benchmarkDecomposition() {
      const hasDecompose =
        (math.Matrix && math.Matrix.decompose) || math.decompose;
      if (!hasDecompose) {
        return false;
      }

      // Benchmark with normal matrices
      benchmark.run(
        "matrix_decomposition_normal",
        (matrix) => {
          return math.Matrix
            ? math.Matrix.decompose(matrix)
            : math.decompose(matrix);
        },
        normalMatrixObjects.map((m) => [m]),
      );

      // Benchmark with extreme matrices
      benchmark.run(
        "matrix_decomposition_extreme",
        (matrix) => {
          return math.Matrix
            ? math.Matrix.decompose(matrix)
            : math.decompose(matrix);
        },
        extremeMatrixObjects.map((m) => [m]),
      );

      // Benchmark with mixed matrices
      benchmark.run(
        "matrix_decomposition_mixed",
        (matrix) => {
          return math.Matrix
            ? math.Matrix.decompose(matrix)
            : math.decompose(matrix);
        },
        mixedMatrixObjects.map((m) => [m]),
      );

      return benchmark.results;
    },

    // Eigenvalues benchmark
    benchmarkEigenvalues() {
      const hasEigenvalues =
        (math.Matrix && math.Matrix.eigenvalues) || math.eigenvalues;
      if (!hasEigenvalues) {
        return false;
      }

      // Benchmark with normal matrices
      benchmark.run(
        "matrix_eigenvalues_normal",
        (matrix) => {
          return math.Matrix
            ? math.Matrix.eigenvalues(matrix)
            : math.eigenvalues(matrix);
        },
        normalMatrixObjects.map((m) => [m]),
      );

      // Benchmark with extreme matrices
      benchmark.run(
        "matrix_eigenvalues_extreme",
        (matrix) => {
          return math.Matrix
            ? math.Matrix.eigenvalues(matrix)
            : math.eigenvalues(matrix);
        },
        extremeMatrixObjects.map((m) => [m]),
      );

      // Benchmark with mixed matrices
      benchmark.run(
        "matrix_eigenvalues_mixed",
        (matrix) => {
          return math.Matrix
            ? math.Matrix.eigenvalues(matrix)
            : math.eigenvalues(matrix);
        },
        mixedMatrixObjects.map((m) => [m]),
      );

      return benchmark.results;
    },
  };

  return suite;
}

/**
 * Create standard benchmark suite for vector operations
 * @param {Object} math Math module to benchmark
 * @param {Object} options Benchmark options
 * @returns {Object} Benchmark suite
 */
function createVectorBenchmarkSuite(math, options = {}) {
  const benchmark = new ExtremeValueBenchmark(options);

  // Generate test vectors
  const normalVectors = ExtremeValueBenchmark.generateExtremeValues("vector", {
    count: 5,
    dimension: 100,
    includeSmall: false,
    includeLarge: false,
    includeMixed: false,
  });

  const extremeVectors = ExtremeValueBenchmark.generateExtremeValues("vector", {
    count: 5,
    dimension: 100,
    includeNormal: false,
  });

  const mixedVectors = ExtremeValueBenchmark.generateExtremeValues("vector", {
    count: 5,
    dimension: 100,
    includeNormal: false,
    includeSmall: false,
    includeLarge: false,
    includeMixed: true,
  });

  // Convert raw arrays to vector objects if needed
  const prepareVector = (v) => {
    if (math.Vector && math.Vector.create) {
      return math.Vector.create(v.length);
    } else if (math.Vector) {
      return new math.Vector(v);
    } else {
      return v;
    }
  };

  const normalVectorObjects = normalVectors.map(prepareVector);
  const extremeVectorObjects = extremeVectors.map(prepareVector);
  const mixedVectorObjects = mixedVectors.map(prepareVector);

  // Create benchmark cases for different operations
  const suite = {
    // Run all benchmarks
    runAll() {
      this.benchmarkDotProduct();
      this.benchmarkNorm();
      this.benchmarkAddition();
      this.benchmarkOrthogonalization();

      return benchmark.results;
    },

    // Dot product benchmark
    benchmarkDotProduct() {
      // Generate pairs of vectors for dot product
      const normalPairs = [];
      const extremePairs = [];
      const mixedPairs = [];

      for (let i = 0; i < normalVectorObjects.length; i++) {
        const j = (i + 1) % normalVectorObjects.length;
        normalPairs.push([normalVectorObjects[i], normalVectorObjects[j]]);
        extremePairs.push([extremeVectorObjects[i], extremeVectorObjects[j]]);
        mixedPairs.push([mixedVectorObjects[i], mixedVectorObjects[j]]);
      }

      // Benchmark with normal vectors
      benchmark.run(
        "vector_dot_product_normal",
        (a, b) => {
          return math.Vector ? math.Vector.dot(a, b) : math.dot(a, b);
        },
        normalPairs,
      );

      // Benchmark with extreme vectors
      benchmark.run(
        "vector_dot_product_extreme",
        (a, b) => {
          return math.Vector ? math.Vector.dot(a, b) : math.dot(a, b);
        },
        extremePairs,
      );

      // Benchmark with mixed vectors
      benchmark.run(
        "vector_dot_product_mixed",
        (a, b) => {
          return math.Vector ? math.Vector.dot(a, b) : math.dot(a, b);
        },
        mixedPairs,
      );

      return benchmark.results;
    },

    // Vector norm benchmark
    benchmarkNorm() {
      // Benchmark with normal vectors
      benchmark.run(
        "vector_norm_normal",
        (vector) => {
          return math.Vector ? math.Vector.norm(vector) : math.norm(vector);
        },
        normalVectorObjects.map((v) => [v]),
      );

      // Benchmark with extreme vectors
      benchmark.run(
        "vector_norm_extreme",
        (vector) => {
          return math.Vector ? math.Vector.norm(vector) : math.norm(vector);
        },
        extremeVectorObjects.map((v) => [v]),
      );

      // Benchmark with mixed vectors
      benchmark.run(
        "vector_norm_mixed",
        (vector) => {
          return math.Vector ? math.Vector.norm(vector) : math.norm(vector);
        },
        mixedVectorObjects.map((v) => [v]),
      );

      return benchmark.results;
    },

    // Vector addition benchmark
    benchmarkAddition() {
      // Generate pairs of vectors for addition
      const normalPairs = [];
      const extremePairs = [];
      const mixedPairs = [];

      for (let i = 0; i < normalVectorObjects.length; i++) {
        const j = (i + 1) % normalVectorObjects.length;
        normalPairs.push([normalVectorObjects[i], normalVectorObjects[j]]);
        extremePairs.push([extremeVectorObjects[i], extremeVectorObjects[j]]);
        mixedPairs.push([mixedVectorObjects[i], mixedVectorObjects[j]]);
      }

      // Benchmark with normal vectors
      benchmark.run(
        "vector_addition_normal",
        (a, b) => {
          return math.Vector ? math.Vector.add(a, b) : math.add(a, b);
        },
        normalPairs,
      );

      // Benchmark with extreme vectors
      benchmark.run(
        "vector_addition_extreme",
        (a, b) => {
          return math.Vector ? math.Vector.add(a, b) : math.add(a, b);
        },
        extremePairs,
      );

      // Benchmark with mixed vectors
      benchmark.run(
        "vector_addition_mixed",
        (a, b) => {
          return math.Vector ? math.Vector.add(a, b) : math.add(a, b);
        },
        mixedPairs,
      );

      return benchmark.results;
    },

    // Vector orthogonalization benchmark
    benchmarkOrthogonalization() {
      const hasOrthogonalize =
        (math.Vector && math.Vector.orthogonalize) || math.orthogonalize;
      if (!hasOrthogonalize) {
        return false;
      }

      // Create sets of vectors for orthogonalization
      const normalSets = [];
      const extremeSets = [];
      const mixedSets = [];

      // Group vectors into sets of 3 for orthogonalization
      for (let i = 0; i < normalVectorObjects.length; i += 3) {
        if (i + 2 < normalVectorObjects.length) {
          normalSets.push([
            [
              normalVectorObjects[i],
              normalVectorObjects[i + 1],
              normalVectorObjects[i + 2],
            ],
          ]);
          extremeSets.push([
            [
              extremeVectorObjects[i],
              extremeVectorObjects[i + 1],
              extremeVectorObjects[i + 2],
            ],
          ]);
          mixedSets.push([
            [
              mixedVectorObjects[i],
              mixedVectorObjects[i + 1],
              mixedVectorObjects[i + 2],
            ],
          ]);
        }
      }

      // Benchmark with normal vectors
      benchmark.run(
        "vector_orthogonalization_normal",
        (vectors) => {
          return math.Vector
            ? math.Vector.orthogonalize(vectors)
            : math.orthogonalize(vectors);
        },
        normalSets,
      );

      // Benchmark with extreme vectors
      benchmark.run(
        "vector_orthogonalization_extreme",
        (vectors) => {
          return math.Vector
            ? math.Vector.orthogonalize(vectors)
            : math.orthogonalize(vectors);
        },
        extremeSets,
      );

      // Benchmark with mixed vectors
      benchmark.run(
        "vector_orthogonalization_mixed",
        (vectors) => {
          return math.Vector
            ? math.Vector.orthogonalize(vectors)
            : math.orthogonalize(vectors);
        },
        mixedSets,
      );

      return benchmark.results;
    },
  };

  return suite;
}

/**
 * Run example benchmarks
 */
function runExampleBenchmarks(verbose = false) {
  console.log("Running extreme value benchmarks...");

  const options = { verbose };

  // Matrix benchmarks
  console.log("\nMatrix Operations:");
  const matrixSuite = createMatrixBenchmarkSuite(Prime, options);
  const matrixResults = matrixSuite.runAll();

  // Vector benchmarks
  console.log("\nVector Operations:");
  const vectorSuite = createVectorBenchmarkSuite(Prime, options);
  const vectorResults = vectorSuite.runAll();

  // Print summary
  console.log("\nBenchmark Summary:");
  console.log("------------------");

  Object.entries(matrixResults).forEach(([name, result]) => {
    console.log(
      `${name}: ${result.stats.median.toFixed(2)}ms (${result.opsPerSecond.toFixed(2)} ops/sec)`,
    );
  });

  Object.entries(vectorResults).forEach(([name, result]) => {
    console.log(
      `${name}: ${result.stats.median.toFixed(2)}ms (${result.opsPerSecond.toFixed(2)} ops/sec)`,
    );
  });

  return {
    matrix: matrixResults,
    vector: vectorResults,
  };
}

// Export the benchmarking utilities
module.exports = {
  ExtremeValueBenchmark,
  createMatrixBenchmarkSuite,
  createVectorBenchmarkSuite,
  runExampleBenchmarks,
};
