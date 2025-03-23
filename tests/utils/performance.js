/**
 * PrimeOS Performance Testing Utilities
 * 
 * These utilities provide standardized approaches to measuring and reporting
 * performance metrics across PrimeOS components.
 */

/**
 * Creates a performance report from Benchmark.js Suite results
 * 
 * @param {Object} suite - Benchmark.js Suite with completed benchmarks
 * @returns {Object} - Performance report with metrics and comparisons
 */
function createPerformanceReport(suite) {
  // Extract basic metrics
  const results = Array.from(suite).map(benchmark => {
    return {
      name: benchmark.name,
      hz: benchmark.hz,
      rme: benchmark.stats.rme,
      samples: benchmark.stats.sample.length,
      mean: benchmark.stats.mean,
      variance: benchmark.stats.variance
    };
  });
  
  // Find fastest and slowest
  const fastest = results.reduce((prev, current) => 
    (prev.hz > current.hz) ? prev : current);
  
  const slowest = results.reduce((prev, current) => 
    (prev.hz < current.hz) ? prev : current);
  
  // Calculate relative performance
  results.forEach(result => {
    result.relativeToFastest = result.hz / fastest.hz;
    result.relativeToSlowest = result.hz / slowest.hz;
  });
  
  // Create summary text
  const summary = results.map(r => {
    return `${r.name}: ${formatOpsPerSecond(r.hz)} ±${r.rme.toFixed(2)}% (${r.samples} samples)`;
  }).join('\n');
  
  return {
    results,
    fastest,
    slowest,
    summary
  };
}

/**
 * Formats operations per second with appropriate unit
 * 
 * @param {number} hz - Operations per second
 * @returns {string} - Formatted string with appropriate units
 */
function formatOpsPerSecond(hz) {
  if (hz >= 1e9) {
    return `${(hz / 1e9).toFixed(2)} GOps/sec`;
  } else if (hz >= 1e6) {
    return `${(hz / 1e6).toFixed(2)} MOps/sec`;
  } else if (hz >= 1e3) {
    return `${(hz / 1e3).toFixed(2)} KOps/sec`;
  } else {
    return `${hz.toFixed(2)} Ops/sec`;
  }
}

/**
 * Measures the execution time of a function
 * 
 * @param {Function} fn - Function to measure
 * @param {Array} args - Arguments to pass to the function
 * @param {number} iterations - Number of iterations to run
 * @returns {Object} - Performance metrics
 */
function measureExecutionTime(fn, args = [], iterations = 1000) {
  const times = [];
  
  // Warm up
  for (let i = 0; i < 10; i++) {
    fn(...args);
  }
  
  // Measure
  for (let i = 0; i < iterations; i++) {
    const start = process.hrtime.bigint();
    fn(...args);
    const end = process.hrtime.bigint();
    times.push(Number(end - start) / 1e6); // Convert to milliseconds
  }
  
  // Calculate statistics
  const sum = times.reduce((a, b) => a + b, 0);
  const mean = sum / times.length;
  const variance = times.reduce((sum, x) => sum + Math.pow(x - mean, 2), 0) / times.length;
  const stdDev = Math.sqrt(variance);
  const min = Math.min(...times);
  const max = Math.max(...times);
  
  // Calculate operations per second
  const opsPerSecond = 1000 / mean;
  
  return {
    mean,
    stdDev,
    min,
    max,
    opsPerSecond,
    iterations,
    formattedOpsPerSecond: formatOpsPerSecond(opsPerSecond)
  };
}

/**
 * Measures memory usage of a function
 * 
 * @param {Function} fn - Function to measure
 * @param {Array} args - Arguments to pass to the function
 * @returns {Object} - Memory usage metrics
 */
function measureMemoryUsage(fn, args = []) {
  // Force garbage collection if available
  if (global.gc) {
    global.gc();
  }
  
  // Measure initial memory usage
  const initialMemory = process.memoryUsage();
  
  // Run the function
  const result = fn(...args);
  
  // Measure final memory usage
  const finalMemory = process.memoryUsage();
  
  // Calculate differences
  const diff = {
    rss: finalMemory.rss - initialMemory.rss,
    heapTotal: finalMemory.heapTotal - initialMemory.heapTotal,
    heapUsed: finalMemory.heapUsed - initialMemory.heapUsed,
    external: finalMemory.external - initialMemory.external
  };
  
  // Format for human readability
  const formatted = {
    rss: formatBytes(diff.rss),
    heapTotal: formatBytes(diff.heapTotal),
    heapUsed: formatBytes(diff.heapUsed),
    external: formatBytes(diff.external)
  };
  
  return {
    initial: initialMemory,
    final: finalMemory,
    diff,
    formatted,
    result
  };
}

/**
 * Formats bytes into human-readable format
 * 
 * @param {number} bytes - Number of bytes
 * @returns {string} - Formatted string with appropriate units
 */
function formatBytes(bytes) {
  if (bytes === 0) return '0 Bytes';
  
  const k = 1024;
  const sizes = ['Bytes', 'KB', 'MB', 'GB', 'TB'];
  const i = Math.floor(Math.log(Math.abs(bytes)) / Math.log(k));
  
  return parseFloat((bytes / Math.pow(k, i)).toFixed(2)) + ' ' + sizes[i];
}

/**
 * Measures scaling characteristics of a function
 * 
 * @param {Function} fn - Function to measure
 * @param {Function} dataGenerator - Function that generates data of specified size
 * @param {Array} sizes - Array of sizes to test
 * @returns {Object} - Scaling metrics
 */
function measureScaling(fn, dataGenerator, sizes = [10, 100, 1000, 10000]) {
  const results = [];
  
  for (const size of sizes) {
    const data = dataGenerator(size);
    const performance = measureExecutionTime(() => fn(data), [], Math.min(1000, Math.max(10, 10000 / size)));
    
    results.push({
      size,
      opsPerSecond: performance.opsPerSecond,
      mean: performance.mean,
      formattedOpsPerSecond: performance.formattedOpsPerSecond
    });
  }
  
  // Calculate scaling factors
  for (let i = 1; i < results.length; i++) {
    const sizeRatio = results[i].size / results[i-1].size;
    const speedRatio = results[i-1].opsPerSecond / results[i].opsPerSecond;
    
    results[i].scalingFactor = speedRatio / sizeRatio;
  }
  
  // Determine scaling characteristics
  let scalingType = 'Unknown';
  const lastFactor = results[results.length - 1].scalingFactor;
  
  if (lastFactor <= 0.1) {
    scalingType = 'Exponential';
  } else if (lastFactor <= 0.3) {
    scalingType = 'Polynomial';
  } else if (lastFactor <= 1.2) {
    scalingType = 'Linear';
  } else if (lastFactor <= 2) {
    scalingType = 'Sublinear';
  } else {
    scalingType = 'Logarithmic';
  }
  
  return {
    results,
    scalingType,
    summary: `Scaling appears to be ${scalingType}`
  };
}

/**
 * Run a performance benchmark for a specific function and input sizes
 * 
 * @param {string} name - Name of the benchmark
 * @param {Function} fn - Function to benchmark
 * @param {Array<any>} inputSizes - Array of input sizes or test cases
 * @param {Function} inputGenerator - Function to generate inputs from sizes
 * @returns {Object} - Benchmark results
 */
function runBenchmark(name, fn, inputSizes, inputGenerator) {
  console.log(`Running benchmark: ${name}`);
  
  const results = [];
  
  for (let i = 0; i < inputSizes.length; i++) {
    const size = inputSizes[i];
    const input = inputGenerator(size);
    const sizeName = typeof size === 'number' ? size : size.name || `Case ${i+1}`;
    
    console.log(`  Testing input size: ${sizeName}`);
    
    const performance = measureExecutionTime(
      () => fn(input), 
      [], 
      Math.min(1000, Math.max(10, 10000 / (typeof size === 'number' ? size : 100)))
    );
    
    results.push({
      size: sizeName,
      opsPerSecond: performance.opsPerSecond,
      mean: performance.mean,
      stdDev: performance.stdDev,
      formattedOpsPerSecond: performance.formattedOpsPerSecond
    });
    
    console.log(`    Result: ${performance.formattedOpsPerSecond}`);
  }
  
  console.log(`Benchmark complete: ${name}`);
  
  return {
    name,
    results,
    fastest: results.reduce((a, b) => a.opsPerSecond > b.opsPerSecond ? a : b),
    slowest: results.reduce((a, b) => a.opsPerSecond < b.opsPerSecond ? a : b)
  };
}

module.exports = {
  createPerformanceReport,
  measureExecutionTime,
  measureMemoryUsage,
  measureScaling,
  runBenchmark,
  formatOpsPerSecond,
  formatBytes
};