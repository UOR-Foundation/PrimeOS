#!/usr/bin/env node

/**
 * Extreme Value Benchmarks Runner for PrimeOS
 * This script runs benchmarks for operations with extreme numerical values
 * to assess performance and numerical stability.
 */

const path = require('path');
const fs = require('fs');
const { performance } = require('perf_hooks');
const { runExampleBenchmarks, ExtremeValueBenchmark } = require('./src/distributed/benchmark-extreme');

// Load all required math modules to ensure they're available
const Prime = require('./src/mathematics.js');
require('./src/math/vector');
require('./src/math/vector-core');
require('./src/math/vector-advanced');
require('./src/math/matrix');
require('./src/math/matrix-core');
require('./src/math/matrix-advanced');

// Parse command line arguments
const args = process.argv.slice(2);
const verbose = args.includes('--verbose') || args.includes('-v');
const outputJson = args.includes('--json') || args.includes('-j');
const runCustom = args.includes('--custom') || args.includes('-c');
const warmupRuns = args.find(arg => arg.startsWith('--warmup=')) || 3;
const measureRuns = args.find(arg => arg.startsWith('--runs=')) || 10;

// Extract numeric values if provided
const warmupCount = typeof warmupRuns === 'string' ? 
  parseInt(warmupRuns.split('=')[1], 10) : warmupRuns;
const measureCount = typeof measureRuns === 'string' ? 
  parseInt(measureRuns.split('=')[1], 10) : measureRuns;

console.log(`
██████╗ ██████╗ ██╗███╗   ███╗███████╗ ██████╗ ███████╗
██╔══██╗██╔══██╗██║████╗ ████║██╔════╝██╔═══██╗██╔════╝
██████╔╝██████╔╝██║██╔████╔██║█████╗  ██║   ██║███████╗
██╔═══╝ ██╔══██╗██║██║╚██╔╝██║██╔══╝  ██║   ██║╚════██║
██║     ██║  ██║██║██║ ╚═╝ ██║███████╗╚██████╔╝███████║
╚═╝     ╚═╝  ╚═╝╚═╝╚═╝     ╚═╝╚══════╝ ╚═════╝ ╚══════╝
                                                       
███████╗██╗  ██╗████████╗██████╗ ███████╗███╗   ███╗███████╗
██╔════╝╚██╗██╔╝╚══██╔══╝██╔══██╗██╔════╝████╗ ████║██╔════╝
█████╗   ╚███╔╝    ██║   ██████╔╝█████╗  ██╔████╔██║█████╗  
██╔══╝   ██╔██╗    ██║   ██╔══██╗██╔══╝  ██║╚██╔╝██║██╔══╝  
███████╗██╔╝ ██╗   ██║   ██║  ██║███████╗██║ ╚═╝ ██║███████╗
╚══════╝╚═╝  ╚═╝   ╚═╝   ╚═╝  ╚═╝╚══════╝╚═╝     ╚═╝╚══════╝
                                                         
██████╗ ███████╗███╗   ██╗ ██████╗██╗  ██╗███╗   ███╗ █████╗ ██████╗ ██╗  ██╗███████╗
██╔══██╗██╔════╝████╗  ██║██╔════╝██║  ██║████╗ ████║██╔══██╗██╔══██╗██║ ██╔╝██╔════╝
██████╔╝█████╗  ██╔██╗ ██║██║     ███████║██╔████╔██║███████║██████╔╝█████╔╝ ███████╗
██╔══██╗██╔══╝  ██║╚██╗██║██║     ██╔══██║██║╚██╔╝██║██╔══██║██╔══██╗██╔═██╗ ╚════██║
██████╔╝███████╗██║ ╚████║╚██████╗██║  ██║██║ ╚═╝ ██║██║  ██║██║  ██║██║  ██╗███████║
╚═════╝ ╚══════╝╚═╝  ╚═══╝ ╚═════╝╚═╝  ╚═╝╚═╝     ╚═╝╚═╝  ╚═╝╚═╝  ╚═╝╚═╝  ╚═╝╚══════╝
`);
console.log(`Extreme Value Performance Benchmarks`);
console.log(`Warmup runs: ${warmupCount}, Measurement runs: ${measureCount}`);
console.log(`Verbose mode: ${verbose ? 'enabled' : 'disabled'}`);
console.log(`Output JSON: ${outputJson ? 'enabled' : 'disabled'}`);
console.log(`\nStarting benchmarks...`);

// Create output directory for benchmark results
const resultsDir = path.resolve(__dirname, 'benchmark-results');
if (!fs.existsSync(resultsDir)) {
  fs.mkdirSync(resultsDir, { recursive: true });
}

// Run a basic benchmark to verify it works
let results;
try {
  console.log('\nRunning simple benchmark for gradient aggregation...');
  
  // Create a benchmark instance
  const benchmark = new ExtremeValueBenchmark({
    verbose,
    warmupRuns: warmupCount,
    measureRuns: measureCount
  });
  
  // Generate test gradients with extreme values
  const gradientSets = [];
  for (let i = 0; i < 5; i++) {
    const gradients = [];
    for (let j = 0; j < 4; j++) {
      gradients.push(Array(100).fill().map((_, k) => {
        if (j === 0) return Math.random() * 2 - 1; // Normal values
        if (j === 1) return (Math.random() * 2 - 1) * 1e-15; // Small values
        if (j === 2) return (Math.random() * 2 - 1) * 1e15; // Large values
        // Mixed values
        const magnitude = k % 3 === 0 ? 1e15 : (k % 3 === 1 ? 1e-15 : 1);
        return (Math.random() * 2 - 1) * magnitude;
      }));
    }
    gradientSets.push(gradients);
  }
  
  // Compare standard summation vs Kahan summation
  benchmark.compare('gradient_aggregation', {
    standard: (gradients) => {
      // Standard summation
      const result = Array(gradients[0].length).fill(0);
      for (const grad of gradients) {
        for (let i = 0; i < grad.length; i++) {
          result[i] += grad[i];
        }
      }
      return result;
    },
    kahan: (gradients) => {
      // Kahan summation
      const result = Array(gradients[0].length).fill(0);
      const compensation = Array(gradients[0].length).fill(0);
      
      for (const grad of gradients) {
        for (let i = 0; i < grad.length; i++) {
          const y = grad[i] - compensation[i];
          const t = result[i] + y;
          compensation[i] = (t - result[i]) - y;
          result[i] = t;
        }
      }
      return result;
    }
  }, gradientSets);
  
  // Benchmark basic vector operations
  console.log('\nRunning basic vector operations benchmark...');
  
  // Generate simple test vectors
  const vectors = [];
  for (let i = 0; i < 5; i++) {
    vectors.push(Array(10).fill().map(() => Math.random() * 2 - 1));
  }
  
  // Simple vector addition
  benchmark.run('vector_addition', (a, b) => {
    return a.map((val, idx) => val + b[idx]);
  }, [[vectors[0], vectors[1]], [vectors[2], vectors[3]]]);
  
  results = benchmark.results;
} catch (error) {
  console.error('Error running benchmarks:', error);
  results = { error: error.message };
}

// Output results
if (outputJson) {
  const outputFile = path.resolve(resultsDir, `extreme-benchmarks-${new Date().toISOString().replace(/:/g, '-')}.json`);
  fs.writeFileSync(outputFile, JSON.stringify(results, null, 2));
  console.log(`\nBenchmark results saved to ${outputFile}`);
}

// Print summary table
console.log('\nBenchmark Summary:');
console.log('=================');

// Function to format ops/sec with appropriate unit
function formatOpsPerSec(opsPerSec) {
  if (opsPerSec >= 1000) {
    return `${(opsPerSec / 1000).toFixed(2)} K/s`;
  }
  return `${opsPerSec.toFixed(2)}/s`;
}

if (results.error) {
  console.log(`Error: ${results.error}`);
} else {
  // Print simple summary table
  console.log('Benchmark | Ops/Sec | Validation Errors');
  console.log('----------|---------|------------------');
  
  for (const [name, result] of Object.entries(results)) {
    if (result.stats && result.opsPerSecond !== undefined) {
      console.log(`${name} | ${formatOpsPerSec(result.opsPerSecond)} | ${result.validationErrors || 0}`);
    }
  }
  
  // For comparison results, handle them specially
  const comparisonResults = Object.entries(results).filter(([name, _]) => name.includes('gradient_aggregation'));
  if (comparisonResults.length > 0) {
    console.log('\nComparison Results:');
    for (const [name, result] of comparisonResults) {
      if (result.results) {
        console.log(`\n${name}:`);
        console.log('Implementation | Ops/Sec | Relative Performance');
        console.log('--------------|---------|---------------------');
        for (const impl of result.results) {
          console.log(`${impl.implementation} | ${formatOpsPerSec(impl.opsPerSecond)} | ${impl.relativeThroughput.toFixed(2)}x`);
        }
      }
    }
  }
}

console.log('\nBenchmarks completed successfully!');