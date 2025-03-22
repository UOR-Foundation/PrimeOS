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
const Prime = require('./src/mathematics.js');

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

// Run custom benchmarks or standard benchmarks
let results;
if (runCustom) {
  console.log('\nRunning custom extreme value benchmarks...');
  
  // Create a benchmark instance
  const benchmark = new ExtremeValueBenchmark({
    verbose,
    warmupRuns: warmupCount,
    measureRuns: measureCount
  });
  
  // Define custom benchmarks
  
  // 1. Matrix inversion with varying magnitudes
  console.log('\nRunning matrix inversion benchmarks with varying magnitudes...');
  
  // Generate test matrices with different extreme value patterns
  const matrices = [
    // Normal matrix
    Array(10).fill().map(() => Array(10).fill().map(() => Math.random() * 2 - 1)),
    
    // Small values matrix
    Array(10).fill().map(() => Array(10).fill().map(() => (Math.random() * 2 - 1) * 1e-15)),
    
    // Large values matrix
    Array(10).fill().map(() => Array(10).fill().map(() => (Math.random() * 2 - 1) * 1e15)),
    
    // Mixed values matrix
    Array(10).fill().map((_, i) => Array(10).fill().map((_, j) => {
      const magnitude = (i + j) % 3 === 0 ? 1e15 : ((i + j) % 3 === 1 ? 1e-15 : 1);
      return (Math.random() * 2 - 1) * magnitude;
    }))
  ];
  
  // Convert raw arrays to Matrix objects
  const matrixObjects = matrices.map(m => new Prime.Matrix(m));
  
  // Run inversion benchmark
  benchmark.run('matrix_inversion_varying_magnitudes', matrix => {
    return Prime.invert(matrix);
  }, matrixObjects.map(m => [m]));
  
  // 2. Gradient aggregation with Kahan summation vs standard summation
  console.log('\nRunning gradient aggregation benchmarks with Kahan vs standard summation...');
  
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
  
  // 3. Vector operations with extreme values
  console.log('\nRunning vector operation benchmarks with extreme values...');
  
  // Generate test vectors
  const vectors = ExtremeValueBenchmark.generateExtremeValues('vector', {
    count: 10,
    dimension: 1000
  });
  
  // Benchmark vector norm calculation
  benchmark.run('vector_norm_extreme_values', vector => {
    return Prime.norm(vector);
  }, vectors.map(v => [v]));
  
  // Benchmark vector dot product
  const vectorPairs = [];
  for (let i = 0; i < vectors.length; i += 2) {
    if (i + 1 < vectors.length) {
      vectorPairs.push([vectors[i], vectors[i + 1]]);
    }
  }
  
  benchmark.run('vector_dot_product_extreme_values', (v1, v2) => {
    return Prime.dot(v1, v2);
  }, vectorPairs);
  
  // 4. Distributed parameter synchronization with extreme values
  console.log('\nRunning parameter synchronization benchmarks with extreme values...');
  
  // Generate parameter sets with varying magnitudes
  const paramSets = [];
  for (let i = 0; i < 5; i++) {
    const magnitude = i === 0 ? 1 : (i === 1 ? 1e-15 : (i === 2 ? 1e15 : (i === 3 ? 1e10 : 1e-10)));
    
    paramSets.push({
      local: {
        weights: Array(10).fill().map(() => Array(10).fill().map(() => 
          (Math.random() * 2 - 1) * magnitude
        )),
        biases: Array(10).fill().map(() => (Math.random() * 2 - 1) * magnitude)
      },
      global: {
        weights: Array(10).fill().map(() => Array(10).fill().map(() => 
          (Math.random() * 2 - 1) * magnitude * 0.9 // Slight difference
        )),
        biases: Array(10).fill().map(() => (Math.random() * 2 - 1) * magnitude * 0.9)
      }
    });
  }
  
  // Define a simple version of the synchronization coherence check
  function checkSynchronizationCoherence(local, global, tolerance = 1e-8) {
    // Check weights
    for (let i = 0; i < local.weights.length; i++) {
      for (let j = 0; j < local.weights[i].length; j++) {
        const diff = Math.abs(local.weights[i][j] - global.weights[i][j]);
        const maxMagnitude = Math.max(Math.abs(local.weights[i][j]), Math.abs(global.weights[i][j]));
        const adaptiveTolerance = tolerance * (1 + maxMagnitude * Number.EPSILON * 1000);
        
        if (diff > adaptiveTolerance) {
          return false;
        }
      }
    }
    
    // Check biases
    for (let i = 0; i < local.biases.length; i++) {
      const diff = Math.abs(local.biases[i] - global.biases[i]);
      const maxMagnitude = Math.max(Math.abs(local.biases[i]), Math.abs(global.biases[i]));
      const adaptiveTolerance = tolerance * (1 + maxMagnitude * Number.EPSILON * 1000);
      
      if (diff > adaptiveTolerance) {
        return false;
      }
    }
    
    return true;
  }
  
  // Compare fixed vs adaptive tolerance
  benchmark.compare('sync_coherence_check', {
    fixed_tolerance: (params) => {
      return checkSynchronizationCoherence(params.local, params.global, 1e-8);
    },
    adaptive_tolerance: (params) => {
      // Adaptive base tolerance based on matrix/vector size
      const totalElements = params.local.weights.length * params.local.weights[0].length + params.local.biases.length;
      const baseTolerance = 1e-8 * Math.sqrt(totalElements);
      
      return checkSynchronizationCoherence(params.local, params.global, baseTolerance);
    }
  }, paramSets);
  
  results = benchmark.results;
} else {
  // Run standard benchmark suite
  results = runExampleBenchmarks(verbose);
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

// Collect all benchmark results
const allResults = [];
for (const category in results) {
  for (const [name, result] of Object.entries(results[category])) {
    allResults.push({
      category,
      name,
      median: result.stats.median,
      opsPerSec: result.opsPerSecond,
      validationErrors: result.validationErrors || 0
    });
  }
}

// Sort by category and name
allResults.sort((a, b) => {
  if (a.category !== b.category) {
    return a.category.localeCompare(b.category);
  }
  return a.name.localeCompare(b.name);
});

// Print table
console.log('Category | Name | Median Time | Ops/Sec | Validation Errors');
console.log('---------|------|-------------|---------|------------------');
for (const result of allResults) {
  console.log(`${result.category} | ${result.name} | ${result.median.toFixed(2)}ms | ${formatOpsPerSec(result.opsPerSec)} | ${result.validationErrors}`);
}

console.log('\nBenchmarks completed successfully!');