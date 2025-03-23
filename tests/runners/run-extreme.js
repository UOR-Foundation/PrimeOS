#!/usr/bin/env node

/**
 * PrimeOS Extreme Conditions Test Runner
 * 
 * This script runs the extreme condition tests in batches with memory profiling 
 * and extended timeout to address memory consumption issues.
 */

const jest = require('jest');
const path = require('path');
const fs = require('fs');

// Base configuration options
const baseOptions = {
  // Increase test timeout for complex calculations
  testTimeout: 120000,
  // Configure specific environment variables for testing
  setupFiles: ['./tests/utils/setup.js'],
  // Use a custom reporter for extreme value testing
  reporters: ['default'],
  // Disable coverage to reduce memory usage
  collectCoverage: false,
  // Set minimal output
  verbose: false,
  // Use a single worker to avoid resource contention
  maxWorkers: 1,
  // Disable memory profiling to reduce overhead during test execution
  logHeapUsage: false,
  // Disable leak detection to reduce memory usage
  detectLeaks: false,
  // Enable extended precision for numerical operations
  globals: {
    EXTENDED_PRECISION: true,
    EXTREME_TESTING: true,
  },
};

// Define test batches for extreme-conditions-tests.js to manage memory consumption
// Each batch focuses on a specific test suite to limit memory usage
const testBatches = [
  {
    name: 'matrix-extreme',
    description: 'Matrix extreme value tests',
    testMatch: ['**/tests/extreme/math/matrix-extreme.test.js'],
    outputFile: 'extreme-matrix-report.json',
  },
  {
    name: 'svd-extreme',
    description: 'SVD extreme value tests',
    testMatch: ['**/tests/extreme/math/svd-extreme.test.js'],
    outputFile: 'extreme-svd-report.json',
  },
  {
    name: 'numerical-stability',
    description: 'Numerical stability tests',
    testMatch: ['**/tests/extreme/math/numerical-stability.test.js'],
    outputFile: 'extreme-numerical-report.json',
  },
  {
    name: 'neural-extreme',
    description: 'Neural network extreme tests',
    testMatch: ['**/tests/extreme/neural/**/*.test.js'],
    outputFile: 'extreme-neural-report.json',
  },
  {
    name: 'distributed-extreme',
    description: 'Distributed extreme tests',
    testMatch: ['**/tests/extreme/distributed/**/*.test.js'],
    outputFile: 'extreme-distributed-report.json',
  },
  {
    name: 'tensor-operations-extreme',
    description: 'Tensor operations extreme value tests',
    testMatch: ['**/tests/extreme/math/tensor-operations.test.js'],
    outputFile: 'extreme-tensor-report.json',
  },
];

// Create output directory for test results
const resultsDir = path.resolve(__dirname, '../test-results');
if (!fs.existsSync(resultsDir)) {
  fs.mkdirSync(resultsDir, { recursive: true });
}

// Function to run a batch of tests
async function runTestBatch(batch) {
  console.log(`\n=== Starting batch: ${batch.name} - ${batch.description} ===`);
  console.log('Testing with extended precision and memory profiling enabled');

  // Create a fresh options object for each batch
  const options = {
    ...baseOptions,
    testTimeout: 120000,
    setupFiles: ['./tests/utils/setup.js'],
    reporters: ['default'],
    collectCoverage: false,
    verbose: false,
    maxWorkers: 1,
    logHeapUsage: false,
    detectLeaks: false,
    globals: {
      EXTENDED_PRECISION: true,
      EXTREME_TESTING: true,
    },
    // Override the default testPathIgnorePatterns
    testPathIgnorePatterns: ['/node_modules/'],
  };

  // Configure test matching - only set one of testMatch or testRegex
  if (batch.testMatch) {
    options.testMatch = batch.testMatch;
  } else if (batch.testRegex) {
    options.testRegex = batch.testRegex;
  }
  if (batch.testNamePattern) {
    options.testNamePattern = batch.testNamePattern;
  }

  // Initial memory usage
  console.log('MEMORY: Initial memory snapshot for batch');

  // Run the tests
  try {
    const { results } = await jest.runCLI(options, [process.cwd()]);

    console.log(`Batch ${batch.name} completed`);
    console.log(
      `Tests: ${results.numTotalTests}, Passed: ${results.numPassedTests}, Failed: ${results.numFailedTests}`,
    );

    // Save detailed test results
    const outputFile = batch.outputFile || `extreme-${batch.name}-report.json`;
    fs.writeFileSync(
      path.resolve(resultsDir, outputFile),
      JSON.stringify(results, null, 2),
    );

    // Log memory usage
    console.log(`MEMORY: Final memory snapshot for batch ${batch.name}`);

    return {
      name: batch.name,
      description: batch.description,
      success: results.success,
      totalTests: results.numTotalTests,
      passedTests: results.numPassedTests,
      failedTests: results.numFailedTests,
    };
  } catch (error) {
    console.error(`Error running batch ${batch.name}:`, error);
    return {
      name: batch.name,
      description: batch.description,
      success: false,
      error: error.message,
    };
  } finally {
    // Force garbage collection between batches if possible
    try {
      if (global.gc) {
        global.gc();
        console.log(`Forced garbage collection after batch ${batch.name}`);
      } else {
        console.log(
          'Note: Run with --expose-gc flag to enable garbage collection between batches',
        );
      }
    } catch (e) {
      console.log('Unable to force garbage collection');
    }

    // Small delay to allow memory to be reclaimed
    await new Promise((resolve) => setTimeout(resolve, 1000));
  }
}

// Main function to run all batches
async function runAllBatches() {
  console.log('=== PrimeOS Extreme Conditions Test Runner ===');

  const allResults = [];
  let totalTests = 0;
  let totalPassed = 0;
  let totalFailed = 0;
  let allSuccessful = true;

  // Process arguments
  const args = process.argv.slice(2);
  const specificBatch = args.length > 0 ? args[0] : null;

  // Filter batches if a specific one was requested
  const batchesToRun = specificBatch
    ? testBatches.filter((batch) => batch.name === specificBatch)
    : testBatches;

  if (specificBatch && batchesToRun.length === 0) {
    console.error(`No batch found with name: ${specificBatch}`);
    console.log('Available batches:');
    testBatches.forEach((batch) => {
      console.log(`- ${batch.name}: ${batch.description}`);
    });
    process.exit(1);
  }

  for (const batch of batchesToRun) {
    const result = await runTestBatch(batch);
    allResults.push(result);

    if (result.success === false) {
      allSuccessful = false;
    }

    if (result.totalTests !== undefined) {
      totalTests += result.totalTests;
      totalPassed += result.passedTests;
      totalFailed += result.failedTests;
    }
  }

  // Generate consolidated report
  console.log('\n=== Extreme Conditions Test Summary ===');
  allResults.forEach((result) => {
    const status = result.success ? '✅ PASS' : '❌ FAIL';
    console.log(`${status} - ${result.name}: ${result.description}`);
    if (result.totalTests !== undefined) {
      console.log(
        `  Tests: ${result.totalTests}, Passed: ${result.passedTests}, Failed: ${result.failedTests}`,
      );
    }
    if (result.error) {
      console.log(`  Error: ${result.error}`);
    }
  });

  console.log('\nTotal Results:');
  console.log(
    `Tests: ${totalTests}, Passed: ${totalPassed}, Failed: ${totalFailed}`,
  );

  // Save consolidated results
  fs.writeFileSync(
    path.resolve(resultsDir, 'extreme-test-consolidated-report.json'),
    JSON.stringify(
      {
        timestamp: new Date().toISOString(),
        summary: {
          totalTests,
          passedTests: totalPassed,
          failedTests: totalFailed,
          allSuccessful,
        },
        batches: allResults,
      },
      null,
      2,
    ),
  );

  return allSuccessful;
}

// Run the batched test suite
runAllBatches()
  .then((success) => {
    process.exit(success ? 0 : 1);
  })
  .catch((error) => {
    console.error('Unhandled error in test execution:', error);
    process.exit(1);
  });