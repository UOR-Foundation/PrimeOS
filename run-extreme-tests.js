#!/usr/bin/env node

/**
 * Extreme Conditions Test Runner for PrimeOS
 * This script runs the extreme condition tests in batches with memory profiling and extended timeout
 * to address memory consumption issues in extreme-conditions-tests.js
 */

const jest = require('jest');
const path = require('path');
const fs = require('fs');
const { execSync } = require('child_process');

// Base configuration options
const baseOptions = {
  // Increase test timeout for complex calculations
  testTimeout: 120000,
  // Configure specific environment variables for testing
  setupFiles: ['./test-setup.js'],
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
    EXTREME_TESTING: true
  }
};

// Define test batches for extreme-conditions-tests.js to manage memory consumption
// Each batch focuses on a specific test suite to limit memory usage
const testBatches = [
  {
    name: 'basic',
    description: 'Basic extreme precision tests',
    testMatch: ['**/extreme-conditions-basic-test.js'],
    outputFile: 'extreme-basic-report.json'
  },
  {
    name: 'rna-folding',
    description: 'RNA Folding simulation tests',
    testRegex: 'extreme-conditions-tests\\.js',
    testNamePattern: 'Extreme Conditions Handling.*RNA.*'
  },
  {
    name: 'high-dimension',
    description: 'High-Dimension Fiber Algebra tests',
    testRegex: 'extreme-conditions-tests\\.js',
    testNamePattern: 'Extreme Conditions Handling.*High-Dimension Fiber Algebra.*'
  },
  {
    name: 'coherence-gradient',
    description: 'Coherence-Gradient Descent tests',
    testRegex: 'extreme-conditions-tests\\.js',
    testNamePattern: 'Extreme Conditions Handling.*Coherence-Gradient Descent.*'
  },
  {
    name: 'numerical-propagation',
    description: 'Numerical Propagation Analysis tests',
    testRegex: 'extreme-conditions-tests\\.js',
    testNamePattern: 'Extreme Conditions Handling.*Numerical Propagation Analysis.*'
  }
];

// Create test setup file if it doesn't exist
const setupFile = path.resolve(__dirname, 'test-setup.js');
if (!fs.existsSync(setupFile)) {
  const setupContent = `// Test setup for extreme conditions
process.env.NODE_ENV = 'test';
process.env.EXTENDED_PRECISION = 'true';
process.env.EXTREME_TESTING = 'true';

// Configure global Math helpers if needed
if (!Math.nextafter) {
  // Add nextafter implementation for ULP-based testing
  // This is a simplified implementation for testing
  Math.nextafter = function(x, y) {
    if (x === y) return y;
    
    // Convert to IEEE-754 representation
    const buffer = new ArrayBuffer(8);
    const bytes = new Uint8Array(buffer);
    const doubles = new Float64Array(buffer);
    
    doubles[0] = x;
    
    // Increment or decrement the bit pattern based on direction
    const sign = y > x ? 1 : -1;
    
    // Handle special cases
    if (!Number.isFinite(x)) return x;
    
    if (x === 0) {
      // Handle positive/negative zero
      if (sign > 0) {
        return Number.MIN_VALUE;
      } else {
        return -Number.MIN_VALUE;
      }
    }
    
    // Increment or decrement the bit pattern
    let hiByte, loByte;
    if (sign > 0) {
      // Next number toward y (where y > x)
      loByte = bytes[0] + 1;
      hiByte = bytes[1];
      if (loByte > 255) {
        loByte = 0;
        hiByte++;
        if (hiByte > 255) {
          // Carry to higher bytes
          let i = 2;
          while (i < 8 && bytes[i] === 255) {
            bytes[i] = 0;
            i++;
          }
          if (i < 8) bytes[i]++;
        } else {
          bytes[1] = hiByte;
        }
      }
      bytes[0] = loByte;
    } else {
      // Next number toward y (where y < x)
      loByte = bytes[0];
      if (loByte === 0) {
        loByte = 255;
        hiByte = bytes[1] - 1;
        if (hiByte < 0) {
          // Borrow from higher bytes
          let i = 2;
          while (i < 8 && bytes[i] === 0) {
            bytes[i] = 255;
            i++;
          }
          if (i < 8) bytes[i]--;
        } else {
          bytes[1] = hiByte;
        }
      } else {
        bytes[0] = loByte - 1;
      }
    }
    
    return doubles[0];
  };
}

// Enhanced Kahan summation for better numerical stability
if (!Math.kahanSum) {
  Math.kahanSum = function(values) {
    let sum = 0;
    let compensation = 0;
    
    for (let i = 0; i < values.length; i++) {
      const y = values[i] - compensation;
      const t = sum + y;
      compensation = (t - sum) - y;
      sum = t;
    }
    
    return sum;
  };
}

// Augment console with memory usage reporting
const originalLog = console.log;
console.log = function(...args) {
  originalLog.apply(console, args);
  if (process.env.EXTREME_TESTING === 'true' && args[0] && typeof args[0] === 'string' && 
      args[0].includes('MEMORY')) {
    const used = process.memoryUsage();
    originalLog('Memory usage:');
    for (let key in used) {
      originalLog(\`  \${key}: \${Math.round(used[key] / 1024 / 1024 * 100) / 100} MB\`);
    }
  }
};

// Add global garbage collection request function
global.requestGC = function() {
  if (global.gc) {
    global.gc();
    console.log('Manual garbage collection performed');
  } else {
    console.log('Garbage collection not available. Run node with --expose-gc flag');
  }
};
`;
  fs.writeFileSync(setupFile, setupContent);
}

// Create output directory for test results
const resultsDir = path.resolve(__dirname, 'test-results');
if (!fs.existsSync(resultsDir)) {
  fs.mkdirSync(resultsDir, { recursive: true });
}

// Function to run a batch of tests
async function runTestBatch(batch) {
  console.log(`\n=== Starting batch: ${batch.name} - ${batch.description} ===`);
  console.log('Testing with extended precision and memory profiling enabled');
  
  const options = { ...baseOptions };
  
  // Configure test matching
  if (batch.testMatch) {
    options.testMatch = batch.testMatch;
  }
  if (batch.testRegex) {
    options.testRegex = batch.testRegex;
  }
  if (batch.testNamePattern) {
    options.testNamePattern = batch.testNamePattern;
  }
  
  // Initial memory usage
  console.log('MEMORY: Initial memory snapshot for batch');
  
  // Run the tests
  try {
    const { results } = await jest.runCLI(options, [__dirname]);
    
    console.log(`Batch ${batch.name} completed`);
    console.log(`Tests: ${results.numTotalTests}, Passed: ${results.numPassedTests}, Failed: ${results.numFailedTests}`);
    
    // Save detailed test results
    const outputFile = batch.outputFile || `extreme-${batch.name}-report.json`;
    fs.writeFileSync(
      path.resolve(resultsDir, outputFile),
      JSON.stringify(results, null, 2)
    );
    
    // Log memory usage
    console.log(`MEMORY: Final memory snapshot for batch ${batch.name}`);
    
    return {
      name: batch.name,
      description: batch.description,
      success: results.success,
      totalTests: results.numTotalTests,
      passedTests: results.numPassedTests,
      failedTests: results.numFailedTests
    };
  } catch (error) {
    console.error(`Error running batch ${batch.name}:`, error);
    return {
      name: batch.name,
      description: batch.description,
      success: false,
      error: error.message
    };
  } finally {
    // Force garbage collection between batches if possible
    try {
      if (global.gc) {
        global.gc();
        console.log(`Forced garbage collection after batch ${batch.name}`);
      } else {
        console.log('Note: Run with --expose-gc flag to enable garbage collection between batches');
      }
    } catch (e) {
      console.log('Unable to force garbage collection');
    }
    
    // Small delay to allow memory to be reclaimed
    await new Promise(resolve => setTimeout(resolve, 1000));
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
    ? testBatches.filter(batch => batch.name === specificBatch)
    : testBatches;
  
  if (specificBatch && batchesToRun.length === 0) {
    console.error(`No batch found with name: ${specificBatch}`);
    console.log('Available batches:');
    testBatches.forEach(batch => {
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
  allResults.forEach(result => {
    const status = result.success ? '✅ PASS' : '❌ FAIL';
    console.log(`${status} - ${result.name}: ${result.description}`);
    if (result.totalTests !== undefined) {
      console.log(`  Tests: ${result.totalTests}, Passed: ${result.passedTests}, Failed: ${result.failedTests}`);
    }
    if (result.error) {
      console.log(`  Error: ${result.error}`);
    }
  });
  
  console.log('\nTotal Results:');
  console.log(`Tests: ${totalTests}, Passed: ${totalPassed}, Failed: ${totalFailed}`);
  
  // Save consolidated results
  fs.writeFileSync(
    path.resolve(resultsDir, 'extreme-test-consolidated-report.json'),
    JSON.stringify({
      timestamp: new Date().toISOString(),
      summary: {
        totalTests,
        passedTests: totalPassed,
        failedTests: totalFailed,
        allSuccessful
      },
      batches: allResults
    }, null, 2)
  );
  
  return allSuccessful;
}

// Run the batched test suite
runAllBatches()
  .then(success => {
    process.exit(success ? 0 : 1);
  })
  .catch(error => {
    console.error('Unhandled error in test execution:', error);
    process.exit(1);
  });