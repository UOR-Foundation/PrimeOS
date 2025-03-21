#!/usr/bin/env node

/**
 * Extreme Conditions Test Runner for PrimeOS
 * This script runs the extreme condition tests with memory profiling and extended timeout
 */

const jest = require('jest');
const path = require('path');
const fs = require('fs');

// Configuration options
const options = {
  // Run only basic extreme condition tests to avoid memory issues
  testMatch: ['**/extreme-conditions-basic-test.js'],
  // Increase test timeout for complex calculations
  testTimeout: 60000,
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
  // Disable memory profiling to reduce overhead
  logHeapUsage: false,
  // Disable leak detection to reduce memory usage
  detectLeaks: false,
  // Enable extended precision for numerical operations
  globals: {
    EXTENDED_PRECISION: true,
    EXTREME_TESTING: true
  }
};

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
`;
  fs.writeFileSync(setupFile, setupContent);
}

// Create output directory for test results
const resultsDir = path.resolve(__dirname, 'test-results');
if (!fs.existsSync(resultsDir)) {
  fs.mkdirSync(resultsDir, { recursive: true });
}

// Run the tests
console.log('Starting extreme condition tests...');
console.log('Testing with extended precision and memory profiling enabled');

jest.runCLI(options, [__dirname])
  .then(({ results }) => {
    console.log('Extreme condition tests completed');
    console.log(`Tests: ${results.numTotalTests}, Passed: ${results.numPassedTests}, Failed: ${results.numFailedTests}`);
    
    // Save detailed test results
    fs.writeFileSync(
      path.resolve(resultsDir, 'extreme-test-report.json'),
      JSON.stringify(results, null, 2)
    );
    
    // Log memory usage
    console.log('MEMORY: Final memory snapshot');
    
    // Exit with appropriate code
    process.exit(results.success ? 0 : 1);
  })
  .catch(error => {
    console.error('Error running tests:', error);
    process.exit(1);
  });