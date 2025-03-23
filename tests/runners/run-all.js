#!/usr/bin/env node

/**
 * PrimeOS Comprehensive Test Runner
 * 
 * This script runs all tests in the proper order, batching them as needed to manage
 * resources efficiently. It coordinates unit, integration, extreme, and performance tests.
 */

const { exec, execSync } = require('child_process');
const path = require('path');
const fs = require('fs');

// Configuration
const config = {
  // Test types and their Jest configuration
  testTypes: [
    {
      name: 'Unit Tests',
      dir: 'unit',
      pattern: 'tests/unit/**/*.test.js',
      memoryLimit: 4096,
      timeout: 60000,
      workers: 4
    },
    {
      name: 'Integration Tests',
      dir: 'integration',
      pattern: 'tests/integration/**/*.test.js',
      memoryLimit: 6144,
      timeout: 90000,
      workers: 2
    },
    {
      name: 'Extreme Tests',
      dir: 'extreme',
      pattern: 'tests/extreme/**/*.test.js',
      memoryLimit: 8192,
      timeout: 120000,
      workers: 1
    },
    {
      name: 'Performance Tests',
      dir: 'performance',
      pattern: 'tests/performance/**/*.test.js',
      memoryLimit: 6144,
      timeout: 180000,
      workers: 1
    }
  ],
  
  // Results directory for test output
  resultsDir: path.resolve(__dirname, '../test-results')
};

// Ensure results directory exists
if (!fs.existsSync(config.resultsDir)) {
  fs.mkdirSync(config.resultsDir, { recursive: true });
}

/**
 * Run tests of a specific type
 * 
 * @param {Object} testType - Test type configuration
 * @returns {Promise<Object>} - Test results
 */
function runTests(testType) {
  return new Promise((resolve, reject) => {
    console.log(`\n=== Running ${testType.name} ===`);
    
    // Build Jest command
    const command = `node --max-old-space-size=${testType.memoryLimit} ./node_modules/.bin/jest --config build/jest.config.js --testMatch="${testType.pattern}" --testTimeout=${testType.timeout} --maxWorkers=${testType.workers} --json`;
    
    console.log(`Command: ${command}\n`);
    
    // Execute command
    exec(command, { maxBuffer: 10 * 1024 * 1024 }, (error, stdout, stderr) => {
      if (stderr) {
        console.error(stderr);
      }
      
      try {
        // Try to parse test results
        const results = JSON.parse(stdout);
        
        // Write results to file
        const resultsPath = path.join(config.resultsDir, `${testType.dir}-results.json`);
        fs.writeFileSync(resultsPath, JSON.stringify(results, null, 2));
        
        // Log summary
        console.log(`\n${testType.name} Summary:`);
        console.log(`- Tests: ${results.numTotalTests}`);
        console.log(`- Passed: ${results.numPassedTests}`);
        console.log(`- Failed: ${results.numFailedTests}`);
        console.log(`- Pending: ${results.numPendingTests}`);
        
        if (results.numFailedTests > 0) {
          console.log('\nFailed Tests:');
          results.testResults.forEach(testFile => {
            if (testFile.numFailingTests > 0) {
              console.log(`- ${testFile.name}`);
              testFile.assertionResults
                .filter(assertion => assertion.status === 'failed')
                .forEach(assertion => {
                  console.log(`  • ${assertion.fullName}: ${assertion.failureMessages[0]}`);
                });
            }
          });
        }
        
        resolve({
          type: testType.name,
          passed: results.numPassedTests,
          failed: results.numFailedTests,
          pending: results.numPendingTests,
          total: results.numTotalTests
        });
      } catch (e) {
        console.error(`Error parsing test results: ${e.message}`);
        reject(error || new Error('Could not parse test results'));
      }
    });
  });
}

/**
 * Run all test types in sequence
 */
async function runAllTests() {
  console.log('=== PrimeOS Comprehensive Test Runner ===');
  console.log(`Start time: ${new Date().toISOString()}`);
  
  const allResults = [];
  let allPassed = true;
  
  // Process command line arguments
  const args = process.argv.slice(2);
  const specificTests = args.length > 0 ? args : null;
  
  // Filter test types to run if specified
  const testTypesToRun = specificTests 
    ? config.testTypes.filter(type => 
        specificTests.some(arg => type.dir.toLowerCase().includes(arg.toLowerCase())))
    : config.testTypes;
  
  if (specificTests && testTypesToRun.length === 0) {
    console.error(`No test types found matching: ${specificTests.join(', ')}`);
    console.log('Available test types:');
    config.testTypes.forEach(type => {
      console.log(`- ${type.name} (${type.dir})`);
    });
    process.exit(1);
  }
  
  try {
    // Run each test type in sequence
    for (const testType of testTypesToRun) {
      try {
        // Attempt to run tests for this type
        const result = await runTests(testType);
        allResults.push(result);
        
        // Check if any tests failed
        if (result.failed > 0) {
          allPassed = false;
        }
      } catch (error) {
        console.error(`Error running ${testType.name}: ${error.message}`);
        allResults.push({
          type: testType.name,
          passed: 0,
          failed: 1,
          pending: 0,
          total: 0,
          error: error.message
        });
        allPassed = false;
      }
      
      // Clear memory between test types
      try {
        global.gc && global.gc();
      } catch (e) {
        // GC not available
      }
    }
    
    // Generate consolidated report
    const consolidated = {
      timestamp: new Date().toISOString(),
      summary: {
        passed: allResults.reduce((sum, result) => sum + result.passed, 0),
        failed: allResults.reduce((sum, result) => sum + result.failed, 0),
        pending: allResults.reduce((sum, result) => sum + result.pending, 0),
        total: allResults.reduce((sum, result) => sum + result.total, 0),
        allPassed
      },
      testTypes: allResults
    };
    
    // Write consolidated results
    fs.writeFileSync(
      path.join(config.resultsDir, 'consolidated-results.json'),
      JSON.stringify(consolidated, null, 2)
    );
    
    // Output final summary
    console.log('\n=== Overall Test Summary ===');
    allResults.forEach(result => {
      const status = result.failed === 0 ? '✅ PASS' : '❌ FAIL';
      console.log(`${status} - ${result.type}: ${result.passed}/${result.total} passed, ${result.failed} failed, ${result.pending} pending`);
    });
    
    console.log('\nTotal Results:');
    console.log(`- Tests: ${consolidated.summary.total}`);
    console.log(`- Passed: ${consolidated.summary.passed}`);
    console.log(`- Failed: ${consolidated.summary.failed}`);
    console.log(`- Pending: ${consolidated.summary.pending}`);
    console.log(`\nOverall Status: ${allPassed ? '✅ PASS' : '❌ FAIL'}`);
    console.log(`End time: ${new Date().toISOString()}`);
    
    // Exit with appropriate code
    process.exit(allPassed ? 0 : 1);
  } catch (error) {
    console.error('Unexpected error in test runner:', error);
    process.exit(1);
  }
}

// Run all tests
runAllTests();