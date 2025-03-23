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
      pattern: 'unit',
      memoryLimit: 4096,
      timeout: 60000,
      workers: 4
    },
    {
      name: 'Integration Tests',
      dir: 'integration',
      pattern: 'integration',
      memoryLimit: 6144,
      timeout: 90000,
      workers: 2
    },
    {
      name: 'Extreme Tests',
      dir: 'extreme',
      pattern: 'extreme',
      memoryLimit: 8192,
      timeout: 120000,
      workers: 1
    },
    {
      name: 'Performance Tests',
      dir: 'performance',
      pattern: 'performance',
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
    
    // Build Jest command - fixed to use correct testPathPattern and output format
    const command = `node --max-old-space-size=${testType.memoryLimit} ./node_modules/.bin/jest --config build/jest.config.js --testPathPattern="${testType.pattern}" --testTimeout=${testType.timeout} --maxWorkers=${testType.workers}`;
    
    console.log(`Command: ${command}\n`);
    
    // Execute command
    exec(command, { maxBuffer: 100 * 1024 * 1024 }, (error, stdout, stderr) => {
      if (stderr) {
        console.error(stderr);
      }
      
      try {
        // Extract the JSON part from stdout which might contain other output
        let jsonStartIdx = stdout.indexOf('{');
        let jsonEndIdx = stdout.lastIndexOf('}');
        let jsonOutput = '';
        
        if (jsonStartIdx >= 0 && jsonEndIdx >= 0 && jsonEndIdx > jsonStartIdx) {
          jsonOutput = stdout.substring(jsonStartIdx, jsonEndIdx + 1);
          
          // Try to parse test results
          const results = JSON.parse(jsonOutput);
          
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
        } else {
          // If we can't find valid JSON, extract test summary from text output
          const testSummaryMatch = stdout.match(/Test Suites:\s+(\d+)\s+failed,\s+(\d+)\s+passed,\s+(\d+)\s+total/);
          
          if (testSummaryMatch) {
            const [, failedSuites, passedSuites, totalSuites] = testSummaryMatch;
            
            // Also extract tests count
            const testCountMatch = stdout.match(/Tests:\s+(\d+)\s+failed,\s+(\d+)\s+skipped,\s+(\d+)\s+passed,\s+(\d+)\s+total/);
            let failedTests = 0, skippedTests = 0, passedTests = 0, totalTests = 0;
            
            if (testCountMatch) {
              [, failedTests, skippedTests, passedTests, totalTests] = testCountMatch;
            }
            
            console.log(`\n${testType.name} Summary (parsed from stdout):`);
            console.log(`- Test Suites: ${failedSuites} failed, ${passedSuites} passed, ${totalSuites} total`);
            console.log(`- Tests: ${totalTests} total, ${passedTests} passed, ${failedTests} failed, ${skippedTests} skipped`);
            
            // Create a simulated results object
            const simulatedResults = {
              numFailedTestSuites: parseInt(failedSuites),
              numPassedTestSuites: parseInt(passedSuites),
              numTotalTestSuites: parseInt(totalSuites),
              numTotalTests: parseInt(totalTests),
              numPassedTests: parseInt(passedTests),
              numFailedTests: parseInt(failedTests),
              numPendingTests: parseInt(skippedTests),
              testResults: []
            };
            
            // Write simulated results to file
            const resultsPath = path.join(config.resultsDir, `${testType.dir}-results.json`);
            fs.writeFileSync(resultsPath, JSON.stringify(simulatedResults, null, 2));
            
            resolve({
              type: testType.name,
              passed: parseInt(passedTests),
              failed: parseInt(failedTests),
              pending: parseInt(skippedTests),
              total: parseInt(totalTests)
            });
          } else {
            // If we still can't parse anything useful
            console.error('Could not parse test results in any format.');
            console.error('Test output:', stdout.substring(0, 1000) + '...');
            
            resolve({
              type: testType.name,
              passed: 0,
              failed: 1,
              pending: 0,
              total: 0,
              error: 'Could not parse test results'
            });
          }
        }
      } catch (e) {
        console.error(`Error parsing test results: ${e.message}`);
        console.error(e.stack);
        
        // Try to extract simple test summary from text output
        const testSummaryMatch = stdout.match(/Test Suites:\s+(\d+)\s+failed,\s+(\d+)\s+passed,\s+(\d+)\s+total/);
        
        if (testSummaryMatch) {
          const [, failedSuites, passedSuites, totalSuites] = testSummaryMatch;
          console.log(`\n${testType.name} Summary (parsed from stdout after JSON parse error):`);
          console.log(`- Test Suites: ${failedSuites} failed, ${passedSuites} passed, ${totalSuites} total`);
          
          resolve({
            type: testType.name,
            passed: parseInt(passedSuites),
            failed: parseInt(failedSuites),
            pending: 0,
            total: parseInt(totalSuites),
            error: e.message
          });
        } else {
          reject(error || new Error('Could not parse test results: ' + e.message));
        }
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