/**
 * PrimeOS JavaScript Library - Storage Integration Test Runner
 * Runs the Matrix and Neural integration tests for the storage module
 * in both Node.js and browser environments
 */

const { exec } = require('child_process');
const path = require('path');
const fs = require('fs');

// Node test files
const nodeTestFiles = [
  'tests/storage/matrix-storage-integration.js',
  'tests/storage/neural-storage-integration.js',
  'tests/storage/storage-provider-tests.js'
];

// Test browser integration separately
const runNodeTests = async () => {
  return new Promise((resolve, reject) => {
    // Validate test files exist
    for (const file of nodeTestFiles) {
      if (!fs.existsSync(path.join(__dirname, '../../', file))) {
        console.error(`Test file not found: ${file}`);
        process.exit(1);
      }
    }

    // Build the Jest command
    const command = `jest ${nodeTestFiles.join(' ')} --verbose`;

    // Run the tests
    console.log('Running Node.js storage integration tests...');
    console.log(`Command: ${command}`);

    const child = exec(command, {
      cwd: path.join(__dirname, '../../')
    });

    // Forward output
    child.stdout.pipe(process.stdout);
    child.stderr.pipe(process.stderr);

    // Handle completion
    child.on('exit', (code) => {
      if (code === 0) {
        console.log('Node.js storage integration tests completed successfully!');
        resolve(code);
      } else {
        console.error(`Node.js storage integration tests failed with code ${code}`);
        reject(code);
      }
    });
  });
};

// Run browser tests
const runBrowserTests = async () => {
  return new Promise((resolve, reject) => {
    console.log('Running browser storage integration tests...');
    
    // Use the browser test runner script
    const browserTestScript = path.join(__dirname, 'run-browser-tests.js');
    
    if (!fs.existsSync(browserTestScript)) {
      console.error('Browser test runner script not found');
      process.exit(1);
    }
    
    const child = exec(`node ${browserTestScript}`, {
      cwd: path.join(__dirname, '../../')
    });
    
    // Forward output
    child.stdout.pipe(process.stdout);
    child.stderr.pipe(process.stderr);
    
    // Handle completion
    child.on('exit', (code) => {
      if (code === 0) {
        console.log('Browser storage integration tests completed successfully!');
        resolve(code);
      } else {
        console.error(`Browser storage integration tests failed with code ${code}`);
        reject(code);
      }
    });
  });
};

// Run all tests
async function runAllTests() {
  try {
    // First run Node.js tests
    await runNodeTests();
    
    // Then run browser tests
    await runBrowserTests();
    
    console.log('\n✅ All storage tests passed in both Node.js and browser environments!');
    process.exit(0);
  } catch (code) {
    console.error('\n❌ Some storage tests failed!');
    process.exit(code);
  }
}

// Start the test process
runAllTests();