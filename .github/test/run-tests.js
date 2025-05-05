/**
 * Run all tests for the Repository API and MCP Server
 */

const { spawn } = require('child_process');
const path = require('path');

// Paths to the test files
const API_TEST_PATH = path.resolve(__dirname, 'api-test.js');
const MCP_TEST_PATH = path.resolve(__dirname, '../entrypoints/mcp/test/mcp-test.js');
const END_TO_END_TEST_PATH = path.resolve(__dirname, 'end-to-end-test.js');

/**
 * Run all tests
 */
async function runAllTests() {
  console.log('=== Running All Repository API Tests ===\n');
  
  // Run the API tests
  console.log('Running API Tests...');
  await runTest(API_TEST_PATH);
  
  console.log('\n=== API Tests Completed ===\n');
  
  // Run the MCP server tests
  console.log('Running MCP Server Tests...');
  await runTest(MCP_TEST_PATH);
  
  console.log('\n=== MCP Server Tests Completed ===\n');
  
  // Run the end-to-end tests
  console.log('Running End-to-End Tests...');
  await runTest(END_TO_END_TEST_PATH);
  
  console.log('\n=== End-to-End Tests Completed ===\n');
  
  console.log('All tests completed!');
}

/**
 * Run a test file
 * 
 * @param {string} testPath - The path to the test file
 * @returns {Promise<void>} - A promise that resolves when the test completes
 */
function runTest(testPath) {
  return new Promise((resolve, reject) => {
    const test = spawn('node', [testPath], { stdio: 'inherit' });
    
    test.on('close', code => {
      if (code === 0) {
        resolve();
      } else {
        reject(new Error(`Test exited with code ${code}`));
      }
    });
    
    test.on('error', error => {
      reject(error);
    });
  });
}

// Run all tests
runAllTests().catch(error => {
  console.error('Tests failed:', error);
  process.exit(1);
});
