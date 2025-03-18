/**
 * PrimeOS Reference Implementation SecureVault Browser Tests Runner
 * Runs SecureVault-specific tests in a headless browser using Puppeteer
 */

const puppeteer = require('puppeteer');
const http = require('http');
const path = require('path');
const handler = require('serve-handler');
const port = 3000;

// Start a local server to serve the test page
async function startServer() {
  const server = http.createServer((request, response) => {
    return handler(request, response, {
      public: path.resolve(__dirname),
      directoryListing: false
    });
  });
  
  await new Promise((resolve) => {
    server.listen(port, () => {
      console.log(`Server running at http://localhost:${port}`);
      resolve();
    });
  });
  
  return server;
}

// Run the SecureVault browser tests
async function runSecureVaultTests() {
  let server;
  let browser;
  let success = false;
  
  try {
    // Start the local server
    console.log('Starting local server for SecureVault browser tests...');
    server = await startServer();
    
    // Launch a headless browser
    console.log('Launching headless browser...');
    browser = await puppeteer.launch({
      headless: 'new',
      args: ['--no-sandbox', '--disable-setuid-sandbox']
    });
    
    // Open a new page
    const page = await browser.newPage();
    
    // Setup console logging from the browser to Node.js
    page.on('console', (msg) => {
      if (msg.type() === 'error') {
        console.error(`Browser console error: ${msg.text()}`);
      } else if (msg.type() === 'warning') {
        console.warn(`Browser console warning: ${msg.text()}`);
      } else {
        console.log(`Browser console: ${msg.text()}`);
      }
    });
    
    // Handle uncaught exceptions
    page.on('pageerror', (error) => {
      console.error(`Browser page error: ${error.message}`);
    });
    
    // Navigate to the test page
    console.log('Navigating to SecureVault test page...');
    await page.goto(`http://localhost:${port}/tests/browser-secure-vault-test.html`, {
      waitUntil: 'networkidle0',
      timeout: 30000
    });
    
    // Run the SecureVault tests
    console.log('Running SecureVault browser tests...');
    await page.evaluate(() => {
      return window._secureVaultTester.runTests();
    });
    
    // Wait for tests to complete
    await new Promise(resolve => setTimeout(resolve, 2000));
    
    // Get test results
    const testResults = await page.evaluate(() => window._svTestResults);
    
    console.log('\n========== SECURE VAULT BROWSER TEST RESULTS ==========');
    console.log(`Tests Passed: ${testResults.passed}`);
    console.log(`Tests Failed: ${testResults.failed}`);
    console.log('\nDetailed Logs:');
    testResults.logs.forEach(log => console.log(log));
    console.log('======================================================\n');
    
    // Determine if tests were successful
    success = testResults.failed === 0 && testResults.passed > 0;
    if (success) {
      console.log('✅ All SecureVault browser tests passed successfully!');
    } else {
      console.error('❌ Some SecureVault browser tests failed.');
    }
  } catch (error) {
    console.error('Error running SecureVault browser tests:', error);
  } finally {
    // Clean up
    if (browser) {
      await browser.close();
      console.log('Browser closed.');
    }
    if (server) {
      server.close();
      console.log('Server stopped.');
    }
    
    // Exit with appropriate code
    process.exit(success ? 0 : 1);
  }
}

// Run the tests
runSecureVaultTests();