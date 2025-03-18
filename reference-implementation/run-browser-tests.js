/**
 * PrimeOS Reference Implementation Browser Tests Runner
 * Runs tests in a headless browser environment using Puppeteer
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

// Run the browser tests
async function runBrowserTests() {
  let server;
  let browser;
  let success = false;
  
  try {
    // Start the local server
    console.log('Starting local server for browser tests...');
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
    console.log('Navigating to test page...');
    await page.goto(`http://localhost:${port}/tests/test.html`, {
      waitUntil: 'networkidle0',
      timeout: 30000
    });
    
    // Wait for the shell to initialize
    console.log('Waiting for shell initialization...');
    await page.waitForFunction(() => {
      return !document.getElementById('loading') || 
             document.getElementById('loading').style.display === 'none';
    }, { timeout: 10000 });
    
    // Run all tests
    console.log('Running browser tests...');
    await page.click('#run-all-tests');
    
    // Wait for tests to complete (1s per test)
    await new Promise(resolve => setTimeout(resolve, 2000));
    
    // Get test results
    const testResults = await page.evaluate(() => window._testResults);
    
    console.log('\n========== BROWSER TEST RESULTS ==========');
    console.log(`Tests Passed: ${testResults.passed}`);
    console.log(`Tests Failed: ${testResults.failed}`);
    console.log('\nDetailed Logs:');
    testResults.logs.forEach(log => console.log(log));
    console.log('==========================================\n');
    
    // Determine if tests were successful
    success = testResults.failed === 0 && testResults.passed > 0;
    if (success) {
      console.log('✅ All browser tests passed successfully!');
    } else {
      console.error('❌ Some browser tests failed.');
    }
  } catch (error) {
    console.error('Error running browser tests:', error);
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
runBrowserTests();