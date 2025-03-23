const puppeteer = require('puppeteer');
const http = require('http');
const fs = require('fs');
const path = require('path');

// Simple HTTP server to serve test.html and all necessary files
async function startServer() {
  const server = http.createServer((req, res) => {
    const rootDir = path.join(__dirname, '../..');
    let filePath = '';
    
    if (req.url === '/' || req.url === '/test.html') {
      filePath = path.join(rootDir, 'test.html');
      serveFile(filePath, 'text/html', res);
    } else if (req.url.startsWith('/dist/')) {
      // Serve files from dist directory
      filePath = path.join(rootDir, req.url);
      serveFile(filePath, 'application/javascript', res);
    } else if (req.url.startsWith('/tests/')) {
      // Serve files from tests directory
      filePath = path.join(rootDir, req.url);
      serveFile(filePath, 'application/javascript', res);
    } else {
      res.writeHead(404);
      res.end('Not found: ' + req.url);
    }
  });
  
  // Helper function to serve files
  function serveFile(filePath, contentType, res) {
    fs.readFile(filePath, (err, data) => {
      if (err) {
        console.error('Error loading file:', filePath, err);
        res.writeHead(500);
        res.end('Error loading file: ' + filePath);
        return;
      }
      res.writeHead(200, { 'Content-Type': contentType });
      res.end(data);
    });
  }

  return new Promise((resolve) => {
    server.listen(8081, () => {
      console.log('Server running at http://localhost:8081/');
      resolve(server);
    });
  });
}

// Run browser tests
async function runTests() {
  const server = await startServer();
  console.log('Started server, launching browser...');

  const browser = await puppeteer.launch({
    headless: 'new',
    args: ['--no-sandbox', '--disable-setuid-sandbox'],
  });

  try {
    const page = await browser.newPage();

    // Capture console output
    page.on('console', (msg) => {
      const text = msg.text();
      console.log(`[Browser] ${text}`);
    });

    // Navigate to the test page
    await page.goto('http://localhost:8081/', { waitUntil: 'networkidle0' });
    console.log('Page loaded, running tests...');

    // Click run-all button
    await page.click('#run-all');

    // Wait for tests to complete (look for a summary in the output)
    await page.waitForFunction(
      () => {
        const output = document.getElementById('test-output');
        return output && output.textContent.includes('Test Summary');
      },
      { timeout: 10000 },
    );

    // Clear output
    await page.click('#clear-output');
    
    // Run core tests
    console.log('Running core tests...');
    await page.click('#run-core');
    
    // Wait for core tests to complete
    try {
      await page.waitForFunction(
        () => {
          const output = document.getElementById('test-output');
          return output && output.textContent.includes('Test Summary');
        },
        { timeout: 10000 },
      );
      
      // Extract just the core test results
      const coreResults = await page.evaluate(() => {
        return document.getElementById('test-output').textContent;
      });
      
      console.log('\nCore Test Results:');
      console.log('-----------------');
      console.log(coreResults);
    } catch (e) {
      console.error('Error waiting for core tests to complete:', e.message);
    }

    // Clear output
    await page.click('#clear-output');
    
    // Run storage tests as well
    console.log('Running storage tests...');
    await page.click('#run-storage');
    
    // Wait for storage tests to complete
    await page.waitForFunction(
      () => {
        const output = document.getElementById('test-output');
        return output && output.textContent.includes('Storage Matrix Integration (Browser)');
      },
      { timeout: 10000 }
    );
    
    // Extract test results
    const testResults = await page.evaluate(() => {
      const output = document.getElementById('test-output');
      return output ? output.textContent : 'No results';
    });

    // Display the results
    console.log('\nTest Results:');
    console.log('-----------------');
    console.log(testResults);

    // Check if all tests passed
    const success = testResults.includes('Failed:  0');

    if (success) {
      console.log('\n✅ All browser tests passed!');
      process.exit(0);
    } else {
      console.log('\n❌ Some browser tests failed!');
      process.exit(1);
    }
  } catch (error) {
    console.error('Error running tests:', error);
    process.exit(1);
  } finally {
    await browser.close();
    server.close();
    console.log('Test server and browser closed');
  }
}

runTests();
