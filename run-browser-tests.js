const puppeteer = require('puppeteer');
const http = require('http');
const fs = require('fs');
const path = require('path');

// Simple HTTP server to serve test.html
async function startServer() {
  const server = http.createServer((req, res) => {
    if (req.url === '/') {
      fs.readFile(path.join(__dirname, 'test.html'), (err, data) => {
        if (err) {
          res.writeHead(500);
          res.end('Error loading test.html');
          return;
        }
        res.writeHead(200, { 'Content-Type': 'text/html' });
        res.end(data);
      });
    } else if (req.url === '/dist/primeos.js') {
      fs.readFile(path.join(__dirname, 'dist/primeos.js'), (err, data) => {
        if (err) {
          res.writeHead(500);
          res.end('Error loading primeos.js');
          return;
        }
        res.writeHead(200, { 'Content-Type': 'application/javascript' });
        res.end(data);
      });
    } else {
      res.writeHead(404);
      res.end('Not found');
    }
  });

  return new Promise(resolve => {
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
    args: ['--no-sandbox', '--disable-setuid-sandbox']
  });
  
  try {
    const page = await browser.newPage();
    
    // Capture console output
    page.on('console', msg => {
      const text = msg.text();
      console.log(`[Browser] ${text}`);
    });

    // Navigate to the test page
    await page.goto('http://localhost:8081/', { waitUntil: 'networkidle0' });
    console.log('Page loaded, running tests...');

    // Click run-all button
    await page.click('#run-all');
    
    // Wait for tests to complete (look for a summary in the output)
    await page.waitForFunction(() => {
      const output = document.getElementById('test-output');
      return output && output.textContent.includes('Test Summary');
    }, { timeout: 10000 });

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