/**
 * PrimeOS Browser Tests - Puppeteer Automated Test Runner
 * 
 * This script uses Puppeteer to test browser components automatically
 */

const puppeteer = require('puppeteer');
const { execSync } = require('child_process');
const fs = require('fs');
const path = require('path');

// Create screenshots directory if it doesn't exist
const screenshotsDir = path.join(__dirname, 'tests', 'screenshots');
if (!fs.existsSync(screenshotsDir)) {
  fs.mkdirSync(screenshotsDir, { recursive: true });
}

async function runBrowserTests() {
  console.log('Starting browser tests for PrimeOS Reference Implementation');
  console.log('--------------------------------------------------------');
  
  let allTestsPassed = true;
  let testResults = {
    total: 0,
    passed: 0,
    failed: 0,
    components: {}
  };
  
  const browser = await puppeteer.launch({
    headless: 'new',
    args: ['--no-sandbox', '--disable-setuid-sandbox']
  });
  
  try {
    // Test the Shell
    const shellResult = await testShell(browser);
    allTestsPassed = allTestsPassed && shellResult.success;
    testResults.components.shell = shellResult;
    testResults.total += shellResult.tests;
    testResults.passed += shellResult.passed;
    testResults.failed += shellResult.failed;
    
    // Test the Topology Visualizer
    const topologyResult = await testTopologyVisualizer(browser);
    allTestsPassed = allTestsPassed && topologyResult.success;
    testResults.components.topologyVisualizer = topologyResult;
    testResults.total += topologyResult.tests;
    testResults.passed += topologyResult.passed;
    testResults.failed += topologyResult.failed;
    
    // Test the Context Sharing
    const contextResult = await testContextSharing(browser);
    allTestsPassed = allTestsPassed && contextResult.success;
    testResults.components.contextSharing = contextResult;
    testResults.total += contextResult.tests;
    testResults.passed += contextResult.passed;
    testResults.failed += contextResult.failed;
    
    // Test the Extension System
    const extensionResult = await testExtensionSystem(browser);
    allTestsPassed = allTestsPassed && extensionResult.success;
    testResults.components.extensionSystem = extensionResult;
    testResults.total += extensionResult.tests;
    testResults.passed += extensionResult.passed;
    testResults.failed += extensionResult.failed;
    
    // Test the Manifold Import/Export
    const importExportResult = await testManifoldImportExport(browser);
    allTestsPassed = allTestsPassed && importExportResult.success;
    testResults.components.manifoldImportExport = importExportResult;
    testResults.total += importExportResult.tests;
    testResults.passed += importExportResult.passed;
    testResults.failed += importExportResult.failed;
    
    // Print test summary
    console.log('\n--------------------------------------------------------');
    console.log('PrimeOS Browser Tests Summary:');
    console.log(`Total Tests: ${testResults.total}`);
    console.log(`Passed: ${testResults.passed}`);
    console.log(`Failed: ${testResults.failed}`);
    console.log('--------------------------------------------------------');
    
    if (allTestsPassed) {
      console.log('\n✅ All browser tests completed successfully!');
    } else {
      console.error('\n❌ Some browser tests failed. Check the logs for details.');
      process.exit(1);
    }
    
    // Write test results to a JSON file
    fs.writeFileSync(
      path.join(__dirname, 'tests', 'browser-test-results.json'), 
      JSON.stringify(testResults, null, 2)
    );
    
  } catch (error) {
    console.error('\n❌ Browser tests failed with an error:', error.message);
    process.exit(1);
  } finally {
    await browser.close();
  }
}

async function testShell(browser) {
  console.log('\nTesting Shell...');
  const result = {
    component: 'Shell',
    tests: 3,
    passed: 0,
    failed: 0,
    logs: []
  };
  
  const page = await browser.newPage();
  
  try {
    // Log browser console messages
    page.on('console', msg => {
      const text = msg.text();
      if (text.includes('Error') || text.includes('error')) {
        result.logs.push(`Console Error: ${text}`);
      }
    });
    
    await page.goto('http://localhost:3000', {
      waitUntil: 'networkidle2',
      timeout: 30000
    });
    
    // Test 1: Shell container exists
    console.log('  - Testing shell container exists...');
    try {
      await page.waitForSelector('#prime-shell', { timeout: 10000 });
      console.log('    ✓ Shell container found');
      result.passed++;
    } catch (error) {
      console.error('    ✗ Shell container not found');
      result.logs.push('Shell container not found');
      result.failed++;
    }
    
    // Test 2: Taskbar exists
    console.log('  - Testing taskbar exists...');
    try {
      const taskbarExists = await page.evaluate(() => !!document.querySelector('.taskbar'));
      if (taskbarExists) {
        console.log('    ✓ Taskbar found');
        result.passed++;
      } else {
        console.error('    ✗ Taskbar not found');
        result.logs.push('Taskbar not found');
        result.failed++;
      }
    } catch (error) {
      console.error('    ✗ Error checking for taskbar:', error.message);
      result.logs.push(`Error checking for taskbar: ${error.message}`);
      result.failed++;
    }
    
    // Test 3: Desktop area exists
    console.log('  - Testing desktop area exists...');
    try {
      const desktopExists = await page.evaluate(() => !!document.querySelector('.desktop'));
      if (desktopExists) {
        console.log('    ✓ Desktop area found');
        result.passed++;
      } else {
        console.error('    ✗ Desktop area not found');
        result.logs.push('Desktop area not found');
        result.failed++;
      }
    } catch (error) {
      console.error('    ✗ Error checking for desktop area:', error.message);
      result.logs.push(`Error checking for desktop area: ${error.message}`);
      result.failed++;
    }
    
    // Take a screenshot for review
    await page.screenshot({ path: path.join(screenshotsDir, 'shell-test.png') });
    
    // Set success flag
    result.success = result.failed === 0;
    
    if (result.success) {
      console.log('✅ Shell tests passed');
    } else {
      console.error('❌ Shell tests failed');
    }
  } catch (error) {
    console.error('❌ Shell tests failed with an error:', error.message);
    result.logs.push(`Test error: ${error.message}`);
    result.failed = result.tests;
    result.success = false;
  } finally {
    await page.close();
    return result;
  }
}

async function testTopologyVisualizer(browser) {
  console.log('\nTesting Topology Visualizer...');
  const result = {
    component: 'TopologyVisualizer',
    tests: 3,
    passed: 0,
    failed: 0,
    logs: []
  };
  
  const page = await browser.newPage();
  
  try {
    await page.goto('http://localhost:3000/tests/topology-visualizer-browser-test.html', {
      waitUntil: 'networkidle2',
      timeout: 30000
    });
    
    // Test 1: Visualization loads
    console.log('  - Testing visualization loads...');
    try {
      await page.waitForSelector('.visualizer-container svg', { timeout: 5000 });
      console.log('    ✓ Visualization loaded successfully');
      result.passed++;
    } catch (error) {
      console.error('    ✗ Visualization failed to load');
      result.logs.push('Visualization failed to load');
      result.failed++;
    }
    
    // Test 2: Adding a node works
    console.log('  - Testing node addition...');
    try {
      await page.click('#add-node');
      await page.waitForFunction(() => {
        const output = document.getElementById('visualizer-output');
        return output.innerHTML.includes('Added node:');
      }, { timeout: 5000 });
      console.log('    ✓ Node added successfully');
      result.passed++;
    } catch (error) {
      console.error('    ✗ Failed to add node');
      result.logs.push('Failed to add node');
      result.failed++;
    }
    
    // Test 3: Event handling works
    console.log('  - Testing event handling...');
    try {
      await page.click('#trigger-manifold-created');
      await page.waitForFunction(() => {
        const output = document.getElementById('event-output');
        return output.innerHTML.includes('Published manifold:created event');
      }, { timeout: 5000 });
      console.log('    ✓ Event handling works correctly');
      result.passed++;
    } catch (error) {
      console.error('    ✗ Event handling failed');
      result.logs.push('Event handling failed');
      result.failed++;
    }
    
    // Take a screenshot for review
    await page.screenshot({ path: path.join(screenshotsDir, 'topology-visualizer-test.png') });
    
    // Set success flag
    result.success = result.failed === 0;
    
    if (result.success) {
      console.log('✅ Topology Visualizer tests passed');
    } else {
      console.error('❌ Topology Visualizer tests failed');
    }
  } catch (error) {
    console.error('❌ Topology Visualizer tests failed with an error:', error.message);
    result.logs.push(`Test error: ${error.message}`);
    result.failed = result.tests;
    result.success = false;
  } finally {
    await page.close();
    return result;
  }
}

async function testContextSharing(browser) {
  console.log('\nTesting Context Sharing...');
  const result = {
    component: 'ContextSharing',
    tests: 3,
    passed: 0,
    failed: 0,
    logs: []
  };
  
  const page = await browser.newPage();
  
  try {
    await page.goto('http://localhost:3000/tests/context-sharing-browser-test.html', {
      waitUntil: 'networkidle2',
      timeout: 30000
    });
    
    // Test 1: Context hub initializes
    console.log('  - Testing context hub initialization...');
    try {
      await page.waitForFunction(() => {
        const logs = document.getElementById('log-container');
        return logs.innerHTML.includes('Context hub initialized');
      }, { timeout: 5000 });
      console.log('    ✓ Context hub initialized successfully');
      result.passed++;
    } catch (error) {
      console.error('    ✗ Context hub failed to initialize');
      result.logs.push('Context hub failed to initialize');
      result.failed++;
    }
    
    // Test 2: Provider creation works
    console.log('  - Testing provider creation...');
    try {
      await page.type('#provider-id', 'test-provider');
      await page.type('#provider-type', 'test-data');
      await page.type('#provider-description', 'Test provider for automated tests');
      await page.click('#create-provider');
      
      await page.waitForFunction(() => {
        const logs = document.getElementById('log-container');
        return logs.innerHTML.includes('Provider registered: test-provider');
      }, { timeout: 5000 });
      console.log('    ✓ Provider created successfully');
      result.passed++;
    } catch (error) {
      console.error('    ✗ Failed to create provider');
      result.logs.push('Failed to create provider');
      result.failed++;
    }
    
    // Test 3: Context update works
    console.log('  - Testing context update...');
    try {
      await page.select('#update-provider', 'test-provider');
      await page.evaluate(() => {
        document.getElementById('context-data').value = JSON.stringify({
          message: 'Hello from automated test',
          timestamp: Date.now()
        }, null, 2);
      });
      await page.click('#update-context');
      
      await page.waitForFunction(() => {
        const logs = document.getElementById('log-container');
        return logs.innerHTML.includes('Context updated for test-provider');
      }, { timeout: 5000 });
      console.log('    ✓ Context updated successfully');
      result.passed++;
    } catch (error) {
      console.error('    ✗ Failed to update context');
      result.logs.push('Failed to update context');
      result.failed++;
    }
    
    // Take a screenshot for review
    await page.screenshot({ path: path.join(screenshotsDir, 'context-sharing-test.png') });
    
    // Set success flag
    result.success = result.failed === 0;
    
    if (result.success) {
      console.log('✅ Context Sharing tests passed');
    } else {
      console.error('❌ Context Sharing tests failed');
    }
  } catch (error) {
    console.error('❌ Context Sharing tests failed with an error:', error.message);
    result.logs.push(`Test error: ${error.message}`);
    result.failed = result.tests;
    result.success = false;
  } finally {
    await page.close();
    return result;
  }
}

async function testExtensionSystem(browser) {
  console.log('\nTesting Extension System...');
  const result = {
    component: 'ExtensionSystem',
    tests: 3,
    passed: 0,
    failed: 0,
    logs: []
  };
  
  const page = await browser.newPage();
  
  try {
    await page.goto('http://localhost:3000/tests/extension-system-browser-test.html', {
      waitUntil: 'networkidle2',
      timeout: 30000
    });
    
    // Test 1: Extension system initializes
    console.log('  - Testing extension system initialization...');
    try {
      await page.waitForFunction(() => {
        const logs = document.getElementById('log-container');
        return logs.innerHTML.includes('Extension system initialized');
      }, { timeout: 5000 });
      console.log('    ✓ Extension system initialized successfully');
      result.passed++;
    } catch (error) {
      console.error('    ✗ Extension system failed to initialize');
      result.logs.push('Extension system failed to initialize');
      result.failed++;
    }
    
    // Test 2: Extension point creation works
    console.log('  - Testing extension point creation...');
    try {
      await page.type('#extension-point-id', 'test:point');
      await page.type('#extension-point-name', 'Test Point');
      await page.type('#extension-point-description', 'Test extension point for automated tests');
      await page.click('#create-extension-point');
      
      await page.waitForFunction(() => {
        const logs = document.getElementById('log-container');
        return logs.innerHTML.includes('Created extension point: Test Point');
      }, { timeout: 5000 });
      console.log('    ✓ Extension point created successfully');
      result.passed++;
    } catch (error) {
      console.error('    ✗ Failed to create extension point');
      result.logs.push('Failed to create extension point');
      result.failed++;
    }
    
    // Test 3: Extension installation works
    console.log('  - Testing extension installation...');
    try {
      await page.type('#extension-id', 'test-extension');
      await page.type('#extension-name', 'Test Extension');
      await page.type('#extension-version', '1.0.0');
      await page.type('#extension-description', 'Test extension for automated tests');
      
      await page.evaluate(() => {
        document.getElementById('extension-content').value = JSON.stringify({
          'ui:toolbar': [
            { id: 'test-button', label: 'Test Button' }
          ],
          'test:point': [
            { id: 'test-item', label: 'Test Item' }
          ]
        }, null, 2);
      });
      
      await page.click('#create-extension');
      
      await page.waitForFunction(() => {
        const logs = document.getElementById('log-container');
        return logs.innerHTML.includes('Installed extension: Test Extension');
      }, { timeout: 5000 });
      console.log('    ✓ Extension installed successfully');
      result.passed++;
    } catch (error) {
      console.error('    ✗ Failed to install extension');
      result.logs.push('Failed to install extension');
      result.failed++;
    }
    
    // Take a screenshot for review
    await page.screenshot({ path: path.join(screenshotsDir, 'extension-system-test.png') });
    
    // Set success flag
    result.success = result.failed === 0;
    
    if (result.success) {
      console.log('✅ Extension System tests passed');
    } else {
      console.error('❌ Extension System tests failed');
    }
  } catch (error) {
    console.error('❌ Extension System tests failed with an error:', error.message);
    result.logs.push(`Test error: ${error.message}`);
    result.failed = result.tests;
    result.success = false;
  } finally {
    await page.close();
    return result;
  }
}

async function testManifoldImportExport(browser) {
  console.log('\nTesting Manifold Import/Export...');
  const result = {
    component: 'ManifoldImportExport',
    tests: 3,
    passed: 0,
    failed: 0,
    logs: []
  };
  
  const page = await browser.newPage();
  
  try {
    await page.goto('http://localhost:3000/tests/manifold-import-export-browser-test.html', {
      waitUntil: 'networkidle2',
      timeout: 30000
    });
    
    // Test 1: Import/Export system initializes
    console.log('  - Testing import/export system initialization...');
    try {
      await page.waitForFunction(() => {
        const logs = document.getElementById('log-container');
        return logs.innerHTML.includes('Import/Export system initialized');
      }, { timeout: 5000 });
      console.log('    ✓ Import/Export system initialized successfully');
      result.passed++;
    } catch (error) {
      console.error('    ✗ Import/Export system failed to initialize');
      result.logs.push('Import/Export system failed to initialize');
      result.failed++;
    }
    
    // Test 2: Manifold creation works
    console.log('  - Testing manifold creation...');
    try {
      await page.click('#create-test-manifold');
      
      await page.waitForFunction(() => {
        const logs = document.getElementById('log-container');
        return logs.innerHTML.includes('Created test manifold:');
      }, { timeout: 5000 });
      console.log('    ✓ Manifold created successfully');
      result.passed++;
    } catch (error) {
      console.error('    ✗ Failed to create manifold');
      result.logs.push('Failed to create manifold');
      result.failed++;
    }
    
    // Test 3: Endpoint addition works
    console.log('  - Testing endpoint addition...');
    try {
      await page.type('#endpoint-name', 'Test Endpoint');
      await page.type('#endpoint-url', 'https://test-endpoint.example.com');
      await page.type('#endpoint-token', 'test-token-123');
      await page.click('#add-endpoint');
      
      await page.waitForFunction(() => {
        const logs = document.getElementById('log-container');
        return logs.innerHTML.includes('Added remote endpoint: Test Endpoint');
      }, { timeout: 5000 });
      console.log('    ✓ Endpoint added successfully');
      result.passed++;
    } catch (error) {
      console.error('    ✗ Failed to add endpoint');
      result.logs.push('Failed to add endpoint');
      result.failed++;
    }
    
    // Take a screenshot for review
    await page.screenshot({ path: path.join(screenshotsDir, 'manifold-import-export-test.png') });
    
    // Set success flag
    result.success = result.failed === 0;
    
    if (result.success) {
      console.log('✅ Manifold Import/Export tests passed');
    } else {
      console.error('❌ Manifold Import/Export tests failed');
    }
  } catch (error) {
    console.error('❌ Manifold Import/Export tests failed with an error:', error.message);
    result.logs.push(`Test error: ${error.message}`);
    result.failed = result.tests;
    result.success = false;
  } finally {
    await page.close();
    return result;
  }
}

// Run all tests
runBrowserTests();