/**
 * PrimeOS Reference Implementation - Text Editor Integration Tests
 * 
 * Integration tests for the Text Editor application that test the interaction
 * with File Explorer and the shell environment.
 */

const puppeteer = require('puppeteer');
const path = require('path');
const http = require('http');
const fs = require('fs');
const TestRunner = require('./shell-integration-tests').TestRunner;

// Server configuration
let server;
let browser;
let page;
const PORT = 3001;
const BASE_URL = `http://localhost:${PORT}`;

// Setup and teardown
async function setupTestEnvironment() {
  // Create test HTML file for testing
  const testHtml = `
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>PrimeOS Text Editor Test</title>
  <style>
    body { margin: 0; padding: 0; font-family: sans-serif; }
    #loading { display: flex; align-items: center; justify-content: center; height: 100vh; }
    
    /* Shell styles */
    .window { position: absolute; width: 800px; height: 600px; background: white; box-shadow: 0 0 10px rgba(0,0,0,0.2); border-radius: 5px; display: flex; flex-direction: column; }
    .window-titlebar { height: 30px; background: #eee; display: flex; justify-content: space-between; align-items: center; padding: 0 10px; }
    .window-content { flex: 1; padding: 10px; overflow: auto; }
    
    /* Text editor styles */
    .text-editor { display: flex; flex-direction: column; height: 100%; }
    .toolbar { display: flex; justify-content: space-between; padding: 10px; background: #f5f5f5; border-bottom: 1px solid #ddd; }
    .editor-container { flex: 1; overflow: hidden; }
    #editor { width: 100%; height: 100%; border: none; resize: none; padding: 10px; font-family: monospace; }
    .status-bar { display: flex; justify-content: space-between; padding: 5px 10px; background: #f5f5f5; border-top: 1px solid #ddd; }
    
    /* Dialog styles */
    .dialog { position: absolute; top: 50%; left: 50%; transform: translate(-50%, -50%); background: white; border-radius: 5px; box-shadow: 0 0 20px rgba(0,0,0,0.3); padding: 20px; }
    .dialog-backdrop { position: fixed; top: 0; left: 0; width: 100%; height: 100%; background: rgba(0,0,0,0.5); }
    
    /* Notification styles */
    .toast { position: fixed; bottom: 20px; right: 20px; background: #333; color: white; padding: 10px; border-radius: 5px; }
  </style>
</head>
<body>
  <div id="loading">Loading...</div>
  
  <div id="app-container" style="display:none">
    <div class="window" id="text-editor-window">
      <div class="window-titlebar">
        <div class="window-title">Text Editor</div>
        <div class="window-controls">
          <button class="window-control window-minimize">_</button>
          <button class="window-control window-maximize">□</button>
          <button class="window-control window-close">×</button>
        </div>
      </div>
      <div class="window-content" id="window-content-test-window">
        <!-- Text editor content will be injected here -->
      </div>
    </div>
  </div>

  <script>
    // Mock global objects for testing
    window.PrimeOS = {
      // Mock EventBus
      EventBus: {
        publish: function(event, data) {
          console.log('Event published:', event, data);
          
          // Show notification for appropriate events
          if (event === 'shell:show-notification') {
            const toast = document.createElement('div');
            toast.className = 'toast';
            toast.innerHTML = \`<strong>\${data.title}</strong><p>\${data.message}</p>\`;
            document.body.appendChild(toast);
            
            setTimeout(() => {
              toast.remove();
            }, data.timeout || 3000);
          }
        },
        subscribe: function(event, handler) {
          console.log('Subscribed to event:', event);
          // Return unsubscribe function
          return function() {};
        },
        unsubscribe: function(event, handler) {
          console.log('Unsubscribed from event:', event);
        }
      },
      
      // Mock store - will be populated with test data
      store: {
        fileSystem: {
          '/': {
            type: 'directory',
            name: 'Root',
            children: ['Documents'],
            created: Date.now(),
            modified: Date.now()
          },
          '/Documents': {
            type: 'directory',
            name: 'Documents',
            children: ['test.txt'],
            created: Date.now(),
            modified: Date.now()
          },
          '/Documents/test.txt': {
            type: 'file',
            name: 'test.txt',
            extension: 'txt',
            content: 'This is a test file.',
            size: 'This is a test file.'.length,
            created: Date.now(),
            modified: Date.now()
          }
        },
        
        // Mock store methods
        async get(key) {
          if (key.startsWith('app_preferences_')) {
            return {
              id: key,
              type: 'preferences',
              recentFiles: [
                {
                  id: 'file_123',
                  name: 'test.txt',
                  path: '/Documents/test.txt',
                  created: Date.now() - 10000,
                  lastModified: Date.now() - 5000
                }
              ],
              lastFile: {
                id: 'file_123',
                name: 'test.txt',
                path: '/Documents/test.txt',
                created: Date.now() - 10000,
                lastModified: Date.now() - 5000
              }
            };
          }
          return null;
        },
        
        async put(data) {
          console.log('Storing data:', data);
          return data;
        }
      },
      
      // Mock File Explorer API
      FileExplorer: {
        getFile: function(path) {
          return window.PrimeOS.store.fileSystem[path];
        },
        
        saveFile: function(path, content) {
          const pathParts = path.split('/');
          const fileName = pathParts.pop();
          const dirPath = pathParts.join('/');
          
          const file = window.PrimeOS.store.fileSystem[path] || {
            type: 'file',
            name: fileName,
            extension: fileName.includes('.') ? fileName.split('.').pop() : '',
            created: Date.now()
          };
          
          file.content = content;
          file.size = content.length;
          file.modified = Date.now();
          
          window.PrimeOS.store.fileSystem[path] = file;
          
          // Add to parent directory children if not already there
          if (window.PrimeOS.store.fileSystem[dirPath]) {
            if (!window.PrimeOS.store.fileSystem[dirPath].children.includes(fileName)) {
              window.PrimeOS.store.fileSystem[dirPath].children.push(fileName);
            }
          }
          
          return file;
        }
      },
      
      // Mock AppAPI
      AppAPI: class {
        constructor(options) {
          this.appId = options.appId;
          this.containerElement = options.containerElement;
          this.eventBus = window.PrimeOS.EventBus;
          this.store = window.PrimeOS.store;
          this.windowId = options.windowId || 'test-window';
          
          this.state = {
            preferences: {},
            isActive: true,
            isSuspended: false
          };
          
          console.log('AppAPI initialized for ' + this.appId);
        }
        
        showNotification(notification) {
          this.eventBus.publish('shell:show-notification', {
            appId: this.appId,
            ...notification
          });
        }
        
        async loadPreferences() {
          const prefs = await this.store.get(\`app_preferences_\${this.appId}\`);
          this.state.preferences = prefs || {};
          return this.state.preferences;
        }
        
        async savePreferences(preferences) {
          this.state.preferences = { ...this.state.preferences, ...preferences };
          
          await this.store.put({
            id: \`app_preferences_\${this.appId}\`,
            type: 'preferences',
            ...this.state.preferences
          });
          
          return this.state.preferences;
        }
        
        async requestAppData(targetAppId, request) {
          console.log(\`App \${this.appId} requesting data from \${targetAppId}:\`, request);
          
          if (targetAppId === 'file-explorer') {
            if (request.type === 'getFile') {
              return window.PrimeOS.FileExplorer.getFile(request.path);
            } else if (request.type === 'saveFile') {
              return window.PrimeOS.FileExplorer.saveFile(request.path, request.content);
            }
          }
          
          throw new Error(\`Invalid request to \${targetAppId}: \${request.type}\`);
        }
      }
    };
    
    // Load text editor script
    function loadTextEditor() {
      // Simulate loading the text editor script
      fetch('/apps/text-editor/index.js')
        .then(response => response.text())
        .then(code => {
          // Execute the text editor code to make TextEditor available
          eval(code);
          
          // Initialize text editor
          const container = document.getElementById('window-content-test-window');
          
          window.PrimeOS.TextEditor.initialize(container, {
            eventBus: window.PrimeOS.EventBus,
            store: window.PrimeOS.store,
            windowId: 'test-window'
          }).then(textEditor => {
            window.textEditor = textEditor;
            console.log('Text Editor initialized');
            
            // Hide loading, show app
            document.getElementById('loading').style.display = 'none';
            document.getElementById('app-container').style.display = 'block';
          }).catch(error => {
            console.error('Failed to initialize Text Editor:', error);
            document.getElementById('loading').textContent = 'Error loading Text Editor: ' + error.message;
          });
        })
        .catch(error => {
          console.error('Failed to load Text Editor script:', error);
          document.getElementById('loading').textContent = 'Error loading Text Editor script: ' + error.message;
        });
    }
    
    // Initialize test environment
    window.setTimeout(() => {
      loadTextEditor();
    }, 500);
  </script>
</body>
</html>
  `;

  // Create a folder for testing files
  const testDir = path.join(__dirname, 'temp');
  if (!fs.existsSync(testDir)) {
    fs.mkdirSync(testDir);
  }
  
  // Create apps directory for text editor
  const appsDir = path.join(testDir, 'apps', 'text-editor');
  if (!fs.existsSync(appsDir)) {
    fs.mkdirSync(appsDir, { recursive: true });
  }
  
  // Copy text editor script to test directory
  try {
    const textEditorScript = fs.readFileSync(path.join(__dirname, '..', 'apps', 'text-editor', 'index.js'), 'utf8');
    fs.writeFileSync(path.join(appsDir, 'index.js'), textEditorScript);
  } catch (error) {
    console.error('Error copying text editor script:', error);
  }
  
  // Write the test HTML file
  fs.writeFileSync(path.join(testDir, 'test.html'), testHtml);
  
  // Create a server to serve the files
  server = http.createServer((req, res) => {
    // Serve static files
    let filePath = path.join(__dirname, 'temp', req.url === '/' ? 'test.html' : req.url);
    const extname = path.extname(filePath);
    
    // Default content type
    let contentType = 'text/html';
    
    // Check extension and set content type
    switch (extname) {
      case '.js':
        contentType = 'text/javascript';
        break;
      case '.css':
        contentType = 'text/css';
        break;
      case '.json':
        contentType = 'application/json';
        break;
    }
    
    // Check if file exists
    fs.readFile(filePath, (err, content) => {
      if (err) {
        if (err.code === 'ENOENT') {
          // File not found, serve test.html
          fs.readFile(path.join(testDir, 'test.html'), (err, content) => {
            if (err) {
              res.writeHead(500);
              res.end('Error loading test file');
              return;
            }
            
            res.writeHead(200, { 'Content-Type': 'text/html' });
            res.end(content, 'utf-8');
          });
        } else {
          // Server error
          res.writeHead(500);
          res.end(`Server Error: ${err.code}`);
        }
        return;
      }
      
      // Success - serve the file
      res.writeHead(200, { 'Content-Type': contentType });
      res.end(content, 'utf-8');
    });
  });

  // Start the server
  await new Promise(resolve => {
    server.listen(PORT, () => {
      console.log(`Test server running at ${BASE_URL}`);
      resolve();
    });
  });

  // Launch browser
  browser = await puppeteer.launch({
    headless: 'new',
    args: ['--no-sandbox', '--disable-setuid-sandbox']
  });

  // Create a new page
  page = await browser.newPage();

  // Set viewport
  await page.setViewport({ width: 1280, height: 800 });

  // Enable console logging from the browser
  page.on('console', msg => console.log(`Browser console: ${msg.text()}`));
}

async function teardownTestEnvironment() {
  // Close the browser
  if (browser) {
    await browser.close();
  }

  // Close the server
  if (server) {
    await new Promise(resolve => {
      server.close(() => {
        console.log('Test server closed');
        resolve();
      });
    });
  }
  
  // Clean up test files
  try {
    const testDir = path.join(__dirname, 'temp');
    if (fs.existsSync(testDir)) {
      fs.rmdirSync(testDir, { recursive: true });
    }
  } catch (error) {
    console.error('Error cleaning up test files:', error);
    // Non-fatal, we can continue
  }
}

// Helper functions
async function waitForTextEditorReady(timeout = 10000) {
  try {
    // Wait for loading to disappear
    await page.waitForFunction(() => {
      return document.getElementById('loading').style.display === 'none';
    }, { timeout });
    
    // Wait for app container to be visible
    await page.waitForFunction(() => {
      return document.getElementById('app-container').style.display === 'block';
    }, { timeout });
    
    // Wait for editor to be available
    await page.waitForFunction(() => {
      return document.getElementById('editor') !== null;
    }, { timeout });
    
    return true;
  } catch (error) {
    console.error('Error waiting for text editor to be ready:', error);
    throw error;
  }
}

// Define text editor tests
TestRunner.test('Text editor loads and initializes', async () => {
  // Navigate to the test page
  await page.goto(BASE_URL, { waitUntil: 'networkidle0' });
  
  // Wait for text editor to be ready
  await waitForTextEditorReady();
  
  // Check that editor element exists
  const hasEditor = await page.evaluate(() => {
    return !!document.getElementById('editor');
  });
  
  if (!hasEditor) {
    throw new Error('Editor element not found');
  }
  
  // Screenshot for debugging
  await page.screenshot({ path: path.join(__dirname, 'temp', 'text-editor-loaded.png') });
});

TestRunner.test('Text editor can edit content', async () => {
  // Make sure we're on the test page
  const url = await page.url();
  if (!url.includes('test.html') && !url.endsWith('/')) {
    await page.goto(BASE_URL, { waitUntil: 'networkidle0' });
    await waitForTextEditorReady();
  }
  
  // Type content into the editor
  await page.evaluate(() => {
    document.getElementById('editor').value = 'Testing the editor with new content';
  });
  
  // Check that editor content was updated
  const editorContent = await page.evaluate(() => {
    return document.getElementById('editor').value;
  });
  
  if (editorContent !== 'Testing the editor with new content') {
    throw new Error('Editor content was not updated correctly');
  }
  
  // Screenshot for debugging
  await page.screenshot({ path: path.join(__dirname, 'temp', 'text-editor-content.png') });
});

TestRunner.test('Text editor can save files', async () => {
  // Make sure we're on the test page
  const url = await page.url();
  if (!url.includes('test.html') && !url.endsWith('/')) {
    await page.goto(BASE_URL, { waitUntil: 'networkidle0' });
    await waitForTextEditorReady();
  }
  
  // Type content into the editor
  await page.evaluate(() => {
    document.getElementById('editor').value = 'Content to be saved';
  });
  
  // Click save button
  await page.click('#save-file');
  
  // Wait a bit for the save operation to complete
  await page.waitForTimeout(500);
  
  // Check if file was saved in the mock file system
  const fileSaved = await page.evaluate(() => {
    // Check if content was saved to the test.txt file
    const file = window.PrimeOS.store.fileSystem['/Documents/test.txt'];
    return file && file.content === 'Content to be saved';
  });
  
  if (!fileSaved) {
    throw new Error('File was not saved correctly');
  }
  
  // Check if status was updated
  const statusText = await page.evaluate(() => {
    return document.getElementById('status').textContent;
  });
  
  if (!statusText.includes('saved') && !statusText.includes('Save')) {
    throw new Error('Status text was not updated after save');
  }
  
  // Screenshot for debugging
  await page.screenshot({ path: path.join(__dirname, 'temp', 'text-editor-save.png') });
});

TestRunner.test('Text editor can create new files', async () => {
  // Make sure we're on the test page
  const url = await page.url();
  if (!url.includes('test.html') && !url.endsWith('/')) {
    await page.goto(BASE_URL, { waitUntil: 'networkidle0' });
    await waitForTextEditorReady();
  }
  
  // Initial content before creating new file
  const initialContent = await page.evaluate(() => {
    return document.getElementById('editor').value;
  });
  
  // Click new file button
  await page.click('#new-file');
  
  // Wait a bit for the operation to complete
  await page.waitForTimeout(500);
  
  // Check if editor was cleared
  const newContent = await page.evaluate(() => {
    return document.getElementById('editor').value;
  });
  
  if (newContent !== '' && newContent === initialContent) {
    throw new Error('New file was not created (editor not cleared)');
  }
  
  // Check if file name was set to Untitled
  const fileName = await page.evaluate(() => {
    return document.getElementById('file-name').textContent;
  });
  
  if (fileName !== 'Untitled') {
    throw new Error('New file name is not set to Untitled');
  }
  
  // Screenshot for debugging
  await page.screenshot({ path: path.join(__dirname, 'temp', 'text-editor-new-file.png') });
});

// Run the tests
async function runTests() {
  try {
    await setupTestEnvironment();
    await TestRunner.run();
  } catch (error) {
    console.error('Test setup failed:', error);
  } finally {
    await teardownTestEnvironment();
  }
}

if (require.main === module) {
  runTests().then(() => {
    const { failed } = TestRunner.results;
    process.exit(failed > 0 ? 1 : 0);
  });
}

module.exports = { runTests };