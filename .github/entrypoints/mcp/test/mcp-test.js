/**
 * Tests for the Repository API MCP Server
 * 
 * Tests the MCP server interface by sending requests and verifying responses
 */

const { spawn } = require('child_process');
const path = require('path');

// Path to the MCP server
const MCP_SERVER_PATH = path.resolve(__dirname, '../index.js');

/**
 * Run all tests
 */
async function runTests() {
  console.log('Running Repository API MCP Server Tests...');
  
  // Start the MCP server
  const server = startMcpServer();
  
  try {
    // Wait for the server to start
    await new Promise(resolve => setTimeout(resolve, 1000));
    
    // Test listing tools
    await testListTools(server);
    
    // Test validate tool
    await testValidateTool(server);
    
    // Test mutate tool
    await testMutateTool(server);
    
    // Test resolve tool
    await testResolveTool(server);
    
    // Test resource templates
    await testResourceTemplates(server);
    
    // Test reading resources
    await testReadResource(server);
    
    console.log('All tests completed!');
  } catch (error) {
    console.error('Test failed:', error);
  } finally {
    // Stop the MCP server
    server.kill();
  }
}

/**
 * Start the MCP server
 * 
 * @returns {ChildProcess} - The MCP server process
 */
function startMcpServer() {
  const server = spawn('node', [MCP_SERVER_PATH]);
  
  server.stdout.on('data', data => {
    // Parse and handle server responses
    try {
      const response = JSON.parse(data.toString());
      handleServerResponse(response);
    } catch (error) {
      // Ignore non-JSON output
    }
  });
  
  server.stderr.on('data', data => {
    // Log server errors
    console.error(`Server error: ${data}`);
  });
  
  server.on('close', code => {
    console.log(`Server exited with code ${code}`);
  });
  
  return server;
}

/**
 * Send a request to the MCP server
 * 
 * @param {ChildProcess} server - The MCP server process
 * @param {string} method - The method to call
 * @param {Object} params - The parameters to send
 * @returns {Promise<Object>} - The server response
 */
function sendRequest(server, method, params = {}) {
  return new Promise((resolve, reject) => {
    const requestId = Date.now().toString();
    
    const request = {
      id: requestId,
      method,
      params
    };
    
    // Set up a response handler
    const responseHandler = response => {
      if (response.id === requestId) {
        if (response.error) {
          reject(response.error);
        } else {
          resolve(response.result);
        }
        
        // Remove the response handler
        responseHandlers = responseHandlers.filter(handler => handler !== responseHandler);
      }
    };
    
    // Add the response handler
    responseHandlers.push(responseHandler);
    
    // Send the request
    server.stdin.write(JSON.stringify(request) + '\n');
  });
}

// Global array of response handlers
let responseHandlers = [];

/**
 * Handle a server response
 * 
 * @param {Object} response - The server response
 */
function handleServerResponse(response) {
  // Call all response handlers
  for (const handler of responseHandlers) {
    handler(response);
  }
}

/**
 * Test listing tools
 * 
 * @param {ChildProcess} server - The MCP server process
 */
async function testListTools(server) {
  console.log('\n--- Testing List Tools ---');
  
  try {
    const result = await sendRequest(server, 'list_tools');
    
    // Verify the tools are returned
    const hasValidateTool = result.tools.some(tool => tool.name === 'validate_json');
    const hasMutateTool = result.tools.some(tool => tool.name === 'index_content');
    const hasResolveTool = result.tools.some(tool => tool.name === 'resolve_content');
    
    console.log('Has validate tool:', hasValidateTool ? 'PASS' : 'FAIL');
    console.log('Has mutate tool:', hasMutateTool ? 'PASS' : 'FAIL');
    console.log('Has resolve tool:', hasResolveTool ? 'PASS' : 'FAIL');
  } catch (error) {
    console.error('List tools failed:', error);
  }
}

/**
 * Test the validate tool
 * 
 * @param {ChildProcess} server - The MCP server process
 */
async function testValidateTool(server) {
  console.log('\n--- Testing Validate Tool ---');
  
  // Test data
  const testSchema = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "type": "object",
    "properties": {
      "name": { "type": "string" },
      "age": { "type": "integer", "minimum": 0 }
    },
    "required": ["name", "age"]
  };
  
  const validData = {
    "name": "John Doe",
    "age": 30
  };
  
  const invalidData = {
    "name": "John Doe",
    "age": -5
  };
  
  try {
    // Test validating valid data
    const validResult = await sendRequest(server, 'call_tool', {
      name: 'validate_json',
      arguments: {
        data: validData,
        schema: testSchema
      }
    });
    
    // Parse the result from the text content
    const validResultObj = JSON.parse(validResult.content[0].text);
    console.log('Validate valid data:', validResultObj.isValid ? 'PASS' : 'FAIL');
    
    // Test validating invalid data
    const invalidResult = await sendRequest(server, 'call_tool', {
      name: 'validate_json',
      arguments: {
        data: invalidData,
        schema: testSchema
      }
    });
    
    // Parse the result from the text content
    const invalidResultObj = JSON.parse(invalidResult.content[0].text);
    console.log('Validate invalid data:', !invalidResultObj.isValid ? 'PASS' : 'FAIL');
    
    // Test validating a schema
    const schemaResult = await sendRequest(server, 'call_tool', {
      name: 'validate_json',
      arguments: {
        schema: testSchema,
        validateSchemaOnly: true
      }
    });
    
    // Parse the result from the text content
    const schemaResultObj = JSON.parse(schemaResult.content[0].text);
    console.log('Validate schema:', schemaResultObj.isValid ? 'PASS' : 'FAIL');
  } catch (error) {
    console.error('Validate tool test failed:', error);
  }
}

/**
 * Test the mutate tool
 * 
 * @param {ChildProcess} server - The MCP server process
 */
async function testMutateTool(server) {
  console.log('\n--- Testing Mutate Tool ---');
  
  // Test data
  const testSchema = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "type": "object",
    "properties": {
      "name": { "type": "string" },
      "age": { "type": "integer", "minimum": 0 }
    },
    "required": ["name", "age"]
  };
  
  const testData = {
    "name": "John Doe",
    "age": 30
  };
  
  try {
    // Test indexing a schema
    const schemaResult = await sendRequest(server, 'call_tool', {
      name: 'index_content',
      arguments: {
        content: testSchema,
        apiName: 'mcp-test',
        endpointName: 'schema',
        mediaType: 'entities',
        isSchema: true
      }
    });
    
    // Parse the result from the text content
    const schemaResultObj = JSON.parse(schemaResult.content[0].text);
    console.log('Index schema:', schemaResultObj.success ? 'PASS' : 'FAIL');
    
    // Test indexing data
    const dataResult = await sendRequest(server, 'call_tool', {
      name: 'index_content',
      arguments: {
        content: testData,
        apiName: 'mcp-test',
        endpointName: 'data',
        mediaType: 'entities'
      }
    });
    
    // Parse the result from the text content
    const dataResultObj = JSON.parse(dataResult.content[0].text);
    console.log('Index data:', dataResultObj.success ? 'PASS' : 'FAIL');
  } catch (error) {
    console.error('Mutate tool test failed:', error);
  }
}

/**
 * Test the resolve tool
 * 
 * @param {ChildProcess} server - The MCP server process
 */
async function testResolveTool(server) {
  console.log('\n--- Testing Resolve Tool ---');
  
  try {
    // Test resolving the schema
    const schemaResult = await sendRequest(server, 'call_tool', {
      name: 'resolve_content',
      arguments: {
        apiName: 'mcp-test',
        endpointName: 'schema',
        mediaType: 'entities'
      }
    });
    
    // Parse the result from the text content
    const schemaResultObj = JSON.parse(schemaResult.content[0].text);
    console.log('Resolve schema:', schemaResultObj.success ? 'PASS' : 'FAIL');
    
    // Test resolving the data
    const dataResult = await sendRequest(server, 'call_tool', {
      name: 'resolve_content',
      arguments: {
        apiName: 'mcp-test',
        endpointName: 'data',
        mediaType: 'entities'
      }
    });
    
    // Parse the result from the text content
    const dataResultObj = JSON.parse(dataResult.content[0].text);
    console.log('Resolve data:', dataResultObj.success ? 'PASS' : 'FAIL');
    
    // Test resolving non-existent content
    const nonExistentResult = await sendRequest(server, 'call_tool', {
      name: 'resolve_content',
      arguments: {
        apiName: 'nonexistent',
        endpointName: 'endpoint',
        mediaType: 'entities'
      }
    });
    
    // Parse the result from the text content
    const nonExistentResultObj = JSON.parse(nonExistentResult.content[0].text);
    console.log('Resolve non-existent content:', !nonExistentResultObj.success ? 'PASS' : 'FAIL');
  } catch (error) {
    console.error('Resolve tool test failed:', error);
  }
}

/**
 * Test listing resource templates
 * 
 * @param {ChildProcess} server - The MCP server process
 */
async function testResourceTemplates(server) {
  console.log('\n--- Testing Resource Templates ---');
  
  try {
    const result = await sendRequest(server, 'list_resource_templates');
    
    // Verify the resource templates are returned
    const hasIndexTemplate = result.resourceTemplates.some(template => 
      template.uriTemplate.startsWith('index://')
    );
    
    console.log('Has index resource template:', hasIndexTemplate ? 'PASS' : 'FAIL');
  } catch (error) {
    console.error('List resource templates failed:', error);
  }
}

/**
 * Test reading resources
 * 
 * @param {ChildProcess} server - The MCP server process
 */
async function testReadResource(server) {
  console.log('\n--- Testing Read Resource ---');
  
  try {
    // Test reading a resource
    const result = await sendRequest(server, 'read_resource', {
      uri: 'index://mcp-test/data/entities'
    });
    
    // Verify the resource content is returned
    console.log('Read resource:', result.contents && result.contents.length > 0 ? 'PASS' : 'FAIL');
    
    // Test reading a non-existent resource
    try {
      await sendRequest(server, 'read_resource', {
        uri: 'index://nonexistent/endpoint/entities'
      });
      console.log('Read non-existent resource:', 'FAIL');
    } catch (error) {
      console.log('Read non-existent resource:', 'PASS');
    }
  } catch (error) {
    console.error('Read resource failed:', error);
  }
}

// Run the tests
runTests().catch(console.error);
