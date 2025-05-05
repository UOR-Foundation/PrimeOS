/**
 * End-to-End Test for the Repository API MCP Server
 * 
 * Tests the end-to-end functionality of the mutate, validate, and resolve index APIs
 * by using the MCP tools to interact with the server.
 */

const { spawn } = require('child_process');
const fs = require('fs');
const path = require('path');

// Test data - fully compliant with JSON Schema Draft 2020-12
const testSchema = {
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://example.com/person.schema.json",
  "title": "Person",
  "description": "A person schema",
  "type": "object",
  "properties": {
    "name": { 
      "type": "string",
      "description": "The person's name"
    },
    "email": { 
      "type": "string", 
      "description": "The person's email address",
      "format": "email" 
    }
  },
  "required": ["name", "email"],
  "additionalProperties": false
};

const validData = {
  "name": "Jane Smith",
  "email": "jane.smith@example.com"
};

const invalidData = {
  "name": "Jane Smith",
  "email": "not-an-email"
};

// Global variable for the server process
let serverProcess;

/**
 * Run the end-to-end tests
 */
async function runEndToEndTests() {
  console.log('=== Running End-to-End Tests ===\n');
  
  // Start the MCP server
  console.log('Starting MCP server...');
  serverProcess = startMcpServer();
  
  try {
    // Wait for the server to start
    await new Promise(resolve => setTimeout(resolve, 2000));
    
    // Test the mutate endpoint
    await testMutateEndpoint();
    
    // Test the validate endpoint
    await testValidateEndpoint();
    
    // Test the resolve endpoint
    await testResolveEndpoint();
    
    console.log('\n=== End-to-End Tests Completed ===');
  } catch (error) {
    console.error('End-to-End test failed:', error);
  } finally {
    // Stop the MCP server
    if (serverProcess) {
      serverProcess.kill();
    }
  }
}

/**
 * Start the MCP server
 * 
 * @returns {ChildProcess} - The MCP server process
 */
function startMcpServer() {
  const serverProcess = spawn('node', [
    path.resolve(__dirname, '../../.github/entrypoints/mcp/index.js')
  ]);
  
  serverProcess.stdout.on('data', data => {
    try {
      // Try to parse as JSON
      const response = JSON.parse(data.toString());
      console.log('Server response:', JSON.stringify(response, null, 2));
    } catch (error) {
      // Not JSON, just log as is
      console.log('Server output:', data.toString());
    }
  });
  
  serverProcess.stderr.on('data', data => {
    console.error('Server error:', data.toString());
  });
  
  serverProcess.on('close', code => {
    console.log(`Server exited with code ${code}`);
  });
  
  return serverProcess;
}

/**
 * Send a request to the MCP server
 * 
 * @param {ChildProcess} serverProcess - The MCP server process
 * @param {Object} request - The request to send
 * @returns {Promise<Object>} - The server response
 */
function sendRequest(serverProcess, request) {
  return new Promise((resolve, reject) => {
    // Set up a response handler
    const responseHandler = data => {
      try {
        const response = JSON.parse(data.toString());
        
        if (response.id === request.id) {
          // Remove the response handler
          serverProcess.stdout.removeListener('data', responseHandler);
          
          if (response.error) {
            reject(response.error);
          } else {
            resolve(response.result);
          }
        }
      } catch (error) {
        // Ignore non-JSON output
      }
    };
    
    // Add the response handler
    serverProcess.stdout.on('data', responseHandler);
    
    // Send the request
    serverProcess.stdin.write(JSON.stringify(request) + '\n');
  });
}

/**
 * Test the mutate endpoint
 */
async function testMutateEndpoint() {
  console.log('\n--- Testing Mutate Endpoint ---');
  
  try {
    // Index a schema
    console.log('Indexing schema...');
    const indexSchemaRequest = {
      id: 'index-schema-request',
      method: 'call_tool',
      params: {
        name: 'index_content',
        arguments: {
          content: testSchema,
          apiName: 'e2e-test',
          endpointName: 'schema',
          mediaType: 'entities',
          isSchema: true
        }
      }
    };
    
    const indexSchemaResult = await sendRequest(serverProcess, indexSchemaRequest);
    const indexSchemaResultObj = JSON.parse(indexSchemaResult.content[0].text);
    console.log('Index schema result:', indexSchemaResultObj.success ? 'SUCCESS' : 'FAILURE');
    
    // Index valid data
    console.log('Indexing valid data...');
    const indexDataRequest = {
      id: 'index-data-request',
      method: 'call_tool',
      params: {
        name: 'index_content',
        arguments: {
          content: validData,
          apiName: 'e2e-test',
          endpointName: 'valid-data',
          mediaType: 'entities'
        }
      }
    };
    
    const indexDataResult = await sendRequest(serverProcess, indexDataRequest);
    const indexDataResultObj = JSON.parse(indexDataResult.content[0].text);
    console.log('Index valid data result:', indexDataResultObj.success ? 'SUCCESS' : 'FAILURE');
    
    // Test strict validation requirements
    
    // 1. Try to index invalid data (should fail validation)
    console.log('Trying to index invalid data (should fail)...');
    const indexInvalidDataRequest = {
      id: 'index-invalid-data-request',
      method: 'call_tool',
      params: {
        name: 'index_content',
        arguments: {
          content: invalidData,
          apiName: 'e2e-test',
          endpointName: 'invalid-data',
          mediaType: 'entities'
        }
      }
    };
    
    const indexInvalidDataResult = await sendRequest(serverProcess, indexInvalidDataRequest);
    const indexInvalidDataResultObj = JSON.parse(indexInvalidDataResult.content[0].text);
    console.log('Index invalid data result (should fail):', !indexInvalidDataResultObj.success ? 'EXPECTED FAILURE (PASS)' : 'UNEXPECTED SUCCESS (FAIL)');
    
    // 2. Try to index content without a schema (should fail)
    console.log('Trying to index content without a schema (should fail)...');
    const indexWithoutSchemaRequest = {
      id: 'index-without-schema-request',
      method: 'call_tool',
      params: {
        name: 'index_content',
        arguments: {
          content: validData,
          apiName: 'no-schema-test',
          endpointName: 'data',
          mediaType: 'entities'
        }
      }
    };
    
    const indexWithoutSchemaResult = await sendRequest(serverProcess, indexWithoutSchemaRequest);
    const indexWithoutSchemaResultObj = JSON.parse(indexWithoutSchemaResult.content[0].text);
    console.log('Index without schema result (should fail):', !indexWithoutSchemaResultObj.success ? 'EXPECTED FAILURE (PASS)' : 'UNEXPECTED SUCCESS (FAIL)');
    
    // 3. Try to index raw content (should fail)
    console.log('Trying to index raw content (should fail)...');
    const indexRawRequest = {
      id: 'index-raw-request',
      method: 'call_tool',
      params: {
        name: 'index_content',
        arguments: {
          content: "This is raw content",
          apiName: 'e2e-test',
          endpointName: 'raw',
          mediaType: 'text',
          isRaw: true
        }
      }
    };
    
    const indexRawResult = await sendRequest(serverProcess, indexRawRequest);
    const indexRawResultObj = JSON.parse(indexRawResult.content[0].text);
    console.log('Index raw content result (should fail):', !indexRawResultObj.success ? 'EXPECTED FAILURE (PASS)' : 'UNEXPECTED SUCCESS (FAIL)');
    
    // Verify files were created for successful operations
    console.log('Verifying files were created...');
    const schemaFileExists = fs.existsSync('e2e-test.schema.entities');
    const validDataFileExists = fs.existsSync('e2e-test.valid-data.entities');
    const invalidDataFileExists = fs.existsSync('e2e-test.invalid-data.entities');
    const noSchemaFileExists = fs.existsSync('no-schema-test.data.entities');
    const rawFileExists = fs.existsSync('e2e-test.raw.text');
    
    console.log('Schema file exists:', schemaFileExists ? 'YES' : 'NO');
    console.log('Valid data file exists:', validDataFileExists ? 'YES' : 'NO');
    console.log('Invalid data file exists (should not exist):', !invalidDataFileExists ? 'NO (PASS)' : 'YES (FAIL)');
    console.log('No-schema file exists (should not exist):', !noSchemaFileExists ? 'NO (PASS)' : 'YES (FAIL)');
    console.log('Raw file exists (should not exist):', !rawFileExists ? 'NO (PASS)' : 'YES (FAIL)');
  } catch (error) {
    console.error('Mutate endpoint test failed:', error);
  }
}

/**
 * Test the validate endpoint
 */
async function testValidateEndpoint() {
  console.log('\n--- Testing Validate Endpoint ---');
  
  try {
    // Validate valid data against schema
    console.log('Validating valid data against schema...');
    const validateValidDataRequest = {
      id: 'validate-valid-data-request',
      method: 'call_tool',
      params: {
        name: 'validate_json',
        arguments: {
          data: validData,
          schema: testSchema
        }
      }
    };
    
    const validateValidDataResult = await sendRequest(serverProcess, validateValidDataRequest);
    const validateValidDataResultObj = JSON.parse(validateValidDataResult.content[0].text);
    console.log('Validate valid data result:', validateValidDataResultObj.isValid ? 'VALID' : 'INVALID');
    
    // Validate invalid data against schema
    console.log('Validating invalid data against schema...');
    const validateInvalidDataRequest = {
      id: 'validate-invalid-data-request',
      method: 'call_tool',
      params: {
        name: 'validate_json',
        arguments: {
          data: invalidData,
          schema: testSchema
        }
      }
    };
    
    const validateInvalidDataResult = await sendRequest(serverProcess, validateInvalidDataRequest);
    const validateInvalidDataResultObj = JSON.parse(validateInvalidDataResult.content[0].text);
    console.log('Validate invalid data result:', validateInvalidDataResultObj.isValid ? 'VALID' : 'INVALID');
    
    // Validate schema
    console.log('Validating schema...');
    const validateSchemaRequest = {
      id: 'validate-schema-request',
      method: 'call_tool',
      params: {
        name: 'validate_json',
        arguments: {
          schema: testSchema,
          validateSchemaOnly: true
        }
      }
    };
    
    const validateSchemaResult = await sendRequest(serverProcess, validateSchemaRequest);
    const validateSchemaResultObj = JSON.parse(validateSchemaResult.content[0].text);
    console.log('Validate schema result:', validateSchemaResultObj.isValid ? 'VALID' : 'INVALID');
    
    // Validate data against indexed schema
    console.log('Validating data against indexed schema...');
    const validateAgainstIndexedSchemaRequest = {
      id: 'validate-against-indexed-schema-request',
      method: 'call_tool',
      params: {
        name: 'validate_json',
        arguments: {
          data: validData,
          apiName: 'e2e-test',
          endpointName: 'schema',
          mediaType: 'entities'
        }
      }
    };
    
    const validateAgainstIndexedSchemaResult = await sendRequest(serverProcess, validateAgainstIndexedSchemaRequest);
    const validateAgainstIndexedSchemaResultObj = JSON.parse(validateAgainstIndexedSchemaResult.content[0].text);
    console.log('Validate against indexed schema result:', validateAgainstIndexedSchemaResultObj.isValid ? 'VALID' : 'INVALID');
  } catch (error) {
    console.error('Validate endpoint test failed:', error);
  }
}

/**
 * Test the resolve endpoint
 */
async function testResolveEndpoint() {
  console.log('\n--- Testing Resolve Endpoint ---');
  
  try {
    // Resolve schema
    console.log('Resolving schema...');
    const resolveSchemaRequest = {
      id: 'resolve-schema-request',
      method: 'call_tool',
      params: {
        name: 'resolve_content',
        arguments: {
          apiName: 'e2e-test',
          endpointName: 'schema',
          mediaType: 'entities'
        }
      }
    };
    
    const resolveSchemaResult = await sendRequest(serverProcess, resolveSchemaRequest);
    const resolveSchemaResultObj = JSON.parse(resolveSchemaResult.content[0].text);
    console.log('Resolve schema result:', resolveSchemaResultObj.success ? 'SUCCESS' : 'FAILURE');
    
    if (resolveSchemaResultObj.success) {
      // Verify the resolved schema matches the original
      const schemaMatches = JSON.stringify(resolveSchemaResultObj.content) === JSON.stringify(testSchema);
      console.log('Resolved schema matches original:', schemaMatches ? 'YES' : 'NO');
    }
    
    // Resolve valid data
    console.log('Resolving valid data...');
    const resolveValidDataRequest = {
      id: 'resolve-valid-data-request',
      method: 'call_tool',
      params: {
        name: 'resolve_content',
        arguments: {
          apiName: 'e2e-test',
          endpointName: 'valid-data',
          mediaType: 'entities'
        }
      }
    };
    
    const resolveValidDataResult = await sendRequest(serverProcess, resolveValidDataRequest);
    const resolveValidDataResultObj = JSON.parse(resolveValidDataResult.content[0].text);
    console.log('Resolve valid data result:', resolveValidDataResultObj.success ? 'SUCCESS' : 'FAILURE');
    
    if (resolveValidDataResultObj.success) {
      // Verify the resolved data matches the original
      const dataMatches = JSON.stringify(resolveValidDataResultObj.content) === JSON.stringify(validData);
      console.log('Resolved data matches original:', dataMatches ? 'YES' : 'NO');
    }
    
    // Resolve invalid data
    console.log('Resolving invalid data...');
    const resolveInvalidDataRequest = {
      id: 'resolve-invalid-data-request',
      method: 'call_tool',
      params: {
        name: 'resolve_content',
        arguments: {
          apiName: 'e2e-test',
          endpointName: 'invalid-data',
          mediaType: 'entities'
        }
      }
    };
    
    const resolveInvalidDataResult = await sendRequest(serverProcess, resolveInvalidDataRequest);
    const resolveInvalidDataResultObj = JSON.parse(resolveInvalidDataResult.content[0].text);
    console.log('Resolve invalid data result:', resolveInvalidDataResultObj.success ? 'SUCCESS' : 'FAILURE');
    
    if (resolveInvalidDataResultObj.success) {
      // Verify the resolved data matches the original
      const dataMatches = JSON.stringify(resolveInvalidDataResultObj.content) === JSON.stringify(invalidData);
      console.log('Resolved invalid data matches original:', dataMatches ? 'YES' : 'NO');
    }
    
    // Resolve non-existent content
    console.log('Resolving non-existent content...');
    const resolveNonExistentRequest = {
      id: 'resolve-non-existent-request',
      method: 'call_tool',
      params: {
        name: 'resolve_content',
        arguments: {
          apiName: 'nonexistent',
          endpointName: 'endpoint',
          mediaType: 'entities'
        }
      }
    };
    
    const resolveNonExistentResult = await sendRequest(serverProcess, resolveNonExistentRequest);
    const resolveNonExistentResultObj = JSON.parse(resolveNonExistentResult.content[0].text);
    console.log('Resolve non-existent content result:', !resolveNonExistentResultObj.success ? 'EXPECTED FAILURE' : 'UNEXPECTED SUCCESS');
  } catch (error) {
    console.error('Resolve endpoint test failed:', error);
  }
}

// Run the end-to-end tests
runEndToEndTests().catch(console.error);
