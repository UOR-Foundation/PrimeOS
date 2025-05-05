#!/usr/bin/env node

const fs = require('fs');
const path = require('path');
const { spawn } = require('child_process');

// Path to the MCP schema file
const schemaFilePath = path.join(process.cwd(), 'mcp25-03.json');

// Function to send a JSON-RPC request to the MCP server
function sendMcpRequest(method, params) {
  return new Promise((resolve, reject) => {
    // Start the MCP server process
    const mcpProcess = spawn('node', ['/workspaces/PrimeOS/.github/entrypoints/mcp/index.js']);
    
    let responseData = '';
    let errorData = '';
    
    mcpProcess.stdout.on('data', (data) => {
      responseData += data.toString();
      
      // Try to parse complete JSON responses
      try {
        const lines = responseData.split('\n');
        for (let i = 0; i < lines.length - 1; i++) {
          const line = lines[i].trim();
          if (line) {
            const response = JSON.parse(line);
            if (response.result) {
              resolve(response.result);
              mcpProcess.kill();
              return;
            } else if (response.error) {
              reject(new Error(`MCP error: ${JSON.stringify(response.error)}`));
              mcpProcess.kill();
              return;
            }
          }
        }
        // Keep the last line which might be incomplete
        responseData = lines[lines.length - 1];
      } catch (err) {
        // Incomplete JSON, continue collecting data
      }
    });
    
    mcpProcess.stderr.on('data', (data) => {
      errorData += data.toString();
      console.error(`MCP stderr: ${data}`);
    });
    
    mcpProcess.on('close', (code) => {
      if (code !== 0 && !responseData.includes('result')) {
        reject(new Error(`MCP process exited with code ${code}: ${errorData}`));
      }
    });
    
    // Send the JSON-RPC request
    const request = {
      jsonrpc: '2.0',
      id: 1,
      method,
      params
    };
    
    mcpProcess.stdin.write(JSON.stringify(request) + '\n');
  });
}

// Main function to add the MCP schema to the index
async function addMcpSchemaToIndex() {
  try {
    console.log('Reading MCP schema file...');
    const schemaContent = JSON.parse(fs.readFileSync(schemaFilePath, 'utf8'));
    
    // Update the schema with the proper $id and add required type property
    schemaContent.$id = 'https://modelcontextprotocol.io/schema';
    schemaContent.title = 'Model Context Protocol Schema';
    schemaContent.description = 'JSON Schema for the Model Context Protocol (MCP) specification';
    schemaContent.type = 'object'; // Add the required type property
    
    console.log('Adding MCP schema to the index...');
    const result = await sendMcpRequest('tools/call', {
      name: 'index_content',
      arguments: {
        content: schemaContent,
        apiName: 'modelcontextprotocol.io',
        endpointName: 'schema',
        mediaType: 'schema.json',
        isSchema: true
      }
    });
    
    console.log('MCP schema added successfully:');
    console.log(JSON.stringify(result, null, 2));
    
    return result;
  } catch (error) {
    console.error('Error adding MCP schema to index:', error);
    throw error;
  }
}

// Execute the main function
addMcpSchemaToIndex()
  .then(() => {
    console.log('Script completed successfully');
    process.exit(0);
  })
  .catch((error) => {
    console.error('Script failed:', error);
    process.exit(1);
  });
