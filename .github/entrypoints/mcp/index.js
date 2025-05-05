#!/usr/bin/env node
/**
 * Repository API MCP Server
 * 
 * Provides tools and resources for the index API
 */

// Import the index API libraries
const validateLib = require('../../lib/index/validate/index.js');
const mutateLib = require('../../lib/index/mutate/index.js');
const resolveLib = require('../../lib/index/resolve/index.js');

/**
 * Improved MCP Server implementation with robust connection handling
 */
class RepositoryApiServer {
  constructor() {
    this.isConnected = false;
    this.lastActivityTime = Date.now();
    this.heartbeatInterval = null;
    this.inputBuffer = '';
    
    // Set up error handling for various signals
    process.on('SIGINT', this.handleShutdown.bind(this, 'SIGINT'));
    process.on('SIGTERM', this.handleShutdown.bind(this, 'SIGTERM'));
    process.on('SIGHUP', this.handleShutdown.bind(this, 'SIGHUP'));
    process.on('SIGBREAK', this.handleShutdown.bind(this, 'SIGBREAK'));
    
    // Handle uncaught exceptions
    process.on('uncaughtException', (error) => {
      console.error(`Uncaught exception: ${error.message}`);
      console.error(error.stack);
      // Don't exit, try to keep the server running
    });
    
    // Handle unhandled promise rejections
    process.on('unhandledRejection', (reason, promise) => {
      console.error('Unhandled promise rejection:', reason);
      // Don't exit, try to keep the server running
    });

    // Set up stdin/stdout handling with improved buffering
    process.stdin.setEncoding('utf8');
    process.stdin.on('data', (chunk) => {
      this.lastActivityTime = Date.now();
      
      // Add the chunk to the buffer
      this.inputBuffer += chunk;
      
      // Process complete JSON objects from the buffer
      this.processInputBuffer();
    });
    
    // Handle stdin end event
    process.stdin.on('end', () => {
      console.error('stdin stream ended');
      this.isConnected = false;
      this.stopHeartbeat();
    });
    
    // Handle stdin error event
    process.stdin.on('error', (error) => {
      console.error(`stdin error: ${error.message}`);
      this.isConnected = false;
      this.stopHeartbeat();
    });
    
    // Handle stdout error event
    process.stdout.on('error', (error) => {
      console.error(`stdout error: ${error.message}`);
      this.isConnected = false;
      this.stopHeartbeat();
    });
  }
  
  /**
   * Process the input buffer to extract complete JSON objects
   */
  processInputBuffer() {
    // Look for newline-delimited JSON objects
    const lines = this.inputBuffer.split('\n');
    
    // Keep the last line if it's incomplete
    this.inputBuffer = lines.pop() || '';
    
    // Process each complete line
    for (const line of lines) {
      if (line.trim()) {
        this.handleInput(line);
      }
    }
  }
  
  /**
   * Handle server shutdown
   * 
   * @param {string} signal - The signal that triggered the shutdown
   */
  handleShutdown(signal) {
    console.error(`Server shutting down due to ${signal}`);
    this.stopHeartbeat();
    this.isConnected = false;
    
    // Flush any pending output
    try {
      process.stdout.write('', () => {
        process.exit(0);
      });
    } catch (error) {
      process.exit(0);
    }
  }
  
  /**
   * Start the heartbeat to keep the connection alive
   */
  startHeartbeat() {
    this.stopHeartbeat(); // Clear any existing interval
    
    this.heartbeatInterval = setInterval(() => {
      // Check if there's been activity in the last 30 seconds
      const inactiveTime = Date.now() - this.lastActivityTime;
      
      if (inactiveTime > 30000) {
        // Send a ping to keep the connection alive
        this.sendPing();
      }
    }, 15000); // Check every 15 seconds
  }
  
  /**
   * Stop the heartbeat
   */
  stopHeartbeat() {
    if (this.heartbeatInterval) {
      clearInterval(this.heartbeatInterval);
      this.heartbeatInterval = null;
    }
  }
  
  /**
   * Send a ping to keep the connection alive
   */
  sendPing() {
    try {
      // Send a comment that won't affect normal operation
      process.stderr.write('Ping: keeping connection alive\n');
      this.lastActivityTime = Date.now();
    } catch (error) {
      console.error(`Error sending ping: ${error.message}`);
      this.isConnected = false;
      this.stopHeartbeat();
    }
  }

  /**
   * Handle input from stdin
   * 
   * @param {string} input - The input from stdin
   */
  handleInput(input) {
    try {
      console.error(`Received input: ${input}`);
      
      const request = JSON.parse(input);
      
      console.error(`Parsed request: ${JSON.stringify(request)}`);
      
      if (!request.method || !request.id) {
        console.error('Invalid request format');
        this.sendError(null, 'Invalid request format');
        return;
      }
      
      switch (request.method) {
        case 'list_tools':
          console.error('Handling list_tools request');
          this.handleListTools(request);
          break;
        case 'call_tool':
          console.error('Handling call_tool request');
          this.handleCallTool(request);
          break;
        case 'list_resources':
          console.error('Handling list_resources request');
          this.handleListResources(request);
          break;
        case 'list_resource_templates':
          console.error('Handling list_resource_templates request');
          this.handleListResourceTemplates(request);
          break;
        case 'read_resource':
          console.error('Handling read_resource request');
          this.handleReadResource(request);
          break;
        default:
          console.error(`Unknown method: ${request.method}`);
          this.sendError(request.id, `Unknown method: ${request.method}`);
      }
    } catch (error) {
      console.error(`Error parsing request: ${error.message}`);
      this.sendError(null, `Error parsing request: ${error.message}`);
    }
  }

  /**
   * Send a response to stdout
   * 
   * @param {string} id - The request ID
   * @param {Object} result - The result to send
   */
  sendResponse(id, result) {
    const response = {
      id,
      result
    };
    
    console.error(`Sending response: ${JSON.stringify(response)}`);
    
    try {
      // Write the response and ensure it's flushed
      const responseStr = JSON.stringify(response) + '\n';
      
      // Use a synchronous write to ensure the response is sent immediately
      process.stdout.write(responseStr, (err) => {
        if (err) {
          console.error(`Error writing response: ${err.message}`);
          this.isConnected = false;
          this.stopHeartbeat();
        } else {
          // Update the last activity time
          this.lastActivityTime = Date.now();
        }
      });
    } catch (error) {
      console.error(`Error sending response: ${error.message}`);
      this.isConnected = false;
      this.stopHeartbeat();
    }
  }

  /**
   * Send an error to stdout
   * 
   * @param {string} id - The request ID
   * @param {string} message - The error message
   * @param {number} code - The error code
   */
  sendError(id, message, code = -32603) {
    const response = {
      id,
      error: {
        code,
        message
      }
    };
    
    console.error(`Sending error: ${JSON.stringify(response)}`);
    
    try {
      // Write the error and ensure it's flushed
      const responseStr = JSON.stringify(response) + '\n';
      
      // Use a synchronous write to ensure the error is sent immediately
      process.stdout.write(responseStr, (err) => {
        if (err) {
          console.error(`Error writing error response: ${err.message}`);
          this.isConnected = false;
          this.stopHeartbeat();
        } else {
          // Update the last activity time
          this.lastActivityTime = Date.now();
        }
      });
    } catch (error) {
      console.error(`Error sending error response: ${error.message}`);
      this.isConnected = false;
      this.stopHeartbeat();
    }
  }

  /**
   * Handle list_tools request
   * 
   * @param {Object} request - The request object
   */
  handleListTools(request) {
    const tools = [
      {
        name: 'validate_json',
        description: 'Validates JSON against a schema or validates a JSON schema',
        inputSchema: {
          type: 'object',
          properties: {
            data: {
              type: 'object',
              description: 'The JSON data to validate (required unless validateSchemaOnly is true)',
            },
            schema: {
              type: 'object',
              description: 'The JSON schema to validate against (required unless apiName, endpointName, and mediaType are provided)',
            },
            apiName: {
              type: 'string',
              description: 'The name of the API (required if schema is not provided)',
            },
            endpointName: {
              type: 'string',
              description: 'The name of the endpoint (required if schema is not provided)',
            },
            mediaType: {
              type: 'string',
              description: 'The media type identifier (required if schema is not provided)',
            },
            validateSchemaOnly: {
              type: 'boolean',
              description: 'If true, validates the schema against the JSON Schema specification',
              default: false,
            },
          },
          anyOf: [
            { required: ['data', 'schema'] },
            { required: ['data', 'apiName', 'endpointName', 'mediaType'] },
            { required: ['schema', 'validateSchemaOnly'] },
          ],
        },
      },
      {
        name: 'index_content',
        description: 'Indexes arbitrary JSON (including its JSON schema)',
        inputSchema: {
          type: 'object',
          properties: {
            content: {
              description: 'The content to index (can be a JSON object or a string)',
            },
            apiName: {
              type: 'string',
              description: 'The name of the API',
            },
            endpointName: {
              type: 'string',
              description: 'The name of the endpoint',
            },
            mediaType: {
              type: 'string',
              description: 'The media type identifier',
            },
            isSchema: {
              type: 'boolean',
              description: 'If true, the content is treated as a JSON schema and validated before indexing',
              default: false,
            },
            isRaw: {
              type: 'boolean',
              description: 'If true, the content is treated as raw content (string)',
              default: false,
            },
          },
          required: ['content', 'apiName', 'endpointName', 'mediaType'],
        },
      },
      {
        name: 'resolve_content',
        description: 'Resolves JSON from the index',
        inputSchema: {
          type: 'object',
          properties: {
            apiName: {
              type: 'string',
              description: 'The name of the API',
            },
            endpointName: {
              type: 'string',
              description: 'The name of the endpoint',
            },
            mediaType: {
              type: 'string',
              description: 'The media type identifier',
            },
            raw: {
              type: 'boolean',
              description: 'If true, returns the raw content (string) instead of parsing as JSON',
              default: false,
            },
          },
          required: ['apiName', 'endpointName', 'mediaType'],
        },
      },
    ];
    
    this.sendResponse(request.id, { tools });
  }

  /**
   * Handle call_tool request
   * 
   * @param {Object} request - The request object
   */
  handleCallTool(request) {
    try {
      if (!request.params || !request.params.name || !request.params.arguments) {
        this.sendError(request.id, 'Invalid call_tool request');
        return;
      }
      
      const { name, arguments: args } = request.params;
      
      let result;
      let isError = false;
      
      switch (name) {
        case 'validate_json':
          result = validateLib.validate(args);
          isError = !result.isValid;
          break;
        case 'index_content':
          result = mutateLib.mutate(args);
          isError = !result.success;
          break;
        case 'resolve_content':
          result = resolveLib.resolve(args);
          isError = !result.success;
          break;
        default:
          this.sendError(request.id, `Unknown tool: ${name}`);
          return;
      }
      
      this.sendResponse(request.id, {
        content: [
          {
            type: 'text',
            text: JSON.stringify(result, null, 2),
          },
        ],
        isError,
      });
    } catch (error) {
      this.sendError(request.id, `Error calling tool: ${error.message}`);
    }
  }

  /**
   * Handle list_resources request
   * 
   * @param {Object} request - The request object
   */
  handleListResources(request) {
    this.sendResponse(request.id, { resources: [] });
  }

  /**
   * Handle list_resource_templates request
   * 
   * @param {Object} request - The request object
   */
  handleListResourceTemplates(request) {
    const resourceTemplates = [
      {
        uriTemplate: 'index://{apiName}/{endpointName}/{mediaType}',
        name: 'Index API content',
        mimeType: 'application/json',
        description: 'Content from the index API',
      },
    ];
    
    this.sendResponse(request.id, { resourceTemplates });
  }

  /**
   * Handle read_resource request
   * 
   * @param {Object} request - The request object
   */
  handleReadResource(request) {
    try {
      if (!request.params || !request.params.uri) {
        this.sendError(request.id, 'Invalid read_resource request');
        return;
      }
      
      const { uri } = request.params;
      
      const match = uri.match(/^index:\/\/([^/]+)\/([^/]+)\/([^/]+)$/);
      
      if (!match) {
        this.sendError(request.id, `Invalid URI format: ${uri}`);
        return;
      }
      
      const apiName = decodeURIComponent(match[1]);
      const endpointName = decodeURIComponent(match[2]);
      const mediaType = decodeURIComponent(match[3]);
      
      const result = resolveLib.resolveJson(apiName, endpointName, mediaType);
      
      if (!result.success) {
        this.sendError(request.id, result.error);
        return;
      }
      
      this.sendResponse(request.id, {
        contents: [
          {
            uri,
            mimeType: 'application/json',
            text: JSON.stringify(result.content, null, 2),
          },
        ],
      });
    } catch (error) {
      this.sendError(request.id, `Error reading resource: ${error.message}`);
    }
  }

/**
 * Run the server
 */
run() {
  console.error('Repository API MCP server running on stdio');
  
  // Initialize connection
  this.isConnected = true;
  this.lastActivityTime = Date.now();
  
  // Start the heartbeat to keep the connection alive
  this.startHeartbeat();
  
  // Send an initialization message to indicate the server is ready
  process.stderr.write('MCP server initialized and ready\n');
  
  // Keep the process alive
  process.stdin.resume();
}
}

const server = new RepositoryApiServer();
server.run();
