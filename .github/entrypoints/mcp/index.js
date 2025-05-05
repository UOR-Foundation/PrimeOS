#!/usr/bin/env node
/**
 * Repository API MCP Server
 * 
 * Provides tools and resources for the index API
 * 
 * Version: 2.0.0 (Updated with search_index tool)
 */

// Standard JSON-RPC error codes
const PARSE_ERROR = -32700;
const INVALID_REQUEST = -32600;
const METHOD_NOT_FOUND = -32601;
const INVALID_PARAMS = -32602;
const INTERNAL_ERROR = -32603;

// Protocol versions
const PROTOCOL_VERSION_2024 = "2024-11-05";
const PROTOCOL_VERSION_2025 = "2025-03-26";

// Import the index API libraries
const validateLib = require('../../lib/index/validate/index.js');
const mutateLib = require('../../lib/index/mutate/index.js');
const resolveLib = require('../../lib/index/resolve/index.js');
const searchLib = require('../../lib/index/search/index.js');

/**
 * Improved MCP Server implementation with robust connection handling
 */
class RepositoryApiServer {
  constructor() {
    this.isConnected = false;
    this.lastActivityTime = Date.now();
    this.heartbeatInterval = null;
    this.inputBuffer = '';
    this.shutdownScheduled = false;
    this.protocolVersion = PROTOCOL_VERSION_2025; // Default to latest protocol version
    
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
    console.error(`Server received ${signal} signal`);
    
    // Only shutdown if explicitly requested via a signal
    if (this.shutdownScheduled) {
      console.error('Shutdown already scheduled, ignoring duplicate signal');
      return;
    }
    
    this.shutdownScheduled = true;
    console.error('Scheduling graceful shutdown');
    
    // Stop the heartbeat but keep the connection alive
    this.stopHeartbeat();
    
    // Flush any pending output before considering shutdown
    try {
      process.stdout.write('', () => {
        // Don't exit immediately - allow pending operations to complete
        console.error('Output flushed, server will remain active for pending operations');
      });
    } catch (error) {
      console.error(`Error flushing output: ${error.message}`);
    }
  }
  
  /**
   * Start the heartbeat to keep the connection alive
   */
  startHeartbeat() {
    this.stopHeartbeat(); // Clear any existing interval
    
    this.heartbeatInterval = setInterval(() => {
      // Check if there's been activity in the last 15 seconds
      const inactiveTime = Date.now() - this.lastActivityTime;
      
      if (inactiveTime > 15000) {
        // Send a ping to keep the connection alive
        this.sendPing();
      }
      
      // If shutdown is scheduled but we're still getting activity, cancel it
      if (this.shutdownScheduled && inactiveTime < 5000) {
        console.error('Cancelling scheduled shutdown due to recent activity');
        this.shutdownScheduled = false;
      }
    }, 5000); // Check more frequently (every 5 seconds)
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
      // Don't disconnect immediately on ping error, try to recover
      console.error('Attempting to recover from ping error');
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
      
      // If we receive any input, we're connected
      if (!this.isConnected) {
        console.error('Connection re-established');
        this.isConnected = true;
        this.startHeartbeat();
      }
      
      // Reset shutdown if it was scheduled
      if (this.shutdownScheduled) {
        console.error('Cancelling scheduled shutdown due to new request');
        this.shutdownScheduled = false;
      }
      
      // Handle JSON-RPC 2.0 protocol
      if (request.jsonrpc === "2.0") {
        if (request.method === "initialize") {
          console.error('Handling initialize request');
          
          // Get the client's requested protocol version
          const clientProtocolVersion = request.params?.protocolVersion || PROTOCOL_VERSION_2025;
          console.error(`Client requested protocol version: ${clientProtocolVersion}`);
          
          // Determine which protocol version to use
          let protocolVersion = PROTOCOL_VERSION_2025;
          let capabilities = {
            tools: {
              listChanged: false
            },
            resources: {
              subscribe: false,
              listChanged: false
            },
            resourceTemplates: true
          };
          
          // If client requests 2024 protocol version, use that
          if (clientProtocolVersion === PROTOCOL_VERSION_2024) {
            protocolVersion = PROTOCOL_VERSION_2024;
            // 2024 version capabilities structure
            capabilities = {
              tools: {
                listChanged: false
              },
              resources: {
                subscribe: false,
                listChanged: false
              },
              resourceTemplates: true
            };
          }
          
          // Store the protocol version for this session
          this.protocolVersion = protocolVersion;
          console.error(`Using protocol version: ${this.protocolVersion}`);
          
          this.sendJsonRpcResponse(request.id, {
            protocolVersion,
            serverInfo: {
              name: "repository-api-server",
              version: "0.1.0"
            },
            capabilities
          });
          return;
        } else if (request.method === "notifications/initialized") {
          console.error('Handling notifications/initialized request');
          // No response needed for notifications
          return;
        } else if (request.method === "tools/list") {
          console.error('Handling tools/list request');
          this.handleListTools(request);
          return;
        } else if (request.method === "tools/call") {
          console.error('Handling tools/call request');
          this.handleJsonRpcCallTool(request);
          return;
        } else if (request.method === "resources/list") {
          console.error('Handling resources/list request');
          this.handleListResources(request);
          return;
        } else if (request.method === "resource_templates/list" || request.method === "resources/templates/list") {
          console.error('Handling resource_templates/list request');
          this.handleListResourceTemplates(request);
          return;
        } else if (request.method === "resources/read") {
          console.error('Handling resources/read request');
          this.handleReadResource(request);
          return;
        } else if (request.method === "notifications/cancelled") {
          console.error('Handling notifications/cancelled request');
          // No response needed for notifications
          return;
        } else if (request.method === "ping") {
          console.error('Handling ping request');
          // Respond immediately to ping requests
          this.sendJsonRpcResponse(request.id, {});
          return;
        }
      }
      
      // Legacy protocol
      if (!request.method || !request.id) {
        console.error('Invalid request format');
        this.sendError(null, 'Invalid request format', INVALID_REQUEST);
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
          this.sendError(request.id, `Unknown method: ${request.method}`, METHOD_NOT_FOUND);
      }
    } catch (error) {
      console.error(`Error parsing request: ${error.message}`);
      this.sendError(null, `Error parsing request: ${error.message}`, PARSE_ERROR);
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
      jsonrpc: "2.0",
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
      jsonrpc: "2.0",
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
   * Send a JSON-RPC 2.0 response to stdout
   * 
   * @param {string} id - The request ID
   * @param {Object} result - The result to send
   */
  sendJsonRpcResponse(id, result) {
    const response = {
      jsonrpc: "2.0",
      id,
      result
    };
    
    console.error(`Sending JSON-RPC response: ${JSON.stringify(response)}`);
    
    try {
      // Write the response and ensure it's flushed
      const responseStr = JSON.stringify(response) + '\n';
      
      // Use a synchronous write to ensure the response is sent immediately
      process.stdout.write(responseStr, (err) => {
        if (err) {
          console.error(`Error writing JSON-RPC response: ${err.message}`);
          this.isConnected = false;
          this.stopHeartbeat();
        } else {
          // Update the last activity time
          this.lastActivityTime = Date.now();
          
        }
      });
    } catch (error) {
      console.error(`Error sending JSON-RPC response: ${error.message}`);
      this.isConnected = false;
      this.stopHeartbeat();
    }
  }

  /**
   * Send a JSON-RPC 2.0 error to stdout
   * 
   * @param {string} id - The request ID
   * @param {string} message - The error message
   * @param {number} code - The error code
   */
  sendJsonRpcError(id, message, code = -32603) {
    const response = {
      jsonrpc: "2.0",
      id,
      error: {
        code,
        message
      }
    };
    
    console.error(`Sending JSON-RPC error: ${JSON.stringify(response)}`);
    
    try {
      // Write the error and ensure it's flushed
      const responseStr = JSON.stringify(response) + '\n';
      
      // Use a synchronous write to ensure the error is sent immediately
      process.stdout.write(responseStr, (err) => {
        if (err) {
          console.error(`Error writing JSON-RPC error response: ${err.message}`);
          this.isConnected = false;
          this.stopHeartbeat();
        } else {
          // Update the last activity time
          this.lastActivityTime = Date.now();
          
        }
      });
    } catch (error) {
      console.error(`Error sending JSON-RPC error response: ${error.message}`);
      this.isConnected = false;
      this.stopHeartbeat();
    }
  }

  /**
   * Handle JSON-RPC 2.0 tools/call request
   * 
   * @param {Object} request - The request object
   */
  handleJsonRpcCallTool(request) {
    try {
      if (!request.params || !request.params.name || !request.params.arguments) {
        this.sendJsonRpcError(request.id, 'Invalid tools/call request', INVALID_PARAMS);
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
        case 'search_index':
          result = searchLib.searchIndex(args);
          isError = !result.success;
          break;
        default:
          this.sendJsonRpcError(request.id, `Unknown tool: ${name}`, METHOD_NOT_FOUND);
          return;
      }
      
      // Format the response according to the protocol version
      let responseContent;
      
      if (this.protocolVersion === PROTOCOL_VERSION_2024) {
        // 2024 version has a slightly different structure for TextContent
        responseContent = {
          content: [
            {
              type: 'text',
              text: JSON.stringify(result, null, 2)
            },
          ],
          isError,
        };
      } else {
        // 2025 version
        responseContent = {
          content: [
            {
              type: 'text',
              text: JSON.stringify(result, null, 2),
              annotations: {} // 2025 version uses annotations
            },
          ],
          isError,
        };
      }
      
      this.sendJsonRpcResponse(request.id, responseContent);
    } catch (error) {
      this.sendJsonRpcError(request.id, `Error calling tool: ${error.message}`, INTERNAL_ERROR);
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
      {
        name: 'search_index',
        description: 'Search for schemas in the index',
        inputSchema: {
          type: 'object',
          properties: {
            namespace: {
              type: 'string',
              description: 'Filter by schema namespace (e.g., "uor.foundation")'
            },
            schemaType: {
              type: 'string',
              description: 'Filter by schema type (e.g., "axiom", "test", "core")'
            },
            property: {
              type: 'string',
              description: 'Search for schemas containing a specific property'
            },
            propertyType: {
              type: 'string',
              description: 'Filter property by type (e.g., "string", "object", "array")'
            },
            references: {
              type: 'string',
              description: 'Find schemas that reference another schema by $id'
            },
            pattern: {
              type: 'string',
              description: 'Text pattern to match against schema $id, title, or description'
            },
            includeContent: {
              type: 'boolean',
              description: 'Whether to include full schema content in results',
              default: false
            },
            limit: {
              type: 'integer',
              description: 'Maximum number of results to return'
            },
            offset: {
              type: 'integer',
              description: 'Number of results to skip (for pagination)',
              default: 0
            },
            sortBy: {
              type: 'string',
              description: 'Field to sort by (id, title, type, namespace)',
              enum: ['id', 'title', 'type', 'namespace', 'entry.apiName', 'entry.endpointName']
            },
            sortOrder: {
              type: 'string',
              description: 'Sort order',
              enum: ['asc', 'desc'],
              default: 'asc'
            }
          }
        }
      }
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
        this.sendError(request.id, 'Invalid call_tool request', INVALID_PARAMS);
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
        case 'search_index':
          result = searchLib.searchIndex(args);
          isError = !result.success;
          break;
        default:
          this.sendError(request.id, `Unknown tool: ${name}`, METHOD_NOT_FOUND);
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
      this.sendError(request.id, `Error calling tool: ${error.message}`, INTERNAL_ERROR);
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
        this.sendError(request.id, 'Invalid read_resource request', INVALID_PARAMS);
        return;
      }
      
      const { uri } = request.params;
      
      const match = uri.match(/^index:\/\/([^/]+)\/([^/]+)\/([^/]+)$/);
      
      if (!match) {
        this.sendError(request.id, `Invalid URI format: ${uri}`, INVALID_PARAMS);
        return;
      }
      
      const apiName = decodeURIComponent(match[1]);
      const endpointName = decodeURIComponent(match[2]);
      const mediaType = decodeURIComponent(match[3]);
      
      const result = resolveLib.resolveJson(apiName, endpointName, mediaType);
      
      if (!result.success) {
        this.sendError(request.id, result.error || 'Resource not found', METHOD_NOT_FOUND);
        return;
      }
      
      // Format the response according to the protocol version
      let responseContent;
      
      if (this.protocolVersion === PROTOCOL_VERSION_2024) {
        // 2024 version has a slightly different structure for TextResourceContents
        responseContent = {
          contents: [
            {
              uri,
              mimeType: 'application/json',
              text: JSON.stringify(result.content, null, 2),
            },
          ],
        };
      } else {
        // 2025 version includes annotations
        responseContent = {
          contents: [
            {
              uri,
              mimeType: 'application/json',
              text: JSON.stringify(result.content, null, 2),
            },
          ],
        };
      }
      
      this.sendResponse(request.id, responseContent);
    } catch (error) {
      this.sendError(request.id, `Error reading resource: ${error.message}`, INTERNAL_ERROR);
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
