/**
 * PrimeOS JavaScript Library - Distributed Communication Module
 * Provides communication capabilities for distributed computation
 */

// Import the Prime object from core
const Prime = require('../../core');
const EventBus = require('../event-bus');

// Create the Communication module using IIFE
(function () {
  /**
   * Message types for distributed communication
   * @enum {string}
   */
  const MessageType = {
    /** Task assignment message */
    TASK_ASSIGNMENT: 'task_assignment',
    /** Task completion message */
    TASK_COMPLETION: 'task_completion',
    /** Task failure message */
    TASK_FAILURE: 'task_failure',
    /** Node discovery message */
    NODE_DISCOVERY: 'node_discovery',
    /** Node status update message */
    NODE_STATUS: 'node_status',
    /** Coherence check message */
    COHERENCE_CHECK: 'coherence_check',
    /** Coherence violation message */
    COHERENCE_VIOLATION: 'coherence_violation',
    /** Neural gradient synchronization message */
    GRADIENT_SYNC: 'gradient_sync',
    /** Neural layer state synchronization message */
    LAYER_SYNC: 'layer_sync',
    /** Heartbeat message */
    HEARTBEAT: 'heartbeat',
  };

  /**
   * Communication channel for secure, reliable distributed messaging
   */
  class CommunicationChannel {
    /**
     * Create a new communication channel
     * @param {Object} config - Channel configuration
     * @param {string} config.nodeId - ID of the local node
     * @param {string} [config.protocol='primeos'] - Communication protocol
     * @param {boolean} [config.encrypted=true] - Whether to encrypt messages
     * @param {number} [config.timeout=5000] - Default operation timeout (ms)
     * @param {number} [config.retryCount=3] - Number of retries for failed operations
     */
    constructor(config) {
      if (!Prime.Utils.isObject(config)) {
        throw new Prime.ValidationError(
          'Channel configuration must be an object',
        );
      }

      if (!config.nodeId) {
        throw new Prime.ValidationError('Node ID is required');
      }

      this.nodeId = config.nodeId;
      this.protocol = config.protocol || 'primeos';
      this.encrypted = config.encrypted !== false;
      this.timeout = config.timeout || 5000;
      this.retryCount = config.retryCount || 3;

      // Connection state
      this.connected = false;
      this.connectionAttempts = 0;

      // Message tracking
      this.pendingMessages = new Map();
      this.messageCounter = 0;

      // Connection metrics
      this.metrics = {
        messagesSent: 0,
        messagesReceived: 0,
        messagesDropped: 0,
        messagesRetried: 0,
        latency: 0,
      };

      // Event bus for channel events
      this.eventBus = new EventBus();

      // Initialize in mock mode (for testing)
      this._initializeMockMode();
    }

    /**
     * Initialize channel in mock mode
     * @private
     */
    _initializeMockMode() {
      Prime.Logger.info(
        `Initializing communication channel for node ${this.nodeId} in mock mode`,
      );

      // Mock implementation doesn't establish real connections
      // This would be replaced with actual connection logic in real deployment
      this.connected = true;

      // Set up periodic mock heartbeat
      this._heartbeatInterval = setInterval(() => {
        this._receiveMockHeartbeat();
      }, 5000);

      // Set up message handler
      this.eventBus.on('message:received', this._handleMessage.bind(this));
    }

    /**
     * Receive mock heartbeat
     * @private
     */
    _receiveMockHeartbeat() {
      // Simulate receiving a heartbeat message
      const heartbeatMessage = {
        type: MessageType.HEARTBEAT,
        source: 'cluster_manager',
        timestamp: Date.now(),
        data: {
          nodeCount: Math.floor(Math.random() * 5) + 1,
        },
      };

      this._handleMessage(heartbeatMessage);
    }

    /**
     * Handle an incoming message
     * @private
     * @param {Object} message - The received message
     */
    _handleMessage(message) {
      if (!message || !message.type) {
        this.metrics.messagesDropped++;
        return;
      }

      // Update metrics
      this.metrics.messagesReceived++;

      // Emit message event based on type
      this.eventBus.emit(`message:${message.type}`, message);

      // For request/response pattern, check for pending responses
      if (
        message.responseToId &&
        this.pendingMessages.has(message.responseToId)
      ) {
        const pendingRequest = this.pendingMessages.get(message.responseToId);

        // Calculate latency
        const latency = Date.now() - pendingRequest.timestamp;
        this.metrics.latency = 0.9 * this.metrics.latency + 0.1 * latency;

        // Resolve pending request
        pendingRequest.resolve(message);
        this.pendingMessages.delete(message.responseToId);
      }
    }

    /**
     * Send a message to a destination node
     * @param {string} destination - Destination node ID
     * @param {string} type - Message type (from MessageType)
     * @param {Object} data - Message payload
     * @param {Object} [options={}] - Send options
     * @param {boolean} [options.requireAck=false] - Whether to require acknowledgment
     * @param {number} [options.timeout] - Operation timeout (ms)
     * @returns {Promise<Object>} Promise that resolves with acknowledgment (if requested)
     */
    async send(destination, type, data, options = {}) {
      if (!this.connected) {
        throw new Prime.CommunicationError(
          'Communication channel not connected',
        );
      }

      if (!destination) {
        throw new Prime.ValidationError('Destination node ID is required');
      }

      if (!Object.values(MessageType).includes(type)) {
        throw new Prime.ValidationError(`Invalid message type: ${type}`);
      }

      // Generate message ID
      const messageId = `msg_${this.nodeId}_${++this.messageCounter}`;

      // Construct message
      const message = {
        id: messageId,
        type,
        source: this.nodeId,
        destination,
        timestamp: Date.now(),
        data: data || {},
      };

      // Apply encryption if enabled
      const preparedMessage = this.encrypted
        ? this._encryptMessage(message)
        : message;

      // Update metrics
      this.metrics.messagesSent++;

      // In mock mode, simulate sending by immediately 'receiving' if destination is self
      if (destination === this.nodeId) {
        // Simulate loopback
        setTimeout(() => this._handleMessage(preparedMessage), 5);

        // No acknowledgment for loopback in mock mode
        return Promise.resolve({ success: true });
      }

      // For mock mode with test destinations
      if (destination === 'test_node' || destination === 'cluster_manager') {
        // Simulate successful send

        // If acknowledgment required, wait for response
        if (options.requireAck) {
          return new Promise((resolve, reject) => {
            const timeout = options.timeout || this.timeout;

            // Store pending message for acknowledgment
            this.pendingMessages.set(messageId, {
              message,
              timestamp: Date.now(),
              resolve,
              reject,
            });

            // Simulate acknowledgment after delay
            setTimeout(
              () => {
                if (this.pendingMessages.has(messageId)) {
                  // Create mock acknowledgment
                  const ack = {
                    id: `ack_${destination}_${Date.now()}`,
                    type: `${type}_ack`,
                    source: destination,
                    destination: this.nodeId,
                    responseToId: messageId,
                    timestamp: Date.now(),
                    data: { success: true },
                  };

                  this._handleMessage(ack);
                }
              },
              Math.random() * 100 + 50,
            ); // Random delay for realism

            // Set timeout for acknowledgment
            setTimeout(() => {
              if (this.pendingMessages.has(messageId)) {
                // No acknowledgment received in time
                this.pendingMessages.delete(messageId);
                reject(
                  new Prime.CommunicationError(
                    'Message acknowledgment timeout',
                  ),
                );
              }
            }, timeout);
          });
        }

        // No acknowledgment required
        return Promise.resolve({ success: true });
      }

      // Unknown destination in mock mode
      return Promise.reject(
        new Prime.CommunicationError(`Unknown destination: ${destination}`),
      );
    }

    /**
     * Send a broadcast message to all nodes
     * @param {string} type - Message type (from MessageType)
     * @param {Object} data - Message payload
     * @returns {Promise<Object>} Promise that resolves when broadcast completes
     */
    async broadcast(type, data) {
      if (!this.connected) {
        throw new Prime.CommunicationError(
          'Communication channel not connected',
        );
      }

      if (!Object.values(MessageType).includes(type)) {
        throw new Prime.ValidationError(`Invalid message type: ${type}`);
      }

      // Generate message ID for broadcast
      const messageId = `broadcast_${this.nodeId}_${++this.messageCounter}`;

      // Construct broadcast message
      const message = {
        id: messageId,
        type,
        source: this.nodeId,
        destination: 'broadcast',
        timestamp: Date.now(),
        data: data || {},
      };

      // Apply encryption if enabled
      const preparedMessage = this.encrypted
        ? this._encryptMessage(message)
        : message;

      // Update metrics
      this.metrics.messagesSent++;

      // In mock mode, simulate broadcast by handling locally
      setTimeout(() => this._handleMessage(preparedMessage), 5);

      // Simulate successful broadcast in mock mode
      return Promise.resolve({
        success: true,
        recipientCount: Math.floor(Math.random() * 5) + 1,
      });
    }

    /**
     * Encrypt a message
     * @private
     * @param {Object} message - Message to encrypt
     * @returns {Object} Encrypted message
     */
    _encryptMessage(message) {
      // This is a mock implementation - in a real system this would
      // use proper encryption

      // Copy the message to avoid modifying the original
      const encryptedMessage = { ...message };

      // Add encryption metadata
      encryptedMessage.encrypted = true;
      encryptedMessage.encryptionAlgorithm = 'mock_aes256';

      return encryptedMessage;
    }

    /**
     * Subscribe to a specific message type
     * @param {string} type - Message type to subscribe to
     * @param {Function} callback - Callback function for messages
     * @returns {Function} Unsubscribe function
     */
    subscribe(type, callback) {
      if (!Object.values(MessageType).includes(type)) {
        throw new Prime.ValidationError(`Invalid message type: ${type}`);
      }

      if (typeof callback !== 'function') {
        throw new Prime.ValidationError('Callback must be a function');
      }

      // Subscribe to message events of specified type
      const eventName = `message:${type}`;
      this.eventBus.on(eventName, callback);

      // Return unsubscribe function
      return () => {
        this.eventBus.off(eventName, callback);
      };
    }

    /**
     * Request data from a destination node
     * @param {string} destination - Destination node ID
     * @param {string} type - Request type
     * @param {Object} data - Request data
     * @param {Object} [options={}] - Request options
     * @param {number} [options.timeout] - Request timeout (ms)
     * @returns {Promise<Object>} Promise that resolves with response
     */
    async request(destination, type, data, options = {}) {
      // This implements a request/response pattern on top of message sending
      const requestType = `${type}_request`;

      if (!Object.values(MessageType).includes(requestType)) {
        throw new Prime.ValidationError(`Invalid request type: ${requestType}`);
      }

      // Send with acknowledgment required
      const sendOptions = {
        requireAck: true,
        timeout: options.timeout || this.timeout,
      };

      try {
        const response = await this.send(
          destination,
          requestType,
          data,
          sendOptions,
        );
        return response;
      } catch (error) {
        // Handle retries if configured
        if (options.retry !== false && this.retryCount > 0) {
          return this._retryRequest(destination, type, data, options);
        }

        throw error;
      }
    }

    /**
     * Retry a failed request
     * @private
     * @param {string} destination - Destination node ID
     * @param {string} type - Request type
     * @param {Object} data - Request data
     * @param {Object} options - Request options
     * @param {number} [attemptCount=0] - Current attempt count
     * @returns {Promise<Object>} Promise that resolves with response
     */
    async _retryRequest(destination, type, data, options, attemptCount = 0) {
      // Max retries exceeded
      if (attemptCount >= this.retryCount) {
        throw new Prime.CommunicationError(
          `Max retry attempts (${this.retryCount}) exceeded for ${type} to ${destination}`,
        );
      }

      // Exponential backoff delay
      const delay = Math.min(100 * Math.pow(2, attemptCount), 2000);

      // Update metrics
      this.metrics.messagesRetried++;

      Prime.Logger.warn(
        `Retrying request ${type} to ${destination} (attempt ${attemptCount + 1})`,
        {
          delay,
          maxRetries: this.retryCount,
        },
      );

      // Wait before retry
      await new Promise((resolve) => setTimeout(resolve, delay));

      // Retry the request
      try {
        const requestType = `${type}_request`;
        const sendOptions = {
          requireAck: true,
          timeout: options.timeout || this.timeout,
        };

        return await this.send(destination, requestType, data, sendOptions);
      } catch (error) {
        // Recursive retry with incremented attempt count
        return this._retryRequest(
          destination,
          type,
          data,
          options,
          attemptCount + 1,
        );
      }
    }

    /**
     * Get channel metrics
     * @returns {Object} Current metrics
     */
    getMetrics() {
      return { ...this.metrics };
    }

    /**
     * Check if the channel is connected
     * @returns {boolean} Connection status
     */
    isConnected() {
      return this.connected;
    }

    /**
     * Disconnect the communication channel
     * @returns {Promise<void>} Promise that resolves when disconnected
     */
    async disconnect() {
      if (!this.connected) {
        return;
      }

      Prime.Logger.info(
        `Disconnecting communication channel for node ${this.nodeId}`,
      );

      // In mock mode, clean up intervals
      if (this._heartbeatInterval) {
        clearInterval(this._heartbeatInterval);
      }

      // Clean up event listeners
      this.eventBus.removeAllListeners();

      // Mark as disconnected
      this.connected = false;

      return Promise.resolve();
    }
  }

  /**
   * Message router for distributed computation
   * Routes messages between nodes and manages communication patterns
   */
  class MessageRouter {
    /**
     * Create a new message router
     * @param {Object} config - Router configuration
     * @param {string} config.nodeId - ID of the local node
     * @param {boolean} [config.cacheMessages=true] - Whether to cache messages
     * @param {number} [config.cacheTTL=60000] - Message cache TTL (ms)
     */
    constructor(config) {
      if (!Prime.Utils.isObject(config)) {
        throw new Prime.ValidationError(
          'Router configuration must be an object',
        );
      }

      if (!config.nodeId) {
        throw new Prime.ValidationError('Node ID is required');
      }

      this.nodeId = config.nodeId;
      this.cacheMessages = config.cacheMessages !== false;
      this.cacheTTL = config.cacheTTL || 60000;

      // Create communication channel
      this.channel = new CommunicationChannel({
        nodeId: this.nodeId,
        encrypted: true,
        timeout: 10000,
      });

      // Message handlers
      this.messageHandlers = new Map();

      // Message cache for deduplication and fault tolerance
      this.messageCache = new Map();

      // Route table for message routing
      this.routeTable = new Map();

      // Router metrics
      this.metrics = {
        messagesRouted: 0,
        handlerInvocations: 0,
        routeTableSize: 0,
        cacheHits: 0,
        cacheMisses: 0,
      };

      // Initialize message handlers
      this._initializeHandlers();

      Prime.Logger.info(`Message router initialized for node ${this.nodeId}`);
    }

    /**
     * Initialize default message handlers
     * @private
     */
    _initializeHandlers() {
      // Register handler for each message type
      for (const type of Object.values(MessageType)) {
        this._registerDefaultHandler(type);
      }

      // Special handling for specific types
      this.registerHandler(
        MessageType.NODE_DISCOVERY,
        this._handleNodeDiscovery.bind(this),
      );
      this.registerHandler(
        MessageType.HEARTBEAT,
        this._handleHeartbeat.bind(this),
      );
    }

    /**
     * Register a default message handler for a specific type
     * @private
     * @param {string} type - Message type
     */
    _registerDefaultHandler(type) {
      const defaultHandler = (message) => {
        Prime.Logger.debug(`Default handler for ${type}`, {
          source: message.source,
          id: message.id,
        });

        return Promise.resolve({
          success: true,
          handled: false,
          timestamp: Date.now(),
        });
      };

      this.registerHandler(type, defaultHandler);
    }

    /**
     * Register a message handler for a specific type
     * @param {string} type - Message type to handle
     * @param {Function} handler - Handler function
     * @throws {Error} If handler is not a function
     */
    registerHandler(type, handler) {
      if (typeof handler !== 'function') {
        throw new Prime.ValidationError('Handler must be a function');
      }

      this.messageHandlers.set(type, handler);

      // Subscribe to this message type on the channel
      this.channel.subscribe(type, async (message) => {
        try {
          await this._dispatchToHandler(type, message);
        } catch (error) {
          Prime.Logger.error(`Error handling ${type} message`, error);
        }
      });
    }

    /**
     * Dispatch a message to its registered handler
     * @private
     * @param {string} type - Message type
     * @param {Object} message - Message to handle
     * @returns {Promise<Object>} Handler result
     */
    async _dispatchToHandler(type, message) {
      // Check if message is already in cache
      if (this.cacheMessages && this.messageCache.has(message.id)) {
        this.metrics.cacheHits++;
        return this.messageCache.get(message.id).result;
      }

      const handler = this.messageHandlers.get(type);

      if (!handler) {
        this.metrics.cacheMisses++;
        return Promise.reject(
          new Error(`No handler registered for message type: ${type}`),
        );
      }

      try {
        // Update metrics
        this.metrics.handlerInvocations++;

        // Invoke handler
        const result = await handler(message);

        // Cache result if enabled
        if (this.cacheMessages) {
          this.messageCache.set(message.id, {
            result,
            timestamp: Date.now(),
          });

          // Schedule cache cleanup
          setTimeout(() => {
            this.messageCache.delete(message.id);
          }, this.cacheTTL);
        }

        return result;
      } catch (error) {
        Prime.Logger.error(`Error in handler for ${type}`, error);
        throw error;
      }
    }

    /**
     * Handle node discovery message
     * @private
     * @param {Object} message - Node discovery message
     */
    async _handleNodeDiscovery(message) {
      const { nodeId, address, capabilities } = message.data;

      if (nodeId && address) {
        // Update route table with new node information
        this.routeTable.set(nodeId, {
          address,
          capabilities: capabilities || {},
          lastSeen: Date.now(),
        });

        this.metrics.routeTableSize = this.routeTable.size;

        Prime.Logger.info(`Discovered node ${nodeId}`, {
          address,
          capabilities,
        });
      }

      return {
        success: true,
        handled: true,
        localNodeId: this.nodeId,
      };
    }

    /**
     * Handle heartbeat message
     * @private
     * @param {Object} message - Heartbeat message
     */
    async _handleHeartbeat(message) {
      // Update route table entry if the node is known
      if (this.routeTable.has(message.source)) {
        const entry = this.routeTable.get(message.source);
        entry.lastSeen = Date.now();

        // Update capabilities if included
        if (message.data && message.data.capabilities) {
          entry.capabilities = message.data.capabilities;
        }
      }

      return {
        success: true,
        handled: true,
        timestamp: Date.now(),
      };
    }

    /**
     * Route a message to its destination
     * @param {string} destination - Destination node ID
     * @param {string} type - Message type
     * @param {Object} data - Message payload
     * @param {Object} [options={}] - Routing options
     * @returns {Promise<Object>} Routing result
     */
    async route(destination, type, data, options = {}) {
      if (!destination) {
        throw new Prime.ValidationError('Destination node ID is required');
      }

      if (!Object.values(MessageType).includes(type)) {
        throw new Prime.ValidationError(`Invalid message type: ${type}`);
      }

      // Check if destination is self
      if (destination === this.nodeId) {
        // Local message handling
        const message = {
          id: `local_${Date.now()}_${++this.metrics.messagesRouted}`,
          type,
          source: this.nodeId,
          destination: this.nodeId,
          timestamp: Date.now(),
          data,
        };

        return this._dispatchToHandler(type, message);
      }

      // Check if destination is known
      if (!this.routeTable.has(destination) && destination !== 'broadcast') {
        // Unknown destination, try discovery first
        await this._discoverNode(destination).catch((error) => {
          // If discovery fails, continue with direct send anyway
          Prime.Logger.warn(`Node discovery failed for ${destination}`, error);
        });
      }

      // Update metrics
      this.metrics.messagesRouted++;

      // Use communication channel to send message
      if (destination === 'broadcast') {
        return this.channel.broadcast(type, data);
      } else {
        return this.channel.send(destination, type, data, options);
      }
    }

    /**
     * Attempt to discover a node
     * @private
     * @param {string} nodeId - Node ID to discover
     * @returns {Promise<Object>} Discovery result
     */
    async _discoverNode(nodeId) {
      // Send discovery request
      return this.channel.broadcast(MessageType.NODE_DISCOVERY, {
        targetNodeId: nodeId,
        requestingNodeId: this.nodeId,
        timestamp: Date.now(),
      });
    }

    /**
     * Send a gradient synchronization message
     * @param {string} destination - Destination node ID
     * @param {Object} gradients - Gradient data
     * @param {Object} [options={}] - Sync options
     * @returns {Promise<Object>} Sync result
     */
    async syncGradients(destination, gradients, options = {}) {
      return this.route(
        destination,
        MessageType.GRADIENT_SYNC,
        {
          gradients,
          layerId: options.layerId,
          iteration: options.iteration,
          timestamp: Date.now(),
        },
        options,
      );
    }

    /**
     * Send a layer state synchronization message
     * @param {string} destination - Destination node ID
     * @param {Object} layerState - Layer state data
     * @param {Object} [options={}] - Sync options
     * @returns {Promise<Object>} Sync result
     */
    async syncLayerState(destination, layerState, options = {}) {
      return this.route(
        destination,
        MessageType.LAYER_SYNC,
        {
          layerState,
          layerId: options.layerId,
          timestamp: Date.now(),
        },
        options,
      );
    }

    /**
     * Broadcast a node status update
     * @param {Object} status - Node status data
     * @returns {Promise<Object>} Broadcast result
     */
    async broadcastStatus(status) {
      return this.route('broadcast', MessageType.NODE_STATUS, {
        nodeId: this.nodeId,
        status,
        capabilities: status.capabilities || {},
        timestamp: Date.now(),
      });
    }

    /**
     * Get router metrics
     * @returns {Object} Current metrics
     */
    getMetrics() {
      const metrics = { ...this.metrics };

      // Add channel metrics
      metrics.channel = this.channel.getMetrics();

      // Add route table info
      metrics.knownNodes = Array.from(this.routeTable.keys());
      metrics.cacheSize = this.messageCache.size;

      return metrics;
    }

    /**
     * Clean up expired cache entries
     * @private
     */
    _cleanupCache() {
      const now = Date.now();
      let expiredCount = 0;

      // Check all cache entries
      for (const [messageId, entry] of this.messageCache.entries()) {
        if (now - entry.timestamp > this.cacheTTL) {
          this.messageCache.delete(messageId);
          expiredCount++;
        }
      }

      if (expiredCount > 0) {
        Prime.Logger.debug(
          `Cleaned up ${expiredCount} expired message cache entries`,
        );
      }
    }

    /**
     * Clean up stale route table entries
     * @private
     */
    _cleanupRouteTable() {
      const now = Date.now();
      const staleThreshold = 300000; // 5 minutes
      let staleCount = 0;

      // Check all route table entries
      for (const [nodeId, entry] of this.routeTable.entries()) {
        if (now - entry.lastSeen > staleThreshold) {
          this.routeTable.delete(nodeId);
          staleCount++;
        }
      }

      if (staleCount > 0) {
        this.metrics.routeTableSize = this.routeTable.size;
        Prime.Logger.info(`Removed ${staleCount} stale nodes from route table`);
      }
    }

    /**
     * Shut down the router
     * @returns {Promise<void>} Promise that resolves when shutdown is complete
     */
    async shutdown() {
      Prime.Logger.info('Shutting down message router');

      // Disconnect channel
      await this.channel.disconnect();

      // Clear all data structures
      this.messageHandlers.clear();
      this.messageCache.clear();
      this.routeTable.clear();

      Prime.Logger.info('Message router shutdown complete');
    }
  }

  // Add classes to Prime.Distributed namespace
  Prime.Distributed.Communication = {
    MessageType,
    CommunicationChannel,
    MessageRouter,
  };
})();

// Export the enhanced Prime object
module.exports = Prime;
