/**
 * PrimeOS JavaScript Library - Distributed Communication Module
 * Provides communication capabilities for distributed computation
 */

// Import the Prime object from core
const Prime = require("../../core");
const EventBus = require("../event-bus");
const crypto = require('crypto'); // Node.js crypto module for secure cryptographic operations

// Create the Communication module using IIFE
(function () {
  /**
   * Message types for distributed communication
   * @enum {string}
   */
  const MessageType = {
    /** Task assignment message */
    TASK_ASSIGNMENT: "task_assignment",
    /** Task completion message */
    TASK_COMPLETION: "task_completion",
    /** Task failure message */
    TASK_FAILURE: "task_failure",
    /** Node discovery message */
    NODE_DISCOVERY: "node_discovery",
    /** Node status update message */
    NODE_STATUS: "node_status",
    /** Coherence check message */
    COHERENCE_CHECK: "coherence_check",
    /** Coherence violation message */
    COHERENCE_VIOLATION: "coherence_violation",
    /** Neural gradient synchronization message */
    GRADIENT_SYNC: "gradient_sync",
    /** Neural layer state synchronization message */
    LAYER_SYNC: "layer_sync",
    /** Heartbeat message */
    HEARTBEAT: "heartbeat",
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
          "Channel configuration must be an object",
        );
      }

      if (!config.nodeId) {
        throw new Prime.ValidationError("Node ID is required");
      }

      this.nodeId = config.nodeId;
      this.protocol = config.protocol || "primeos";
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
      this.eventBus.on("message:received", this._handleMessage.bind(this));
    }

    /**
     * Receive mock heartbeat
     * @private
     */
    _receiveMockHeartbeat() {
      // Simulate receiving a heartbeat message
      const heartbeatMessage = {
        type: MessageType.HEARTBEAT,
        source: "cluster_manager",
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

      // Process the message
      let processedMessage = message;

      // If message is encrypted, decrypt it first
      if (message.encrypted === true && message.encryptedData) {
        try {
          processedMessage = this._decryptMessage(message);
        } catch (error) {
          Prime.Logger.error("Failed to decrypt message", {
            error,
            messageId: message.id,
            source: message.source,
          });
          this.metrics.messagesDropped++;
          return;
        }
      }

      // Emit message event based on type
      this.eventBus.emit(`message:${processedMessage.type}`, processedMessage);

      // For request/response pattern, check for pending responses
      if (
        processedMessage.responseToId &&
        this.pendingMessages.has(processedMessage.responseToId)
      ) {
        const pendingRequest = this.pendingMessages.get(
          processedMessage.responseToId,
        );

        // Calculate latency
        const latency = Date.now() - pendingRequest.timestamp;
        this.metrics.latency = 0.9 * this.metrics.latency + 0.1 * latency;

        // Resolve pending request
        pendingRequest.resolve(processedMessage);
        this.pendingMessages.delete(processedMessage.responseToId);
      }
    }

    /**
     * Decrypt an encrypted message
     * @private
     * @param {Object} encryptedMessage - Encrypted message
     * @returns {Object} Decrypted message
     */
    _decryptMessage(encryptedMessage) {
      try {
        // Validate required fields
        if (
          !encryptedMessage.encryptedData ||
          !encryptedMessage.iv ||
          !encryptedMessage.salt ||
          !encryptedMessage.authTag
        ) {
          throw new Error("Invalid encrypted message format");
        }

        // Get the encryption key
        const encryptionKey = this._getEncryptionKey();

        // Convert components from Base64
        const iv = this._base64ToBytes(encryptedMessage.iv);
        const salt = this._base64ToBytes(encryptedMessage.salt);
        const authTag = this._base64ToBytes(encryptedMessage.authTag);
        const encryptedData = this._base64ToBytes(
          encryptedMessage.encryptedData,
        );

        // Derive the key using the provided salt
        const derivedKey = this._deriveKey(encryptionKey, salt);

        // AES-GCM decryption in Node.js crypto module handles authTag verification
        // internally, so we pass it to the decryption method. Authentication
        // occurs as part of the decryption process.
        const decryptedBytes = this._aesGcmDecrypt(
          encryptedData,
          derivedKey,
          iv,
          authTag
        );

        // Convert bytes to string
        const decryptedText = new TextDecoder().decode(decryptedBytes);

        // Parse the JSON
        const decryptedMessage = JSON.parse(decryptedText);

        // Add metadata for debugging and security auditing
        decryptedMessage.securityMetadata = {
          wasEncrypted: true,
          decryptedAt: Date.now(),
          algorithm: encryptedMessage.encryptionAlgorithm,
          originalMetadata: encryptedMessage.metadata || {},
        };

        return decryptedMessage;
      } catch (error) {
        Prime.Logger.error("Decryption error", error);
        throw new Prime.CommunicationError("Failed to decrypt message", {
          cause: error,
        });
      }
    }

    /**
     * Decrypt data using AES-256-GCM
     * @private
     * @param {Uint8Array} encryptedData - Encrypted data
     * @param {Uint8Array} key - Decryption key
     * @param {Uint8Array} iv - Initialization vector
     * @param {Uint8Array} authTag - Authentication tag
     * @returns {Uint8Array} Decrypted data
     */
    _aesGcmDecrypt(encryptedData, key, iv, authTag) {
      try {
        // Convert inputs to Buffer objects
        const keyBuffer = Buffer.from(key);
        const ivBuffer = Buffer.from(iv);
        const encryptedBuffer = Buffer.from(encryptedData);
        const authTagBuffer = authTag ? Buffer.from(authTag) : null;
        
        // Create a decipher using AES-256-GCM
        const decipher = crypto.createDecipheriv('aes-256-gcm', keyBuffer, ivBuffer);
        
        // Set authentication tag if provided
        if (authTagBuffer) {
          decipher.setAuthTag(authTagBuffer);
        }
        
        // Decrypt the data
        let decryptedData = decipher.update(encryptedBuffer);
        decryptedData = Buffer.concat([decryptedData, decipher.final()]);
        
        return new Uint8Array(decryptedData);
      } catch (error) {
        // If decryption fails (e.g., due to tampering), this will throw an error
        Prime.Logger.error('AES-GCM decryption error', error);
        throw new Prime.CommunicationError('Failed to decrypt message: authentication failed', {
          cause: error
        });
      }
    }

    /**
     * Convert Base64 string to bytes
     * @private
     * @param {string} base64 - Base64 string
     * @returns {Uint8Array} Byte array
     */
    _base64ToBytes(base64) {
      // Use Buffer to properly convert from Base64
      const buffer = Buffer.from(base64, 'base64');
      return new Uint8Array(buffer);
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
          "Communication channel not connected",
        );
      }

      if (!destination) {
        throw new Prime.ValidationError("Destination node ID is required");
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
      if (destination === "test_node" || destination === "cluster_manager") {
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
                    "Message acknowledgment timeout",
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
          "Communication channel not connected",
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
        destination: "broadcast",
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
     * Encrypt a message with AES-256-GCM encryption
     * @private
     * @param {Object} message - Message to encrypt
     * @returns {Object} Encrypted message with metadata
     */
    _encryptMessage(message) {
      try {
        // Get or create encryption key for this session
        const encryptionKey = this._getEncryptionKey();

        // Serialize the message
        const messageJson = JSON.stringify(message);

        // Generate a random 12-byte IV (Initialization Vector)
        const iv = this._generateRandomBytes(12);

        // Generate a random 16-byte salt for key derivation
        const salt = this._generateRandomBytes(16);

        // Derive encryption key using PBKDF2 with the salt
        const derivedKey = this._deriveKey(encryptionKey, salt);

        // Encrypt the message using AES-256-GCM
        // Returns both encryptedData and authTag
        const { encryptedData, authTag } = this._aesGcmEncrypt(messageJson, derivedKey, iv);

        // Construct the encrypted message envelope
        return {
          id: message.id, // Keep original ID for message tracking
          type: message.type, // Keep original type for message routing
          source: message.source, // Keep source for routing
          destination: message.destination, // Keep destination for routing
          timestamp: message.timestamp, // Keep timestamp for metrics
          encrypted: true, // Flag to indicate encryption
          encryptionAlgorithm: "aes-256-gcm",
          iv: this._bytesToBase64(iv),
          salt: this._bytesToBase64(salt),
          authTag: this._bytesToBase64(authTag),
          encryptedData: this._bytesToBase64(encryptedData),
          // Include metadata for debugging and security auditing
          metadata: {
            encryptedAt: Date.now(),
            keyId: this._getKeyId(),
            version: "1.0",
          },
        };
      } catch (error) {
        Prime.Logger.error("Encryption error", error);
        throw new Prime.CommunicationError("Failed to encrypt message", {
          cause: error,
        });
      }
    }

    /**
     * Get or create encryption key for this channel
     * @private
     * @returns {Uint8Array} Encryption key
     */
    _getEncryptionKey() {
      if (!this._encryptionKey) {
        // Check if we have a stored key for this node
        const storedKey = this._retrieveStoredKey();
        
        if (storedKey) {
          // Use the stored key if available
          this._encryptionKey = storedKey;
        } else {
          // Generate a new secure random key using crypto module
          this._encryptionKey = this._generateRandomBytes(32); // 256-bit key
          
          // Store the key for future use
          this._storeKey(this._encryptionKey);
        }
        
        // Generate a key ID based on the key content
        this._keyId = this._generateKeyId(this._encryptionKey);
      }

      return this._encryptionKey;
    }
    
    /**
     * Retrieve stored encryption key for this node
     * @private
     * @returns {Uint8Array|null} Stored key or null if not found
     */
    _retrieveStoredKey() {
      try {
        // For security, we're using an in-memory key storage during the session
        // In a production environment, this would integrate with a secure key vault
        // or hardware security module (HSM)
        if (!Prime.Distributed.KeyStorage) {
          Prime.Distributed.KeyStorage = new Map();
        }
        
        const keyId = `channel_key_${this.nodeId}`;
        const storedKey = Prime.Distributed.KeyStorage.get(keyId);
        
        if (storedKey) {
          Prime.Logger.debug(`Retrieved stored encryption key for node ${this.nodeId}`);
          return storedKey;
        }
        
        return null;
      } catch (error) {
        Prime.Logger.warn(`Error retrieving stored key: ${error.message}`);
        return null;
      }
    }
    
    /**
     * Store encryption key for this node
     * @private
     * @param {Uint8Array} key - The encryption key to store
     */
    _storeKey(key) {
      try {
        // For security, we're using an in-memory key storage during the session
        // In a production environment, this would integrate with a secure key vault
        // or hardware security module (HSM)
        if (!Prime.Distributed.KeyStorage) {
          Prime.Distributed.KeyStorage = new Map();
        }
        
        const keyId = `channel_key_${this.nodeId}`;
        Prime.Distributed.KeyStorage.set(keyId, key);
        
        Prime.Logger.debug(`Stored encryption key for node ${this.nodeId}`);
      } catch (error) {
        Prime.Logger.warn(`Error storing key: ${error.message}`);
        // Continue using the key in memory even if storage fails
      }
    }

    /**
     * Get current encryption key ID
     * @private
     * @returns {string} Key ID
     */
    _getKeyId() {
      if (!this._keyId) {
        const key = this._getEncryptionKey();
        this._keyId = this._generateKeyId(key);
      }
      return this._keyId;
    }

    /**
     * Derive a cryptographically secure key from a seed
     * @private
     * @param {string} seed - Seed for key generation
     * @param {number} length - Key length in bytes
     * @returns {Uint8Array} Generated key
     */
    _deriveKeyFromSeed(seed, length) {
      // Convert seed to byte array
      const seedBytes = new TextEncoder().encode(seed);
      
      // Generate a random salt for key derivation
      const salt = this._generateRandomBytes(16);
      
      // Use PBKDF2 for secure key derivation
      // Parameters: password, salt, iterations, key length, hash algorithm
      const iterations = 100000; // High iteration count for security
      const keyLength = length; // Length as requested
      const hashAlgorithm = 'sha256';
      
      // Convert seedBytes to Buffer
      const seedBuffer = Buffer.from(seedBytes);
      const saltBuffer = Buffer.from(salt);
      
      // Generate the key using PBKDF2
      const derivedKeyBuffer = crypto.pbkdf2Sync(
        seedBuffer, 
        saltBuffer, 
        iterations, 
        keyLength, 
        hashAlgorithm
      );
      
      return new Uint8Array(derivedKeyBuffer);
    }

    /**
     * Generate cryptographically secure random bytes
     * @private
     * @param {number} length - Number of bytes to generate
     * @returns {Uint8Array} Random bytes
     */
    _generateRandomBytes(length) {
      // Use Node.js crypto.randomBytes for cryptographically secure random numbers
      const buffer = crypto.randomBytes(length);
      return new Uint8Array(buffer);
    }

    /**
     * Derive encryption key using salt
     * @private
     * @param {Uint8Array} masterKey - Master encryption key
     * @param {Uint8Array} salt - Salt for key derivation
     * @returns {Uint8Array} Derived key
     */
    _deriveKey(masterKey, salt) {
      // Use PBKDF2 for secure key derivation
      // Parameters: password, salt, iterations, key length, hash algorithm
      const iterations = 100000; // High iteration count for security
      const keyLength = 32; // 256-bit key
      const hashAlgorithm = 'sha256';
      
      // Convert masterKey to Buffer if it's a Uint8Array
      const masterKeyBuffer = Buffer.from(masterKey);
      const saltBuffer = Buffer.from(salt);
      
      // Generate the key using PBKDF2
      const derivedKeyBuffer = crypto.pbkdf2Sync(
        masterKeyBuffer, 
        saltBuffer, 
        iterations, 
        keyLength, 
        hashAlgorithm
      );
      
      return new Uint8Array(derivedKeyBuffer);
    }

    /**
     * Encrypt data using AES-256-GCM
     * @private
     * @param {string} plaintext - Data to encrypt
     * @param {Uint8Array} key - Encryption key
     * @param {Uint8Array} iv - Initialization vector
     * @returns {Object} Encrypted data and auth tag
     */
    _aesGcmEncrypt(plaintext, key, iv) {
      // Convert inputs to Buffer objects
      const keyBuffer = Buffer.from(key);
      const ivBuffer = Buffer.from(iv);
      const plaintextBuffer = Buffer.from(plaintext);
      
      // Create a cipher using AES-256-GCM
      const cipher = crypto.createCipheriv('aes-256-gcm', keyBuffer, ivBuffer);
      
      // Encrypt the data
      let encryptedData = cipher.update(plaintextBuffer);
      encryptedData = Buffer.concat([encryptedData, cipher.final()]);
      
      // Get the authentication tag
      const authTag = cipher.getAuthTag();
      
      return {
        encryptedData: new Uint8Array(encryptedData),
        authTag: new Uint8Array(authTag)
      };
    }

    /**
     * Generate authentication tag for message integrity
     * @private
     * @param {string} message - Message to authenticate
     * @param {Uint8Array} key - Authentication key
     * @returns {Uint8Array} Authentication tag
     */
    _generateMessageAuthTag(message, key) {
      // Use HMAC-SHA256 for secure message authentication
      const keyBuffer = Buffer.from(key);
      const messageBuffer = Buffer.from(message);
      
      // Create HMAC using SHA-256
      const hmac = crypto.createHmac('sha256', keyBuffer);
      
      // Update with the message
      hmac.update(messageBuffer);
      
      // Get the digest
      const digest = hmac.digest();
      
      // Return the first 16 bytes (128 bits) as the authentication tag
      return new Uint8Array(digest.slice(0, 16));
    }

    /**
     * Verify authentication tag for message integrity
     * @private
     * @param {Uint8Array} encryptedData - The encrypted data
     * @param {Uint8Array} key - The encryption key
     * @param {Uint8Array} iv - The initialization vector
     * @param {Uint8Array} receivedTag - The received authentication tag
     * @returns {boolean} Whether the tag is valid
     */
    _verifyAuthTag(encryptedData, key, iv, receivedTag) {
      try {
        // Create authentication context using both encrypted data and IV
        const authContext = Buffer.concat([
          Buffer.from(iv),
          Buffer.from(encryptedData)
        ]);
        
        // Generate the expected tag using HMAC
        const computedTag = this._computeAuthTag(authContext, key);
        
        // Use a constant-time comparison function to prevent timing attacks
        return crypto.timingSafeEqual(
          Buffer.from(computedTag), 
          Buffer.from(receivedTag)
        );
      } catch (error) {
        Prime.Logger.error("Authentication tag verification error", error);
        return false;
      }
    }

    /**
     * Compute authentication tag for verification
     * @private
     * @param {Buffer|Uint8Array} data - Data to authenticate
     * @param {Uint8Array} key - Authentication key
     * @returns {Uint8Array} Computed authentication tag
     */
    _computeAuthTag(data, key) {
      // Use HMAC-SHA256 for secure message authentication
      const keyBuffer = Buffer.from(key);
      const dataBuffer = Buffer.isBuffer(data) ? data : Buffer.from(data);
      
      // Create HMAC using SHA-256
      const hmac = crypto.createHmac('sha256', keyBuffer);
      
      // Update with the data
      hmac.update(dataBuffer);
      
      // Get the digest
      const digest = hmac.digest();
      
      // Return the first 16 bytes (128 bits) as the authentication tag
      return new Uint8Array(digest.slice(0, 16));
    }

    /**
     * Generate key ID from encryption key
     * @private
     * @param {Uint8Array} key - Encryption key
     * @returns {string} Key ID
     */
    _generateKeyId(key) {
      // Use a cryptographic hash function to create a unique ID for the key
      const hash = crypto.createHash('sha256');
      hash.update(Buffer.from(key));
      
      // Get the digest as hex and format as a key ID
      const digest = hash.digest('hex');
      return `key-${digest.substring(0, 16)}`;
    }

    /**
     * Convert bytes to Base64 string
     * @private
     * @param {Uint8Array} bytes - Bytes to convert
     * @returns {string} Base64 string
     */
    _bytesToBase64(bytes) {
      // Use Buffer to properly convert to Base64
      const buffer = Buffer.from(bytes);
      return buffer.toString('base64');
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

      if (typeof callback !== "function") {
        throw new Prime.ValidationError("Callback must be a function");
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
     * Receive a message (used for testing)
     * @param {Object} message - The message to receive
     * @returns {Promise<Object>} Promise that resolves when the message is handled
     */
    receive(message) {
      return new Promise((resolve) => {
        setTimeout(() => {
          this._handleMessage(message);
          resolve({ status: "received" });
        }, 5);
      });
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
          "Router configuration must be an object",
        );
      }

      if (!config.nodeId) {
        throw new Prime.ValidationError("Node ID is required");
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
      if (typeof handler !== "function") {
        throw new Prime.ValidationError("Handler must be a function");
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
        throw new Prime.ValidationError("Destination node ID is required");
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
      if (!this.routeTable.has(destination) && destination !== "broadcast") {
        // Unknown destination, try discovery first
        await this._discoverNode(destination).catch((error) => {
          // If discovery fails, continue with direct send anyway
          Prime.Logger.warn(`Node discovery failed for ${destination}`, error);
        });
      }

      // Update metrics
      this.metrics.messagesRouted++;

      // Use communication channel to send message
      if (destination === "broadcast") {
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
      return this.route("broadcast", MessageType.NODE_STATUS, {
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
      Prime.Logger.info("Shutting down message router");

      // Disconnect channel
      await this.channel.disconnect();

      // Clear all data structures
      this.messageHandlers.clear();
      this.messageCache.clear();
      this.routeTable.clear();

      Prime.Logger.info("Message router shutdown complete");
    }
  }

  /**
   * Communication hub for distributed computation
   * Manages communication between nodes in the distributed system
   */
  class CommunicationHub {
    /**
     * Create a new communication hub
     * @param {Object} config - Hub configuration
     * @param {ClusterManager} config.clusterManager - Cluster manager instance
     * @param {boolean} [config.encrypted=true] - Whether to encrypt messages
     * @param {number} [config.messageQueueCapacity=1000] - Maximum messages in queue
     */
    constructor(config) {
      if (!Prime.Utils.isObject(config)) {
        throw new Prime.ValidationError("Hub configuration must be an object");
      }

      if (!config.clusterManager) {
        throw new Prime.ValidationError("Cluster manager is required");
      }

      this.clusterManager = config.clusterManager;
      this.encrypted = config.encrypted !== false;
      this.messageQueueCapacity = config.messageQueueCapacity || 1000;

      // Node ID for this hub (use cluster manager coordinator or generate one)
      this.nodeId = config.nodeId || "hub_" + Date.now().toString(36);

      // Communication channels for each node
      this.channels = new Map();

      // Message queues for each node, prioritized by message priority
      this.messageQueues = new Map();

      // Event bus for hub events
      this.eventBus = new EventBus();

      // Hub metrics
      this.metrics = {
        messagesRouted: 0,
        messagesSent: 0,
        messagesReceived: 0,
        messagesDropped: 0,
        lastUpdate: Date.now(),
      };

      // Initialize hub
      this._initialize();

      Prime.Logger.info("Communication hub initialized", {
        nodeId: this.nodeId,
        encryptionEnabled: this.encrypted,
      });
    }

    /**
     * Initialize the communication hub
     * @private
     */
    _initialize() {
      // Set up event listeners on the cluster manager
      if (this.clusterManager.eventBus) {
        this.clusterManager.eventBus.on(
          "node:registered",
          this._handleNodeRegistered.bind(this),
        );
        this.clusterManager.eventBus.on(
          "node:unregistered",
          this._handleNodeUnregistered.bind(this),
        );
      }

      // Initialize channels for existing nodes
      const nodes = this.clusterManager.nodes || new Map();
      for (const [nodeId, node] of nodes.entries()) {
        this._createChannelForNode(nodeId, node);
      }

      // Create a primary communication channel for hub-wide messages
      this.primaryChannel = new CommunicationChannel({
        nodeId: this.nodeId,
        encrypted: this.encrypted,
      });

      // Subscribe to important message types
      this.primaryChannel.subscribe(
        MessageType.NODE_DISCOVERY,
        this._handleNodeDiscovery.bind(this),
      );
      this.primaryChannel.subscribe(
        MessageType.COHERENCE_VIOLATION,
        this._handleCoherenceViolation.bind(this),
      );
    }

    /**
     * Handle node registration event
     * @private
     * @param {Object} eventData - Event data
     */
    _handleNodeRegistered(eventData) {
      const { nodeId } = eventData;
      const node = this.clusterManager.getNode(nodeId);

      if (node) {
        this._createChannelForNode(nodeId, node);
      }
    }

    /**
     * Handle node unregistration event
     * @private
     * @param {Object} eventData - Event data
     */
    _handleNodeUnregistered(eventData) {
      const { nodeId } = eventData;
      this._removeChannelForNode(nodeId);
    }

    /**
     * Create a communication channel for a node
     * @private
     * @param {string} nodeId - Node ID
     * @param {ClusterNode} node - Cluster node
     */
    _createChannelForNode(nodeId, node) {
      // Skip if channel already exists
      if (this.channels.has(nodeId)) {
        return;
      }

      // Create channel
      const channel = new CommunicationChannel({
        nodeId: this.nodeId,
        encrypted: this.encrypted,
      });

      // Store channel
      this.channels.set(nodeId, channel);

      // Create message queue for this node
      this.messageQueues.set(nodeId, {
        high: [],
        medium: [],
        low: [],
        lastProcessed: Date.now(),
      });

      Prime.Logger.info(`Created communication channel for node ${nodeId}`, {
        nodeType: node.type,
        address: node.address,
      });
    }

    /**
     * Remove a communication channel for a node
     * @private
     * @param {string} nodeId - Node ID
     */
    _removeChannelForNode(nodeId) {
      // Get channel
      const channel = this.channels.get(nodeId);
      if (!channel) {
        return;
      }

      // Disconnect channel
      channel.disconnect().catch((error) => {
        Prime.Logger.warn(`Error disconnecting channel for node ${nodeId}`, {
          error: error.message,
        });
      });

      // Remove channel and queue
      this.channels.delete(nodeId);
      this.messageQueues.delete(nodeId);

      Prime.Logger.info(`Removed communication channel for node ${nodeId}`);
    }

    /**
     * Handle node discovery message
     * @private
     * @param {Object} message - Node discovery message
     */
    _handleNodeDiscovery(message) {
      const { nodeId, address, capabilities } = message.data || {};

      if (nodeId && address) {
        // Check if node is already registered
        if (!this.clusterManager.getNode(nodeId)) {
          // Auto-register the node with the cluster manager
          try {
            this.clusterManager.addNode({
              id: nodeId,
              type: Prime.Distributed.Cluster.NodeType.WORKER,
              address,
              capabilities,
            });

            Prime.Logger.info(`Auto-registered discovered node ${nodeId}`, {
              address,
              capabilities,
            });
          } catch (error) {
            Prime.Logger.warn(`Failed to auto-register node ${nodeId}`, {
              error: error.message,
            });
          }
        }
      }
    }

    /**
     * Handle coherence violation message
     * @private
     * @param {Object} message - Coherence violation message
     */
    _handleCoherenceViolation(message) {
      const { violation } = message.data || {};

      if (violation) {
        Prime.Logger.warn("Coherence violation received", {
          type: violation.type,
          severity: violation.severity,
          source: message.source,
        });

        // Emit violation event
        this.eventBus.emit("coherence:violation", {
          violation,
          source: message.source,
          timestamp: Date.now(),
        });
      }
    }

    /**
     * Route a message to its destination
     * @param {Object} message - Message to route
     * @returns {Promise<Object>} Routing result
     */
    async routeMessage(message) {
      if (!message || !message.type || !message.destination) {
        throw new Prime.ValidationError("Invalid message format");
      }

      // Validate message type
      if (!Object.values(MessageType).includes(message.type)) {
        throw new Prime.ValidationError(`Invalid message type: ${message.type}`);
      }

      // Update metrics
      this.metrics.messagesRouted++;
      this.metrics.lastUpdate = Date.now();

      // Get destination node
      const destination = message.destination;

      // Check if channel exists for destination
      if (!this.channels.has(destination)) {
        // Auto-create channel if node exists in cluster manager
        const node = this.clusterManager.getNode(destination);
        if (node) {
          this._createChannelForNode(destination, node);
        } else {
          this.metrics.messagesDropped++;
          throw new Prime.CommunicationError(
            `No channel available for destination: ${destination}`,
          );
        }
      }

      const channel = this.channels.get(destination);

      // Add message to queue based on priority
      const queue = this.messageQueues.get(destination);
      if (queue) {
        const priority = message.priority || "medium";
        const priorityQueue = queue[priority.toLowerCase()] || queue.medium;

        // Check queue capacity
        if (
          priorityQueue.length >=
          this.messageQueueCapacity / Object.keys(queue).length
        ) {
          this.metrics.messagesDropped++;
          throw new Prime.CommunicationError(
            `Message queue for ${destination} is full`,
          );
        }

        // Add to queue
        priorityQueue.push(message);

        // Return success
        return {
          success: true,
          queued: true,
          destination,
        };
      }

      // If no queue, send directly
      try {
        const result = await channel.send(
          destination,
          message.type,
          message.payload || message.data || {},
        );
        this.metrics.messagesSent++;
        return result;
      } catch (error) {
        this.metrics.messagesDropped++;
        throw error;
      }
    }

    /**
     * Process message queue for a node
     * @param {string} nodeId - Node ID
     * @returns {Promise<Object>} Processing result
     */
    async processMessageQueue(nodeId) {
      const queue = this.messageQueues.get(nodeId);
      if (!queue) {
        return { processed: 0, success: true };
      }

      const channel = this.channels.get(nodeId);
      if (!channel) {
        return { processed: 0, success: false, error: "No channel for node" };
      }

      let processed = 0;
      let errors = 0;

      // Process in priority order: high, medium, low
      for (const priority of ["high", "medium", "low"]) {
        const priorityQueue = queue[priority];
        if (!priorityQueue || priorityQueue.length === 0) {
          continue;
        }

        // Process all messages in this priority queue
        while (priorityQueue.length > 0) {
          const message = priorityQueue.shift();
          try {
            await channel.send(
              nodeId,
              message.type,
              message.payload || message.data || {},
            );
            processed++;
            this.metrics.messagesSent++;
          } catch (error) {
            errors++;
            this.metrics.messagesDropped++;
            Prime.Logger.error(`Error sending message to ${nodeId}`, {
              error: error.message,
              messageType: message.type,
            });
          }
        }
      }

      // Update last processed timestamp
      queue.lastProcessed = Date.now();

      return {
        processed,
        errors,
        success: errors === 0,
      };
    }

    /**
     * Send a message to multiple nodes
     * @param {Array<string>} destinations - Destination node IDs
     * @param {string} type - Message type
     * @param {Object} data - Message data
     * @param {Object} [options={}] - Send options
     * @returns {Promise<Object>} Send results
     */
    async multicast(destinations, type, data, options = {}) {
      if (!Array.isArray(destinations) || destinations.length === 0) {
        throw new Prime.ValidationError(
          "Destinations must be a non-empty array",
        );
      }

      if (!Object.values(MessageType).includes(type)) {
        throw new Prime.ValidationError(`Invalid message type: ${type}`);
      }

      // Send to each destination
      const results = await Promise.allSettled(
        destinations.map((destination) => {
          return this.routeMessage({
            type,
            destination,
            data,
            priority: options.priority || "medium",
          });
        }),
      );

      // Compile results
      const successCount = results.filter(
        (result) => result.status === "fulfilled",
      ).length;
      const errorCount = results.length - successCount;

      return {
        success: errorCount === 0,
        totalDestinations: destinations.length,
        successCount,
        errorCount,
      };
    }

    /**
     * Broadcast a message to all nodes
     * @param {string} type - Message type
     * @param {Object} data - Message data
     * @returns {Promise<Object>} Broadcast result
     */
    async broadcast(type, data) {
      if (!Object.values(MessageType).includes(type)) {
        throw new Prime.ValidationError(`Invalid message type: ${type}`);
      }

      try {
        // Use primary channel for broadcasting
        const result = await this.primaryChannel.broadcast(type, data);
        this.metrics.messagesSent++;
        return result;
      } catch (error) {
        this.metrics.messagesDropped++;
        throw error;
      }
    }

    /**
     * Get cluster status through communication hub
     * @returns {Promise<Object>} Cluster status
     */
    async getClusterStatus() {
      // Get nodes from cluster manager
      const nodeIds = Array.from(this.clusterManager.nodes.keys());
      const nodeStatuses = {};

      // Get status for each node
      for (const nodeId of nodeIds) {
        const node = this.clusterManager.getNode(nodeId);
        if (node) {
          nodeStatuses[nodeId] = node.getStatus();
        }
      }

      // Calculate aggregates
      const totalNodes = nodeIds.length;
      const readyNodes = Object.values(nodeStatuses).filter(
        (status) => status.state === "ready" || status.state === "working",
      ).length;
      const errorNodes = Object.values(nodeStatuses).filter(
        (status) => status.state === "error",
      ).length;

      return {
        timestamp: Date.now(),
        nodes: nodeStatuses,
        aggregates: {
          totalNodes,
          readyNodes,
          errorNodes,
          readyPercentage: totalNodes > 0 ? (readyNodes / totalNodes) * 100 : 0,
        },
        hub: {
          nodeId: this.nodeId,
          channels: this.channels.size,
          metrics: this.getMetrics(),
        },
      };
    }

    /**
     * Get the number of connected nodes
     * @returns {number} Number of nodes
     */
    getNodeCount() {
      return this.channels.size;
    }

    /**
     * Get all communication channels
     * @returns {Object} Map of nodeId to channel
     */
    getChannels() {
      // Convert Map to plain object for easier use in tests
      const channelsObj = {};
      for (const [nodeId, channel] of this.channels.entries()) {
        channelsObj[nodeId] = channel;
      }
      return channelsObj;
    }

    /**
     * Get communication channel for a specific node
     * @param {string} nodeId - Node ID
     * @returns {CommunicationChannel} Communication channel
     */
    getChannelForNode(nodeId) {
      return this.channels.get(nodeId);
    }

    /**
     * Get metrics for the communication hub
     * @returns {Object} Hub metrics
     */
    getMetrics() {
      // Get channel metrics
      const channelMetrics = {};
      for (const [nodeId, channel] of this.channels.entries()) {
        channelMetrics[nodeId] = channel.getMetrics();
      }

      // Get queue metrics
      const queueMetrics = {};
      for (const [nodeId, queue] of this.messageQueues.entries()) {
        queueMetrics[nodeId] = {
          highPriority: queue.high.length,
          mediumPriority: queue.medium.length,
          lowPriority: queue.low.length,
          total: queue.high.length + queue.medium.length + queue.low.length,
          lastProcessed: queue.lastProcessed,
        };
      }

      return {
        ...this.metrics,
        channels: {
          count: this.channels.size,
          details: channelMetrics,
        },
        queues: {
          count: this.messageQueues.size,
          details: queueMetrics,
        },
      };
    }

    /**
     * Shut down the communication hub
     * @returns {Promise<void>} Promise that resolves when shutdown is complete
     */
    async shutdown() {
      Prime.Logger.info("Shutting down communication hub");

      // Disconnect all channels
      const disconnectPromises = [];
      for (const channel of this.channels.values()) {
        disconnectPromises.push(channel.disconnect());
      }

      // Disconnect primary channel
      if (this.primaryChannel) {
        disconnectPromises.push(this.primaryChannel.disconnect());
      }

      // Wait for all disconnections
      await Promise.all(disconnectPromises);

      // Clear all data structures
      this.channels.clear();
      this.messageQueues.clear();

      // Remove event listeners
      this.eventBus.removeAllListeners();

      Prime.Logger.info("Communication hub shutdown complete");
    }
  }

  // Add classes to Prime.Distributed namespace
  Prime.Distributed.Communication = {
    MessageType,
    CommunicationChannel,
    MessageRouter,
    CommunicationHub
  };
})();

// Export the enhanced Prime object
module.exports = Prime;