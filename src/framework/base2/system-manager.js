/**
 * PrimeOS JavaScript Library - Framework
 * Base 2 System Manager
 */

// Import core
const Prime = require('../../core.js');
const MathUtils = require('../math');

/**
 * System Manager - Handles memory, security, and resource management
 */
const SystemManager = {
  /**
   * Create a system manager
   * @param {Object} config - Configuration object
   * @returns {Object} System manager
   */
  create: function (config = {}) {
    return {
      type: 'systemManager',
      security: config.security || {},
      memory: config.memory || {},
      name: config.name || 'SystemManager',
      _resources: {},

      // Memory statistics with enhanced precision
      _memoryTracking: {
        peakUsage: 0,
        allocations: 0,
        frees: 0,
        history: [],
        startTime: Date.now(),
        allocationsByType: {},
        lastGcTime: null,
        gcStatistics: {
          runsTotal: 0,
          bytesReclaimed: 0,
          totalTimeSpent: 0,
        },
      },

      /**
       * Allocate memory with enhanced numerical stability and validation
       * @param {number} size - Size to allocate
       * @param {Object} [options] - Allocation options
       * @returns {Object} Allocated memory
       */
      allocateMemory: function (size, options = {}) {
        // Validate input parameters with enhanced numerical checks
        if (!Prime.Utils.isNumber(size)) {
          throw new Prime.ValidationError('Size must be a number', {
            context: { providedSize: size, type: typeof size },
          });
        }

        // Ensure size is finite and non-NaN
        if (!Number.isFinite(size)) {
          throw new Prime.ValidationError('Size must be a finite number', {
            context: {
              providedSize: size,
              isNaN: Number.isNaN(size),
              isInfinite: !Number.isFinite(size),
            },
          });
        }

        if (size <= 0) {
          throw new Prime.ValidationError('Size must be a positive number', {
            context: { providedSize: size },
          });
        }

        // Check available system memory before allocation
        const memoryStats = this._getMemoryStats();
        const requestedSizeMB = size / (1024 * 1024);

        // Apply memory limits if configured
        if (options.enforceLimits !== false && this.memory.limits) {
          const { totalLimit, processLimit, allocationLimit } =
            this.memory.limits;

          // Check if total memory limit would be exceeded
          if (totalLimit && memoryStats.totalAllocated + size > totalLimit) {
            throw new Prime.ResourceExhaustionError(
              'Memory allocation would exceed total memory limit',
              {
                context: {
                  requested: size,
                  totalAllocated: memoryStats.totalAllocated,
                  totalLimit,
                  available: Math.max(
                    0,
                    totalLimit - memoryStats.totalAllocated,
                  ),
                },
              },
            );
          }

          // Check process memory limit
          if (
            processLimit &&
            memoryStats.processAllocations[options.processId] &&
            memoryStats.processAllocations[options.processId] + size >
              processLimit
          ) {
            throw new Prime.ResourceExhaustionError(
              'Memory allocation would exceed process memory limit',
              {
                context: {
                  processId: options.processId,
                  requested: size,
                  processAllocated:
                    memoryStats.processAllocations[options.processId],
                  processLimit,
                  available: Math.max(
                    0,
                    processLimit -
                      memoryStats.processAllocations[options.processId],
                  ),
                },
              },
            );
          }

          // Check individual allocation size limit
          if (allocationLimit && size > allocationLimit) {
            throw new Prime.ResourceExhaustionError(
              'Memory allocation size exceeds individual allocation limit',
              {
                context: {
                  requested: size,
                  allocationLimit,
                  exceedsByBytes: size - allocationLimit,
                },
              },
            );
          }
        }

        // Generate a cryptographically secure allocation identifier
        // Use UUID v4 with higher entropy
        const address = Prime.Utils.uuid();

        // Record allocation details with enhanced metadata
        const allocation = {
          type: 'memory',
          size,
          allocated: Date.now(),
          expiresAt: options.ttl ? Date.now() + options.ttl : null,
          lastAccessed: Date.now(),
          processId: options.processId || 'system',
          priority: options.priority || 'normal',
          purpose: options.purpose || 'general',
          metadata: options.metadata || {},
          accessCount: 0,
        };

        // Store the allocation
        this._resources[address] = allocation;

        // Schedule automatic cleanup if TTL is specified
        if (options.ttl) {
          // Use setTimeout in browser or node.js, or a custom scheduler in other environments
          if (typeof setTimeout === 'function') {
            setTimeout(() => {
              try {
                // Check if resource still exists and hasn't been manually freed
                if (this._resources[address]) {
                  this.freeMemory(address, { reason: 'ttl_expired' });

                  // Log cleanup if logging is enabled
                  if (
                    Prime.Logger &&
                    this.memory.logging?.expirations !== false
                  ) {
                    Prime.Logger.debug(
                      `Memory at address ${address} automatically freed after TTL expiration`,
                    );
                  }
                }
              } catch (error) {
                // Log error but don't crash
                if (Prime.Logger) {
                  Prime.Logger.error(
                    `Error freeing expired memory at address ${address}:`,
                    error,
                  );
                }
              }
            }, options.ttl);
          } else {
            // Add to pending expirations if setTimeout isn't available
            this._pendingExpirations = this._pendingExpirations || [];
            this._pendingExpirations.push({
              address,
              expiresAt: allocation.expiresAt,
            });
          }
        }

        // Update memory tracking statistics with the allocationType
        const allocationType = options.allocationType || 'general';
        this._updateMemoryStats(
          address,
          size,
          'allocate',
          options.processId,
          allocationType,
        );

        // Perform garbage collection if memory usage is high
        this._checkAndPerformGarbageCollection();

        // Return allocation details to the caller
        return {
          address,
          size,
          allocated: allocation.allocated,
          expiresAt: allocation.expiresAt,

          // Add accessor methods for caller convenience
          access: () => this._accessMemory(address),
          free: () => this.freeMemory(address),
          extend: (ttl) => this._extendMemoryTTL(address, ttl),
        };
      },

      /**
       * Access allocated memory to update last accessed time
       * @private
       * @param {string} address - Memory address
       * @returns {boolean} Success
       */
      _accessMemory: function (address) {
        if (!this._resources[address]) {
          return false;
        }

        this._resources[address].lastAccessed = Date.now();
        this._resources[address].accessCount++;
        return true;
      },

      /**
       * Extend memory TTL
       * @private
       * @param {string} address - Memory address
       * @param {number} ttl - New TTL in milliseconds
       * @returns {boolean} Success
       */
      _extendMemoryTTL: function (address, ttl) {
        if (
          !this._resources[address] ||
          !Prime.Utils.isNumber(ttl) ||
          ttl <= 0
        ) {
          return false;
        }

        this._resources[address].expiresAt = Date.now() + ttl;
        return true;
      },

      /**
       * Get memory usage statistics with enhanced precision and categorization
       * @private
       * @returns {Object} Memory statistics
       */
      _getMemoryStats: function () {
        const stats = {
          totalAllocated: 0,
          totalCount: 0,
          processAllocations: {},
          byPriority: {
            high: 0,
            normal: 0,
            low: 0,
          },
          byPurpose: {},
          byAllocationType: {},
          ageStatistics: {
            lessThan1Minute: 0,
            lessThan1Hour: 0,
            moreThan1Hour: 0,
            moreThan1Day: 0,
          },
          usageStatistics: {
            neverAccessed: 0,
            lowUsage: 0, // <= 5 accesses
            mediumUsage: 0, // 6-100 accesses
            highUsage: 0, // > 100 accesses
          },
        };

        // Current time for age calculations
        const now = Date.now();

        // Calculate current memory usage using Kahan summation for better precision
        let totalAllocated = 0;
        let compensation = 0;

        for (const address in this._resources) {
          const resource = this._resources[address];
          if (resource.type === 'memory') {
            // Update total statistics with Kahan summation
            const y = resource.size - compensation;
            const t = totalAllocated + y;
            compensation = t - totalAllocated - y;
            totalAllocated = t;

            stats.totalCount++;

            // Update process statistics
            const processId = resource.processId || 'system';
            stats.processAllocations[processId] =
              (stats.processAllocations[processId] || 0) + resource.size;

            // Update priority statistics
            const priority = resource.priority || 'normal';
            stats.byPriority[priority] =
              (stats.byPriority[priority] || 0) + resource.size;

            // Update purpose statistics
            const purpose = resource.purpose || 'general';
            stats.byPurpose[purpose] =
              (stats.byPurpose[purpose] || 0) + resource.size;

            // Update allocation type statistics
            const allocationType =
              resource.metadata.allocationType || 'general';
            stats.byAllocationType[allocationType] =
              (stats.byAllocationType[allocationType] || 0) + resource.size;

            // Update age statistics
            const age = now - resource.allocated;
            if (age < 60000) {
              // less than 1 minute
              stats.ageStatistics.lessThan1Minute += resource.size;
            } else if (age < 3600000) {
              // less than 1 hour
              stats.ageStatistics.lessThan1Hour += resource.size;
            } else if (age < 86400000) {
              // less than 1 day
              stats.ageStatistics.moreThan1Hour += resource.size;
            } else {
              // more than 1 day
              stats.ageStatistics.moreThan1Day += resource.size;
            }

            // Update usage statistics
            const accessCount = resource.accessCount || 0;
            if (accessCount === 0) {
              stats.usageStatistics.neverAccessed += resource.size;
            } else if (accessCount <= 5) {
              stats.usageStatistics.lowUsage += resource.size;
            } else if (accessCount <= 100) {
              stats.usageStatistics.mediumUsage += resource.size;
            } else {
              stats.usageStatistics.highUsage += resource.size;
            }
          }
        }

        // Use the more precise Kahan sum
        stats.totalAllocated = totalAllocated;

        return stats;
      },

      /**
       * Update memory tracking statistics with enhanced categorization
       * @private
       * @param {string} address - Memory address
       * @param {number} size - Memory size
       * @param {string} operation - Operation type ('allocate' or 'free')
       * @param {string} processId - Process identifier
       * @param {string} allocationType - Type of allocation
       */
      _updateMemoryStats: function (
        address,
        size,
        operation,
        processId,
        allocationType = 'general',
      ) {
        // Initialize allocationsByType if needed
        this._memoryTracking.allocationsByType[allocationType] = this
          ._memoryTracking.allocationsByType[allocationType] || {
          count: 0,
          totalBytes: 0,
          peakBytes: 0,
        };

        // Update metrics based on operation
        if (operation === 'allocate') {
          this._memoryTracking.allocations++;

          // Update allocation type statistics
          this._memoryTracking.allocationsByType[allocationType].count++;
          this._memoryTracking.allocationsByType[allocationType].totalBytes +=
            size;

          // Update peak usage by type
          if (
            this._memoryTracking.allocationsByType[allocationType].totalBytes >
            this._memoryTracking.allocationsByType[allocationType].peakBytes
          ) {
            this._memoryTracking.allocationsByType[allocationType].peakBytes =
              this._memoryTracking.allocationsByType[allocationType].totalBytes;
          }

          // Update peak memory usage for all allocations
          const currentUsage = this._getMemoryStats().totalAllocated;
          if (currentUsage > this._memoryTracking.peakUsage) {
            this._memoryTracking.peakUsage = currentUsage;
          }
        } else if (operation === 'free') {
          this._memoryTracking.frees++;

          // Update allocation type statistics if we know the type
          if (
            this._resources[address] &&
            this._resources[address].metadata &&
            this._resources[address].metadata.allocationType
          ) {
            const type = this._resources[address].metadata.allocationType;
            if (this._memoryTracking.allocationsByType[type]) {
              this._memoryTracking.allocationsByType[type].totalBytes -= size;
            }
          }
        }

        // Record operation in history if enabled
        if (this.memory.tracking && this.memory.tracking.keepHistory) {
          // Limit history size
          const maxHistory = this.memory.tracking.historyLimit || 1000;
          if (this._memoryTracking.history.length >= maxHistory) {
            this._memoryTracking.history.shift();
          }

          // Add operation to history
          this._memoryTracking.history.push({
            timestamp: Date.now(),
            operation,
            address,
            size,
            processId: processId || 'system',
            allocationType,
          });
        }
      },

      /**
       * Check and perform garbage collection if needed with enhanced adaptive thresholds
       * @private
       */
      _checkAndPerformGarbageCollection: function () {
        // Skip if not configured
        if (!this.memory || !this.memory.gcThreshold) {
          return;
        }

        // Get current memory stats
        const stats = this._getMemoryStats();

        // Define adaptive GC threshold based on memory usage patterns
        let adaptiveThreshold = this.memory.gcThreshold;

        // Scale threshold logarithmically for large memory allocations
        if (stats.totalAllocated > 1024 * 1024 * 1024) {
          // > 1GB
          // Use logarithmic scale for large memory usage
          const baseThreshold = this.memory.gcThreshold;
          const logFactor =
            Math.log10(stats.totalAllocated / (1024 * 1024)) / 3; // log10(MB)/3
          adaptiveThreshold = baseThreshold * Math.max(1, logFactor);
        }

        // Consider time since last GC
        const timeSinceLastGc = this._memoryTracking.lastGcTime
          ? Date.now() - this._memoryTracking.lastGcTime
          : Infinity;

        // More aggressive GC if we haven't run in a while
        if (timeSinceLastGc > 3600000) {
          // > 1 hour
          adaptiveThreshold *= 0.8;
        }

        // Check if threshold is exceeded
        if (stats.totalAllocated > adaptiveThreshold) {
          // Log gc event
          if (Prime.Logger && this.memory.logging?.gc !== false) {
            Prime.Logger.info(
              `Memory threshold exceeded (${stats.totalAllocated} bytes), running garbage collection`,
            );
          }

          // Perform garbage collection
          this._garbageCollect();
        }
      },

      /**
       * Perform garbage collection with enhanced numerical stability and adaptive strategies
       * @private
       * @param {Object} [options] - Garbage collection options
       * @returns {Object} Collection statistics
       */
      _garbageCollect: function (options = {}) {
        const stats = {
          scanned: 0,
          freed: 0,
          bytesReclaimed: 0,
          startTime: Date.now(),
          endTime: null,
          byType: {},
        };

        // Track memory before and after
        const memBefore = this._getMemoryStats().totalAllocated;

        // Define resource cleanup priority with adaptive strategies
        const cleanupOrder = [
          // First, clean expired allocations
          (resource) =>
            resource.type === 'memory' &&
            resource.expiresAt &&
            resource.expiresAt < Date.now(),

          // Target unused resources first
          (resource) =>
            resource.type === 'memory' &&
            resource.accessCount === 0 &&
            Date.now() - resource.allocated > 60000, // Unused for at least 60 seconds

          // Then clean low priority resources with no recent access
          (resource) =>
            resource.type === 'memory' &&
            resource.priority === 'low' &&
            Date.now() - resource.lastAccessed >
              (this.memory.idleTimeout || 300000),

          // Finally, clean normal priority resources with very old access times
          (resource) =>
            resource.type === 'memory' &&
            resource.priority === 'normal' &&
            Date.now() - resource.lastAccessed >
              (this.memory.extendedIdleTimeout || 1800000),
        ];

        // Apply each cleanup rule in sequence until enough memory is freed
        for (const rule of cleanupOrder) {
          // Get candidate resources for this rule
          const candidateAddresses = [];

          for (const address in this._resources) {
            const resource = this._resources[address];
            stats.scanned++;

            if (rule(resource)) {
              candidateAddresses.push(address);
            }
          }

          // Sort candidates by priority (free oldest accessed first, then least frequently accessed)
          candidateAddresses.sort((a, b) => {
            // First sort by last accessed time
            const timeSort =
              this._resources[a].lastAccessed - this._resources[b].lastAccessed;
            if (timeSort !== 0) return timeSort;

            // If tied, sort by access count (less used first)
            return (
              (this._resources[a].accessCount || 0) -
              (this._resources[b].accessCount || 0)
            );
          });

          // Free resources
          for (const address of candidateAddresses) {
            const resource = this._resources[address];
            const resourceSize = resource.size;
            const resourceType = resource.metadata.allocationType || 'general';

            try {
              this.freeMemory(address, { reason: 'gc' });
              stats.freed++;
              stats.bytesReclaimed += resourceSize;

              // Track reclamation by type
              stats.byType[resourceType] =
                (stats.byType[resourceType] || 0) + resourceSize;

              // Stop if we've freed enough memory
              if (
                options.targetBytes &&
                stats.bytesReclaimed >= options.targetBytes
              ) {
                break;
              }
            } catch (error) {
              // Log error but continue with other resources
              if (Prime.Logger) {
                Prime.Logger.warn(
                  `Error during garbage collection for address ${address}:`,
                  error,
                );
              }
            }
          }

          // Check if we've freed enough memory
          if (
            options.targetBytes &&
            stats.bytesReclaimed >= options.targetBytes
          ) {
            break;
          }
        }

        // Complete statistics
        stats.endTime = Date.now();
        stats.duration = stats.endTime - stats.startTime;

        // Calculate precise memory reduction
        const memAfter = this._getMemoryStats().totalAllocated;
        stats.actualBytesReclaimed = Math.max(0, memBefore - memAfter);

        // Update GC tracking statistics
        this._memoryTracking.lastGcTime = Date.now();
        this._memoryTracking.gcStatistics.runsTotal++;
        this._memoryTracking.gcStatistics.bytesReclaimed +=
          stats.actualBytesReclaimed;
        this._memoryTracking.gcStatistics.totalTimeSpent += stats.duration;

        return stats;
      },

      /**
       * Free memory with enhanced reporting and validation
       * @param {string} address - Memory address
       * @param {Object} [options] - Free options
       * @returns {boolean} Success
       */
      freeMemory: function (address, options = {}) {
        // Validate the address
        if (!this._resources[address]) {
          if (options.ignoreErrors) {
            return false;
          }
          throw new Prime.InvalidOperationError(
            `Unknown memory address: ${address}`,
            {
              context: {
                availableAddresses: Object.keys(this._resources).length,
              },
            },
          );
        }

        if (this._resources[address].type !== 'memory') {
          if (options.ignoreErrors) {
            return false;
          }
          throw new Prime.InvalidOperationError(
            `Address ${address} is not a memory resource`,
            {
              context: { resourceType: this._resources[address].type },
            },
          );
        }

        // Capture resource information before deletion for tracking
        const resourceSize = this._resources[address].size;
        const processId = this._resources[address].processId;
        const allocationType =
          this._resources[address].metadata.allocationType || 'general';

        // Run cleanup callback if provided
        if (options.cleanup && typeof options.cleanup === 'function') {
          try {
            options.cleanup(this._resources[address]);
          } catch (error) {
            // Log cleanup error but proceed with freeing
            if (Prime.Logger) {
              Prime.Logger.warn(
                `Error in memory cleanup callback for address ${address}:`,
                error,
              );
            }
          }
        }

        // Apply custom free logic here for specialized memory types
        // (code omitted - would depend on memory implementation)

        // Delete the resource tracking
        delete this._resources[address];

        // Update memory tracking statistics
        this._updateMemoryStats(
          address,
          resourceSize,
          'free',
          processId,
          allocationType,
        );

        // Log memory free if enabled
        if (Prime.Logger && this.memory.logging?.frees !== false) {
          Prime.Logger.debug(
            `Memory at address ${address} freed (${resourceSize} bytes)`,
            {
              reason: options.reason || 'manual',
              processId,
              allocationType,
            },
          );
        }

        return true;
      },

      /**
       * Check if an operation is permitted with enhanced context
       * @param {string} operation - Operation name
       * @param {Object} context - Operation context
       * @returns {boolean} True if operation is permitted
       */
      checkPermission: function (operation, context = {}) {
        // In a real implementation, this would check against a security policy
        // For now, just check if the operation is allowed

        if (this.security.policy && this.security.policy[operation]) {
          const policy = this.security.policy[operation];

          if (typeof policy === 'function') {
            try {
              return policy(context);
            } catch (error) {
              // Log error but default to secure behavior (deny)
              Prime.Logger.error(
                `Error evaluating security policy for ${operation}:`,
                error,
              );
              return false;
            }
          } else if (typeof policy === 'boolean') {
            return policy;
          }
        }

        // Default to permissive policy
        return true;
      },

      /**
       * Allocate a resource with enhanced validation
       * @param {string} type - Resource type
       * @param {Object} config - Resource configuration
       * @returns {Object} Allocated resource
       */
      allocateResource: function (type, config = {}) {
        // Check permission
        if (!this.checkPermission('allocateResource', { type, config })) {
          throw new Prime.InvalidOperationError(
            `Permission denied: allocateResource ${type}`,
          );
        }

        const address = Prime.Utils.uuid();

        this._resources[address] = {
          type,
          config,
          allocated: Date.now(),
          accessCount: 0,
          lastAccessed: Date.now(),
        };

        return { address, type, config };
      },

      /**
       * Free a resource
       * @param {string} address - Resource address
       * @returns {boolean} Success
       */
      freeResource: function (address) {
        if (!this._resources[address]) {
          throw new Prime.InvalidOperationError(
            `Invalid resource address: ${address}`,
          );
        }

        // Check permission
        if (
          !this.checkPermission('freeResource', {
            address,
            resource: this._resources[address],
          })
        ) {
          throw new Prime.InvalidOperationError(
            `Permission denied: freeResource ${address}`,
          );
        }

        delete this._resources[address];
        return true;
      },

      /**
       * Get resource usage with enhanced numerical precision
       * @returns {Object} Resource usage statistics
       */
      getResourceUsage: function () {
        // Check permission
        if (!this.checkPermission('getResourceUsage', {})) {
          throw new Prime.InvalidOperationError(
            'Permission denied: getResourceUsage',
          );
        }

        const stats = {
          memory: {
            count: 0,
            totalSize: 0,
            totalSizeMB: 0,
          },
          byType: {},
          memoryTracking: {
            uptime: Date.now() - this._memoryTracking.startTime,
            peakUsage: this._memoryTracking.peakUsage,
            peakUsageMB: this._memoryTracking.peakUsage / (1024 * 1024),
            totalAllocations: this._memoryTracking.allocations,
            totalFrees: this._memoryTracking.frees,
            allocationsByType: this._memoryTracking.allocationsByType,
            gcStatistics: this._memoryTracking.gcStatistics,
          },
        };

        // Use Kahan summation for better numerical precision
        let totalMemory = 0;
        let compensation = 0;

        for (const address in this._resources) {
          const resource = this._resources[address];

          // Count by type
          if (!stats.byType[resource.type]) {
            stats.byType[resource.type] = {
              count: 0,
              totalSize: 0,
            };
          }

          stats.byType[resource.type].count++;

          // Special handling for memory
          if (resource.type === 'memory') {
            stats.memory.count++;

            // Update with Kahan summation for better precision
            const y = resource.size - compensation;
            const t = totalMemory + y;
            compensation = t - totalMemory - y;
            totalMemory = t;

            // Update by-type tracking
            stats.byType[resource.type].totalSize += resource.size;
          }
        }

        stats.memory.totalSize = totalMemory;
        stats.memory.totalSizeMB = totalMemory / (1024 * 1024);

        return stats;
      },
    };
  },
};

module.exports = SystemManager;
