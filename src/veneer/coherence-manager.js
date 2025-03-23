/**
 * PrimeOS Veneer - Coherence Manager
 * Manages coherence monitoring, validation, and enforcement
 */

const Prime = require('../core');
const { PrimeError } = require('../core/error');
const { MathematicalCoherenceValidator } = require('../framework/base0/manifold-validator');
const { CoherenceValidator } = require('../framework/base0/coherence-validation');
const { CoherenceVerification } = require('../coherence/verification');
const EventEmitter = require('events');

/**
 * Coherence Manager Error class
 */
class CoherenceManagerError extends PrimeError {
  constructor(message, details = {}, code = 'COHERENCE_ERROR') {
    super(message, details, code);
    this.name = 'CoherenceManagerError';
  }
}

/**
 * Coherence violation types
 */
const ViolationType = {
  RESOURCE_LIMIT: 'resource_limit',
  NUMERICAL_INSTABILITY: 'numerical_instability',
  LOGICAL_INCONSISTENCY: 'logical_inconsistency',
  CROSS_APP_CONFLICT: 'cross_app_conflict',
  CONSTRAINT_VIOLATION: 'constraint_violation',
  INTERFACE_MISMATCH: 'interface_mismatch', 
  LIFECYCLE_CONFLICT: 'lifecycle_conflict',
  PERMISSION_VIOLATION: 'permission_violation',
  RESOURCE_LEAK: 'resource_leak',
  UNKNOWN: 'unknown'
};

/**
 * Coherence violation severity levels
 */
const ViolationSeverity = {
  CRITICAL: 'critical',   // System failure, requires immediate action
  HIGH: 'high',           // Severe issue, impacts functionality
  MEDIUM: 'medium',       // Moderate issue, potential impact
  LOW: 'low',             // Minor issue, unlikely to impact
  INFO: 'info'            // Informational, no immediate impact
};

/**
 * Resolution strategy types
 */
const ResolutionStrategy = {
  RESTART_APP: 'restart_app',
  RESOURCE_ADJUSTMENT: 'resource_adjustment',
  NUMERIC_STABILIZATION: 'numeric_stabilization',
  STATE_ROLLBACK: 'state_rollback',
  ISOLATION: 'isolation',
  USER_PROMPT: 'user_prompt',
  PAUSE_CONFLICTING: 'pause_conflicting',
  LOG_ONLY: 'log_only',
  NO_ACTION: 'no_action'
};

/**
 * Coherence violation class
 * Represents a detected coherence violation
 */
class CoherenceViolation {
  /**
   * Create a new coherence violation
   * @param {string} type - Type of violation
   * @param {string} severity - Severity level
   * @param {string} message - Description of the violation
   * @param {Object} details - Additional details
   * @param {Object} source - Source information (app, component, etc.)
   */
  constructor(type, severity, message, details = {}, source = {}) {
    this.type = type;
    this.severity = severity;
    this.message = message;
    this.details = details;
    this.source = source;
    this.detectedAt = Date.now();
    this.resolved = false;
    this.resolutionStrategy = null;
    this.resolutionTime = null;
  }

  /**
   * Mark the violation as resolved
   * @param {string} strategy - Resolution strategy used
   */
  markResolved(strategy) {
    this.resolved = true;
    this.resolutionStrategy = strategy;
    this.resolutionTime = Date.now();
  }

  /**
   * Get the duration of the violation in ms
   * @returns {number} Duration in milliseconds
   */
  getDuration() {
    if (!this.resolved) {
      return Date.now() - this.detectedAt;
    }
    return this.resolutionTime - this.detectedAt;
  }

  /**
   * Create a JSON representation of the violation
   * @returns {Object} JSON representation
   */
  toJSON() {
    return {
      type: this.type,
      severity: this.severity,
      message: this.message,
      details: this.details,
      source: this.source,
      detectedAt: this.detectedAt,
      resolved: this.resolved,
      resolutionStrategy: this.resolutionStrategy,
      resolutionTime: this.resolutionTime,
      duration: this.getDuration()
    };
  }
}

/**
 * Coherence resolution class
 * Represents a resolution for a coherence violation
 */
class CoherenceResolution {
  /**
   * Create a new coherence resolution
   * @param {CoherenceViolation} violation - The violation to resolve
   * @param {string} strategy - Resolution strategy
   * @param {Object} actions - Specific actions to take
   */
  constructor(violation, strategy, actions = {}) {
    this.violation = violation;
    this.strategy = strategy;
    this.actions = actions;
    this.createdAt = Date.now();
    this.applied = false;
    this.success = false;
    this.appliedAt = null;
    this.results = null;
  }

  /**
   * Mark the resolution as applied
   * @param {boolean} success - Whether application was successful
   * @param {Object} results - Results of application
   */
  markApplied(success, results = {}) {
    this.applied = true;
    this.success = success;
    this.appliedAt = Date.now();
    this.results = results;

    if (success) {
      this.violation.markResolved(this.strategy);
    }
  }

  /**
   * Create a JSON representation of the resolution
   * @returns {Object} JSON representation
   */
  toJSON() {
    return {
      violation: this.violation.toJSON(),
      strategy: this.strategy,
      actions: this.actions,
      createdAt: this.createdAt,
      applied: this.applied,
      success: this.success,
      appliedAt: this.appliedAt,
      results: this.results
    };
  }
}

/**
 * Coherence Manager for PrimeOS Veneer
 * Manages coherence monitoring, validation, and enforcement
 */
class CoherenceManager extends EventEmitter {
  /**
   * Create a new coherence manager
   * @param {Object} options - Configuration options
   */
  constructor(options = {}) {
    super();
    
    this.options = {
      monitoringInterval: options.monitoringInterval || 5000, // 5 seconds
      baselineThreshold: options.baselineThreshold || 0.8, // 80% coherence required
      strictMode: options.strictMode || false,
      autoResolve: options.autoResolve !== false,
      maxViolationHistory: options.maxViolationHistory || 100,
      maxResolutionHistory: options.maxResolutionHistory || 100,
      enableManifoldValidation: options.enableManifoldValidation !== false,
      numericalTolerance: options.numericalTolerance || 1e-10,
      ...options
    };
    
    // Initialize validators
    this.mathematicalValidator = new MathematicalCoherenceValidator({
      strictMode: this.options.strictMode,
      numericalTolerance: this.options.numericalTolerance,
      enableManifoldValidation: this.options.enableManifoldValidation
    });
    
    this.validator = new CoherenceValidator({
      strictMode: this.options.strictMode,
      toleranceLevel: this.options.numericalTolerance,
      enforceUorConstraints: true,
      enableManifoldValidation: this.options.enableManifoldValidation,
      manifoldCoherenceThreshold: this.options.baselineThreshold
    });
    
    // Reference to the veneer instance
    this.veneer = null;
    
    // Monitoring state
    this.monitoringActive = false;
    this.monitoringTimer = null;
    this.lastMonitoringRun = null;
    
    // Coherence state
    this.systemCoherence = 1.0;
    this.appCoherenceScores = new Map();
    
    // Violation tracking
    this.activeViolations = new Map();
    this.violationHistory = [];
    this.resolutionHistory = [];
    
    // Performance tracking
    this.stats = {
      checksPerformed: 0,
      violationsDetected: 0,
      violationsResolved: 0,
      resolutionsAttempted: 0,
      successfulResolutions: 0,
      failedResolutions: 0,
      totalCheckTime: 0,
      totalResolutionTime: 0
    };
    
    // Register custom resolution handlers
    this._registerDefaultResolutionHandlers();
    
    // Create constraint registry
    this._registerDefaultConstraints();
    
    // Bind methods
    this.startMonitoring = this.startMonitoring.bind(this);
    this.stopMonitoring = this.stopMonitoring.bind(this);
    this.checkCoherence = this.checkCoherence.bind(this);
    this.checkAppCoherence = this.checkAppCoherence.bind(this);
    this.checkCrossAppCoherence = this.checkCrossAppCoherence.bind(this);
    this.reportViolation = this.reportViolation.bind(this);
    this.resolveViolation = this.resolveViolation.bind(this);
  }
  
  /**
   * Set the veneer instance for coherence manager
   * @param {Object} veneer - PrimeVeneer instance
   */
  setVeneer(veneer) {
    this.veneer = veneer;
    
    // Register for veneer events
    if (veneer) {
      veneer.on('application:registered', this._onAppRegistered.bind(this));
      veneer.on('application:unregistered', this._onAppUnregistered.bind(this));
      veneer.on('resource:allocated', this._onResourceAllocated.bind(this));
      veneer.on('resource:released', this._onResourceReleased.bind(this));
    }
  }
  
  /**
   * Start coherence monitoring
   * @returns {Promise<void>}
   */
  async startMonitoring() {
    if (this.monitoringActive) {
      return;
    }
    
    this.monitoringActive = true;
    Prime.Logger.info('Starting coherence monitoring');
    
    // Run initial check
    await this.checkCoherence();
    
    // Setup timer for regular checks
    this.monitoringTimer = setInterval(async () => {
      try {
        await this.checkCoherence();
      } catch (error) {
        Prime.Logger.error('Error during coherence monitoring', { error });
      }
    }, this.options.monitoringInterval);
    
    this.emit('monitoring:started');
  }
  
  /**
   * Stop coherence monitoring
   */
  stopMonitoring() {
    if (!this.monitoringActive) {
      return;
    }
    
    this.monitoringActive = false;
    
    if (this.monitoringTimer) {
      clearInterval(this.monitoringTimer);
      this.monitoringTimer = null;
    }
    
    Prime.Logger.info('Stopped coherence monitoring');
    this.emit('monitoring:stopped');
  }
  
  /**
   * Check system coherence
   * @returns {Promise<Object>} Coherence check results
   */
  async checkCoherence() {
    const startTime = Date.now();
    this.lastMonitoringRun = startTime;
    this.stats.checksPerformed++;
    
    // Results container
    const results = {
      timestamp: startTime,
      systemCoherence: 1.0,
      appCoherenceScores: {},
      crossAppCoherence: 1.0,
      resourceCoherence: 1.0,
      violations: [],
      resolutions: []
    };
    
    try {
      // Only proceed if veneer is available and initialized
      if (!this.veneer || !this.veneer.state.initialized) {
        return results;
      }
      
      // Check all app coherence
      const apps = Array.from(this.veneer.applications.values());
      for (const app of apps) {
        const appResults = await this.checkAppCoherence(app.id);
        results.appCoherenceScores[app.id] = appResults.coherence;
        
        this.appCoherenceScores.set(app.id, appResults.coherence);
        
        if (appResults.violations.length > 0) {
          results.violations.push(...appResults.violations);
        }
      }
      
      // Check cross-app coherence
      if (apps.length > 1) {
        for (let i = 0; i < apps.length; i++) {
          for (let j = i + 1; j < apps.length; j++) {
            const crossResults = await this.checkCrossAppCoherence(
              apps[i].id, 
              apps[j].id
            );
            
            if (crossResults.violations.length > 0) {
              results.violations.push(...crossResults.violations);
            }
          }
        }
      }
      
      // Check resource utilization coherence
      const resourceResults = await this._checkResourceCoherence();
      results.resourceCoherence = resourceResults.coherence;
      
      if (resourceResults.violations.length > 0) {
        results.violations.push(...resourceResults.violations);
      }
      
      // Calculate overall system coherence
      results.systemCoherence = this._calculateSystemCoherence(results);
      this.systemCoherence = results.systemCoherence;
      
      // Handle any violations
      if (results.violations.length > 0) {
        for (const violation of results.violations) {
          this.reportViolation(violation);
          
          // Auto-resolve if enabled
          if (this.options.autoResolve) {
            const resolution = await this.resolveViolation(violation);
            if (resolution) {
              results.resolutions.push(resolution);
            }
          }
        }
      }
      
      // Update veneer state
      if (this.veneer) {
        this.veneer.state.systemCoherence = results.systemCoherence;
      }
      
      // Emit events
      this.emit('coherence:checked', results);
      
      if (results.systemCoherence < this.options.baselineThreshold) {
        this.emit('coherence:degraded', {
          coherence: results.systemCoherence,
          threshold: this.options.baselineThreshold,
          violations: results.violations.length
        });
      }
      
      const endTime = Date.now();
      this.stats.totalCheckTime += (endTime - startTime);
      
      return results;
    } catch (error) {
      Prime.Logger.error('Error checking coherence', { error });
      
      const endTime = Date.now();
      this.stats.totalCheckTime += (endTime - startTime);
      
      return {
        ...results,
        error: error.message,
        errorDetails: error
      };
    }
  }
  
  /**
   * Check coherence of a specific application
   * @param {string} appId - Application ID
   * @returns {Promise<Object>} Coherence check results
   */
  async checkAppCoherence(appId) {
    const results = {
      appId,
      coherence: 1.0,
      violations: []
    };
    
    // Only proceed if veneer is available and initialized
    if (!this.veneer || !this.veneer.state.initialized) {
      return results;
    }
    
    // Get app from veneer
    const app = this.veneer.applications.get(appId);
    if (!app) {
      return results;
    }
    
    // Check app's own reported coherence
    if (app.instance && typeof app.instance.calculateCoherence === 'function') {
      try {
        const appReportedCoherence = app.instance.calculateCoherence();
        results.reportedCoherence = appReportedCoherence;
        
        // If app reports low coherence, create a violation
        if (appReportedCoherence < this.options.baselineThreshold) {
          results.violations.push(new CoherenceViolation(
            ViolationType.LOGICAL_INCONSISTENCY,
            ViolationSeverity.MEDIUM,
            `Application ${appId} reports low coherence`,
            { 
              reportedCoherence: appReportedCoherence,
              threshold: this.options.baselineThreshold
            },
            { appId, component: 'self-reporting' }
          ));
        }
      } catch (error) {
        Prime.Logger.warn(`Error getting coherence from app ${appId}`, { error });
      }
    }
    
    // Check for lifecycle state coherence
    try {
      const lifecycleCheckResult = this._checkLifecycleCoherence(app);
      if (!lifecycleCheckResult.valid) {
        results.violations.push(new CoherenceViolation(
          ViolationType.LIFECYCLE_CONFLICT,
          ViolationSeverity.HIGH,
          lifecycleCheckResult.message,
          lifecycleCheckResult.details,
          { appId, component: 'lifecycle' }
        ));
      }
    } catch (error) {
      Prime.Logger.warn(`Error checking lifecycle coherence for ${appId}`, { error });
    }
    
    // Check for resource coherence
    try {
      const resourceCheckResult = this._checkAppResourceCoherence(app);
      if (!resourceCheckResult.valid) {
        results.violations.push(new CoherenceViolation(
          ViolationType.RESOURCE_LEAK,
          resourceCheckResult.severity || ViolationSeverity.MEDIUM,
          resourceCheckResult.message,
          resourceCheckResult.details,
          { appId, component: 'resources' }
        ));
      }
    } catch (error) {
      Prime.Logger.warn(`Error checking resource coherence for ${appId}`, { error });
    }
    
    // Calculate overall app coherence
    results.coherence = this._calculateAppCoherence(app, results.violations);
    
    return results;
  }
  
  /**
   * Check coherence between two applications
   * @param {string} appId1 - First application ID
   * @param {string} appId2 - Second application ID
   * @returns {Promise<Object>} Cross-app coherence results
   */
  async checkCrossAppCoherence(appId1, appId2) {
    const results = {
      app1: appId1,
      app2: appId2,
      coherence: 1.0,
      violations: []
    };
    
    // Only proceed if veneer is available and initialized
    if (!this.veneer || !this.veneer.state.initialized) {
      return results;
    }
    
    // Get apps from veneer
    const app1 = this.veneer.applications.get(appId1);
    const app2 = this.veneer.applications.get(appId2);
    
    if (!app1 || !app2) {
      return results;
    }
    
    // Check for interface compatibility
    const interfaceResult = this._checkInterfaceCoherence(app1, app2);
    if (!interfaceResult.valid) {
      results.violations.push(new CoherenceViolation(
        ViolationType.INTERFACE_MISMATCH,
        ViolationSeverity.MEDIUM,
        interfaceResult.message,
        interfaceResult.details,
        { 
          app1: appId1, 
          app2: appId2, 
          component: 'interfaces' 
        }
      ));
    }
    
    // Check for resource conflicts
    const resourceResult = this._checkCrossAppResourceCoherence(app1, app2);
    if (!resourceResult.valid) {
      results.violations.push(new CoherenceViolation(
        ViolationType.CROSS_APP_CONFLICT,
        resourceResult.severity || ViolationSeverity.MEDIUM,
        resourceResult.message,
        resourceResult.details,
        { 
          app1: appId1, 
          app2: appId2, 
          component: 'resources' 
        }
      ));
    }
    
    // Calculate cross-app coherence
    if (results.violations.length > 0) {
      // Reduce coherence based on number and severity of violations
      const severityWeights = {
        [ViolationSeverity.CRITICAL]: 0.5,
        [ViolationSeverity.HIGH]: 0.3,
        [ViolationSeverity.MEDIUM]: 0.2,
        [ViolationSeverity.LOW]: 0.1,
        [ViolationSeverity.INFO]: 0.05
      };
      
      let totalPenalty = 0;
      for (const violation of results.violations) {
        totalPenalty += severityWeights[violation.severity] || 0.1;
      }
      
      results.coherence = Math.max(0, 1 - totalPenalty);
    }
    
    return results;
  }
  
  /**
   * Report a coherence violation
   * @param {CoherenceViolation} violation - The violation to report
   * @returns {string} Violation ID
   */
  reportViolation(violation) {
    // Generate a unique ID for the violation
    const violationId = `violation_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
    
    // Add to active violations
    this.activeViolations.set(violationId, violation);
    
    // Add to history
    this.violationHistory.push({
      id: violationId,
      violation: violation.toJSON()
    });
    
    // Limit history size
    if (this.violationHistory.length > this.options.maxViolationHistory) {
      this.violationHistory = this.violationHistory.slice(-this.options.maxViolationHistory);
    }
    
    // Update stats
    this.stats.violationsDetected++;
    
    // Log violation
    Prime.Logger.warn(`Coherence violation detected: ${violation.message}`, {
      type: violation.type,
      severity: violation.severity,
      source: violation.source
    });
    
    // Emit event
    this.emit('coherence:violation', {
      id: violationId,
      violation: violation.toJSON()
    });
    
    return violationId;
  }
  
  /**
   * Resolve a coherence violation
   * @param {CoherenceViolation|string} violationOrId - Violation or violation ID
   * @returns {Promise<CoherenceResolution|null>} Resolution if successful
   */
  async resolveViolation(violationOrId) {
    const startTime = Date.now();
    this.stats.resolutionsAttempted++;
    
    // Get the violation
    let violation;
    let violationId;
    
    if (typeof violationOrId === 'string') {
      violationId = violationOrId;
      violation = this.activeViolations.get(violationId);
    } else {
      violation = violationOrId;
      
      // Find the ID from active violations
      for (const [id, activeViolation] of this.activeViolations.entries()) {
        if (activeViolation === violation) {
          violationId = id;
          break;
        }
      }
    }
    
    if (!violation) {
      Prime.Logger.warn('Cannot resolve: violation not found', { violationId });
      return null;
    }
    
    // Don't try to resolve already resolved violations
    if (violation.resolved) {
      return null;
    }
    
    try {
      // Determine resolution strategy based on violation type
      const strategyResult = await this._determineResolutionStrategy(violation);
      const { strategy, actions } = strategyResult;
      
      // Create resolution
      const resolution = new CoherenceResolution(violation, strategy, actions);
      
      // Apply resolution
      const success = await this._applyResolution(resolution);
      
      // Mark as applied
      resolution.markApplied(success, { appliedAt: Date.now() });
      
      // Update stats
      if (success) {
        this.stats.successfulResolutions++;
        this.stats.violationsResolved++;
      } else {
        this.stats.failedResolutions++;
      }
      
      // Add to history
      this.resolutionHistory.push({
        id: `resolution_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
        resolution: resolution.toJSON()
      });
      
      // Limit history size
      if (this.resolutionHistory.length > this.options.maxResolutionHistory) {
        this.resolutionHistory = this.resolutionHistory.slice(-this.options.maxResolutionHistory);
      }
      
      // If successful, remove from active violations
      if (success && violationId) {
        this.activeViolations.delete(violationId);
      }
      
      // Log and emit event
      const endTime = Date.now();
      this.stats.totalResolutionTime += (endTime - startTime);
      
      Prime.Logger.info(`Coherence resolution ${success ? 'succeeded' : 'failed'}: ${violation.message}`, {
        strategy,
        type: violation.type,
        severity: violation.severity,
        source: violation.source
      });
      
      this.emit('coherence:resolution', {
        violation: violation.toJSON(),
        resolution: resolution.toJSON(),
        success
      });
      
      return resolution;
    } catch (error) {
      const endTime = Date.now();
      this.stats.totalResolutionTime += (endTime - startTime);
      this.stats.failedResolutions++;
      
      Prime.Logger.error('Error resolving coherence violation', {
        error,
        violation: violation.toJSON()
      });
      
      return null;
    }
  }
  
  /**
   * Get active coherence violations
   * @returns {Array<CoherenceViolation>} Active violations
   */
  getActiveViolations() {
    return Array.from(this.activeViolations.values());
  }
  
  /**
   * Get coherence violation history
   * @param {number} [limit=null] - Maximum number of items to return
   * @returns {Array<Object>} Violation history
   */
  getViolationHistory(limit = null) {
    const history = [...this.violationHistory];
    return limit ? history.slice(-limit) : history;
  }
  
  /**
   * Get coherence resolution history
   * @param {number} [limit=null] - Maximum number of items to return
   * @returns {Array<Object>} Resolution history
   */
  getResolutionHistory(limit = null) {
    const history = [...this.resolutionHistory];
    return limit ? history.slice(-limit) : history;
  }
  
  /**
   * Get coherence statistics
   * @returns {Object} Statistics
   */
  getStats() {
    const avgCheckTime = this.stats.checksPerformed > 0
      ? this.stats.totalCheckTime / this.stats.checksPerformed
      : 0;
    
    const avgResolutionTime = this.stats.resolutionsAttempted > 0
      ? this.stats.totalResolutionTime / this.stats.resolutionsAttempted
      : 0;
    
    const resolutionSuccessRate = this.stats.resolutionsAttempted > 0
      ? this.stats.successfulResolutions / this.stats.resolutionsAttempted
      : 0;
    
    return {
      ...this.stats,
      avgCheckTime,
      avgResolutionTime,
      resolutionSuccessRate,
      activeViolations: this.activeViolations.size,
      systemCoherence: this.systemCoherence,
      lastCheck: this.lastMonitoringRun
    };
  }
  
  /**
   * Reset coherence statistics
   */
  resetStats() {
    this.stats = {
      checksPerformed: 0,
      violationsDetected: 0,
      violationsResolved: 0,
      resolutionsAttempted: 0,
      successfulResolutions: 0,
      failedResolutions: 0,
      totalCheckTime: 0,
      totalResolutionTime: 0
    };
  }
  
  /**
   * Calculate system coherence score
   * @private
   * @param {Object} results - Check results
   * @returns {number} Coherence score (0-1)
   */
  _calculateSystemCoherence(results) {
    // Weight components
    const weights = {
      apps: 0.5,         // App coherence
      crossApp: 0.3,     // Cross-app coherence
      resources: 0.2     // Resource utilization coherence
    };
    
    // Calculate app coherence component
    let appCoherence = 0;
    const appScores = Object.values(results.appCoherenceScores);
    
    if (appScores.length > 0) {
      appCoherence = appScores.reduce((sum, score) => sum + score, 0) / appScores.length;
    } else {
      appCoherence = 1.0; // Perfect if no apps
    }
    
    // Calculate weighted sum
    const weightedCoherence = 
      (appCoherence * weights.apps) +
      (results.crossAppCoherence * weights.crossApp) +
      (results.resourceCoherence * weights.resources);
    
    // Apply violation penalty if any
    let violationPenalty = 0;
    
    if (results.violations.length > 0) {
      // Penalize based on severity
      const severityWeights = {
        [ViolationSeverity.CRITICAL]: 0.2,
        [ViolationSeverity.HIGH]: 0.1,
        [ViolationSeverity.MEDIUM]: 0.05,
        [ViolationSeverity.LOW]: 0.02,
        [ViolationSeverity.INFO]: 0.01
      };
      
      for (const violation of results.violations) {
        violationPenalty += severityWeights[violation.severity] || 0.05;
      }
      
      // Cap the penalty
      violationPenalty = Math.min(0.5, violationPenalty);
    }
    
    return Math.max(0, Math.min(1, weightedCoherence - violationPenalty));
  }
  
  /**
   * Calculate app coherence score
   * @private
   * @param {Object} app - Application object
   * @param {Array} violations - Detected violations
   * @returns {number} Coherence score (0-1)
   */
  _calculateAppCoherence(app, violations) {
    // Base coherence from reported value
    let baseCoherence = app.coherenceScore || 1.0;
    
    // Adjust based on violations
    if (violations.length > 0) {
      // Determine penalty based on violation severity
      const severityWeights = {
        [ViolationSeverity.CRITICAL]: 0.4,
        [ViolationSeverity.HIGH]: 0.2,
        [ViolationSeverity.MEDIUM]: 0.1,
        [ViolationSeverity.LOW]: 0.05,
        [ViolationSeverity.INFO]: 0.02
      };
      
      let penalty = 0;
      for (const violation of violations) {
        penalty += severityWeights[violation.severity] || 0.1;
      }
      
      // Cap the penalty
      penalty = Math.min(0.8, penalty);
      
      // Apply penalty
      baseCoherence = Math.max(0, baseCoherence - penalty);
    }
    
    return baseCoherence;
  }
  
  /**
   * Check resource coherence across the system
   * @private
   * @returns {Promise<Object>} Resource coherence results
   */
  async _checkResourceCoherence() {
    const results = {
      coherence: 1.0,
      violations: []
    };
    
    if (!this.veneer) {
      return results;
    }
    
    // Check each resource type
    const resourceTypes = ['storage', 'compute', 'memory', 'network'];
    const resourceUtilization = {};
    
    for (const type of resourceTypes) {
      if (!this.veneer.resources[type]) {
        continue;
      }
      
      const resource = this.veneer.resources[type];
      
      // If resource has allocations property and it's a Map
      if (resource.allocations && resource.allocations instanceof Map) {
        const utilization = resource.allocations.size / Math.max(1, this.veneer.options.maxApps);
        resourceUtilization[type] = utilization;
        
        // Check for high utilization
        if (utilization > 0.9) {
          results.violations.push(new CoherenceViolation(
            ViolationType.RESOURCE_LIMIT,
            ViolationSeverity.HIGH,
            `High ${type} resource utilization detected`,
            { 
              utilization, 
              allocations: resource.allocations.size,
              maxApps: this.veneer.options.maxApps
            },
            { component: 'resources', resourceType: type }
          ));
        } else if (utilization > 0.7) {
          results.violations.push(new CoherenceViolation(
            ViolationType.RESOURCE_LIMIT,
            ViolationSeverity.MEDIUM,
            `Elevated ${type} resource utilization detected`,
            { 
              utilization, 
              allocations: resource.allocations.size,
              maxApps: this.veneer.options.maxApps
            },
            { component: 'resources', resourceType: type }
          ));
        }
      }
    }
    
    // Calculate resource coherence
    if (Object.keys(resourceUtilization).length > 0) {
      let totalUtilization = 0;
      for (const type in resourceUtilization) {
        totalUtilization += resourceUtilization[type];
      }
      
      const avgUtilization = totalUtilization / Object.keys(resourceUtilization).length;
      
      // Coherence decreases as utilization increases
      results.coherence = 1 - (avgUtilization * 0.5); // At 100% utilization, coherence is 0.5
    }
    
    return results;
  }
  
  /**
   * Check app resource coherence
   * @private
   * @param {Object} app - Application object
   * @returns {Object} Check result
   */
  _checkAppResourceCoherence(app) {
    const result = {
      valid: true,
      message: 'Resources are coherent',
      details: {},
      severity: ViolationSeverity.MEDIUM
    };
    
    // Check for resources that should be allocated
    const requestedResources = app.resources.requested || {};
    const allocatedResources = app.resources.allocated || {};
    
    const missingResources = [];
    
    for (const type in requestedResources) {
      if (!allocatedResources[type]) {
        missingResources.push(type);
      }
    }
    
    if (missingResources.length > 0) {
      result.valid = false;
      result.message = `App ${app.id} is missing requested resources`;
      result.details = {
        missingResources,
        requestedResources,
        allocatedResources
      };
      
      return result;
    }
    
    // If app is in RUNNING state, check all required resources
    if (app.state === 'running' && app.instance) {
      const resourceTypes = ['storage', 'compute', 'memory'];
      const missingRequired = [];
      
      for (const type of resourceTypes) {
        if (app.instance.manifest && 
            app.instance.manifest.resources && 
            app.instance.manifest.resources[type] &&
            Object.keys(app.instance.manifest.resources[type]).length > 0 &&
            (!allocatedResources[type])) {
          missingRequired.push(type);
        }
      }
      
      if (missingRequired.length > 0) {
        result.valid = false;
        result.message = `Running app ${app.id} is missing required resources`;
        result.details = {
          missingRequired,
          state: app.state,
          allocatedResources
        };
        
        // This is a more severe issue
        result.severity = ViolationSeverity.HIGH;
        
        return result;
      }
    }
    
    return result;
  }
  
  /**
   * Check cross-app resource coherence
   * @private
   * @param {Object} app1 - First application
   * @param {Object} app2 - Second application
   * @returns {Object} Check result
   */
  _checkCrossAppResourceCoherence(app1, app2) {
    const result = {
      valid: true,
      message: 'No resource conflicts detected',
      details: {},
      severity: ViolationSeverity.MEDIUM
    };
    
    // Helper function to safely get resources from app objects
    const getAppResources = (app) => {
      if (!app) return {};
      
      // Handle both test mock resources and real resources
      if (app.resources && app.resources.allocated) {
        return app.resources.allocated;
      }
      
      // If resources is directly on the app (test mocks might do this)
      if (app.allocated) {
        return app.allocated;
      }
      
      return {};
    };
    
    // Get resources from both apps
    const app1Resources = getAppResources(app1);
    const app2Resources = getAppResources(app2);
    
    const conflicts = {};
    let hasConflicts = false;
    
    // Check for storage conflicts with shared key prefixes
    if (app1Resources.storage && app2Resources.storage) {
      // Get prefixes, handling both direct structure and resource objects
      const getPrefix = (resource) => {
        if (typeof resource === 'object') {
          return resource.keyPrefix;
        }
        
        if (typeof resource.getPrefix === 'function') {
          return resource.getPrefix();
        }
        
        return null;
      };
      
      const prefix1 = getPrefix(app1Resources.storage);
      const prefix2 = getPrefix(app2Resources.storage);
      
      // If both apps have a prefix and they're the same, it's a conflict
      if (prefix1 && prefix2 && prefix1 === prefix2) {
        conflicts.storage = {
          conflict: 'key_prefix',
          app1Value: prefix1,
          app2Value: prefix2
        };
        hasConflicts = true;
      }
    }
    
    // Check for other resource types as well
    for (const type in app1Resources) {
      if (type !== 'storage' && app2Resources[type]) {
        // Check for conflicts in other resource types
        // This would depend on the specific resource type
        if (type === 'compute' && 
            app1Resources[type].exclusive && 
            app2Resources[type].exclusive) {
          conflicts[type] = {
            conflict: 'exclusive_access',
            app1Id: app1.id,
            app2Id: app2.id
          };
          hasConflicts = true;
        }
      }
    }
    
    if (hasConflicts) {
      result.valid = false;
      result.message = `Resource conflicts detected between ${app1.id} and ${app2.id}`;
      result.details = { conflicts };
      
      return result;
    }
    
    return result;
  }
  
  /**
   * Check interface coherence between apps
   * @private
   * @param {Object} app1 - First application
   * @param {Object} app2 - Second application
   * @returns {Object} Check result
   */
  _checkInterfaceCoherence(app1, app2) {
    const result = {
      valid: true,
      message: 'Interfaces are compatible',
      details: {}
    };
    
    // Get interfaces from app instance or direct metadata
    // First try the instance metadata path (used in tests)
    const getInterfaces = (app) => {
      // Try to get from app.instance.metadata.interfaces
      if (app.instance && app.instance.metadata && app.instance.metadata.interfaces) {
        return app.instance.metadata.interfaces;
      }
      
      // Try to get from direct app.metadata.interfaces
      if (app.metadata && app.metadata.interfaces) {
        return app.metadata.interfaces;
      }
      
      // Default empty interfaces
      return { provides: [], consumes: [] };
    };
    
    const app1Interfaces = getInterfaces(app1);
    const app2Interfaces = getInterfaces(app2);
    
    // Extract interface arrays with defaults
    const app1Consumes = app1Interfaces.consumes || [];
    const app2Provides = app2Interfaces.provides || [];
    
    const app2Consumes = app2Interfaces.consumes || [];
    const app1Provides = app1Interfaces.provides || [];
    
    const missingInterfaces = [];
    
    // Check if app2 provides what app1 needs
    for (const iface of app1Consumes) {
      if (!app2Provides.includes(iface)) {
        missingInterfaces.push({
          consumer: app1.id,
          provider: app2.id,
          interface: iface
        });
      }
    }
    
    // Check if app1 provides what app2 needs
    for (const iface of app2Consumes) {
      if (!app1Provides.includes(iface)) {
        missingInterfaces.push({
          consumer: app2.id,
          provider: app1.id,
          interface: iface
        });
      }
    }
    
    if (missingInterfaces.length > 0) {
      result.valid = false;
      result.message = `Interface mismatches detected between ${app1.id} and ${app2.id}`;
      result.details = { missingInterfaces };
    }
    
    return result;
  }
  
  /**
   * Check application lifecycle coherence
   * @private
   * @param {Object} app - Application object
   * @returns {Object} Check result
   */
  _checkLifecycleCoherence(app) {
    const result = {
      valid: true,
      message: 'Lifecycle state is coherent',
      details: {}
    };
    
    // Check for lifecycle state issues
    if (!app.instance) {
      return result;
    }
    
    // If veneer says running but app says something else
    if (app.state === 'running' && 
        app.instance.state !== 'running' && 
        app.instance.state !== 'RUNNING') {
      result.valid = false;
      result.message = `App lifecycle state mismatch: veneer says '${app.state}' but app says '${app.instance.state}'`;
      result.details = {
        veneerState: app.state,
        appState: app.instance.state
      };
      
      return result;
    }
    
    // Check for stopped apps with resources
    if ((app.state === 'stopped' || app.instance.state === 'stopped' || 
         app.instance.state === 'STOPPED') && 
        app.resources.allocated && 
        Object.keys(app.resources.allocated).length > 0) {
      result.valid = false;
      result.message = `Stopped app ${app.id} still has allocated resources`;
      result.details = {
        state: app.state,
        appState: app.instance.state,
        allocatedResources: Object.keys(app.resources.allocated)
      };
      
      return result;
    }
    
    return result;
  }
  
  /**
   * Register default resolution handlers
   * @private
   */
  _registerDefaultResolutionHandlers() {
    // We'll implement these strategies in the resolution handler
  }
  
  /**
   * Register default coherence constraints
   * @private
   */
  _registerDefaultConstraints() {
    // Add app-level constraints
    this.validator.registerConstraint('app', {
      name: 'resource_allocation',
      validator: (app, context) => {
        if (!app) return false;
        
        // Check if all requested resources are allocated
        const requested = app.resources && app.resources.requested ? 
          Object.keys(app.resources.requested) : [];
        const allocated = app.resources && app.resources.allocated ? 
          Object.keys(app.resources.allocated) : [];
        
        for (const resource of requested) {
          if (!allocated.includes(resource)) {
            return false;
          }
        }
        
        return true;
      },
      priority: 8
    });
    
    this.validator.registerConstraint('app', {
      name: 'lifecycle_consistency',
      validator: (app, context) => {
        if (!app || !app.instance) return true;
        
        // Check if veneer and app agree on state
        const veneerState = app.state;
        const appState = app.instance.state;
        
        // Handle case differences and different state models
        if (veneerState === 'running' && appState !== 'running' && appState !== 'RUNNING') {
          return false;
        }
        
        if (veneerState === 'paused' && appState !== 'paused' && appState !== 'PAUSED') {
          return false;
        }
        
        if (veneerState === 'stopped' && appState !== 'stopped' && appState !== 'STOPPED') {
          return false;
        }
        
        return true;
      },
      priority: 9
    });
  }
  
  /**
   * Determine resolution strategy for a violation
   * @private
   * @param {CoherenceViolation} violation - Violation to resolve
   * @returns {Promise<Object>} Resolution strategy and actions
   */
  async _determineResolutionStrategy(violation) {
    // Default strategy maps by violation type
    const defaultStrategyMap = {
      [ViolationType.RESOURCE_LIMIT]: ResolutionStrategy.RESOURCE_ADJUSTMENT,
      [ViolationType.NUMERICAL_INSTABILITY]: ResolutionStrategy.NUMERIC_STABILIZATION,
      [ViolationType.LOGICAL_INCONSISTENCY]: ResolutionStrategy.RESTART_APP,
      [ViolationType.CROSS_APP_CONFLICT]: ResolutionStrategy.PAUSE_CONFLICTING,
      [ViolationType.CONSTRAINT_VIOLATION]: ResolutionStrategy.LOG_ONLY,
      [ViolationType.INTERFACE_MISMATCH]: ResolutionStrategy.LOG_ONLY,
      [ViolationType.LIFECYCLE_CONFLICT]: ResolutionStrategy.RESTART_APP,
      [ViolationType.PERMISSION_VIOLATION]: ResolutionStrategy.ISOLATION,
      [ViolationType.RESOURCE_LEAK]: ResolutionStrategy.RESOURCE_ADJUSTMENT,
      [ViolationType.UNKNOWN]: ResolutionStrategy.LOG_ONLY
    };
    
    // For critical severity, prefer more aggressive strategies
    if (violation.severity === ViolationSeverity.CRITICAL) {
      if (violation.type === ViolationType.LOGICAL_INCONSISTENCY || 
          violation.type === ViolationType.RESOURCE_LEAK ||
          violation.type === ViolationType.LIFECYCLE_CONFLICT) {
        return {
          strategy: ResolutionStrategy.RESTART_APP,
          actions: {
            appId: violation.source.appId,
            restart: true
          }
        };
      }
    }
    
    // For high severity, consider more active intervention
    if (violation.severity === ViolationSeverity.HIGH) {
      if (violation.type === ViolationType.RESOURCE_LIMIT) {
        return {
          strategy: ResolutionStrategy.RESOURCE_ADJUSTMENT,
          actions: {
            resourceType: violation.source.resourceType,
            adjustLimit: true,
            reduceUsage: true
          }
        };
      }
    }
    
    // Use default strategy mapping
    const strategy = defaultStrategyMap[violation.type] || ResolutionStrategy.LOG_ONLY;
    
    // Create appropriate actions based on strategy
    let actions = {};
    
    switch (strategy) {
      case ResolutionStrategy.RESTART_APP:
        actions = {
          appId: violation.source.appId,
          restart: true
        };
        break;
        
      case ResolutionStrategy.RESOURCE_ADJUSTMENT:
        actions = {
          resourceType: violation.source.resourceType,
          adjustLimit: violation.severity === ViolationSeverity.HIGH,
          reduceUsage: true
        };
        break;
        
      case ResolutionStrategy.PAUSE_CONFLICTING:
        actions = {
          app1: violation.source.app1,
          app2: violation.source.app2,
          pauseFirst: true
        };
        break;
        
      case ResolutionStrategy.ISOLATION:
        actions = {
          appId: violation.source.appId,
          isolate: true
        };
        break;
        
      default:
        actions = {
          log: true,
          notify: violation.severity === ViolationSeverity.HIGH || 
                 violation.severity === ViolationSeverity.CRITICAL
        };
    }
    
    return { strategy, actions };
  }
  
  /**
   * Apply a resolution
   * @private
   * @param {CoherenceResolution} resolution - Resolution to apply
   * @returns {Promise<boolean>} Success status
   */
  async _applyResolution(resolution) {
    const { strategy, actions, violation } = resolution;
    
    if (!this.veneer) {
      return false;
    }
    
    try {
      // Apply the resolution based on strategy
      switch (strategy) {
        case ResolutionStrategy.RESTART_APP: {
          const appId = actions.appId || violation.source.appId;
          const app = this.veneer.getApplication(appId);
          
          if (!app) {
            return false;
          }
          
          // Stop the app if it's running
          if (app.state === 'running' || app.state === 'RUNNING') {
            await app.stop();
          }
          
          // Wait a short time
          await new Promise(resolve => setTimeout(resolve, 500));
          
          // Restart the app
          await app.init();
          await app.start();
          
          return true;
        }
          
        case ResolutionStrategy.RESOURCE_ADJUSTMENT: {
          const resourceType = actions.resourceType || violation.source.resourceType;
          
          if (actions.reduceUsage) {
            // Find apps using this resource and release if possible
            const apps = Array.from(this.veneer.applications.values());
            
            // First check for paused apps to release resources from
            for (const app of apps) {
              // Check if app has the resource allocated
              const hasResource = app.resources && 
                                 app.resources.allocated && 
                                 app.resources.allocated[resourceType];
              
              if (hasResource) {
                // Only release resources from paused or non-critical apps
                const isPaused = app.state === 'paused' || 
                               app.state === 'PAUSED' || 
                               (app.instance && app.instance.state === 'paused');
                
                if (isPaused) {
                  try {
                    await this.veneer.releaseResource(app.id, resourceType);
                    Prime.Logger.info(`Released ${resourceType} resources from paused app ${app.id}`);
                    return true;
                  } catch (error) {
                    Prime.Logger.error(`Error releasing ${resourceType} from ${app.id}`, { error });
                  }
                }
              }
            }
            
            // If no paused apps found, try to find a low-priority app
            const lowPriorityApps = apps.filter(app => {
              // Has the resource and is not a system app
              return app.resources && 
                    app.resources.allocated && 
                    app.resources.allocated[resourceType] &&
                    !app.metadata.system;
            }).sort((a, b) => {
              // Sort by priority (lower first)
              const priorityA = a.metadata.priority || 5;
              const priorityB = b.metadata.priority || 5;
              return priorityA - priorityB;
            });
            
            if (lowPriorityApps.length > 0) {
              const appToAdjust = lowPriorityApps[0];
              
              try {
                await this.veneer.releaseResource(appToAdjust.id, resourceType);
                Prime.Logger.info(`Released ${resourceType} resources from low-priority app ${appToAdjust.id}`);
                return true;
              } catch (error) {
                Prime.Logger.error(`Error releasing ${resourceType} from ${appToAdjust.id}`, { error });
              }
            }
          }
          
          // If we got here, we couldn't free up resources
          Prime.Logger.warn(`Could not free up ${resourceType} resources, no suitable apps found`);
          return false;
        }
          
        case ResolutionStrategy.PAUSE_CONFLICTING: {
          const app1Id = actions.app1 || violation.source.app1;
          const app2Id = actions.app2 || violation.source.app2;
          
          const app1 = this.veneer.getApplication(app1Id);
          const app2 = this.veneer.getApplication(app2Id);
          
          if (!app1 || !app2) {
            return false;
          }
          
          // Pause the first app if it's running
          if (actions.pauseFirst && app1.state === 'running') {
            await app1.pause();
            Prime.Logger.info(`Paused app ${app1Id} to resolve conflict with ${app2Id}`);
            return true;
          }
          
          // Otherwise pause the second app
          if (app2.state === 'running') {
            await app2.pause();
            Prime.Logger.info(`Paused app ${app2Id} to resolve conflict with ${app1Id}`);
            return true;
          }
          
          return false;
        }
          
        case ResolutionStrategy.LOG_ONLY:
          // Just log the violation
          Prime.Logger.warn(`Coherence violation logged: ${violation.message}`, {
            type: violation.type,
            severity: violation.severity,
            source: violation.source
          });
          
          return true;
          
        default:
          // Unknown strategy
          return false;
      }
    } catch (error) {
      Prime.Logger.error('Error applying resolution', {
        error,
        strategy,
        violation: violation.toJSON()
      });
      
      return false;
    }
  }
  
  /**
   * Handle app registration event
   * @private
   * @param {Object} event - App registration event
   */
  _onAppRegistered(event) {
    // Reset coherence score for the app
    this.appCoherenceScores.set(event.appId, 1.0);
    
    // Schedule a coherence check if monitoring is active
    if (this.monitoringActive) {
      setTimeout(() => {
        this.checkAppCoherence(event.appId).catch(error => {
          Prime.Logger.error('Error checking coherence for new app', { 
            error, 
            appId: event.appId 
          });
        });
      }, 1000);
    }
  }
  
  /**
   * Handle app unregistration event
   * @private
   * @param {Object} event - App unregistration event
   */
  _onAppUnregistered(event) {
    // Remove coherence score for the app
    this.appCoherenceScores.delete(event.appId);
    
    // Remove any violations for this app
    for (const [violationId, violation] of this.activeViolations.entries()) {
      if (violation.source.appId === event.appId || 
          violation.source.app1 === event.appId ||
          violation.source.app2 === event.appId) {
        // Mark as resolved
        violation.markResolved(ResolutionStrategy.NO_ACTION);
        
        // Remove from active violations
        this.activeViolations.delete(violationId);
      }
    }
  }
  
  /**
   * Handle resource allocation event
   * @private
   * @param {Object} event - Resource allocation event
   */
  _onResourceAllocated(event) {
    // No immediate action needed, coherence checks will catch issues
  }
  
  /**
   * Handle resource release event
   * @private
   * @param {Object} event - Resource release event
   */
  _onResourceReleased(event) {
    // No immediate action needed, coherence checks will catch issues
  }
}

// Add to Prime namespace
Prime.Veneer = Prime.Veneer || {};
Prime.Veneer.CoherenceManager = CoherenceManager;
Prime.Veneer.CoherenceViolation = CoherenceViolation;
Prime.Veneer.CoherenceResolution = CoherenceResolution;
Prime.Veneer.ViolationType = ViolationType;
Prime.Veneer.ViolationSeverity = ViolationSeverity;
Prime.Veneer.ResolutionStrategy = ResolutionStrategy;
Prime.Veneer.CoherenceManagerError = CoherenceManagerError;

module.exports = {
  CoherenceManager,
  CoherenceViolation,
  CoherenceResolution,
  ViolationType,
  ViolationSeverity,
  ResolutionStrategy,
  CoherenceManagerError
};