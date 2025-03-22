/**
 * PrimeOS JavaScript Library - Distributed Coherence Recovery Module
 * Recovery strategies and implementations for coherence violations
 */

// Import the Prime object from core
const Prime = require('../core');

/**
 * Recovery strategies for coherence violations
 * @enum {string}
 */
const RecoveryStrategy = {
  /** Continue with adjusted parameters */
  CONTINUE: 'continue',
  /** Rollback to last known good state */
  ROLLBACK: 'rollback',
  /** Reset affected components */
  RESET: 'reset',
  /** Resynchronize with coordinator */
  RESYNC: 'resync',
  /** Repartition computation graph */
  REPARTITION: 'repartition'
};

/**
 * Recovery manager for coherence violations
 */
const RecoveryManager = {
  /**
   * Recommend recovery actions based on coherence check results
   * @param {Object} checkResult - Results from coherence check
   * @param {Object} options - Recovery options
   * @returns {Object} Recommended recovery actions
   */
  recommendRecoveryActions: function(checkResult, options = {}) {
    if (!checkResult || !checkResult.violations || checkResult.violations.length === 0) {
      return {
        required: false,
        message: 'No recovery actions needed',
        actions: []
      };
    }
    
    // Initialize recovery plan
    const recoveryPlan = {
      required: true,
      actions: [],
      hasUrgentActions: false
    };
    
    // Import violation types and severity
    const ViolationTypes = Prime.Distributed.Coherence.Violations.Types;
    const Severity = Prime.Distributed.Coherence.Violations.Severity;
    
    // Process each violation and determine recovery action
    for (const violation of checkResult.violations) {
      let action = {
        forViolation: violation,
        strategy: RecoveryStrategy.CONTINUE,
        urgency: 'low',
        description: 'Monitor the situation'
      };
      
      // Determine appropriate recovery strategy based on violation type and severity
      if (violation.severity === Severity.CRITICAL) {
        // Critical violations require immediate intervention
        if (violation.type === ViolationTypes.NUMERICAL || 
            violation.type === ViolationTypes.GRADIENT) {
          action.strategy = RecoveryStrategy.ROLLBACK;
          action.urgency = 'immediate';
          action.description = 'Rollback to last known good state due to critical numerical issue';
        } else if (violation.type === ViolationTypes.NETWORK) {
          action.strategy = RecoveryStrategy.REPARTITION;
          action.urgency = 'immediate';
          action.description = 'Repartition computation to recover from network failure';
        } else {
          action.strategy = RecoveryStrategy.RESET;
          action.urgency = 'immediate';
          action.description = 'Reset affected components';
        }
        recoveryPlan.hasUrgentActions = true;
      } else if (violation.severity === Severity.HIGH) {
        // High severity issues require significant intervention
        if (violation.type === ViolationTypes.SYNCHRONIZATION) {
          action.strategy = RecoveryStrategy.RESYNC;
          action.urgency = 'high';
          action.description = 'Resynchronize with coordinator to resolve sync issues';
        } else if (violation.type === ViolationTypes.DIMENSIONAL) {
          action.strategy = RecoveryStrategy.RESET;
          action.urgency = 'high';
          action.description = 'Reset affected components with dimensional mismatches';
        } else {
          action.strategy = RecoveryStrategy.ROLLBACK;
          action.urgency = 'high';
          action.description = 'Rollback to previous consistent state';
        }
      } else if (violation.severity === Severity.MEDIUM) {
        // Medium severity allows for more measured responses
        if (violation.type === ViolationTypes.GRADIENT) {
          action.strategy = RecoveryStrategy.CONTINUE;
          action.urgency = 'medium';
          action.description = 'Adjust gradient clipping parameters and continue';
        } else if (violation.type === ViolationTypes.SYNCHRONIZATION) {
          action.strategy = RecoveryStrategy.RESYNC;
          action.urgency = 'medium';
          action.description = 'Schedule resynchronization at next convenient point';
        } else {
          action.strategy = RecoveryStrategy.CONTINUE;
          action.urgency = 'medium';
          action.description = 'Continue with adjusted parameters';
        }
      } else {
        // Low severity allows for minimal intervention
        action.strategy = RecoveryStrategy.CONTINUE;
        action.urgency = 'low';
        action.description = 'Continue with monitoring';
      }
      
      // Add action to plan
      recoveryPlan.actions.push(action);
    }
    
    // Determine overall recovery message
    if (recoveryPlan.hasUrgentActions) {
      recoveryPlan.message = 'Urgent recovery actions required';
    } else if (recoveryPlan.actions.some(a => a.urgency === 'high')) {
      recoveryPlan.message = 'High priority recovery actions recommended';
    } else if (recoveryPlan.actions.some(a => a.urgency === 'medium')) {
      recoveryPlan.message = 'Recovery actions recommended';
    } else {
      recoveryPlan.message = 'Minor recovery actions suggested';
    }
    
    return recoveryPlan;
  },
  
  /**
   * Apply numerical corrections to tensor data
   * @param {Array|Array<Array>} tensor - Tensor to correct
   * @param {Object} options - Correction options
   * @returns {Object} Correction result
   */
  applyNumericalCorrections: function(tensor, options = {}) {
    if (!Array.isArray(tensor)) {
      return {
        success: false,
        message: 'Invalid tensor format',
        correctedTensor: null,
        corrections: 0
      };
    }
    
    const threshold = options.threshold || 1e-7;
    const maxValue = options.maxValue || 1e6;
    const replaceNaN = options.replaceNaN !== undefined ? options.replaceNaN : 0;
    const replaceInfinity = options.replaceInfinity !== undefined ? options.replaceInfinity : 0;
    
    let corrections = 0;
    let correctedTensor;
    
    const isMatrix = Array.isArray(tensor[0]);
    
    if (isMatrix) {
      // Create a deep copy for 2D tensor/matrix
      correctedTensor = tensor.map(row => {
        if (!Array.isArray(row)) {
          corrections++;
          return [];
        }
        
        return row.map(value => {
          // Check for non-finite values
          if (!Number.isFinite(value)) {
            corrections++;
            return Number.isNaN(value) ? replaceNaN : replaceInfinity;
          }
          
          // Check for extremely large values
          if (Math.abs(value) > maxValue) {
            corrections++;
            return value > 0 ? maxValue : -maxValue;
          }
          
          // Check for extremely small values
          if (Math.abs(value) > 0 && Math.abs(value) < threshold) {
            corrections++;
            return 0;
          }
          
          return value;
        });
      });
    } else {
      // Create a copy for 1D tensor/vector
      correctedTensor = tensor.map(value => {
        // Check for non-finite values
        if (!Number.isFinite(value)) {
          corrections++;
          return Number.isNaN(value) ? replaceNaN : replaceInfinity;
        }
        
        // Check for extremely large values
        if (Math.abs(value) > maxValue) {
          corrections++;
          return value > 0 ? maxValue : -maxValue;
        }
        
        // Check for extremely small values
        if (Math.abs(value) > 0 && Math.abs(value) < threshold) {
          corrections++;
          return 0;
        }
        
        return value;
      });
    }
    
    return {
      success: true,
      correctedTensor,
      corrections,
      message: corrections > 0 ? 
        `Applied ${corrections} numerical corrections` : 
        'No corrections needed'
    };
  },
  
  /**
   * Apply gradient clipping to prevent exploding gradients
   * @param {Array|Array<Array>} gradients - Gradients to clip
   * @param {Object} options - Clipping options
   * @returns {Object} Clipping result
   */
  applyGradientClipping: function(gradients, options = {}) {
    if (!Array.isArray(gradients)) {
      return {
        success: false,
        message: 'Invalid gradients format',
        clippedGradients: null,
        clippingApplied: false
      };
    }
    
    const clipValue = options.clipValue || 5.0;
    const clipNorm = options.clipNorm || null;
    const clipMethod = options.clipMethod || 'value'; // 'value' or 'norm'
    
    let clippedGradients;
    let clippingApplied = false;
    
    // For norm-based clipping, compute the global norm first
    let globalNorm = 0;
    if (clipMethod === 'norm' && clipNorm !== null) {
      const flattenedSquares = [];
      
      // Flatten and compute squared values
      const isMatrix = Array.isArray(gradients[0]);
      if (isMatrix) {
        for (const row of gradients) {
          if (!Array.isArray(row)) continue;
          for (const value of row) {
            if (Number.isFinite(value)) {
              flattenedSquares.push(value * value);
            }
          }
        }
      } else {
        for (const value of gradients) {
          if (Number.isFinite(value)) {
            flattenedSquares.push(value * value);
          }
        }
      }
      
      // Compute global norm (L2 norm)
      const sumOfSquares = flattenedSquares.reduce((sum, sq) => sum + sq, 0);
      globalNorm = Math.sqrt(sumOfSquares);
    }
    
    const isMatrix = Array.isArray(gradients[0]);
    
    if (clipMethod === 'value') {
      // Simple value clipping
      if (isMatrix) {
        clippedGradients = gradients.map(row => {
          if (!Array.isArray(row)) return [];
          
          return row.map(value => {
            if (!Number.isFinite(value)) {
              clippingApplied = true;
              return 0;
            }
            
            if (Math.abs(value) > clipValue) {
              clippingApplied = true;
              return value > 0 ? clipValue : -clipValue;
            }
            
            return value;
          });
        });
      } else {
        clippedGradients = gradients.map(value => {
          if (!Number.isFinite(value)) {
            clippingApplied = true;
            return 0;
          }
          
          if (Math.abs(value) > clipValue) {
            clippingApplied = true;
            return value > 0 ? clipValue : -clipValue;
          }
          
          return value;
        });
      }
    } else if (clipMethod === 'norm' && clipNorm !== null) {
      // Rescale based on norm if needed
      const rescale = globalNorm > clipNorm ? clipNorm / globalNorm : 1.0;
      
      // Only apply rescaling if needed
      if (rescale < 1.0) {
        clippingApplied = true;
        
        if (isMatrix) {
          clippedGradients = gradients.map(row => {
            if (!Array.isArray(row)) return [];
            
            return row.map(value => {
              if (!Number.isFinite(value)) {
                return 0;
              }
              return value * rescale;
            });
          });
        } else {
          clippedGradients = gradients.map(value => {
            if (!Number.isFinite(value)) {
              return 0;
            }
            return value * rescale;
          });
        }
      } else {
        // No rescaling needed
        clippedGradients = gradients;
      }
    } else {
      // Default to input if method is not recognized
      clippedGradients = gradients;
    }
    
    return {
      success: true,
      clippedGradients,
      clippingApplied,
      globalNorm: clipMethod === 'norm' ? globalNorm : null,
      message: clippingApplied ? 
        'Applied gradient clipping' : 
        'No clipping applied'
    };
  }
};

// Add to Prime namespace
Prime.Distributed = Prime.Distributed || {};
Prime.Distributed.Coherence = Prime.Distributed.Coherence || {};
Prime.Distributed.Coherence.Recovery = {
  Strategies: RecoveryStrategy,
  Manager: RecoveryManager
};

module.exports = Prime;