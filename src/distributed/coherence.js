/**
 * PrimeOS JavaScript Library - Distributed Coherence Module
 * Advanced coherence checks for distributed neural networks
 */

// Import the Prime object from core
const Prime = require('../core');
const EventBus = require('./event-bus');

// Create the Coherence module using IIFE
(function() {
  /**
   * Coherence violation types for distributed systems
   * @enum {string}
   */
  const CoherenceViolationType = {
    /** Numerical precision violations */
    NUMERICAL: 'numerical',
    /** Network split/partition violations */
    NETWORK: 'network',
    /** Parameter synchronization violations */
    SYNCHRONIZATION: 'synchronization',
    /** Mathematical property violations */
    MATHEMATICAL: 'mathematical',
    /** Gradient divergence violations */
    GRADIENT: 'gradient',
    /** Dimensionality violations */
    DIMENSIONAL: 'dimensional'
  };

  /**
   * Severity levels for coherence violations
   * @enum {string}
   */
  const ViolationSeverity = {
    /** Minor issues that can be automatically corrected */
    LOW: 'low',
    /** Significant issues requiring attention */
    MEDIUM: 'medium',
    /** Critical issues requiring immediate action */
    HIGH: 'high',
    /** Fatal issues requiring system shutdown */
    CRITICAL: 'critical'
  };

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
   * Distributed coherence manager
   * Advanced coherence checks for distributed neural networks
   */
  class DistributedCoherenceManager {
    /**
     * Create a new distributed coherence manager
     * @param {Object} config - Configuration options
     * @param {boolean} [config.strictChecking=false] - Whether to enforce strict coherence checking
     * @param {Object} [config.thresholds={}] - Thresholds for different coherence metrics
     * @param {string} [config.defaultRecoveryStrategy='continue'] - Default recovery strategy
     */
    constructor(config = {}) {
      this.config = {
        strictChecking: config.strictChecking || false,
        thresholds: {
          numerical: config.thresholds?.numerical || 1e-7,
          gradient: config.thresholds?.gradient || 0.1,
          synchronization: config.thresholds?.synchronization || 0.01,
          ...config.thresholds
        },
        defaultRecoveryStrategy: config.defaultRecoveryStrategy || RecoveryStrategy.CONTINUE
      };

      // Get required mathematical validators from core framework or create a simple one
      this.mathValidator = Prime.Mathematics && Prime.Mathematics.createValidator ? 
        Prime.Mathematics.createValidator({
          precision: this.config.thresholds.numerical
        }) : 
        {
          // Simple fallback validator 
          validateFinite: (value) => Number.isFinite(value),
          validateRange: (value, min, max) => value >= min && value <= max,
          validateTensor: (tensor) => {
            if (!Array.isArray(tensor)) return false;
            if (Array.isArray(tensor[0])) {
              // Matrix case
              const width = tensor[0].length;
              return tensor.every(row => 
                Array.isArray(row) && 
                row.length === width && 
                row.every(val => Number.isFinite(val))
              );
            } else {
              // Vector case
              return tensor.every(val => Number.isFinite(val));
            }
          }
        };
      
      // Create event bus for coherence events
      this.eventBus = new EventBus();
      
      // Performance metrics
      this.metrics = {
        checksPerformed: 0,
        violationsDetected: 0,
        recoveryActions: 0,
        averageCoherenceScore: 1.0,
        violationsByType: {}
      };
      
      // Initialize violation counters
      Object.values(CoherenceViolationType).forEach(type => {
        this.metrics.violationsByType[type] = 0;
      });
      
      // Log initialization if Logger is available
      if (Prime.Logger && Prime.Logger.info) {
        Prime.Logger.info('Distributed coherence manager initialized', {
          strictMode: this.config.strictChecking,
          numericalThreshold: this.config.thresholds.numerical
        });
      } else {
        console.log('Distributed coherence manager initialized:', {
          strictMode: this.config.strictChecking,
          numericalThreshold: this.config.thresholds.numerical
        });
      }
    }

    /**
     * Check coherence of distributed neural network layer
     * @param {Object} layer - Layer to check
     * @param {Object} context - Context for coherence check
     * @returns {Object} Coherence check results
     */
    checkLayerCoherence(layer, context = {}) {
      if (!layer) {
        // Use ValidationError if available, otherwise fallback to Error
        const ErrorClass = Prime.ValidationError || Error;
        throw new ErrorClass('Layer is required for coherence check');
      }
      
      // Update performance metrics
      this.metrics.checksPerformed++;
      
      // Start with basic coherence checks
      const checks = {
        weights: layer.weights ? this._checkTensorCoherence(layer.weights, 'matrix') : { valid: true, coherence: 1.0 },
        biases: layer.biases ? this._checkTensorCoherence(layer.biases, 'vector') : { valid: true, coherence: 1.0 }
      };
      
      // Check dimensional coherence
      const dimensionsValid = this._checkDimensionalCoherence(layer);
      
      // Enhanced checks for distributed layers
      if (context.isDistributed) {
        // Check partition correctness
        checks.partition = this._checkPartitionCoherence(layer, context);
        
        // Check synchronization with other nodes
        if (context.globalParams) {
          checks.synchronization = this._checkSynchronizationCoherence(layer, context.globalParams);
        }
        
        // Check gradient stability if gradients provided
        if (context.gradients) {
          checks.gradients = this._checkGradientCoherence(context.gradients, context);
        }
      }
      
      // Aggregate results
      const coherenceScore = this._aggregateCoherenceResults(checks);
      
      // Update metrics
      this._updateMetrics(coherenceScore, checks);
      
      // Identify violations
      const violations = this._identifyViolations(checks);
      
      // Force lower coherence score if we have critical or high severity violations
      let finalCoherenceScore = coherenceScore;
      for (const violation of violations) {
        if (violation.severity === ViolationSeverity.CRITICAL) {
          finalCoherenceScore = Math.min(finalCoherenceScore, 0.1); // Critical violations force very low score
          break;
        } else if (violation.severity === ViolationSeverity.HIGH) {
          finalCoherenceScore = Math.min(finalCoherenceScore, 0.3); // High severity forces low score
        }
      }
      
      // Special handling for gradient explosion (common in neural networks)
      if (checks.gradients && checks.gradients.isExploding) {
        // Gradient explosion is a severe issue, so force a low score
        finalCoherenceScore = Math.min(finalCoherenceScore, 0.3);
      }
      
      // Create final result
      const result = {
        isCoherent: finalCoherenceScore >= (this.config.thresholds.overall || 0.7),
        coherenceScore: finalCoherenceScore,
        originalCoherenceScore: coherenceScore, // Keep the original for reference
        dimensionsValid,
        checks,
        violations
      };
      
      // Add recovery recommendations if coherence is low
      if (!result.isCoherent) {
        result.recovery = this._recommendRecoveryActions(result);
      }
      
      return result;
    }
    
    /**
     * Check coherence of a tensor (vector or matrix)
     * @private
     * @param {Array|Array<Array>} tensor - Tensor to check
     * @param {string} type - Type of tensor ('vector' or 'matrix')
     * @returns {Object} Coherence check result
     */
    _checkTensorCoherence(tensor, type) {
      // Determine tensor structure
      const isTensor = Array.isArray(tensor);
      const isMatrix = isTensor && Array.isArray(tensor[0]);
      
      // Validate basic structure
      if (type === 'matrix' && !isMatrix) {
        return {
          valid: false,
          coherence: 0.0,
          message: 'Matrix expected but received non-matrix structure'
        };
      }
      
      if (type === 'vector' && (!isTensor || isMatrix)) {
        return {
          valid: false,
          coherence: 0.0,
          message: 'Vector expected but received non-vector structure'
        };
      }
      
      // Check numerical coherence
      let nonFiniteCount = 0;
      let totalElements = 0;
      
      if (isMatrix) {
        // Check matrix elements
        for (let i = 0; i < tensor.length; i++) {
          const row = tensor[i];
          if (!Array.isArray(row)) {
            return {
              valid: false,
              coherence: 0.0,
              message: 'Matrix contains non-array rows'
            };
          }
          
          for (let j = 0; j < row.length; j++) {
            totalElements++;
            if (!Number.isFinite(row[j])) {
              nonFiniteCount++;
            }
          }
        }
        
        // Check row length consistency
        const firstRowLength = tensor[0].length;
        const hasConsistentRows = tensor.every(row => row.length === firstRowLength);
        
        if (!hasConsistentRows) {
          return {
            valid: false,
            coherence: 0.0,
            message: 'Matrix has inconsistent row lengths'
          };
        }
      } else {
        // Check vector elements
        for (let i = 0; i < tensor.length; i++) {
          totalElements++;
          if (!Number.isFinite(tensor[i])) {
            nonFiniteCount++;
          }
        }
      }
      
      // Calculate coherence score
      const coherenceScore = totalElements > 0 ? 1.0 - (nonFiniteCount / totalElements) : 0.0;
      
      // Create constraint results
      const constraintResults = [];
      
      if (isMatrix) {
        constraintResults.push({
          name: 'matrix_structure',
          satisfied: true,
          priority: 9
        });
        
        constraintResults.push({
          name: 'matrix_elements',
          satisfied: nonFiniteCount === 0,
          priority: 8
        });
      } else {
        constraintResults.push({
          name: 'array_elements',
          satisfied: true,
          priority: 8
        });
        
        constraintResults.push({
          name: 'finite_elements',
          satisfied: nonFiniteCount === 0,
          priority: 7
        });
      }
      
      return {
        valid: nonFiniteCount === 0,
        coherence: coherenceScore,
        constraintResults,
        message: nonFiniteCount === 0 ? 
          'All constraints satisfied' : 
          'Some constraints violated'
      };
    }
    
    /**
     * Check dimensional coherence of layer structure
     * @private
     * @param {Object} layer - Layer to check
     * @returns {boolean} Whether dimensions are coherent
     */
    _checkDimensionalCoherence(layer) {
      // Basic validation
      if (!layer.config) {
        return false;
      }
      
      // Check weight matrix dimensions
      if (layer.weights) {
        // Check rows match input size
        if (layer.weights.length !== layer.config.inputSize) {
          return false;
        }
        
        // Check columns match output size
        if (layer.weights[0].length !== layer.config.outputSize) {
          return false;
        }
      }
      
      // Check bias vector dimensions
      if (layer.biases && layer.biases.length !== layer.config.outputSize) {
        return false;
      }
      
      return true;
    }
    
    /**
     * Check coherence of neural network partitioning
     * @private
     * @param {Object} layer - Layer to check
     * @param {Object} context - Check context
     * @returns {Object} Partition coherence result
     */
    _checkPartitionCoherence(layer, context) {
      // Default to valid if no partition scheme provided
      if (!context.partitionScheme) {
        return {
          valid: true,
          coherence: 1.0,
          message: 'No partition scheme specified'
        };
      }
      
      const scheme = context.partitionScheme;
      
      // Check partition scheme coherence based on type
      if (scheme.type === Prime.Distributed.Partition.PartitionType.INTRA_LAYER) {
        return this._checkIntraLayerPartition(layer, scheme);
      } else if (scheme.type === Prime.Distributed.Partition.PartitionType.LAYER_WISE) {
        return this._checkLayerWisePartition(layer, scheme);
      } else if (scheme.type === Prime.Distributed.Partition.PartitionType.DATA_PARALLEL) {
        return this._checkDataParallelPartition(layer, scheme);
      }
      
      // Unknown partition type
      return {
        valid: false,
        coherence: 0.0,
        message: `Unknown partition type: ${scheme.type}`
      };
    }
    
    /**
     * Check coherence of intra-layer partitioning
     * @private
     * @param {Object} layer - Layer to check
     * @param {Object} scheme - Partition scheme
     * @returns {Object} Partition coherence result
     */
    _checkIntraLayerPartition(layer, scheme) {
      // In intra-layer partitioning, we need to ensure the
      // partitioning respects mathematical coherence by
      // enforcing clean boundaries for linear operations
      
      // Check if layer configuration exists in scheme
      if (!scheme.layerConfig || !scheme.layerConfig[layer.id]) {
        return {
          valid: false,
          coherence: 0.0,
          message: 'Layer not found in partition scheme'
        };
      }
      
      // Get layer assignments
      const layerNodes = scheme.getNodeLayers(layer.id);
      if (!layerNodes || layerNodes.length === 0) {
        return {
          valid: false,
          coherence: 0.0,
          message: 'Layer nodes not assigned in partition scheme'
        };
      }
      
      // For intra-layer partitioning, nodes should divide the layer evenly
      const nodeCount = layerNodes.length;
      const outputSize = layer.config.outputSize;
      
      // Perfect coherence is when output size is divisible by node count
      const partitionBalance = nodeCount > 1 ? 
        1.0 - (outputSize % nodeCount) / outputSize : 1.0;
      
      return {
        valid: true, // Accept even imperfect partitioning
        coherence: partitionBalance,
        message: partitionBalance === 1.0 ? 
          'Optimal intra-layer partitioning' : 
          'Sub-optimal intra-layer partitioning'
      };
    }
    
    /**
     * Check coherence of layer-wise partitioning
     * @private
     * @param {Object} layer - Layer to check
     * @param {Object} scheme - Partition scheme
     * @returns {Object} Partition coherence result
     */
    _checkLayerWisePartition(layer, scheme) {
      // In layer-wise partitioning, each layer should be assigned to a single node
      
      // Check if layer is assigned to any node
      let layerAssigned = false;
      
      for (const [nodeId, layers] of scheme.layerAssignments.entries()) {
        if (layers.includes(layer.id)) {
          layerAssigned = true;
          break;
        }
      }
      
      if (!layerAssigned) {
        return {
          valid: false,
          coherence: 0.0,
          message: 'Layer not assigned to any node'
        };
      }
      
      // For layer-wise partitioning, coherence is perfect if we find it
      return {
        valid: true,
        coherence: 1.0,
        message: 'Layer assigned to node in partition scheme'
      };
    }
    
    /**
     * Check coherence of data-parallel partitioning
     * @private
     * @param {Object} layer - Layer to check
     * @param {Object} scheme - Partition scheme
     * @returns {Object} Partition coherence result
     */
    _checkDataParallelPartition(layer, scheme) {
      // In data-parallel partitioning, each node has a complete copy of the layer
      // Coherence depends on the synchronization of parameters
      
      // Check if layer configuration exists in scheme
      if (!scheme.layerConfig || !scheme.layerConfig[layer.id]) {
        return {
          valid: false,
          coherence: 0.0,
          message: 'Layer not found in partition scheme'
        };
      }
      
      // Data-parallel partitioning is coherent by design
      // Actual coherence depends on synchronization (checked separately)
      return {
        valid: true,
        coherence: 1.0,
        message: 'Data-parallel partitioning is coherent by design'
      };
    }
    
    /**
     * Check synchronization coherence between local and global parameters
     * @private
     * @param {Object} layer - Layer with local parameters
     * @param {Object} globalParams - Global parameters for comparison
     * @returns {Object} Synchronization coherence result
     */
    _checkSynchronizationCoherence(layer, globalParams) {
      if (!layer.weights || !globalParams.weights) {
        return {
          valid: false,
          coherence: 0.0,
          message: 'Missing weights for synchronization check'
        };
      }
      
      // Calculate weight difference
      const weightDifference = this._computeSyncDifference(
        layer.weights,
        globalParams.weights
      );
      
      // Calculate bias difference if available
      let biasDifference = 0;
      if (layer.biases && globalParams.biases) {
        biasDifference = this._computeSyncDifference(
          layer.biases,
          globalParams.biases
        );
      }
      
      // Combined difference (weighted average)
      const combinedDifference = 0.8 * weightDifference + 0.2 * biasDifference;
      
      // Coherence score based on difference
      const coherenceScore = Math.max(0, 1.0 - (combinedDifference / this.config.thresholds.synchronization));
      
      return {
        valid: coherenceScore > 0.7,
        coherence: coherenceScore,
        weightDifference,
        biasDifference,
        message: coherenceScore > 0.7 ? 
          'Parameters synchronized within tolerance' : 
          'Parameters out of sync beyond tolerance'
      };
    }
    
    /**
     * Compute the synchronization difference between local and global parameters
     * @private
     * @param {Array|Array<Array>} localParams - Local parameters
     * @param {Array|Array<Array>} globalParams - Global parameters
     * @returns {number} Normalized difference (0-1 scale)
     */
    _computeSyncDifference(localParams, globalParams) {
      let diffSum = 0;
      let valueCount = 0;
      
      // Handle matrix parameters
      if (Array.isArray(localParams[0]) && Array.isArray(globalParams[0])) {
        const rows = Math.min(localParams.length, globalParams.length);
        
        for (let i = 0; i < rows; i++) {
          const cols = Math.min(localParams[i].length, globalParams[i].length);
          
          for (let j = 0; j < cols; j++) {
            diffSum += Math.pow(localParams[i][j] - globalParams[i][j], 2);
            valueCount++;
          }
        }
      } 
      // Handle vector parameters
      else if (Array.isArray(localParams) && Array.isArray(globalParams)) {
        const len = Math.min(localParams.length, globalParams.length);
        
        for (let i = 0; i < len; i++) {
          diffSum += Math.pow(localParams[i] - globalParams[i], 2);
          valueCount++;
        }
      }
      
      if (valueCount === 0) return 1.0; // Maximum difference if no comparison possible
      
      // Compute root mean squared difference
      return Math.sqrt(diffSum / valueCount);
    }
    
    /**
     * Check gradient coherence 
     * @private
     * @param {Object} gradients - Gradients to check
     * @param {Object} context - Check context
     * @returns {Object} Gradient coherence result
     */
    _checkGradientCoherence(gradients, context) {
      if (!gradients || !gradients.dW) {
        return {
          valid: false,
          coherence: 0.0,
          message: 'Missing gradients for coherence check'
        };
      }
      
      // Calculate gradient norm
      const weightGradNorm = this._computeGradientNorm(gradients.dW);
      
      // Calculate bias gradient norm if available
      let biasGradNorm = 0;
      if (gradients.dB) {
        biasGradNorm = this._computeGradientNorm(gradients.dB);
      }
      
      // Check for exploding gradients
      const maxNorm = context.maxGradientNorm || 10.0;
      const isExploding = weightGradNorm > maxNorm || biasGradNorm > maxNorm;
      
      // Check for vanishing gradients
      const minNorm = context.minGradientNorm || 1e-7;
      const isVanishing = weightGradNorm < minNorm && (gradients.dB ? biasGradNorm < minNorm : true);
      
      // Compute coherence score - critically, ensure exploding gradients have a low score
      let normScore = 1.0; // Default to fully coherent
      
      if (isExploding) {
        // For exploding gradients, give a dramatically lower score
        // The further beyond maxNorm, the lower the score
        const excessFactor = Math.max(weightGradNorm, biasGradNorm) / maxNorm;
        normScore = Math.max(0.0, Math.min(0.4, 1.0 / excessFactor)); // Cap at 0.4 and ensure >= 0
      } else if (isVanishing) {
        // For vanishing gradients, give a moderately low score
        normScore = 0.3;
      }
      
      return {
        valid: !isExploding && !isVanishing,
        coherence: normScore,
        weightGradNorm,
        biasGradNorm,
        isExploding,
        isVanishing,
        message: isExploding ? 
          'Exploding gradients detected' : 
          (isVanishing ? 'Vanishing gradients detected' : 'Gradient magnitude within acceptable range')
      };
    }
    
    /**
     * Compute the L2 norm of a gradient tensor
     * @private
     * @param {Array|Array<Array>} gradients - Gradient tensor
     * @returns {number} Gradient L2 norm
     */
    _computeGradientNorm(gradients) {
      let sumSquared = 0;
      
      if (Array.isArray(gradients[0])) {
        // Matrix gradients
        for (let i = 0; i < gradients.length; i++) {
          for (let j = 0; j < gradients[i].length; j++) {
            sumSquared += Math.pow(gradients[i][j], 2);
          }
        }
      } else {
        // Vector gradients
        for (let i = 0; i < gradients.length; i++) {
          sumSquared += Math.pow(gradients[i], 2);
        }
      }
      
      return Math.sqrt(sumSquared);
    }
    
    /**
     * Aggregate coherence results into a single score
     * @private
     * @param {Object} checks - All coherence check results
     * @returns {number} Aggregated coherence score (0-1)
     */
    _aggregateCoherenceResults(checks) {
      // Define weights for different check types
      const weights = {
        weights: 0.3,
        biases: 0.1,
        partition: 0.2,
        synchronization: 0.2,
        gradients: 0.2
      };
      
      let totalScore = 0;
      let totalWeight = 0;
      
      // Calculate weighted sum of coherence scores
      for (const [key, result] of Object.entries(checks)) {
        if (result && typeof result.coherence === 'number') {
          totalScore += result.coherence * (weights[key] || 0.1);
          totalWeight += (weights[key] || 0.1);
        }
      }
      
      // If no valid checks, return 0
      if (totalWeight === 0) return 0;
      
      // Return normalized score
      return totalScore / totalWeight;
    }
    
    /**
     * Update coherence metrics
     * @private
     * @param {number} score - Overall coherence score
     * @param {Object} checks - All coherence check results
     */
    _updateMetrics(score, checks) {
      // Update average coherence score (exponential moving average)
      this.metrics.averageCoherenceScore = 
        0.9 * this.metrics.averageCoherenceScore + 0.1 * score;
      
      // Check if any violations detected
      const hasViolations = score < 0.7;
      
      if (hasViolations) {
        this.metrics.violationsDetected++;
      }
    }
    
    /**
     * Identify specific coherence violations from check results
     * @private
     * @param {Object} checks - All coherence check results
     * @returns {Array<Object>} List of identified violations
     */
    _identifyViolations(checks) {
      const violations = [];
      
      // Check weights coherence
      if (checks.weights) {
        // Check valid property
        if (!checks.weights.valid) {
          violations.push({
            type: CoherenceViolationType.NUMERICAL,
            severity: ViolationSeverity.MEDIUM,
            message: 'Weight matrix coherence violation',
            score: checks.weights.coherence
          });
        } 
        // Check for low coherence even if technically valid
        else if (checks.weights.coherence < 1.0) {
          // Check constraint results if available
          if (checks.weights.constraintResults) {
            // Look for unsatisfied constraints
            const failedConstraint = checks.weights.constraintResults.find(c => !c.satisfied);
            if (failedConstraint) {
              violations.push({
                type: CoherenceViolationType.NUMERICAL,
                severity: ViolationSeverity.LOW,
                message: `Weight matrix constraint violation: ${failedConstraint.name}`,
                score: checks.weights.coherence
              });
            }
          }
        }
      }
      
      // Check biases coherence
      if (checks.biases) {
        // Check valid property
        if (!checks.biases.valid) {
          violations.push({
            type: CoherenceViolationType.NUMERICAL,
            severity: ViolationSeverity.LOW,
            message: 'Bias vector coherence violation',
            score: checks.biases.coherence
          });
        }
        // Check for low coherence even if technically valid
        else if (checks.biases.coherence < 1.0) {
          // Check constraint results if available
          if (checks.biases.constraintResults) {
            // Look for unsatisfied constraints
            const failedConstraint = checks.biases.constraintResults.find(c => !c.satisfied);
            if (failedConstraint) {
              violations.push({
                type: CoherenceViolationType.NUMERICAL,
                severity: ViolationSeverity.LOW,
                message: `Bias vector constraint violation: ${failedConstraint.name}`,
                score: checks.biases.coherence
              });
            }
          }
        }
      }
      
      // Check partition coherence
      if (checks.partition && !checks.partition.valid) {
        violations.push({
          type: CoherenceViolationType.DIMENSIONAL,
          severity: ViolationSeverity.HIGH,
          message: 'Network partition coherence violation',
          score: checks.partition.coherence
        });
      }
      
      // Check synchronization coherence
      if (checks.synchronization && !checks.synchronization.valid) {
        violations.push({
          type: CoherenceViolationType.SYNCHRONIZATION,
          severity: ViolationSeverity.MEDIUM,
          message: 'Parameter synchronization coherence violation',
          details: {
            weightDifference: checks.synchronization.weightDifference,
            biasDifference: checks.synchronization.biasDifference
          },
          score: checks.synchronization.coherence
        });
      }
      
      // Check gradient coherence
      if (checks.gradients) {
        if (checks.gradients.isExploding) {
          violations.push({
            type: CoherenceViolationType.GRADIENT,
            severity: ViolationSeverity.HIGH,
            message: 'Exploding gradient detected',
            details: {
              weightGradNorm: checks.gradients.weightGradNorm,
              biasGradNorm: checks.gradients.biasGradNorm
            },
            score: checks.gradients.coherence
          });
        } else if (checks.gradients.isVanishing) {
          violations.push({
            type: CoherenceViolationType.GRADIENT,
            severity: ViolationSeverity.MEDIUM,
            message: 'Vanishing gradient detected',
            details: {
              weightGradNorm: checks.gradients.weightGradNorm,
              biasGradNorm: checks.gradients.biasGradNorm
            },
            score: checks.gradients.coherence
          });
        }
      }
      
      return violations;
    }
    
    /**
     * Recommend recovery actions based on coherence violations
     * @private
     * @param {Object} result - Coherence check result
     * @returns {Object} Recommended recovery actions
     */
    _recommendRecoveryActions(result) {
      const recovery = {
        strategy: this.config.defaultRecoveryStrategy,
        actions: []
      };
      
      // Process each violation
      for (const violation of result.violations) {
        switch (violation.type) {
          case CoherenceViolationType.NUMERICAL:
            recovery.actions.push({
              type: 'numerical_correction',
              target: 'weights',
              description: 'Apply numerical stability correction to weights'
            });
            break;
            
          case CoherenceViolationType.SYNCHRONIZATION:
            // For severe sync issues, recommend resync
            if (violation.severity === ViolationSeverity.HIGH) {
              recovery.strategy = RecoveryStrategy.RESYNC;
              recovery.actions.push({
                type: 'full_resync',
                description: 'Perform full parameter resynchronization with coordinator'
              });
            } else {
              recovery.actions.push({
                type: 'partial_resync',
                description: 'Fetch latest parameters from coordinator'
              });
            }
            break;
            
          case CoherenceViolationType.GRADIENT:
            // For exploding gradients
            if (violation.message.includes('Exploding')) {
              recovery.actions.push({
                type: 'gradient_clipping',
                description: 'Apply gradient clipping to prevent explosion',
                params: { maxNorm: 5.0 }
              });
            } 
            // For vanishing gradients
            else if (violation.message.includes('Vanishing')) {
              recovery.actions.push({
                type: 'activation_check',
                description: 'Check activation functions and consider using alternatives'
              });
            }
            break;
            
          case CoherenceViolationType.DIMENSIONAL:
            // Dimensional issues are serious and may require repartitioning
            recovery.strategy = RecoveryStrategy.REPARTITION;
            recovery.actions.push({
              type: 'repartition',
              description: 'Recalculate partitioning scheme to maintain coherence'
            });
            break;
        }
      }
      
      // For critical violations, recommend rollback
      const hasCritical = result.violations.some(
        v => v.severity === ViolationSeverity.CRITICAL
      );
      
      if (hasCritical) {
        recovery.strategy = RecoveryStrategy.ROLLBACK;
        recovery.actions.unshift({
          type: 'rollback',
          description: 'Roll back to last known good state'
        });
      }
      
      return recovery;
    }

    /**
     * Apply coherence correction to a neural network layer
     * @param {Object} layer - Layer to correct
     * @param {Array<Object>} violations - Detected coherence violations
     * @param {Object} context - Context for correction
     * @returns {Object} Correction results
     */
    applyCoherenceCorrection(layer, violations, context = {}) {
      if (!layer || !violations || violations.length === 0) {
        return { applied: false, message: 'No corrections needed' };
      }
      
      // Track which corrections were applied
      const corrections = [];
      let appliedAny = false;
      
      // Apply corrections for each violation type
      for (const violation of violations) {
        switch (violation.type) {
          case CoherenceViolationType.NUMERICAL:
            if (this._applyNumericalCorrection(layer, violation, context)) {
              appliedAny = true;
              corrections.push('numerical_stability');
            }
            break;
            
          case CoherenceViolationType.GRADIENT:
            if (context.gradients && this._applyGradientCorrection(layer, violation, context)) {
              appliedAny = true;
              corrections.push('gradient_scaling');
            }
            break;
            
          case CoherenceViolationType.SYNCHRONIZATION:
            if (context.globalParams && this._applySynchronizationCorrection(layer, context.globalParams, violation)) {
              appliedAny = true;
              corrections.push('parameter_sync');
            }
            break;
        }
      }
      
      // Update metrics if corrections applied
      if (appliedAny) {
        this.metrics.recoveryActions++;
      }
      
      return {
        applied: appliedAny,
        corrections,
        message: appliedAny ? 
          `Applied corrections: ${corrections.join(', ')}` : 
          'No corrections applied'
      };
    }
    
    /**
     * Apply numerical stability correction to layer
     * @private
     * @param {Object} layer - Layer to correct
     * @param {Object} violation - Coherence violation
     * @param {Object} context - Correction context
     * @returns {boolean} Whether correction was applied
     */
    _applyNumericalCorrection(layer, violation, context) {
      if (!layer.weights) return false;
      
      // Check for NaN or infinity values
      let corrected = false;
      
      // Correct weights
      for (let i = 0; i < layer.weights.length; i++) {
        for (let j = 0; j < layer.weights[i].length; j++) {
          if (!Number.isFinite(layer.weights[i][j])) {
            // Replace non-finite values with small random values
            layer.weights[i][j] = (Math.random() - 0.5) * 0.01;
            corrected = true;
          }
        }
      }
      
      // Correct biases if present
      if (layer.biases) {
        for (let i = 0; i < layer.biases.length; i++) {
          if (!Number.isFinite(layer.biases[i])) {
            layer.biases[i] = (Math.random() - 0.5) * 0.01;
            corrected = true;
          }
        }
      }
      
      return corrected;
    }
    
    /**
     * Apply gradient correction
     * @private
     * @param {Object} layer - Layer to correct
     * @param {Object} violation - Coherence violation
     * @param {Object} context - Correction context
     * @returns {boolean} Whether correction was applied
     */
    _applyGradientCorrection(layer, violation, context) {
      // Skip if no gradients in context
      if (!context.gradients || !context.gradients.dW) {
        return false;
      }
      
      const gradients = context.gradients;
      let corrected = false;
      
      // Check for exploding gradients
      if (violation.message.includes('Exploding')) {
        const maxNorm = context.maxGradientNorm || 5.0;
        const currentNorm = this._computeGradientNorm(gradients.dW);
        
        // Apply gradient clipping
        if (currentNorm > maxNorm) {
          const scale = maxNorm / currentNorm;
          
          // Scale weight gradients
          for (let i = 0; i < gradients.dW.length; i++) {
            for (let j = 0; j < gradients.dW[i].length; j++) {
              gradients.dW[i][j] *= scale;
            }
          }
          
          // Scale bias gradients if present
          if (gradients.dB) {
            for (let i = 0; i < gradients.dB.length; i++) {
              gradients.dB[i] *= scale;
            }
          }
          
          corrected = true;
        }
      }
      
      return corrected;
    }
    
    /**
     * Apply parameter synchronization correction
     * @private
     * @param {Object} layer - Layer to correct
     * @param {Object} globalParams - Global parameters
     * @param {Object} violation - Coherence violation
     * @returns {boolean} Whether correction was applied
     */
    _applySynchronizationCorrection(layer, globalParams, violation) {
      if (!layer.weights || !globalParams.weights) {
        return false;
      }
      
      let corrected = false;
      
      // For severe violations, fully sync with global params
      if (violation.severity === ViolationSeverity.HIGH || violation.severity === ViolationSeverity.CRITICAL) {
        // Deep copy weights
        for (let i = 0; i < Math.min(layer.weights.length, globalParams.weights.length); i++) {
          for (let j = 0; j < Math.min(layer.weights[i].length, globalParams.weights[i].length); j++) {
            layer.weights[i][j] = globalParams.weights[i][j];
          }
        }
        
        // Deep copy biases if present
        if (layer.biases && globalParams.biases) {
          for (let i = 0; i < Math.min(layer.biases.length, globalParams.biases.length); i++) {
            layer.biases[i] = globalParams.biases[i];
          }
        }
        
        corrected = true;
      } 
      // For medium/low violations, blend local and global params
      else {
        const blendFactor = violation.severity === ViolationSeverity.MEDIUM ? 0.7 : 0.3; // Adjust based on severity
        
        // Blend weights
        for (let i = 0; i < Math.min(layer.weights.length, globalParams.weights.length); i++) {
          for (let j = 0; j < Math.min(layer.weights[i].length, globalParams.weights[i].length); j++) {
            layer.weights[i][j] = (blendFactor * globalParams.weights[i][j]) + 
              ((1 - blendFactor) * layer.weights[i][j]);
          }
        }
        
        // Blend biases if present
        if (layer.biases && globalParams.biases) {
          for (let i = 0; i < Math.min(layer.biases.length, globalParams.biases.length); i++) {
            layer.biases[i] = (blendFactor * globalParams.biases[i]) + 
              ((1 - blendFactor) * layer.biases[i]);
          }
        }
        
        corrected = true;
      }
      
      return corrected;
    }

    /**
     * Check coherence between nodes in a distributed system
     * @param {Array<Object>} nodeResults - Coherence results from multiple nodes
     * @returns {Object} Global coherence assessment
     */
    assessGlobalCoherence(nodeResults) {
      if (!Array.isArray(nodeResults) || nodeResults.length === 0) {
        return {
          isCoherent: false,
          score: 0,
          message: 'No node results to assess'
        };
      }
      
      // Calculate average coherence score
      let totalScore = 0;
      let coherentNodes = 0;
      
      for (const result of nodeResults) {
        if (result && typeof result.coherenceScore === 'number') {
          totalScore += result.coherenceScore;
          if (result.isCoherent) {
            coherentNodes++;
          }
        }
      }
      
      const averageScore = totalScore / nodeResults.length;
      const coherentRatio = coherentNodes / nodeResults.length;
      
      // Collect all violations
      const allViolations = [];
      for (const result of nodeResults) {
        if (result.violations && Array.isArray(result.violations)) {
          allViolations.push(...result.violations);
        }
      }
      
      // Identify most common and most severe violations
      const violationsByType = {};
      let mostSevereViolation = null;
      
      // Initialize violationsByType with all types (so we have zero counts for missing types)
      Object.values(CoherenceViolationType).forEach(type => {
        violationsByType[type] = 0;
      });
      
      for (const violation of allViolations) {
        // Count by type (using the type directly, not the enum name)
        if (violation.type) {
          violationsByType[violation.type] = (violationsByType[violation.type] || 0) + 1;
        }
        
        // Track most severe
        if (!mostSevereViolation || 
            (violation.severity && mostSevereViolation.severity && 
             ViolationSeverity[violation.severity] > ViolationSeverity[mostSevereViolation.severity])) {
          mostSevereViolation = violation;
        }
      }
      
      // Find most common violation type
      let mostCommonType = null;
      let highestCount = 0;
      
      for (const [type, count] of Object.entries(violationsByType)) {
        if (count > highestCount) {
          highestCount = count;
          mostCommonType = type;
        }
      }
      
      // Generate assessment message
      let message = '';
      if (averageScore > 0.9) {
        message = 'Global coherence excellent';
      } else if (averageScore > 0.7) {
        message = 'Global coherence good';
      } else if (averageScore > 0.5) {
        message = 'Global coherence marginal';
      } else {
        message = 'Global coherence poor';
      }
      
      if (mostCommonType) {
        message += `, most common issue: ${mostCommonType}`;
      }
      
      // Determine if global system is coherent
      const isGloballyCoherent = averageScore > 0.7 && coherentRatio > 0.8;
      
      // Global recovery recommendation
      let globalRecovery = null;
      
      if (!isGloballyCoherent) {
        if (averageScore < 0.3) {
          // Severe global coherence issues
          globalRecovery = {
            strategy: RecoveryStrategy.ROLLBACK,
            description: 'Roll back entire distributed system to last known good state'
          };
        } else if (mostCommonType === CoherenceViolationType.SYNCHRONIZATION) {
          // Synchronization issues
          globalRecovery = {
            strategy: RecoveryStrategy.RESYNC,
            description: 'Perform global parameter synchronization'
          };
        } else if (mostCommonType === CoherenceViolationType.DIMENSIONAL) {
          // Dimensional issues
          globalRecovery = {
            strategy: RecoveryStrategy.REPARTITION,
            description: 'Recalculate global partitioning scheme'
          };
        } else {
          // Default recovery
          globalRecovery = {
            strategy: RecoveryStrategy.CONTINUE,
            description: 'Apply local corrections on affected nodes'
          };
        }
      }
      
      return {
        isCoherent: isGloballyCoherent,
        score: averageScore,
        coherentNodeRatio: coherentRatio,
        violationCounts: violationsByType,
        mostSevereViolation,
        message,
        recovery: globalRecovery
      };
    }

    /**
     * Get coherence metrics
     * @returns {Object} Current coherence metrics
     */
    getMetrics() {
      return { ...this.metrics };
    }

    /**
     * Reset coherence metrics
     */
    resetMetrics() {
      this.metrics = {
        checksPerformed: 0,
        violationsDetected: 0,
        recoveryActions: 0,
        averageCoherenceScore: 1.0,
        violationsByType: {}
      };
      
      // Reset violation counters
      Object.values(CoherenceViolationType).forEach(type => {
        this.metrics.violationsByType[type] = 0;
      });
    }
    
    /**
     * Subscribe to coherence events
     * @param {string} event - Event name
     * @param {Function} callback - Event callback
     * @returns {Function} Unsubscribe function
     */
    subscribe(event, callback) {
      return this.eventBus.on(event, callback);
    }
  }

  // Add classes and enums to Prime.Distributed namespace
  Prime.Distributed.Coherence = {
    CoherenceViolationType,
    ViolationSeverity,
    RecoveryStrategy,
    DistributedCoherenceManager
  };
})();

// Export the enhanced Prime object
module.exports = Prime;