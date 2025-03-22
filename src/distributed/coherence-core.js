/**
 * PrimeOS JavaScript Library - Distributed Coherence Core Module
 * Core coherence checking functionality for distributed systems
 */

// Import the Prime object from core
const Prime = require('../core');
const EventBus = require('./event-bus');

// Import coherence sub-modules
require('./coherence-violations');
require('./coherence-recovery');
require('./coherence-metrics');

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
      defaultRecoveryStrategy: config.defaultRecoveryStrategy || 
        Prime.Distributed.Coherence.Recovery.Strategies.CONTINUE
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
    this.eventBus = EventBus;
    
    // Create metrics manager
    this.metricsManager = new Prime.Distributed.Coherence.Metrics.Manager({
      historySize: config.metricsHistorySize || 100,
      reportingInterval: config.metricsReportingInterval || 10
    });
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
    
    // Start with basic coherence checks
    const checks = {
      weights: layer.weights ? this._checkTensorCoherence(layer.weights, 'matrix') : { valid: true, coherence: 1.0 },
      biases: layer.biases ? this._checkTensorCoherence(layer.biases, 'vector') : { valid: true, coherence: 1.0 }
    };
    
    // Check dimensional coherence
    const dimensionalCheck = Prime.Distributed.Coherence.Violations.Detector.detectDimensionalViolations(layer);
    const dimensionsValid = !dimensionalCheck.hasViolations;
    
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
        checks.gradients = Prime.Distributed.Coherence.Violations.Detector.detectGradientViolations(
          context.gradients, 
          {
            explodinThreshold: this.config.thresholds.gradient,
            vanishingThreshold: this.config.thresholds.numerical
          }
        );
      }
    }
    
    // Aggregate results
    const coherenceScore = this._aggregateCoherenceResults(checks);
    
    // Identify violations
    const violations = this._identifyViolations(checks, context || {});
    
    // Force lower coherence score if we have critical or high severity violations
    let finalCoherenceScore = coherenceScore;
    for (const violation of violations) {
      if (violation.severity === Prime.Distributed.Coherence.Violations.Severity.CRITICAL) {
        finalCoherenceScore = Math.min(finalCoherenceScore, 0.1); // Critical violations force very low score
        break;
      } else if (violation.severity === Prime.Distributed.Coherence.Violations.Severity.HIGH) {
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
      result.recovery = Prime.Distributed.Coherence.Recovery.Manager.recommendRecoveryActions(result);
    }
    
    // Update metrics
    this.metricsManager.updateMetrics(
      finalCoherenceScore, 
      { violations }, 
      result.recovery
    );
    
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
    // Use the detector from violations module
    const numericalCheck = Prime.Distributed.Coherence.Violations.Detector.detectNumericalViolations(
      tensor, 
      this.config.thresholds.numerical
    );
    
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
    
    // Count elements for coherence calculation
    let totalElements = 0;
    
    if (isMatrix) {
      for (const row of tensor) {
        if (Array.isArray(row)) {
          totalElements += row.length;
        }
      }
    } else {
      totalElements = tensor.length;
    }
    
    // Calculate coherence score
    const coherenceScore = totalElements > 0 ? 
      1.0 - (numericalCheck.violationsCount / totalElements) : 0.0;
    
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
        satisfied: !numericalCheck.hasViolations,
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
        satisfied: !numericalCheck.hasViolations,
        priority: 7
      });
    }
    
    return {
      valid: !numericalCheck.hasViolations,
      coherence: coherenceScore,
      constraintResults,
      numericalCheck,
      message: !numericalCheck.hasViolations ? 
        'All constraints satisfied' : 
        numericalCheck.message
    };
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
    if (scheme.type === 'intra-layer') {
      return this._checkIntraLayerPartition(layer, scheme);
    } else if (scheme.type === 'layer-wise') {
      return this._checkLayerWisePartition(layer, scheme);
    } else if (scheme.type === 'data-parallel') {
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
    const layerNodes = scheme.getNodeLayers ? 
      scheme.getNodeLayers(layer.id) : 
      scheme.layerNodes?.[layer.id] || [];
      
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
    
    if (scheme.layerAssignments instanceof Map) {
      for (const [nodeId, layers] of scheme.layerAssignments.entries()) {
        if (layers.includes(layer.id)) {
          layerAssigned = true;
          break;
        }
      }
    } else if (typeof scheme.layerAssignments === 'object') {
      for (const nodeId in scheme.layerAssignments) {
        const layers = scheme.layerAssignments[nodeId];
        if (Array.isArray(layers) && layers.includes(layer.id)) {
          layerAssigned = true;
          break;
        }
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
      message: 'Layer properly assigned in layer-wise partitioning'
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
    // For data-parallel partitioning, each node should have a complete copy of the model
    // so coherence is about parameter synchronization
    
    // Check if synchronization status is available
    if (!scheme.syncStatus) {
      return {
        valid: true,
        coherence: 0.8, // Assume mostly coherent without sync info
        message: 'Cannot verify data-parallel synchronization (no sync status)'
      };
    }
    
    // Check if this layer's parameters are synchronized
    const layerSyncStatus = scheme.syncStatus[layer.id];
    if (!layerSyncStatus) {
      return {
        valid: true,
        coherence: 0.7, // Lower coherence when no layer-specific info
        message: 'Layer synchronization status not available'
      };
    }
    
    // Calculate coherence based on sync stats
    let coherence = 1.0;
    
    if (layerSyncStatus.lastSyncTimestamp) {
      // Calculate age of synchronization
      const syncAge = Date.now() - layerSyncStatus.lastSyncTimestamp;
      const syncAgeThreshold = scheme.maxSyncAge || 5000; // Default 5 seconds
      
      // Reduce coherence for old syncs
      if (syncAge > syncAgeThreshold) {
        // Exponential decay of coherence with sync age
        coherence = Math.exp(-syncAge / syncAgeThreshold) * 0.3 + 0.7;
      }
    } else {
      // No synchronization has occurred
      coherence = 0.5;
    }
    
    // Further adjust for any sync errors
    if (layerSyncStatus.syncErrors && layerSyncStatus.syncErrors > 0) {
      // Reduce coherence for each sync error, with diminishing impact
      coherence = coherence * Math.exp(-layerSyncStatus.syncErrors / 10);
    }
    
    return {
      valid: coherence >= 0.7, // Valid if coherence is reasonably high
      coherence,
      message: coherence >= 0.9 ? 
        'Parameters well-synchronized across nodes' :
        coherence >= 0.7 ?
          'Parameters adequately synchronized across nodes' :
          'Parameters not sufficiently synchronized across nodes'
    };
  }
  
  /**
   * Check synchronization coherence between local and global parameters
   * @private
   * @param {Object} layer - Local layer
   * @param {Object} globalParams - Global parameters
   * @returns {Object} Synchronization coherence result
   */
  _checkSynchronizationCoherence(layer, globalParams) {
    if (!layer || !globalParams) {
      return {
        valid: false,
        coherence: 0.0,
        message: 'Missing local or global parameters'
      };
    }
    
    // Extract layer ID or index
    const layerId = layer.id || layer.index || 0;
    
    // Get global parameters for this layer
    const globalLayerParams = globalParams[layerId];
    if (!globalLayerParams) {
      return {
        valid: false,
        coherence: 0.0,
        message: 'Layer not found in global parameters'
      };
    }
    
    // Check weights synchronization
    let weightsSynchronized = true;
    let weightsDivergence = 0;
    
    if (layer.weights && globalLayerParams.weights) {
      const localWeights = layer.weights;
      const globalWeights = globalLayerParams.weights;
      
      // Check dimensions match
      if (localWeights.length !== globalWeights.length ||
          (localWeights[0] && globalWeights[0] && 
           localWeights[0].length !== globalWeights[0].length)) {
        weightsSynchronized = false;
        weightsDivergence = 1.0; // Maximum divergence for mismatched dimensions
      } else {
        // Calculate average divergence
        let totalDiff = 0;
        let count = 0;
        
        for (let i = 0; i < localWeights.length; i++) {
          const localRow = localWeights[i];
          const globalRow = globalWeights[i];
          
          if (Array.isArray(localRow) && Array.isArray(globalRow)) {
            for (let j = 0; j < localRow.length; j++) {
              const localVal = localRow[j];
              const globalVal = globalRow[j];
              
              if (Number.isFinite(localVal) && Number.isFinite(globalVal)) {
                // Calculate normalized difference
                const maxVal = Math.max(Math.abs(localVal), Math.abs(globalVal), 1e-10);
                totalDiff += Math.abs(localVal - globalVal) / maxVal;
                count++;
              }
            }
          }
        }
        
        // Calculate average divergence
        weightsDivergence = count > 0 ? totalDiff / count : 0;
        weightsSynchronized = weightsDivergence <= this.config.thresholds.synchronization;
      }
    }
    
    // Check biases synchronization
    let biasesSynchronized = true;
    let biasesDivergence = 0;
    
    if (layer.biases && globalLayerParams.biases) {
      const localBiases = layer.biases;
      const globalBiases = globalLayerParams.biases;
      
      // Check dimensions match
      if (localBiases.length !== globalBiases.length) {
        biasesSynchronized = false;
        biasesDivergence = 1.0; // Maximum divergence for mismatched dimensions
      } else {
        // Calculate average divergence
        let totalDiff = 0;
        let count = 0;
        
        for (let i = 0; i < localBiases.length; i++) {
          const localVal = localBiases[i];
          const globalVal = globalBiases[i];
          
          if (Number.isFinite(localVal) && Number.isFinite(globalVal)) {
            // Calculate normalized difference
            const maxVal = Math.max(Math.abs(localVal), Math.abs(globalVal), 1e-10);
            totalDiff += Math.abs(localVal - globalVal) / maxVal;
            count++;
          }
        }
        
        // Calculate average divergence
        biasesDivergence = count > 0 ? totalDiff / count : 0;
        biasesSynchronized = biasesDivergence <= this.config.thresholds.synchronization;
      }
    }
    
    // Calculate overall synchronization coherence
    const overallDivergence = Math.max(weightsDivergence, biasesDivergence);
    const synchronizationCoherence = 1.0 - overallDivergence;
    
    return {
      valid: weightsSynchronized && biasesSynchronized,
      coherence: synchronizationCoherence,
      weightsDivergence,
      biasesDivergence,
      message: synchronizationCoherence > 0.95 ? 
        'Parameters well-synchronized with global state' :
        synchronizationCoherence > 0.8 ?
          'Parameters adequately synchronized with global state' :
          'Parameters significantly diverged from global state'
    };
  }
  
  /**
   * Aggregate individual coherence check results into an overall score
   * @private
   * @param {Object} checks - Individual check results
   * @returns {number} Aggregated coherence score
   */
  _aggregateCoherenceResults(checks) {
    if (!checks || typeof checks !== 'object') {
      return 0.0;
    }
    
    // Define weights for different check types
    const weights = {
      weights: 0.4,
      biases: 0.3,
      partition: 0.1,
      synchronization: 0.15,
      gradients: 0.05
    };
    
    let totalWeight = 0;
    let weightedSum = 0;
    
    // Calculate weighted sum of coherence scores
    for (const [checkType, checkResult] of Object.entries(checks)) {
      if (checkResult && typeof checkResult.coherence === 'number') {
        const weight = weights[checkType] || 0.1;
        weightedSum += checkResult.coherence * weight;
        totalWeight += weight;
      }
    }
    
    // Calculate weighted average
    const aggregatedScore = totalWeight > 0 ? weightedSum / totalWeight : 0;
    
    // Ensure score is in valid range
    return Math.max(0, Math.min(1, aggregatedScore));
  }
  
  /**
   * Identify violations from check results
   * @private
   * @param {Object} checks - Check results
   * @param {Object} context - Check context
   * @returns {Array} Identified violations
   */
  _identifyViolations(checks, context) {
    const violations = [];
    
    // Import violation types and severity
    const ViolationTypes = Prime.Distributed.Coherence.Violations.Types;
    const Severity = Prime.Distributed.Coherence.Violations.Severity;
    
    // Check for weight tensor violations
    if (checks.weights && !checks.weights.valid) {
      if (checks.weights.numericalCheck && checks.weights.numericalCheck.violations) {
        // Add all numerical violations directly
        violations.push(...checks.weights.numericalCheck.violations);
      } else {
        // Add a generic violation
        violations.push({
          type: ViolationTypes.NUMERICAL,
          severity: Severity.HIGH,
          message: 'Invalid weight tensor structure or values',
          check: 'weights'
        });
      }
    }
    
    // Check for bias tensor violations
    if (checks.biases && !checks.biases.valid) {
      if (checks.biases.numericalCheck && checks.biases.numericalCheck.violations) {
        // Add all numerical violations directly
        violations.push(...checks.biases.numericalCheck.violations);
      } else {
        // Add a generic violation
        violations.push({
          type: ViolationTypes.NUMERICAL,
          severity: Severity.MEDIUM,
          message: 'Invalid bias tensor structure or values',
          check: 'biases'
        });
      }
    }
    
    // Check for partition violations
    if (checks.partition && !checks.partition.valid) {
      violations.push({
        type: ViolationTypes.NETWORK,
        severity: Severity.HIGH,
        message: checks.partition.message || 'Invalid partition configuration',
        check: 'partition'
      });
    }
    
    // Check for synchronization violations
    if (checks.synchronization && !checks.synchronization.valid) {
      const divergence = Math.max(
        checks.synchronization.weightsDivergence || 0,
        checks.synchronization.biasesDivergence || 0
      );
      
      // Determine severity based on divergence level
      let severity = Severity.LOW;
      if (divergence > 0.3) {
        severity = Severity.HIGH;
      } else if (divergence > 0.1) {
        severity = Severity.MEDIUM;
      }
      
      violations.push({
        type: ViolationTypes.SYNCHRONIZATION,
        severity,
        divergence,
        message: checks.synchronization.message || 'Parameter synchronization violation',
        check: 'synchronization'
      });
    }
    
    // Check for gradient violations
    if (checks.gradients && checks.gradients.hasViolations) {
      // Add all gradient violations directly
      if (checks.gradients.violations) {
        violations.push(...checks.gradients.violations);
      }
    }
    
    return violations;
  }
  
  /**
   * Apply corrections to restore coherence
   * @param {Object} layer - Layer to correct
   * @param {Object} checkResult - Coherence check result
   * @returns {Object} Correction result
   */
  applyCoherenceCorrections(layer, checkResult) {
    if (!layer || !checkResult) {
      return {
        success: false,
        message: 'Missing layer or check result',
        corrections: 0
      };
    }
    
    // Don't apply corrections if coherent
    if (checkResult.isCoherent) {
      return {
        success: true,
        message: 'Layer is already coherent',
        corrections: 0,
        correctedLayer: layer
      };
    }
    
    // Create a copy of the layer to avoid modifying original
    const correctedLayer = { ...layer };
    let totalCorrections = 0;
    
    // Apply numerical corrections to weights if needed
    if (layer.weights && checkResult.checks.weights && !checkResult.checks.weights.valid) {
      const weightsCorrection = Prime.Distributed.Coherence.Recovery.Manager.applyNumericalCorrections(
        layer.weights,
        {
          threshold: this.config.thresholds.numerical,
          maxValue: 1e6
        }
      );
      
      if (weightsCorrection.success) {
        correctedLayer.weights = weightsCorrection.correctedTensor;
        totalCorrections += weightsCorrection.corrections;
      }
    }
    
    // Apply numerical corrections to biases if needed
    if (layer.biases && checkResult.checks.biases && !checkResult.checks.biases.valid) {
      const biasesCorrection = Prime.Distributed.Coherence.Recovery.Manager.applyNumericalCorrections(
        layer.biases,
        {
          threshold: this.config.thresholds.numerical,
          maxValue: 1e6
        }
      );
      
      if (biasesCorrection.success) {
        correctedLayer.biases = biasesCorrection.correctedTensor;
        totalCorrections += biasesCorrection.corrections;
      }
    }
    
    // Apply gradient clipping if needed
    if (layer.gradients && checkResult.checks.gradients && checkResult.checks.gradients.hasViolations) {
      const gradientCorrection = Prime.Distributed.Coherence.Recovery.Manager.applyGradientClipping(
        layer.gradients,
        {
          clipMethod: 'value',
          clipValue: 5.0
        }
      );
      
      if (gradientCorrection.success && gradientCorrection.clippingApplied) {
        correctedLayer.gradients = gradientCorrection.clippedGradients;
        totalCorrections++;
      }
    }
    
    // Return correction results
    return {
      success: totalCorrections > 0,
      message: totalCorrections > 0 ? 
        `Applied ${totalCorrections} corrections to restore coherence` : 
        'No corrections applied',
      corrections: totalCorrections,
      correctedLayer
    };
  }
  
  /**
   * Get current coherence metrics
   * @returns {Object} Coherence metrics
   */
  getMetrics() {
    return this.metricsManager.getMetricsSnapshot();
  }
  
  /**
   * Reset coherence metrics
   */
  resetMetrics() {
    return this.metricsManager.resetMetrics();
  }
}

// Add to Prime namespace
Prime.Distributed = Prime.Distributed || {};
Prime.Distributed.Coherence = Prime.Distributed.Coherence || {};
Prime.Distributed.Coherence.Manager = DistributedCoherenceManager;

module.exports = Prime;