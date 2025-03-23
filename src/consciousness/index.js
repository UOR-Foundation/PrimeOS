/**
 * PrimeOS JavaScript Library - Consciousness Module
 * Coherence-based consciousness simulation capabilities
 */

// Import the Prime object from core
const Prime = require('../core');

// Create the Consciousness namespace
Prime.Consciousness = {};

/**
 * Initialize the consciousness module
 * @returns {Promise<Object>} Initialization result
 */
Prime.Consciousness.initialize = async function () {
  console.log('Initializing Consciousness module...');
  return {
    success: true,
    timestamp: Date.now(),
  };
};

// Import core components
const ConsciousnessOperator = require('./operator');
const SelfReferentialLoop = require('./self-reference');
const TemporalIntegration = require('./temporal');
const StateRepresentation = require('./state');
const AttentionMechanism = require('./attention');
const MemoryStructure = require('./memory');
const DecisionMaking = require('./decision');
const ThresholdManager = require('./threshold');
const ConsciousnessModule = require('./module');

// Register core components directly
Prime.Consciousness.Operator = ConsciousnessOperator;
Prime.Consciousness.SelfReferentialLoop = SelfReferentialLoop;
Prime.Consciousness.TemporalIntegration = TemporalIntegration;
Prime.Consciousness.StateRepresentation = StateRepresentation;
Prime.Consciousness.AttentionMechanism = AttentionMechanism;
Prime.Consciousness.MemoryStructure = MemoryStructure;
Prime.Consciousness.DecisionMaking = DecisionMaking;
Prime.Consciousness.ThresholdManager = ThresholdManager;
Prime.Consciousness.Module = ConsciousnessModule;

// Import submodules
require('./models');
require('./awareness');

// Export the enhanced Prime object
module.exports = Prime;
