/**
 * PrimeOS JavaScript Library - Distributed Coherence Module
 * Advanced coherence checks for distributed neural networks
 */

// Import the Prime object from core
const Prime = require('../core');

// Import coherence components
require('./coherence-violations');
require('./coherence-recovery');
require('./coherence-metrics');
require('./coherence-core');

// Export the enhanced Prime object
module.exports = Prime;