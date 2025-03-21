/**
 * PrimeOS JavaScript Library - Distributed Computation Module
 * Provides coherence-preserving distributed computation for neural networks
 */

// Import the Prime object from core
const Prime = require("../core");

// Create the Distributed namespace
Prime.Distributed = {};

// Import submodules
require("./cluster");
require("./communication");
require("./partition");
require("./coherence");

// Export the enhanced Prime object
module.exports = Prime;
