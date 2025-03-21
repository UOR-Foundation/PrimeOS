/**
 * PrimeOS JavaScript Library - Consciousness Module
 * Coherence-based consciousness simulation capabilities
 */

// Import the Prime object from core
const Prime = require("../core");

// Create the Consciousness namespace
Prime.Consciousness = {};

// Import submodules
require("./models");
require("./awareness");

// Export the enhanced Prime object
module.exports = Prime;
