/**
 * PrimeOS JavaScript Library - Coherence Mock Loader
 * Loads the mock implementation for tests
 */

// Import the real coherence module
require("./coherence");

// Import the mock module to override necessary functions
require("./coherence/verify-mock");

// Export the enhanced Prime object
module.exports = require("./core");
