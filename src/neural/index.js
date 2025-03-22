/**
 * PrimeOS JavaScript Library - Neural Module
 * Advanced neural computation capabilities with coherence integration
 */

// Import the Prime object from core
const Prime = require("../core");

// Create the Neural namespace
Prime.Neural = {};

// Import submodules
require("./layer");
require("./optimization");
require("./layer/convolutional");
require("./layer/recurrent");
require("./model");
require("./distributed");

// Export the enhanced Prime object
module.exports = Prime;
