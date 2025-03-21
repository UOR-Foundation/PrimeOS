/**
 * PrimeOS JavaScript Library - Math Index
 * Exports all math modules
 */

// Import the Prime object from core
const Prime = require("../core");

// Create the Math namespace if it doesn't exist
Prime.Math = Prime.Math || {};

// Import all math modules
require("./vector");
require("./matrix");
require("./clifford");

// In the future, these modules will be added:
// require('./lie');
// require('./numerical');
// require('./spectral');

// Export the enhanced Prime object
module.exports = Prime;
