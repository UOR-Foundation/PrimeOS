/**
 * PrimeOS JavaScript Library - Core Index
 * Exports all core modules
 */

// Import all core modules in the correct order to handle dependencies
const Prime = require("./prime");
require("./utils");
require("./error");
require("./version");
require("./event-bus");
require("./logger");
require("./module-loader");

// Import additional modules
require("../storage");

// Export the fully configured Prime object
module.exports = Prime;
