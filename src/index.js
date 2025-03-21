/**
 * PrimeOS JavaScript Library - Main entry point
 * This file exports all PrimeOS modules
 * Version 1.0.0
 */

// Import refactored core Prime
const Prime = require("./core");

// Import refactored math module
require("./math");

// Import neural module
require("./neural");

// Import consciousness module
require("./consciousness");

// Import distributed computation module
require("./distributed");

// Import legacy modules
// These will be refactored in future phases
require("./coherence.js");
require("./framework/index.js");
require("./components/index.js");

// Initialize framework as a top-level property
Prime.framework = Prime.createPrimeFramework();

// Export all modules
module.exports = Prime;

// Also provide named exports
module.exports.Utils = Prime.Utils;
module.exports.EventBus = Prime.EventBus;
module.exports.EventBusClass = Prime.EventBusClass;
module.exports.Logger = Prime.Logger;
module.exports.Math = Prime.Math;
module.exports.Neural = Prime.Neural;
module.exports.Consciousness = Prime.Consciousness;
module.exports.Distributed = Prime.Distributed;

// Legacy exports
module.exports.ModuleLogger = Prime.ModuleLogger;
module.exports.Clifford = Prime.Clifford;
module.exports.Lie = Prime.Lie;
module.exports.coherence = Prime.coherence;
module.exports.UOR = Prime.UOR;
module.exports.Base0 = Prime.Base0;
module.exports.Base1 = Prime.Base1;
module.exports.Base2 = Prime.Base2;
module.exports.Base3 = Prime.Base3;
module.exports.createPrimeFramework = Prime.createPrimeFramework;
module.exports.createComponent = Prime.createComponent;
module.exports.ComponentRegistry = Prime.ComponentRegistry;
module.exports.ComponentFactory = Prime.ComponentFactory;
module.exports.ComponentTemplate = Prime.ComponentTemplate;
module.exports.render = Prime.render;
module.exports.performance = Prime.performance;
module.exports.analytic = Prime.analytic;
module.exports.generateDocumentation = Prime.generateDocumentation;
module.exports.Components = Prime.Components;
