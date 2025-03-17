/**
 * PrimeOS JavaScript Library - Main entry point
 * This file exports all PrimeOS modules
 * Version 1.0.0
 */

// Import core Prime and ensure all modules are loaded in correct order
const Prime = require('./core.js');
require('./mathematics.js');
require('./coherence.js');
require('./framework/index.js');

// Import refactored component system
require('./components/index.js');

// Export all modules
module.exports = Prime;

// Also provide named exports
module.exports.Utils = Prime.Utils;
module.exports.EventBus = Prime.EventBus;
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