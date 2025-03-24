# PrimeOS Neural Module

## Overview
The Neural module provides neural network capabilities for PrimeOS, including various layer types, activation functions, optimization algorithms, and training functionality. This module is designed to be coherent, robust, and production-ready.

## Namespace Structure

The Neural module uses a consistent namespace structure to organize its components and prevent circular dependencies:

```
Prime.Neural                     - Main namespace for all neural functionality
  |-- Neural                     - Main facade class providing high-level API
  |-- Layer                      - Namespace for layer implementations
  |     |-- NeuralLayer          - Base layer class
  |     |-- DenseLayer/Dense     - Dense (fully connected) layer
  |     |-- ConvolutionalLayer   - Convolutional layer
  |     |-- RecurrentLayer       - Recurrent layer (LSTM, GRU)
  |     |-- SelfOptimizingLayer  - Self-adapting layer
  |-- Activation                 - Namespace for activation functions
  |     |-- get()                - Factory method to get activation functions
  |     |-- sigmoid, relu, etc.  - Individual activation implementations
  |-- Optimization               - Namespace for optimizers
  |     |-- OptimizerFactory     - Factory for creating optimizers
  |     |-- SGDOptimizer         - SGD implementation
  |     |-- AdamOptimizer        - Adam implementation
  |-- Model                      - Namespace for model implementations
  |     |-- Sequential           - Sequential model
  |     |-- Functional           - Functional model
  |-- Distributed                - Namespace for distributed training
  |     |-- Model                - Distributed model implementation
  |     |-- Parameter            - Parameter synchronization
  |-- Errors                     - Neural-specific error types
        |-- NeuralError          - Base error class
        |-- LayerError           - Layer-related errors
        |-- ModelError           - Model-related errors
        |-- ActivationError      - Activation-related errors
        |-- etc.
```

## Namespace Initialization Pattern

The neural module follows a standardized pattern for namespace initialization to prevent circular dependencies and ensure consistent behavior:

1. **Early Namespace Creation**: Namespaces are created at the top of each module file before any class definitions or imports to ensure they exist.

```javascript
// Initialize Layer namespace if it doesn't exist
(function(Prime) {
  // Ensure namespaces exist to prevent "cannot read property of undefined" errors
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Layer = Prime.Neural.Layer || {};
  Prime.Neural.Errors = Prime.Neural.Errors || {};
  
  // Track namespace initialization
  Prime.Neural._namespaceInitialized = Prime.Neural._namespaceInitialized || {};
  Prime.Neural._namespaceInitialized["Layer"] = true;
})(Prime);
```

2. **Module Loading Order**: Modules are loaded in a specific order to ensure dependencies are satisfied:
   - error.js (first to ensure error types exist)
   - layer/index.js (base layer types)
   - activation/index.js, optimization/index.js (specialized modules)
   - layer implementations (dense, convolutional, recurrent)
   - model implementations (model.js, model-builder.js)

3. **Deferred Registration**: Classes are defined within IIFEs and then registered to the namespace after definition.

```javascript
// Class definition within IIFE
(function () {
  class NeuralLayer {
    // Class implementation
  }
  
  // Register to namespace after definition
  Prime.Neural.Layer.NeuralLayer = NeuralLayer;
})();
```

4. **Error Handling with Fallbacks**: Error classes are accessed with fallbacks to prevent errors when the namespace structure isn't fully loaded.

```javascript
throw new (Prime.Neural.Errors.LayerError || Prime.ValidationError)(
  "Layer configuration must be an object",
  { providedType: typeof config },
  "INVALID_LAYER_CONFIG"
);
```

5. **Utility Functions**: Namespace management utilities are provided:

```javascript
// Utility methods for namespace management
Prime.Neural._ensureNamespace = function(path) {
  // Takes a string like "Neural.Layer.Dense" and ensures all objects in the path exist
  const parts = path.split('.');
  let current = Prime;
  
  for (const part of parts) {
    current[part] = current[part] || {};
    current = current[part];
  }
  
  return current;
};
```

## Best Practices

When extending the Neural module:

1. **Always initialize namespaces first** at the top of your file.
2. **Use fallback error types** for error handling to maintain backward compatibility.
3. **Wrap class definitions in IIFEs** to create closure scopes.
4. **Register classes to namespaces after definition**.
5. **Export Prime at the end** of the file, not the class directly.
6. **Use the available utility functions** like _ensureNamespace instead of manually checking existence.
7. **Follow the error handling pattern** with contexts and error codes.
8. **Add initialization tracking** to prevent duplicate initialization.

## Testing

For testing, use the resetForTesting() function to reinitialize the Neural module state:

```javascript
Prime.Neural.resetForTesting();
```

This will clear the state and reload all modules in the correct order.

## Module Usage

High-level API access is provided through the Prime.Neural.Neural class:

```javascript
// Create a layer
const layer = Prime.Neural.Neural.createLayer("dense", { inputSize: 10, outputSize: 5 });

// Create an optimizer
const optimizer = Prime.Neural.Neural.createOptimizer("adam", { learningRate: 0.001 });

// Apply activation function
const activated = Prime.Neural.Neural.activate(input, "relu");

// Create a model
const model = Prime.Neural.Neural.createModel({ type: "sequential" });
```

## Error Handling

Always use the Neural-specific error classes for better context and debugging:

```javascript
try {
  // Some operation
} catch (error) {
  throw new Prime.Neural.Errors.LayerError(
    "Descriptive error message",
    { contextData: value },
    "ERROR_CODE",
    error  // Original error as cause
  );
}
```