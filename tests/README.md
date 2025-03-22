# PrimeOS Consciousness Module Tests

## Overview

This directory contains tests for the PrimeOS Consciousness Module, which implements a coherence-based consciousness simulation. The implementation is based on mathematical principles of coherence and includes components for memory, decision-making, threshold management, and state representation.

## Test Structure

The tests are organized as follows:

1. **Basic Component Tests** (`/workspaces/PrimeOS/test-consciousness.js`)
   - Simple tests for individual components (MemoryStructure, DecisionMaking, ThresholdManager)
   - Verifies each component can be instantiated and its basic methods work

2. **Integration Tests** (`/workspaces/PrimeOS/tests/consciousness-integration-tests.js`)
   - Comprehensive tests for all components working together
   - Verifies the full functionality of each component
   - Tests the ConsciousnessModule as an integration of all components

3. **Neural Integration Tests** (`/workspaces/PrimeOS/tests/consciousness-tests.js`)
   - Tests integration with the neural network framework
   - Verifies coherence manifold operations
   - Tests neural-consciousness interactions

## Running Tests

To run all tests, use the test runner script:

```bash
node run-consciousness-tests.js
```

This will run all tests and provide a summary of results.

To run individual test suites:

```bash
# Basic component tests
node test-consciousness.js

# Integration tests
node tests/consciousness-integration-tests.js

# Neural integration tests
node tests/consciousness-tests.js
```

## Test Coverage

The tests cover:

- **MemoryStructure**
  - Memory storage and retrieval
  - Memory indexing by coherence patterns
  - Memory consolidation

- **DecisionMaking**
  - Fast and deliberative decision modes
  - Multi-perspective evaluation
  - Decision outcome tracking

- **ThresholdManager**
  - Adaptive threshold management
  - Arousal level modeling
  - Consciousness level determination

- **ConsciousnessModule**
  - Component integration
  - State updating
  - Event-based communication
  - API functions (decision making, memory retrieval, etc.)

## Further Improvements

Potential areas for improved test coverage:

1. Performance testing under high load
2. Edge case testing with extreme state values
3. Long-duration running tests for stability
4. Test visualization of consciousness states
5. Integration tests with distributed systems

## Development Notes

When extending or modifying the consciousness module, make sure to:

1. Update the relevant tests to reflect changes
2. Run the full test suite to ensure all integration points work
3. Add new tests for any new functionality
4. Update this README if the test structure changes