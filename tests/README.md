# PrimeOS Tests

This directory contains tests for the PrimeOS codebase. The tests are organized by type and component, following a standardized structure to improve maintainability and clarity.

## Test Organization

The tests are organized into the following categories:

- **Unit Tests**: Test individual components in isolation (`tests/unit/`)
- **Integration Tests**: Test interactions between components (`tests/integration/`)
- **Extreme Condition Tests**: Test behavior under extreme numerical conditions (`tests/extreme/`)
- **Performance Tests**: Test performance characteristics (`tests/performance/`)

Each category is further organized by the component or subsystem being tested.

## Running Tests

Use the provided npm scripts to run tests:

```bash
# Run all tests
npm test:all

# Run all unit tests
npm test:unit

# Run specific unit tests
npm test:unit:core
npm test:unit:math
npm test:unit:components
# etc.

# Run integration tests
npm test:integration

# Run extreme condition tests
npm test:extreme

# Run performance tests
npm test:performance
```

## Test Utilities

Common test utilities are provided in the `tests/utils/` directory:

- **Assertions**: Common assertion helpers in `assertions.js`
- **Mocking**: Standardized mocking utilities in `mocking.js`
- **Setup**: Shared setup/teardown utilities in `setup.js`
- **Environments**: Environment handling utilities in `environments.js`

## Writing New Tests

When writing new tests, follow these guidelines:

1. Create test files in the appropriate directory based on what you're testing
2. Use the `.test.js` extension for all test files (e.g., `vector.test.js`)
3. Import utilities from `tests/utils` to maintain consistency
4. Use the provided templates as a starting point

Example:

```javascript
/**
 * PrimeOS Unit Tests - [Component]
 * 
 * Tests for the [Component] functionality.
 */

const Prime = require('../../../src/[path].js');
const { Assertions, Mocking } = require('../../utils');

describe('[Component Name]', () => {
  // Tests go here
});
```

## Test Matrix

A comprehensive test matrix documenting the coverage of all components can be found in `tests/matrix.md`. This matrix provides an overview of what's tested and where coverage gaps exist.

## Extreme Condition Testing

Extreme condition tests require special treatment due to their resource intensity. These tests use a dedicated test runner (`tests/runners/run-extreme.js`) that runs tests in batches with memory management.

To run a specific extreme test batch:

```bash
npm run test:extreme:math
npm run test:extreme:neural
# etc.
```

## Refactoring Plan

A detailed plan for the ongoing test refactoring can be found in `tests/tests-refactor-plan.md`. This document outlines the current status, goals, and tasks for improving the test suite.

## Test Refactoring Completion

All tests have been migrated to the new structure and organized according to test type and component. The old test files have been removed, and the test suite now follows a consistent, maintainable structure.

For historical reference, a mapping of the old test files to their replacements can be found in `tests/DEPRECATED-TESTS.md`.