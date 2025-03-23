# PrimeOS Pragmatic Refactoring Plan

## Overview

This document outlines a focused, pragmatic refactoring plan for the PrimeOS codebase. The primary goal is to resolve existing issues, improve stability, and ensure all core functionality works correctly. This plan focuses on immediate needs rather than adding new features.

## Key Principles

1. **Focus on Stability**: Prioritize fixing existing issues over adding new features
2. **Incremental Changes**: Make small, verifiable changes with test validation
3. **Fix Circular Dependencies**: Resolve module loading issues to prevent runtime errors
4. **Optimize Memory Usage**: Address memory inefficiencies in critical areas
5. **Ensure Test Coverage**: Get existing tests passing reliably

## Immediate Focus Areas

### 1. Fix Remaining Circular Dependencies

#### Current Issues
- Some modules are still failing due to circular dependencies
- Inconsistent approaches to dependency handling across the codebase
- Test failures due to module loading errors

#### Action Plan
1. **Apply successful patterns from math modules to other areas**: ✅
   - Use property descriptor checks before assignment
   - Implement lazy loading with proper error handling
   - Create empty placeholder objects to break cycles

2. **Fix distributed/coherence.js dependency issues**:
   - Ensure all coherence submodules handle circular dependencies correctly
   - Verify inter-module references use consistent patterns
   - Add fallbacks for missing dependencies during initialization

3. **Fix framework/base0 module dependencies**:
   - Apply the getter/setter pattern for manifold.js exports
   - Ensure coherence-validator.js lazy loading works correctly
   - Fix any cross-references between framework modules

### 2. Memory Optimization for Critical Areas

#### Current Issues
- Tests failing with out-of-memory errors
- Inefficient object creation in hot paths
- Excessive copying of large data structures

#### Action Plan
1. **Optimize test memory usage**:
   - Add limits to test data size
   - Clean up references between tests
   - Add incremental garbage collection calls in long-running tests

2. **Optimize matrix operations**:
   - Ensure TypedArrays are used consistently
   - Add in-place operation options where missing
   - Reduce temporary object creation in calculation chains

3. **Optimize coherence checking**:
   - Add sampling options for large-scale coherence checks
   - Implement incremental validation for large objects
   - Reduce object copying in validation operations

### 3. Test Reliability Improvements

#### Current Issues
- Inconsistent test results with the same code
- Tests running out of memory or timing out
- Missing test isolation between components

#### Action Plan
1. **Fix high-priority test failures**:
   - Resolve matrix-refactor test failures
   - Fix coherence-verification test issues
   - Make refactor-verification tests reliable

2. **Improve test isolation**:
   - Ensure tests clean up global state
   - Add better error handling in test setup/teardown
   - Create isolated module loading for tests

3. **Add targeted test runners**:
   - Create specific test runners for high-risk areas
   - Add memory monitoring to tests
   - Implement test segmentation for large test suites

## Component-Specific Tasks

### 1. Math Package

#### Remaining Issues
- Occasional circular dependency warnings
- Memory inefficiency in some operations
- Inconsistent TypedArray usage

#### Action Items
- Verify all math modules handle circular dependencies correctly ✅
- Ensure consistent TypedArray usage across operations
- Add in-place operation options for all major functions

### 2. Distributed Package

#### Remaining Issues
- Coherence module circular dependencies
- Memory issues in distributed communication
- Event handling race conditions

#### Action Items
- Fix circular dependencies in coherence.js and related modules
- Implement proper module loading order in distributed components
- Ensure event listeners are properly cleaned up

### 3. Framework Base0 Package

#### Remaining Issues
- Manifold operations consuming excessive memory
- Inconsistent coherence validator loading
- Cross-references between framework modules

#### Action Items
- Fix circular dependencies between manifold modules
- Optimize memory usage in manifold operations
- Ensure coherence validator properly lazy-loads components

## Testing Strategy

1. **Incremental Testing**:
   - Test each module fix individually
   - Run targeted tests for each component
   - Ensure stability before moving to the next component

2. **Memory Testing**:
   - Add memory constraints to tests
   - Monitor memory usage during test runs
   - Identify memory leaks and high-consumption areas

3. **Regression Testing**:
   - Run the full test suite after each major fix
   - Verify that fixes don't introduce new issues
   - Document test outcomes for tracking progress

## Implementation Schedule

### Phase 1: Circular Dependency Resolution (Complete)
- Fix math module circular dependencies ✅
- Apply patterns from math modules to other areas ✅
- Document the approach for consistent usage ✅

### Phase 2: Framework Module Fixes (In Progress)
- Fix circular dependencies in framework modules
- Resolve manifold operation issues
- Ensure coherence validator works correctly

### Phase 3: Distributed Module Fixes
- Resolve coherence module dependencies
- Fix distributed communication issues
- Ensure all distributed components load correctly

### Phase 4: Memory Optimization
- Implement TypedArray usage consistently
- Add in-place operations where missing
- Reduce temporary object creation

### Phase 5: Test Suite Stabilization
- Get all tests passing consistently
- Fix memory issues in tests
- Improve test isolation

## Progress Tracking

| Component | Circular Deps Fixed | Memory Optimized | Tests Passing |
|-----------|---------------------|------------------|---------------|
| Math | ✅ | Partial | ✅ |
| Framework/Base0 | In Progress | No | No |
| Distributed | No | No | No |
| Consciousness | No | No | No |

## Current Focus

We are currently focusing on the following tasks:

1. Fix circular dependencies in framework/base0 modules
2. Address memory issues in distributed/coherence.js
3. Resolve test failures in coherence-verification.js

## Next Steps

1. Complete framework module fixes
2. Move to distributed module fixes
3. Implement memory optimizations
4. Stabilize test suite