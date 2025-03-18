# PrimeOS Core Library Enhancement Plan

## Problem Analysis

Based on the test failures observed, the primary issues with the PrimeOS src/ library are:

1. **Missing `CoherenceError` class**: 
   - The `src/core.js` file has a comprehensive error hierarchy but lacks the `CoherenceError` class that is being used in `Manifold.updateVariant()`.
   - The test setup provides a mock, but the actual implementation is needed in the core library.

2. **Coherence Validation Issues**:
   - The `src/framework/base0/manifold.js` implementation is throwing coherence errors that prevent the tests from passing.
   - The mathematical foundation requires proper coherence checks before variant updates.

3. **Incomplete Integration Between Components**:
   - SecureVault tests fail when retrieving stored secrets
   - SettingsStore tests show issues with the resetToDefaults method and updating API keys

## Enhancement Strategy

### 1. Core Error Hierarchy

- Add `CoherenceError` class to the error hierarchy in `src/core.js`
- Ensure it follows the same pattern as other error classes
- Make it properly extend `PrimeError` with appropriate default code and contextual information

### 2. Coherence System Improvements

- Review and enhance the coherence validator implementation 
- Ensure the Manifold class properly handles coherence checks
- Add robustness to the updateVariant method to prevent test failures
- Implement mathematical coherence validation with proper thresholds

### 3. Component Integration

- Fix the SecureVault implementation to properly store and retrieve secrets
- Ensure the SettingsStore implementation properly resets to defaults
- Fix API key update functionality

## Implementation Plan

### Phase 1: Error Hierarchy Enhancement

1. Add `CoherenceError` class to `src/core.js` alongside other error classes
2. Ensure it has appropriate properties and methods
3. Verify error inheritance chain

### Phase 2: Coherence System Improvements

1. Enhance `src/framework/base0/coherence-validator.js` implementation
2. Improve the Manifold class's coherence checks
3. Add robustness to updateVariant method in Manifold 
4. Implement proper coherence impact calculation

### Phase 3: Component Integration

1. Fix SecureVault implementation to properly store/retrieve secrets
2. Enhance SettingsStore implementation for resetting defaults
3. Fix API key functionality

## Testing Strategy

- Verify each enhancement with the failing tests
- Maintain mathematical coherence principles
- Ensure no regression in passing tests
- Add documentation for components affected

## Mathematical Considerations

The coherence system is based on mathematical principles of invariance and manifold theory. The enhancements must maintain the mathematical integrity of the system while ensuring practical functionality. The coherence validator must accurately calculate impact of state changes on the mathematical coherence of the system.

## Implementation Priorities

1. Fix `CoherenceError` class - highest priority as it's blocking many tests
2. Enhance coherence validation - critical for maintaining mathematical foundation
3. Fix component-specific implementations - necessary for end-to-end functionality