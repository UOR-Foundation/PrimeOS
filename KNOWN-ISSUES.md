# Known Issues in PrimeOS

## Integration Tests

All integration tests are now passing correctly.

~~1. **Component System:**~~
   ~~- Component lifecycle and events: Component should be initialized~~ ✅ **FIXED**

This issue has been resolved by implementing proper component initialization that supports both `init()` and `initialize()` methods.

## Extreme Numerical Conditions

The new extreme condition handling has the following limitations:

1. **Numerical Precision:**
   - Enhanced numerical precision relies on IEEE-754 double precision limitations
   - For ultra-high precision operations, external libraries may be required
   - The NextAfter implementation is a simplified version for testing, not a fully compliant IEEE-754 implementation

2. **Extreme Value Performance:**
   - The Eigendecomposition implementation currently only supports symmetric matrices
   - Linear system solver may encounter performance issues with very large matrices
   - Gradient descent may require manual tuning for highly non-convex functions

3. **RNA Folding Simulations:**
   - The RNA folding simulation tests use simplified physics that may not fully capture real molecular dynamics
   - Extreme condition tests should be validated with domain-specific libraries for production use
   - Memory consumption can be significant for large simulations
   - **IMPORTANT**: Current extreme condition tests require significant memory (8GB+) to run completely
   - Extreme condition tests, UOR verification tests, and integration tests are excluded from CI workflows
   - CI workflow uses `npm run test:ci` which only runs core, mathematics, framework, and coherence tests

4. **Test Coverage:**
   - Not all extreme conditions are covered by automated tests yet
   - Users should validate results from ExtremePrecision module in their specific domains
   - Corner cases should be manually verified for critical applications

## Testing Strategy

Due to memory constraints in CI environments, we've implemented a tiered testing approach:

1. **CI-safe tests** - Run in CI/CD pipelines and before publishing
   ```bash
   npm run test:ci  # Runs core, mathematics, framework, and coherence tests
   ```

2. **High-memory tests** - Should be run locally (requires 8GB+ RAM):
   ```bash
   # Run extreme condition tests
   npm run test:extreme
   
   # Run UOR verification tests
   npm run test:uor
   
   # Run integration tests
   npm run test:integration
   ```

3. **Complete test suite** - Run all tests when preparing for major releases:
   ```bash
   npm run test:all  # Runs all test suites including browser tests
   ```

CI/CD pipeline is configured to use the `test:ci` script to prevent out-of-memory errors during automated builds and deployments.