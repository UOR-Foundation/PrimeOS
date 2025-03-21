# Known Issues in PrimeOS

## Integration Tests

Some integration tests are currently failing but are not blocking the CI/CD pipeline. These will be addressed in future development:

1. **Component System:**
   - Component lifecycle and events: Component should be initialized

These issues are related to incomplete implementations of certain features that will be completed in future releases.

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

4. **Test Coverage:**
   - Not all extreme conditions are covered by automated tests yet
   - Users should validate results from ExtremePrecision module in their specific domains
   - Corner cases should be manually verified for critical applications

To run the extreme condition tests: `node run-extreme-tests.js`