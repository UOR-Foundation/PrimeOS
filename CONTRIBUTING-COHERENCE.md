# Contributing to PrimeOS Distributed Coherence

This guide explains how to contribute to the PrimeOS distributed coherence module and its testing infrastructure.

## Overview

The distributed coherence module provides mathematical coherence validation for distributed neural networks in PrimeOS. It ensures that numerical operations, tensor structures, gradients, and parameter synchronization maintain mathematical integrity across distributed compute nodes.

## Repository Structure

- `/src/distributed/coherence.js` - Core implementation of distributed coherence management
- `/src/distributed/cluster/index.js` - Implementation of cluster node management with coherence integration
- `/tests/distributed-coherence-integration-tests.js` - Integration tests for coherence functionality
- `/tests/distributed-coherence-benchmarks.js` - Performance benchmarks for coherence checks
- `/tests/distributed-coherence-mock-network.js` - End-to-end simulation of coherence in a distributed network
- `/docs/distributed-coherence-testing.md` - Documentation on coherence testing approach

## Getting Started

1. Clone the repository:
   ```bash
   git clone https://github.com/UOR-Foundation/PrimeOS.git
   cd PrimeOS
   ```

2. Install dependencies:
   ```bash
   npm install
   ```

3. Run the coherence tests:
   ```bash
   npm run test:coherence
   npm run test:coherence:bench
   npm run test:coherence:mock
   ```

## Development Guidelines

### Adding New Coherence Checks

To add a new type of coherence check to the `DistributedCoherenceManager`:

1. Add a new check method to the class:
   ```javascript
   _checkNewCoherenceType(layer, context) {
     // Implement coherence check logic
     // Return a result object with valid, coherence, and message properties
   }
   ```

2. Update the `checkLayerCoherence` method to include your new check
3. Add detection logic to the `_identifyViolations` method
4. Add correction logic to the `applyCoherenceCorrection` method
5. Update enums if needed (CoherenceViolationType, ViolationSeverity, etc.)

### Adding New Tests

When adding new coherence tests:

1. Follow the existing test structure in one of the test files
2. Include both passing and failing test cases
3. Test normal operation and edge cases
4. Include tests for violation detection and correction
5. Provide clear assertion messages

Example test structure:
```javascript
// Test new coherence check type
{
  // Create test data
  const testLayer = { /* ... */ };
  
  // Create coherence manager
  const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
  
  // Execute coherence check
  const result = coherenceManager.checkLayerCoherence(testLayer, {
    // Test-specific context
  });
  
  // Assert expectations
  assert(result.checks.newCheck !== undefined, "Should include new check");
  assert(result.checks.newCheck.valid === true, "New check should be valid");
}
```

### Adding New Benchmarks

To add new benchmarks:

1. Add a new benchmark registration to `distributed-coherence-benchmarks.js`
2. Use the `BenchmarkSuite.register` method to define your benchmark
3. Test with various sizes and configurations
4. Include memory usage measurements where appropriate

Example benchmark structure:
```javascript
benchmarkSuite.register('new_coherence_benchmark', async (context) => {
  // Setup test conditions
  const parameters = [/* ... */];
  const param = parameters[context.iteration % parameters.length];
  
  // Create coherence manager
  const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
  
  // Measure performance
  const startTime = performance.now();
  const result = coherenceManager.someOperation(param);
  const endTime = performance.now();
  
  return {
    parameter: param,
    result: result,
    executionTime: endTime - startTime
  };
}, {
  type: Prime.Distributed.Benchmark.BenchmarkType.COMPUTATION,
  description: 'Benchmark description',
  tags: ['coherence', 'new-feature']
});
```

## Extending the Mock Network Simulation

The mock network simulation provides an end-to-end test environment for coherence checking. To extend it:

1. Modify `distributed-coherence-mock-network.js`
2. Add new network configurations in the `NETWORK_CONFIG` object
3. Implement additional simulation scenarios
4. Add more detailed coherence monitoring and reporting

## Mathematical Foundations

Coherence checks should be mathematically rigorous. When implementing new checks, consider:

1. **Numerical Stability** - Handle edge cases like NaN, Infinity, and subnormal numbers
2. **Tensor Structure** - Verify dimensional consistency and structural integrity
3. **Gradient Properties** - Check for desirable gradient properties (bounded magnitude, etc.)
4. **Synchronization Metrics** - Use appropriate distance metrics for parameter synchronization
5. **Recovery Mechanisms** - Ensure corrections maintain mathematical properties

## Pull Request Guidelines

When submitting pull requests for coherence-related changes:

1. Include comprehensive tests for new functionality
2. Include benchmark results for performance-sensitive changes
3. Document mathematical justification for coherence checks
4. Explain correction strategies and their mathematical basis
5. Ensure all existing tests and benchmarks continue to pass

## Documentation Guidelines

Documentation for coherence functionality should include:

1. Mathematical description of coherence checks
2. Examples of coherence violations and correction
3. Performance characteristics at different scales
4. Integration guidance for new neural network components
5. References to relevant mathematical papers or resources

## Additional Resources

- [primeos-spec.md](./primeos-spec.md) - Full PrimeOS specification
- [mathematics.js](./src/mathematics.js) - Mathematical foundations
- [coherence.js](./src/coherence.js) - Core coherence implementation
- [Distributed Module Tests](./tests/distributed-tests.js) - Distributed system tests