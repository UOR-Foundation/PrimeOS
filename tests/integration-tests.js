/**
 * PrimeOS JavaScript Library - Integration Tests
 * Tests for validating integration between different PrimeOS modules
 * Version 1.0.0
 */

// Import Prime library with all modules
import { Prime } from '../src/components-2.js';

/**
 * Test runner with detailed reporting
 */
const TestRunner = {
  tests: [],
  results: {
    passed: 0,
    failed: 0,
    skipped: 0,
    total: 0,
    failures: []
  },

  /**
   * Register a test
   * @param {string} name - Test name
   * @param {Function} fn - Test function
   * @param {boolean} [skip=false] - Whether to skip this test
   */
  test: function(name, fn, skip = false) {
    this.tests.push({ name, fn, skip });
  },

  /**
   * Run all registered tests
   * @returns {Object} Test results
   */
  run: async function() {
    this.results = {
      passed: 0,
      failed: 0,
      skipped: 0,
      total: this.tests.length,
      failures: []
    };

    console.log(`Running ${this.tests.length} tests...\n`);

    for (const test of this.tests) {
      if (test.skip) {
        console.log(`⚪ SKIPPED: ${test.name}`);
        this.results.skipped++;
        continue;
      }

      try {
        await test.fn();
        console.log(`✅ PASSED: ${test.name}`);
        this.results.passed++;
      } catch (error) {
        console.error(`❌ FAILED: ${test.name}`);
        console.error(`   Error: ${error.message}`);
        
        if (error.stack) {
          const stackLines = error.stack.split('\n').slice(1, 3);
          console.error(`   Stack: ${stackLines.join('\n          ')}`);
        }
        
        this.results.failed++;
        this.results.failures.push({
          name: test.name,
          error
        });
      }
    }

    const summary = `
Test Summary:
-------------
Total:   ${this.results.total}
Passed:  ${this.results.passed}
Failed:  ${this.results.failed}
Skipped: ${this.results.skipped}
`;

    console.log(summary);

    if (this.results.failures.length > 0) {
      console.log('Failed Tests:');
      for (const failure of this.results.failures) {
        console.log(`- ${failure.name}: ${failure.error.message}`);
      }
    }

    return this.results;
  },

  /**
   * Assert that a condition is true
   * @param {boolean} condition - Condition to check
   * @param {string} message - Error message if condition is false
   */
  assert: function(condition, message) {
    if (!condition) {
      throw new Error(message || 'Assertion failed');
    }
  },

  /**
   * Assert that two values are deeply equal
   * @param {*} actual - Actual value
   * @param {*} expected - Expected value
   * @param {string} message - Error message if values are not equal
   */
  assertEqual: function(actual, expected, message) {
    // Convert to JSON for deep comparison
    const actualStr = JSON.stringify(actual);
    const expectedStr = JSON.stringify(expected);

    if (actualStr !== expectedStr) {
      throw new Error(message || `Expected ${expectedStr}, but got ${actualStr}`);
    }
  }
};

/**
 * Test that Prime object exists with core modules
 */
TestRunner.test('Prime core exists', () => {
  TestRunner.assert(Prime !== undefined, 'Prime object should exist');
  TestRunner.assert(typeof Prime.version === 'string', 'Prime version should exist');
  TestRunner.assert(Prime.Utils !== undefined, 'Prime.Utils should exist');
  TestRunner.assert(Prime.EventBus !== undefined, 'Prime.EventBus should exist');
});

/**
 * Test integration between component model and coherence system
 */
TestRunner.test('Component integration with coherence', () => {
  // Skip if coherence system is not available
  if (!Prime.coherence) {
    console.log('Skipping coherence test - Prime.coherence not available');
    return;
  }

  // Create a component with coherence constraints
  const component = Prime.createComponent({
    meta: {
      name: 'TestComponent'
    },
    invariant: {
      constraints: [
        Prime.coherence.createConstraint(
          state => state.count >= 0,
          { name: 'NonNegativeCount', weight: 2 }
        )
      ]
    },
    variant: {
      count: 10
    }
  });

  // Test component is coherent
  const coherenceNorm = component.coherenceNorm();
  TestRunner.assert(
    coherenceNorm === 0,
    `Component should be coherent, got norm ${coherenceNorm}`
  );

  // Test component can be updated maintaining coherence
  component.setState({ count: 20 });
  TestRunner.assertEqual(component.variant.count, 20, 'Component count should be updated');

  // Test component throws on coherence violation
  let errorThrown = false;
  try {
    component.setState({ count: -10 });
  } catch (error) {
    errorThrown = true;
    TestRunner.assert(
      error instanceof Prime.CoherenceViolationError,
      'Should throw CoherenceViolationError'
    );
  }

  TestRunner.assert(errorThrown, 'Should throw error for coherence violation');
  TestRunner.assertEqual(component.variant.count, 20, 'Component count should remain unchanged');
});

/**
 * Test integration between component model and component registry
 */
TestRunner.test('Component integration with registry', () => {
  // Create a component
  const component = Prime.createComponent({
    meta: {
      name: 'RegistryTest',
      id: 'registry-test-1'
    },
    variant: {
      value: 42
    }
  });

  // Register component
  Prime.ComponentRegistry.register(component);

  // Test component can be retrieved
  const retrieved = Prime.ComponentRegistry.get('registry-test-1');
  TestRunner.assert(retrieved === component, 'Retrieved component should be the same instance');
  TestRunner.assertEqual(retrieved.variant.value, 42, 'Retrieved component should have correct state');

  // Update component and test registry has updated instance
  component.setState({ value: 84 });
  const updated = Prime.ComponentRegistry.get('registry-test-1');
  TestRunner.assertEqual(updated.variant.value, 84, 'Registry should have updated instance');

  // Unregister component
  const unregistered = Prime.ComponentRegistry.unregister(component);
  TestRunner.assert(unregistered, 'Component should be unregistered successfully');
  TestRunner.assert(
    Prime.ComponentRegistry.get('registry-test-1') === undefined,
    'Component should no longer be in registry'
  );
});

/**
 * Test integration between component factory and templates
 */
TestRunner.test('Component factory integration', () => {
  // Create a template
  const template = new Prime.ComponentTemplate({
    meta: {
      type: 'counter'
    },
    invariant: {
      increment: function() {
        this.setState({ count: this.variant.count + 1 });
      },
      decrement: function() {
        this.setState({ count: this.variant.count - 1 });
      }
    },
    variant: {
      count: 0
    }
  });

  // Register as a component type
  template.registerType('counter');

  // Test type is registered
  TestRunner.assert(
    Prime.ComponentFactory.hasType('counter'),
    'Counter type should be registered'
  );

  // Create a component using the factory
  const counter = Prime.ComponentFactory.create('counter', {
    meta: {
      name: 'MyCounter'
    }
  });

  // Test component was created correctly
  TestRunner.assert(counter.meta.type === 'counter', 'Component should have correct type');
  TestRunner.assert(counter.meta.name === 'MyCounter', 'Component should have custom name');
  TestRunner.assertEqual(counter.variant.count, 0, 'Component should have initial count');
  TestRunner.assert(typeof counter.invocable.increment === 'function', 'Component should have increment method');

  // Test component behavior
  counter.invocable.increment();
  TestRunner.assertEqual(counter.variant.count, 1, 'Counter should increment');
  counter.invocable.decrement();
  TestRunner.assertEqual(counter.variant.count, 0, 'Counter should decrement');

  // Unregister type
  Prime.ComponentFactory.unregister('counter');
  TestRunner.assert(
    !Prime.ComponentFactory.hasType('counter'),
    'Counter type should no longer be registered'
  );
});

/**
 * Test component lifecycle integration
 */
TestRunner.test('Component lifecycle integration', () => {
  // Create a mock parent for mounting
  const parent = {
    _children: []
  };

  // Create a component with lifecycle hooks
  const lifecycleEvents = [];
  const component = Prime.createComponent({
    meta: {
      name: 'LifecycleTest'
    },
    invariant: {
      initialize: function() {
        lifecycleEvents.push('initialize');
      },
      mount: function(parent) {
        lifecycleEvents.push('mount');
      },
      update: function(newState, prevState) {
        lifecycleEvents.push('update');
      },
      unmount: function() {
        lifecycleEvents.push('unmount');
      }
    },
    variant: {
      value: 'initial'
    }
  });

  // Initialize component
  component.lifecycle.initialize();
  TestRunner.assert(component.meta.initialized, 'Component should be marked as initialized');
  TestRunner.assert(lifecycleEvents.includes('initialize'), 'Initialize event should be triggered');

  // Mount component
  component.lifecycle.mount(parent);
  TestRunner.assert(component.meta.mounted, 'Component should be marked as mounted');
  TestRunner.assert(lifecycleEvents.includes('mount'), 'Mount event should be triggered');
  TestRunner.assert(component._parent === parent, 'Component should reference parent');
  TestRunner.assert(parent._children.includes(component), 'Parent should reference component');

  // Update component
  component.lifecycle.update({ value: 'updated' });
  TestRunner.assertEqual(component.variant.value, 'updated', 'Component value should be updated');
  TestRunner.assert(lifecycleEvents.includes('update'), 'Update event should be triggered');

  // Unmount component
  component.lifecycle.unmount();
  TestRunner.assert(!component.meta.mounted, 'Component should not be marked as mounted');
  TestRunner.assert(lifecycleEvents.includes('unmount'), 'Unmount event should be triggered');
  TestRunner.assert(component._parent === null, 'Component should not reference parent');
  TestRunner.assert(!parent._children.includes(component), 'Parent should not reference component');
});

/**
 * Test rendering system integration with components
 */
TestRunner.test('Rendering integration with components', () => {
  // Skip if render system is not available
  if (!Prime.render) {
    console.log('Skipping render test - Prime.render not available');
    return;
  }

  // Create a component with render method
  const component = Prime.createComponent({
    meta: {
      name: 'RenderTest'
    },
    invariant: {
      render: function(element, options) {
        // Mock DOM rendering
        element.innerHTML = `<div>Count: ${this.variant.count}</div>`;
        return element;
      },
      renderCanvas: function(ctx, options) {
        // Mock canvas rendering
        ctx.fillText(`Count: ${this.variant.count}`, 10, 20);
        return ctx;
      }
    },
    variant: {
      count: 42
    }
  });

  // Test DOM rendering
  const mockElement = { innerHTML: '' };
  Prime.render.toDOM(component, mockElement);
  TestRunner.assertEqual(
    mockElement.innerHTML,
    '<div>Count: 42</div>',
    'DOM should render component correctly'
  );

  // Test Canvas rendering (with mock context)
  let canvasText = '';
  const mockContext = {
    fillText: (text, x, y) => { canvasText = text; }
  };
  Prime.render.toCanvas(component, mockContext);
  TestRunner.assertEqual(
    canvasText,
    'Count: 42',
    'Canvas should render component correctly'
  );
});

/**
 * Test performance module integration
 */
TestRunner.test('Performance module integration', async () => {
  // Skip if performance module is not available
  if (!Prime.performance) {
    console.log('Skipping performance test - Prime.performance not available');
    return;
  }

  // Configure performance options
  Prime.performance.configure({
    memoizationLimit: 500,
    logPerformance: false
  });

  // Create a function to optimize
  const slowSum = (n) => {
    let sum = 0;
    for (let i = 1; i <= n; i++) {
      sum += i;
    }
    return sum;
  };

  // Optimize the function
  const fastSum = Prime.performance.optimize(slowSum, {
    memoize: true,
    validateInput: (n) => typeof n === 'number' && n >= 0
  });

  // Test function works correctly
  TestRunner.assertEqual(fastSum(100), 5050, 'Optimized function should work correctly');
  
  // Test function is memoized
  const result1 = fastSum(1000); // First call (slow)
  const start = performance.now ? performance.now() : Date.now();
  const result2 = fastSum(1000); // Second call (should be instant)
  const end = performance.now ? performance.now() : Date.now();
  
  TestRunner.assert(end - start < 5, 'Memoized function should execute quickly');
  TestRunner.assertEqual(result1, result2, 'Results should be identical');

  // Test function validates input
  let errorThrown = false;
  try {
    fastSum('not a number');
  } catch (error) {
    errorThrown = true;
    TestRunner.assert(
      error instanceof Prime.ValidationError,
      'Should throw ValidationError'
    );
  }
  TestRunner.assert(errorThrown, 'Should throw error for invalid input');

  // Test benchmark
  const benchmark = await Prime.performance.benchmark(
    () => fastSum(500),
    { iterations: 10, warmup: 2 }
  );

  TestRunner.assert(typeof benchmark.mean === 'number', 'Benchmark should report mean time');
  TestRunner.assert(benchmark.iterations === 10, 'Benchmark should run requested iterations');
});

/**
 * Test analytical tools integration
 */
TestRunner.test('Analytical tools integration', () => {
  // Skip if analytical module is not available
  if (!Prime.analytic) {
    console.log('Skipping analytic test - Prime.analytic not available');
    return;
  }

  // Test prime counting function
  const primeCount = Prime.analytic.primeCountingFunction(20);
  TestRunner.assertEqual(primeCount, 8, 'Prime counting function should work correctly');

  // Test prime detection
  TestRunner.assert(Prime.analytic.isPrime(17), '17 should be identified as prime');
  TestRunner.assert(!Prime.analytic.isPrime(16), '16 should not be identified as prime');

  // Test totient function
  const totient = Prime.analytic.totientFunction(12);
  TestRunner.assertEqual(totient, 4, 'Totient function should work correctly for 12');
});

/**
 * Test documentation generator integration
 */
TestRunner.test('Documentation generator integration', () => {
  // Skip if documentation generator is not available
  if (!Prime.generateDocumentation) {
    console.log('Skipping documentation test - Prime.generateDocumentation not available');
    return;
  }

  // Generate documentation in different formats
  const markdown = Prime.generateDocumentation({ format: 'markdown' });
  TestRunner.assert(typeof markdown === 'string', 'Markdown documentation should be generated');
  TestRunner.assert(markdown.startsWith('# PrimeOS JavaScript Library Documentation'), 'Markdown should have correct title');

  const html = Prime.generateDocumentation({ format: 'html' });
  TestRunner.assert(typeof html === 'string', 'HTML documentation should be generated');
  TestRunner.assert(html.includes('<!DOCTYPE html>'), 'HTML should have correct structure');

  const json = Prime.generateDocumentation({ format: 'json' });
  TestRunner.assert(typeof json === 'object', 'JSON documentation should be generated');
  TestRunner.assert(json.name === 'PrimeOS JavaScript Library', 'JSON should have correct name');
  TestRunner.assert(Array.isArray(json.modules), 'JSON should have modules array');
});

/**
 * Test framework integration with Prime components
 */
TestRunner.test('Framework integration', () => {
  // Skip if framework modules are not available
  if (!Prime.Base0 || !Prime.Base1 || !Prime.Base2 || !Prime.Base3) {
    console.log('Skipping framework test - Prime.Base0-3 not all available');
    return;
  }

  // Create framework instance
  const framework = Prime.createPrimeFramework();
  
  TestRunner.assert(framework.base0 !== undefined, 'Framework should have base0');
  TestRunner.assert(framework.base1 !== undefined, 'Framework should have base1');
  TestRunner.assert(framework.base2 !== undefined, 'Framework should have base2');
  TestRunner.assert(framework.base3 !== undefined, 'Framework should have base3');

  // Test application creation
  const app = framework.createApplication({
    name: 'TestApp',
    behavior: {
      actions: {
        increment: (state) => ({ count: state.count + 1 }),
        decrement: (state) => ({ count: state.count - 1 })
      },
      initialState: {
        count: 0
      }
    },
    structure: {
      components: [
        {
          type: 'div',
          props: { id: 'counter' },
          children: [
            {
              type: 'span',
              props: { innerText: (state) => `Count: ${state.count}` }
            }
          ]
        }
      ]
    }
  });

  TestRunner.assert(app.name === 'TestApp', 'App should have correct name');
  TestRunner.assert(app.behavior.state.count === 0, 'App should have initial state');
  
  // Test app behavior
  app.behavior.dispatch('increment');
  TestRunner.assertEqual(app.behavior.state.count, 1, 'App state should update');
});

// Run all tests
TestRunner.run().then(results => {
  // Allow visualization of complete test run
  console.log('\nTest run complete.');
  
  // Exit with proper code if in Node.js environment
  if (typeof process !== 'undefined' && process.exit) {
    process.exit(results.failed > 0 ? 1 : 0);
  }
}).catch(error => {
  console.error('Error running tests:', error);
  
  // Exit with error code if in Node.js environment
  if (typeof process !== 'undefined' && process.exit) {
    process.exit(1);
  }
});
