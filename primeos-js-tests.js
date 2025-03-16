/**
 * PrimeOS JavaScript Library Tests
 * 
 * A comprehensive test suite for validating the Prime JavaScript Library
 */

// Simple test framework
const TestRunner = (function() {
  const suites = {};
  let currentSuite = null;
  let passed = 0;
  let failed = 0;
  let skipped = 0;
  
  function describe(name, fn) {
    currentSuite = name;
    suites[name] = { tests: [], beforeEach: null, afterEach: null };
    fn();
    currentSuite = null;
  }
  
  function it(name, fn) {
    if (!currentSuite) throw new Error('Test must be within a suite');
    suites[currentSuite].tests.push({ name, fn, skip: false });
  }
  
  function xit(name, fn) {
    if (!currentSuite) throw new Error('Test must be within a suite');
    suites[currentSuite].tests.push({ name, fn, skip: true });
  }
  
  function beforeEach(fn) {
    if (!currentSuite) throw new Error('beforeEach must be within a suite');
    suites[currentSuite].beforeEach = fn;
  }
  
  function afterEach(fn) {
    if (!currentSuite) throw new Error('afterEach must be within a suite');
    suites[currentSuite].afterEach = fn;
  }
  
  function assert(condition, message) {
    if (!condition) {
      throw new Error(message || 'Assertion failed');
    }
  }
  
  function assertDeepEqual(actual, expected, message) {
    const actualStr = JSON.stringify(actual);
    const expectedStr = JSON.stringify(expected);
    if (actualStr !== expectedStr) {
      throw new Error(message || `Expected ${expectedStr} but got ${actualStr}`);
    }
  }
  
  function assertAlmostEqual(actual, expected, epsilon = 1e-6, message) {
    if (Math.abs(actual - expected) > epsilon) {
      throw new Error(message || `Expected ${expected} but got ${actual}`);
    }
  }
  
  function assertThrows(fn, errorType, message) {
    try {
      fn();
      throw new Error(message || 'Expected function to throw');
    } catch (e) {
      if (errorType && !(e instanceof errorType)) {
        throw new Error(message || `Expected error of type ${errorType.name} but got ${e.constructor.name}`);
      }
    }
  }
  
  async function runTests() {
    console.log('Running tests...');
    
    for (const suiteName in suites) {
      console.log(`\nSuite: ${suiteName}`);
      const suite = suites[suiteName];
      
      for (const test of suite.tests) {
        if (test.skip) {
          console.log(`  - [SKIP] ${test.name}`);
          skipped++;
          continue;
        }
        
        try {
          if (suite.beforeEach) await suite.beforeEach();
          await test.fn();
          if (suite.afterEach) await suite.afterEach();
          
          console.log(`  - [PASS] ${test.name}`);
          passed++;
        } catch (e) {
          console.error(`  - [FAIL] ${test.name}`);
          console.error(`    ${e.message}`);
          if (e.stack) console.error(`    ${e.stack.split('\n')[1]}`);
          failed++;
        }
      }
    }
    
    console.log(`\nTest results: ${passed} passed, ${failed} failed, ${skipped} skipped`);
    
    return { passed, failed, skipped };
  }
  
  return {
    describe,
    it,
    xit,
    beforeEach,
    afterEach,
    assert,
    assertDeepEqual,
    assertAlmostEqual,
    assertThrows,
    runTests
  };
})();

// Extract test methods for easier access
const { 
  describe, 
  it, 
  xit, 
  beforeEach, 
  afterEach, 
  assert, 
  assertDeepEqual, 
  assertAlmostEqual, 
  assertThrows 
} = TestRunner;

/**
 * Tests for the Mathematical Core
 */

describe('Clifford Algebra', () => {
  let Cl;
  
  beforeEach(() => {
    // Create a 3D Clifford algebra with Euclidean signature
    Cl = Prime.Clifford.create({ dimension: 3, signature: [1, 1, 1] });
  });
  
  it('should create scalar elements correctly', () => {
    const scalar = Cl.scalar(5);
    assert(scalar.components[0]?.["1"] === 5, "Scalar value should be 5");
  });
  
  it('should create vector elements correctly', () => {
    const vector = Cl.vector([1, 2, 3]);
    assert(vector.components[1]?.["e1"] === 1, "X component should be 1");
    assert(vector.components[1]?.["e2"] === 2, "Y component should be 2");
    assert(vector.components[1]?.["e3"] === 3, "Z component should be 3");
  });
  
  it('should convert vector to array correctly', () => {
    const vector = Cl.vector([1, 2, 3]);
    const arr = vector.toArray();
    assertDeepEqual(arr, [1, 2, 3], "Vector to array conversion failed");
  });
  
  it('should add multivectors correctly', () => {
    const v1 = Cl.vector([1, 2, 3]);
    const v2 = Cl.vector([4, 5, 6]);
    const sum = v1.add(v2);
    
    assert(sum.components[1]?.["e1"] === 5, "Sum X component should be 5");
    assert(sum.components[1]?.["e2"] === 7, "Sum Y component should be 7");
    assert(sum.components[1]?.["e3"] === 9, "Sum Z component should be 9");
  });
  
  it('should compute the geometric product correctly', () => {
    const v1 = Cl.vector([1, 0, 0]); // e1
    const v2 = Cl.vector([0, 1, 0]); // e2
    const product = v1.multiply(v2);
    
    // e1*e2 should be a bivector e12
    assert(product.components[2]?.["e1e2"] === 1, "Product should be bivector e12");
  });
  
  it('should compute the square of a vector correctly', () => {
    const v = Cl.vector([1, 2, 3]);
    const squared = v.multiply(v);
    
    // With Euclidean signature, v² = |v|² = 1² + 2² + 3² = 14
    assert(squared.components[0]?.["1"] === 14, "Square should be scalar 14");
  });
  
  it('should compute the reverse correctly', () => {
    const bivector = Cl.bivector([[0, 1], [0, 0], [0, 0]]); // e1e2
    const reversed = bivector.reverse();
    
    // Reverse of e1e2 should be -e1e2
    assert(reversed.components[2]?.["e1e2"] === -1, "Reverse of e1e2 should be -e1e2");
  });
  
  it('should calculate the norm correctly', () => {
    const v = Cl.vector([3, 4, 0]);
    const norm = v.norm();
    
    // |v| = √(3² + 4²) = 5
    assert(norm === 5, "Norm should be 5");
  });
});

describe('Coherence', () => {
  it('should calculate inner product between multivectors', () => {
    const Cl = Prime.Clifford.create({ dimension: 2, signature: [1, 1] });
    const v1 = Cl.vector([1, 0]);
    const v2 = Cl.vector([0, 1]);
    
    const innerProduct = Prime.coherence.innerProduct(v1, v2);
    
    // Vectors are orthogonal, so inner product should be 0
    assert(innerProduct.components[0]?.["1"] === 0, "Inner product should be 0");
  });
  
  it('should calculate norm of an array', () => {
    const arr = [3, 4];
    const norm = Prime.coherence.norm(arr);
    
    // |[3, 4]| = 5
    assert(norm === 5, "Norm should be 5");
  });
  
  it('should verify coherence of an object', () => {
    const coherentObj = { x: 3, y: 4 };
    coherentObj.coherenceNorm = () => 0;
    
    const result = Prime.coherence.isCoherent(coherentObj);
    assert(result === true, "Object should be coherent");
  });
  
  it('should create and validate coherence constraints', () => {
    const constraint = Prime.coherence.createConstraint(
      state => state.count >= 0,
      "Non-negative count"
    );
    
    assert(constraint.check({ count: 5 }) === true, "Constraint should pass for positive count");
    assert(constraint.check({ count: -1 }) === false, "Constraint should fail for negative count");
    assert(constraint.weight === 1, "Default weight should be 1");
  });
  
  it('should create coherence-constrained state', () => {
    const state = Prime.coherence.createState(
      { count: 0 },
      [
        Prime.coherence.createConstraint(state => state.count >= 0)
      ]
    );
    
    // Valid update
    state.update({ count: 5 });
    assert(state.value.count === 5, "State should update with valid value");
    
    // Invalid update should throw
    assertThrows(
      () => state.update({ count: -1 }), 
      Prime.CoherenceViolationError,
      "Should throw CoherenceViolationError for invalid update"
    );
  });
});

describe('Lie Groups', () => {
  it('should create SO(3) rotation group', () => {
    const so3 = Prime.Lie.SO(3);
    assert(so3.name === "SO(3)", "Group name should be SO(3)");
    assert(so3.dimension === 3, "Dimension should be 3");
    assert(so3.generators.length === 3, "SO(3) should have 3 generators");
  });
  
  it('should create rotation transformations', () => {
    const so3 = Prime.Lie.SO(3);
    const rotation = so3.rotation([0, 0, 1], Math.PI/2); // 90° around z-axis
    
    assert(rotation.params.type === 'rotation', "Transformation type should be rotation");
    assert(rotation.params.angle === Math.PI/2, "Angle should be PI/2");
  });
  
  it('should apply rotation to a vector', () => {
    const so3 = Prime.Lie.SO(3);
    const rotation = so3.rotation([0, 0, 1], Math.PI/2); // 90° around z-axis
    
    const vector = [1, 0, 0]; // Unit vector along x-axis
    const rotated = rotation.apply(vector);
    
    // After 90° rotation around z, [1,0,0] should become approximately [0,1,0]
    assertAlmostEqual(rotated[0], 0, 1e-6, "X component should be 0");
    assertAlmostEqual(rotated[1], 1, 1e-6, "Y component should be 1");
    assertAlmostEqual(rotated[2], 0, 1e-6, "Z component should be 0");
  });
  
  it('should compose transformations via multiplication', () => {
    const so3 = Prime.Lie.SO(3);
    const rotation1 = so3.rotation([0, 0, 1], Math.PI/4); // 45° around z
    const rotation2 = so3.rotation([0, 0, 1], Math.PI/4); // Another 45° around z
    
    const combined = rotation1.multiply(rotation2);
    const vector = [1, 0, 0];
    const rotated = combined.apply(vector);
    
    // After 90° rotation around z, [1,0,0] should become approximately [0,1,0]
    assertAlmostEqual(rotated[0], 0, 1e-6, "X component should be 0");
    assertAlmostEqual(rotated[1], 1, 1e-6, "Y component should be 1");
    assertAlmostEqual(rotated[2], 0, 1e-6, "Z component should be 0");
  });
});

describe('Universal Object Reference (UOR)', () => {
  it('should create reference points', () => {
    const Cl = Prime.Clifford.create({ dimension: 3, signature: [1, 1, 1] });
    const reference = Prime.UOR.createReference({
      manifold: 'testSpace',
      point: [0, 0, 0],
      fiber: Cl
    });
    
    assert(reference.manifold === 'testSpace', "Manifold should be 'testSpace'");
    assertDeepEqual(reference.point, [0, 0, 0], "Point should be origin");
    assert(reference.fiber === Cl, "Fiber should be the Clifford algebra");
  });
  
  it('should create objects at reference points', () => {
    const Cl = Prime.Clifford.create({ dimension: 3, signature: [1, 1, 1] });
    const reference = Prime.UOR.createReference({
      manifold: 'testSpace',
      point: [0, 0, 0],
      fiber: Cl
    });
    
    const vector = Cl.vector([1, 2, 3]);
    const object = reference.createObject(vector);
    
    assert(object.reference === reference, "Object should have the correct reference");
    assert(object.value === vector, "Object should have the correct value");
  });
  
  it('should transform objects', () => {
    const Cl = Prime.Clifford.create({ dimension: 3, signature: [1, 1, 1] });
    const reference = Prime.UOR.createReference({
      manifold: 'testSpace',
      point: [0, 0, 0],
      fiber: Cl
    });
    
    const vector = [1, 0, 0];
    const object = reference.createObject(vector);
    
    const so3 = Prime.Lie.SO(3);
    const rotation = so3.rotation([0, 0, 1], Math.PI/2);
    
    const transformed = object.transform(rotation);
    
    // After 90° rotation around z, [1,0,0] should become approximately [0,1,0]
    const result = transformed.value;
    assertAlmostEqual(result[0], 0, 1e-6, "X component should be 0");
    assertAlmostEqual(result[1], 1, 1e-6, "Y component should be 1");
    assertAlmostEqual(result[2], 0, 1e-6, "Z component should be 0");
  });
  
  it('should create fiber bundles', () => {
    const Cl = Prime.Clifford.create({ dimension: 3, signature: [1, 1, 1] });
    const so3 = Prime.Lie.SO(3);
    
    const bundle = Prime.UOR.createFiberBundle({
      baseManifold: 'testManifold',
      fiber: Cl,
      structure: so3
    });
    
    assert(bundle.baseManifold === 'testManifold', "Base manifold should be correct");
    assert(bundle.fiber === Cl, "Fiber should be the Clifford algebra");
    assert(bundle.structure === so3, "Structure group should be SO(3)");
  });
  
  it('should create sections of a fiber bundle', () => {
    const Cl = Prime.Clifford.create({ dimension: 3, signature: [1, 1, 1] });
    const so3 = Prime.Lie.SO(3);
    
    const bundle = Prime.UOR.createFiberBundle({
      baseManifold: 'testManifold',
      fiber: Cl,
      structure: so3
    });
    
    const section = bundle.createSection(point => {
      // Simple section that returns the point coordinates as a vector
      return point;
    });
    
    const testPoint = [1, 2, 3];
    const valueAtPoint = section.valueAt(testPoint);
    
    assert(valueAtPoint.value === testPoint, "Section should return correct value at point");
  });
});

/**
 * Tests for Prime Framework Architecture
 */

describe('Base 0: Neural Network Specification', () => {
  it('should create embedding model', () => {
    const embedding = Prime.Base0.createEmbeddingModel({
      dimensions: 128,
      metric: 'euclidean'
    });
    
    assert(embedding.dimensions === 128, "Dimensions should be 128");
    assert(embedding.metric === 'euclidean', "Metric should be euclidean");
    assert(typeof embedding.embed === 'function', "Should have embed function");
    assert(typeof embedding.distance === 'function', "Should have distance function");
  });
  
  it('should calculate distances in embedding space', () => {
    const embedding = Prime.Base0.createEmbeddingModel({
      dimensions: 3,
      metric: 'euclidean'
    });
    
    const a = [1, 0, 0];
    const b = [0, 1, 0];
    
    // Distance between [1,0,0] and [0,1,0] in Euclidean space is √2
    const distance = embedding.distance(a, b);
    assertAlmostEqual(distance, Math.sqrt(2), 1e-6, "Euclidean distance should be √2");
  });
  
  it('should create logic model', () => {
    const logic = Prime.Base0.createLogicModel({
      rules: [
        { name: 'example', apply: x => x }
      ],
      constraints: [
        { name: 'positive', check: x => x > 0 }
      ]
    });
    
    assert(Array.isArray(logic.rules), "Rules should be an array");
    assert(Array.isArray(logic.constraints), "Constraints should be an array");
    assert(typeof logic.apply === 'function', "Should have apply function");
    assert(typeof logic.validate === 'function', "Should have validate function");
  });
  
  it('should create representation model', () => {
    const representation = Prime.Base0.createRepresentationModel({
      transformations: [
        { name: 'identity', apply: x => x }
      ]
    });
    
    assert(Array.isArray(representation.transformations), "Transformations should be an array");
    assert(typeof representation.transform === 'function', "Should have transform function");
    assert(typeof representation.represent === 'function', "Should have represent function");
  });
  
  it('should create processor', () => {
    const processor = Prime.Base0.createProcessor({
      operations: [
        { name: 'identity', apply: x => x }
      ]
    });
    
    assert(Array.isArray(processor.operations), "Operations should be an array");
    assert(typeof processor.process === 'function', "Should have process function");
    assert(typeof processor.compose === 'function', "Should have compose function");
  });
});

describe('Base 1: Resource', () => {
  it('should create runtime model', () => {
    const embedding = Prime.Base0.createEmbeddingModel({});
    const logic = Prime.Base0.createLogicModel({});
    const representation = Prime.Base0.createRepresentationModel({});
    const processor = Prime.Base0.createProcessor({});
    
    const runtime = Prime.Base1.createRuntimeModel({
      embeddings: embedding,
      logic: logic,
      representation: representation,
      processor: processor
    });
    
    assert(runtime.type === 'runtime', "Type should be runtime");
    assert(runtime.embeddings === embedding, "Embeddings should be set");
    assert(runtime.logic === logic, "Logic should be set");
    assert(runtime.representation === representation, "Representation should be set");
    assert(runtime.processor === processor, "Processor should be set");
    
    assert(typeof runtime.start === 'function', "Should have start function");
    assert(typeof runtime.run === 'function', "Should have run function");
    assert(typeof runtime.stop === 'function', "Should have stop function");
  });
  
  it('should create observation model', () => {
    const observation = Prime.Base1.createObservationModel({
      sources: [{ name: 'test', getData: () => {} }],
      filters: [{ name: 'example', apply: x => x }]
    });
    
    assert(observation.type === 'observation', "Type should be observation");
    assert(Array.isArray(observation.sources), "Sources should be an array");
    assert(Array.isArray(observation.filters), "Filters should be an array");
    
    assert(typeof observation.resolve === 'function', "Should have resolve function");
    assert(typeof observation.fetch === 'function', "Should have fetch function");
    assert(typeof observation.observe === 'function', "Should have observe function");
  });
  
  it('should create interaction model', () => {
    const interaction = Prime.Base1.createInteractionModel({
      mutations: [{ name: 'update', apply: (obj, data) => ({ ...obj, ...data }) }],
      validators: [obj => typeof obj === 'object']
    });
    
    assert(interaction.type === 'interaction', "Type should be interaction");
    assert(Array.isArray(interaction.mutations), "Mutations should be an array");
    assert(Array.isArray(interaction.validators), "Validators should be an array");
    
    assert(typeof interaction.mutate === 'function', "Should have mutate function");
    assert(typeof interaction.save === 'function', "Should have save function");
    assert(typeof interaction.validate === 'function', "Should have validate function");
  });
  
  it('should create representation model', () => {
    const representation = Prime.Base1.createRepresentationModel({
      renderers: [
        { 
          name: 'text', 
          canRender: (obj, target) => typeof obj === 'string',
          render: (obj, target) => obj 
        }
      ]
    });
    
    assert(representation.type === 'representation', "Type should be representation");
    assert(Array.isArray(representation.renderers), "Renderers should be an array");
    
    assert(typeof representation.present === 'function', "Should have present function");
    assert(typeof representation.render === 'function', "Should have render function");
  });
});

describe('Base 2: Kernel', () => {
  it('should create resource client', () => {
    const runtime = Prime.Base1.createRuntimeModel({});
    const observation = Prime.Base1.createObservationModel({});
    const interaction = Prime.Base1.createInteractionModel({});
    const representation = Prime.Base1.createRepresentationModel({});
    
    const client = Prime.Base2.createResourceClient({
      runtime,
      observation,
      interaction,
      representation
    });
    
    assert(client.type === 'resourceClient', "Type should be resourceClient");
    assert(client.runtime === runtime, "Runtime should be set");
    assert(client.observation === observation, "Observation should be set");
    assert(client.interaction === interaction, "Interaction should be set");
    assert(client.representation === representation, "Representation should be set");
    
    assert(typeof client.getRuntime === 'function', "Should have getRuntime function");
    assert(typeof client.getObservation === 'function', "Should have getObservation function");
    assert(typeof client.getInteraction === 'function', "Should have getInteraction function");
    assert(typeof client.getRepresentation === 'function', "Should have getRepresentation function");
  });
  
  it('should create application manager', () => {
    const manager = Prime.Base2.createApplicationManager({
      bundles: [
        { id: 'test', name: 'Test Bundle' }
      ]
    });
    
    assert(manager.type === 'applicationManager', "Type should be applicationManager");
    assert(Array.isArray(manager.bundles), "Bundles should be an array");
    assert(manager.bundles.length === 1, "Should have one bundle");
    
    assert(typeof manager.loadBundle === 'function', "Should have loadBundle function");
    assert(typeof manager.unloadBundle === 'function', "Should have unloadBundle function");
    assert(typeof manager.getBundle === 'function', "Should have getBundle function");
  });
  
  it('should create system manager', () => {
    const manager = Prime.Base2.createSystemManager({
      security: { policy: 'restrictive' },
      memory: { limit: 1024 * 1024 }
    });
    
    assert(manager.type === 'systemManager', "Type should be systemManager");
    assert(typeof manager.security === 'object', "Security should be an object");
    assert(typeof manager.memory === 'object', "Memory should be an object");
    
    assert(typeof manager.allocateMemory === 'function', "Should have allocateMemory function");
    assert(typeof manager.freeMemory === 'function', "Should have freeMemory function");
    assert(typeof manager.checkPermission === 'function', "Should have checkPermission function");
  });
  
  it('should register and call syscalls', () => {
    // Register syscalls
    Prime.Base2.registerSyscalls([
      { 
        name: 'testCall', 
        handler: (arg) => arg * 2 
      }
    ]);
    
    // Call the syscall
    const result = Prime.Base2.syscall('testCall', 5);
    assert(result === 10, "Syscall should return the correct result");
    
    // Call a non-existent syscall
    assertThrows(
      () => Prime.Base2.syscall('nonExistent'), 
      Prime.InvalidOperationError,
      "Should throw for non-existent syscall"
    );
  });
});

describe('Base 3: Application', () => {
  let app;
  
  beforeEach(() => {
    app = Prime.Base3.createApplication({
      name: 'TestApp',
      
      behavior: {
        actions: {
          increment: (state) => ({ count: state.count + 1 }),
          decrement: (state) => ({ count: state.count - 1 }),
          setCount: (state, value) => ({ count: value })
        },
        initialState: {
          count: 0
        }
      },
      
      framework: {
        layout: 'flex',
        styling: {
          container: {
            padding: '20px'
          }
        },
        animations: {
          fadeIn: {
            duration: '0.5s'
          }
        }
      },
      
      structure: {
        components: [
          {
            type: 'div',
            props: { 
              id: 'container',
              className: 'container'
            },
            children: [
              {
                type: 'p',
                props: { id: 'counter' }
              }
            ]
          }
        ]
      }
    });
  });
  
  it('should create application with correct structure', () => {
    assert(app.name === 'TestApp', "Name should be TestApp");
    
    assert(typeof app.behavior === 'object', "Should have behavior model");
    assert(typeof app.behavior.actions === 'object', "Should have actions");
    assert(typeof app.behavior.state === 'object', "Should have state");
    
    assert(typeof app.framework === 'object', "Should have framework model");
    assert(app.framework.layout === 'flex', "Layout should be flex");
    assert(typeof app.framework.styling === 'object', "Should have styling");
    
    assert(typeof app.structure === 'object', "Should have structure model");
    assert(Array.isArray(app.structure.components), "Components should be an array");
  });
  
  it('should handle state management correctly', () => {
    // Initial state
    const initialState = app.behavior.getState();
    assert(initialState.count === 0, "Initial count should be 0");
    
    // Dispatch increment action
    app.behavior.dispatch('increment');
    assert(app.behavior.getState().count === 1, "Count should be 1 after increment");
    
    // Dispatch decrement action
    app.behavior.dispatch('decrement');
    assert(app.behavior.getState().count === 0, "Count should be 0 after decrement");
    
    // Dispatch action with payload
    app.behavior.dispatch('setCount', 10);
    assert(app.behavior.getState().count === 10, "Count should be 10 after setCount");
    
    // Reset state
    app.behavior.resetState();
    assert(app.behavior.getState().count === 0, "Count should be 0 after reset");
  });
  
  it('should find components by ID', () => {
    const container = app.structure.findComponent('container');
    const counter = app.structure.findComponent('counter');
    
    assert(container !== null, "Should find container component");
    assert(container.props.className === 'container', "Container should have correct class");
    
    assert(counter !== null, "Should find counter component");
    assert(counter.type === 'p', "Counter should be a paragraph");
  });
  
  it('should handle lifecycle methods', () => {
    // Mock container
    const container = { innerHTML: '' };
    
    // Mount app
    const mountResult = app.mount(container);
    assert(mountResult === true, "Mount should return true");
    assert(app._container === container, "Container should be set");
    
    // Start app
    const startResult = app.start();
    assert(startResult === true, "Start should return true");
    assert(app._isRunning === true, "App should be running");
    
    // Stop app
    const stopResult = app.stop();
    assert(stopResult === true, "Stop should return true");
    assert(app._isRunning === false, "App should not be running");
    
    // Unmount app
    const unmountResult = app.unmount();
    assert(unmountResult === true, "Unmount should return true");
    assert(app._container === null, "Container should be null");
  });
});

/**
 * Tests for Component Model
 */

describe('Component Model', () => {
  it('should create component with correct structure', () => {
    const component = Prime.createComponent({
      meta: {
        name: 'Counter',
        version: '1.0.0'
      },
      
      invariant: {
        increment: (count) => count + 1,
        decrement: (count) => count - 1
      },
      
      variant: {
        count: 0
      }
    });
    
    assert(typeof component.meta === 'object', "Should have meta object");
    assert(component.meta.name === 'Counter', "Name should be Counter");
    
    assert(typeof component.invariant === 'object', "Should have invariant object");
    assert(typeof component.invariant.increment === 'function', "Should have increment function");
    
    assert(typeof component.variant === 'object', "Should have variant object");
    assert(component.variant.count === 0, "Count should be 0");
    
    assert(typeof component.invocable === 'object', "Should have invocable object");
    assert(typeof component.invocable.increment === 'function', "Invocable should have increment function");
    
    assert(typeof component.lifecycle === 'object', "Should have lifecycle object");
    assert(typeof component.lifecycle.initialize === 'function', "Should have initialize function");
    assert(typeof component.lifecycle.mount === 'function', "Should have mount function");
    assert(typeof component.lifecycle.update === 'function', "Should have update function");
    assert(typeof component.lifecycle.unmount === 'function', "Should have unmount function");
  });
  
  it('should call invariant methods via invocable interface', () => {
    const component = Prime.createComponent({
      invariant: {
        add: (a, b) => a + b,
        multiply: (a, b) => a * b
      },
      variant: {}
    });
    
    const sumResult = component.invocable.add(2, 3);
    assert(sumResult === 5, "Add should return 5");
    
    const productResult = component.invocable.multiply(2, 3);
    assert(productResult === 6, "Multiply should return 6");
  });
  
  it('should update variant state', () => {
    const component = Prime.createComponent({
      invariant: {},
      variant: {
        count: 0,
        name: 'Test'
      }
    });
    
    // Update the state
    component.lifecycle.update({ count: 5 });
    
    assert(component.variant.count === 5, "Count should be updated to 5");
    assert(component.variant.name === 'Test', "Name should remain unchanged");
    
    // Update multiple properties
    component.lifecycle.update({ count: 10, name: 'Updated' });
    
    assert(component.variant.count === 10, "Count should be updated to 10");
    assert(component.variant.name === 'Updated', "Name should be updated to 'Updated'");
  });
});

/**
 * Tests for Advanced Mathematical Features
 */

describe('Spectral Analysis', () => {
  it('should decompose a multivector', () => {
    const Cl = Prime.Clifford.create({ dimension: 2, signature: [1, 1] });
    const vector = Cl.vector([3, 4]);
    
    const spectrum = Prime.spectral.decompose(vector);
    
    assert(Array.isArray(spectrum.eigenvalues), "Eigenvalues should be an array");
    assert(Array.isArray(spectrum.eigenvectors), "Eigenvectors should be an array");
  });
  
  it('should filter a spectrum', () => {
    const Cl = Prime.Clifford.create({ dimension: 2, signature: [1, 1] });
    const vector = Cl.vector([3, 4]);
    
    const spectrum = Prime.spectral.decompose(vector);
    const filtered = Prime.spectral.filter(vector, (eigenvalue) => eigenvalue > 0);
    
    assert(Array.isArray(filtered.eigenvalues), "Filtered eigenvalues should be an array");
    assert(Array.isArray(filtered.eigenvectors), "Filtered eigenvectors should be an array");
  });
});

describe('Analytic Functions', () => {
  it('should calculate prime counting function', () => {
    const count10 = Prime.analytic.primeCountingFunction(10);
    assert(count10 === 4, "π(10) should be 4 (2, 3, 5, 7)");
    
    const count20 = Prime.analytic.primeCountingFunction(20);
    assert(count20 === 8, "π(20) should be 8 (2, 3, 5, 7, 11, 13, 17, 19)");
  });
  
  it('should estimate nth prime', () => {
    const p10 = Prime.analytic.nthPrimeEstimate(10);
    assert(p10 > 20 && p10 < 40, "10th prime estimate should be roughly 29");
    
    const p100 = Prime.analytic.nthPrimeEstimate(100);
    assert(p100 > 500 && p100 < 600, "100th prime estimate should be roughly 541");
  });
  
  it('should calculate logarithmic integral', () => {
    const li10 = Prime.analytic.logarithmicIntegral(10);
    assert(li10 > 5 && li10 < 7, "Li(10) should be approximately 6");
  });
  
  it('should calculate zeta function', () => {
    const zeta2 = Prime.analytic.zetaFunction(2);
    assertAlmostEqual(zeta2, Math.PI * Math.PI / 6, 0.1, "ζ(2) should be approximately π²/6");
  });
});

/**
 * Tests for Interoperability
 */

describe('Rendering', () => {
  // These tests would require a DOM environment
  // We'll create simplified versions that mainly check API existence
  
  it('should have toDOM rendering function', () => {
    assert(typeof Prime.render.toDOM === 'function', "Should have toDOM function");
  });
  
  it('should have toCanvas rendering function', () => {
    assert(typeof Prime.render.toCanvas === 'function', "Should have toCanvas function");
  });
  
  it('should have toWebGL rendering function', () => {
    assert(typeof Prime.render.toWebGL === 'function', "Should have toWebGL function");
  });
});

/**
 * Tests for Performance & Versioning
 */

describe('Performance', () => {
  it('should configure performance settings', () => {
    // Default settings
    assert(typeof Prime.performance.config === 'object', "Should have config object");
    
    // Update settings
    Prime.performance.configure({
      useWebAssembly: true,
      precision: 'single'
    });
    
    assert(Prime.performance.config.useWebAssembly === true, "useWebAssembly should be true");
    assert(Prime.performance.config.precision === 'single', "precision should be single");
  });
  
  it('should have benchmark function', () => {
    assert(typeof Prime.performance.benchmark === 'function', "Should have benchmark function");
  });
});

describe('Versioning', () => {
  it('should have version property', () => {
    assert(typeof Prime.version === 'string', "Should have version string");
    assert(/^\d+\.\d+\.\d+$/.test(Prime.version), "Version should be in semver format");
  });
  
  it('should check compatibility', () => {
    const compatible = Prime.isCompatible({
      features: ['coherence', 'spectral'],
      minVersion: '0.1.0'
    });
    
    assert(typeof compatible === 'boolean', "Should return boolean compatibility result");
  });
  
  it('should retrieve deprecation warnings', () => {
    const warnings = Prime.getDeprecationWarnings();
    assert(Array.isArray(warnings), "Should return array of warnings");
  });
});

// Run all tests
if (typeof window !== 'undefined') {
  // In browser environment
  window.addEventListener('load', () => {
    TestRunner.runTests().then(results => {
      console.log('Tests completed in browser environment');
    });
  });
} else if (typeof module !== 'undefined' && module.exports) {
  // In Node.js environment
  TestRunner.runTests().then(results => {
    console.log('Tests completed in Node.js environment');
    process.exit(results.failed > 0 ? 1 : 0);
  });
}

// Export the test runner for external use
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { TestRunner };
}
