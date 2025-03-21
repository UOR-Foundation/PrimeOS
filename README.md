# PrimeOS JavaScript Library

A neural network-based operating system built on the Prime Framework, representing a fundamental shift in computing paradigms. Rather than traditional procedural execution, PrimeOS treats computation as a neural network process governed by mathematical coherence principles.

## Features

- **Coherence-Driven Computing**: All operations optimize for mathematical coherence, ensuring consistency across the system
- **Universal Component Model**: Consistent design patterns applied across all system levels
- **Functional Interface**: Pure functions and immutable data structures used throughout the system
- **Neural Computation**: All components implemented as neural network models
- **Resource Optimization**: Intelligent allocation based on coherence requirements
- **Extreme Condition Handling**: Robust numerical computations for demanding scientific applications (e.g., RNA folding)

## Mathematical Foundation

PrimeOS is built on the Universal Object Reference (UOR) framework, which provides the mathematical foundation for the system:

- **Clifford Algebras**: Geometric algebras serve as the mathematical foundation for representing data and operations
- **Coherence and Inner Product Norms**: Mathematical coherence measures how well system components satisfy constraints
- **Lie Groups**: Employed as symmetry operations that transform elements in the system

## Prime Framework Architecture

PrimeOS is organized into four hierarchical bases:

1. **Base 0: Neural Network Specification** - Abstract mathematical foundation
2. **Base 1: Resource** - Lowest-level concrete implementation
3. **Base 2: Kernel** - Orchestrator of the system
4. **Base 3: Application** - User-space applications

## Installation

### From npm (once published)
```bash
npm install primeos
```

### Directly from GitHub
```bash
npm install UOR-Foundation/PrimeOS
```

### From GitHub Packages
```bash
# Add this to your .npmrc
@uor-foundation:registry=https://npm.pkg.github.com

# Then install
npm install @uor-foundation/primeos
```

## Usage

```javascript
import Prime from '@uor-foundation/primeos';

// Create a Prime Framework instance
const framework = Prime.createPrimeFramework();

// Create an application
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

// Start the application
app.start();
```

## Documentation

Comprehensive documentation is available in the [primeos-spec.md](./primeos-spec.md) file.

## Testing

PrimeOS has a comprehensive testing suite with tiered strategies for various environments:

### Test Categories

1. **CI-Safe Tests**: Core modules that run in CI environments
   - Core tests (core functionality)
   - Mathematics tests (mathematical operations)
   - Framework tests (framework components)
   - Coherence tests (coherence validation)

2. **Memory-Intensive Tests**: Require significant RAM (8GB+)
   - Extreme condition tests (numerical stability)
   - UOR verification tests (universal object references)
   - Integration tests (cross-module functionality)

3. **Browser Tests**: Testing in browser environments
   - Uses Puppeteer to launch a headless browser
   - Validates browser-specific functionality

### Running Tests

```bash
# Run CI-safe tests (used in CI/CD pipelines and publishing)
npm run test:ci

# Run individual test categories
npm test                # Standard tests (excludes memory-intensive tests)
npm run test:extreme    # Extreme condition tests (high memory usage)
npm run test:uor        # UOR verification tests (high memory usage)
npm run test:integration # Integration tests
npm run test:browser    # Browser environment tests

# Run distributed coherence tests
npm run test:coherence         # Run distributed coherence tests
npm run test:coherence:bench   # Run distributed coherence benchmarks
npm run test:coherence:mock    # Run mock distributed network simulation

# Run complete test suite (all tests)
npm run test:all
```

See [KNOWN-ISSUES.md](./KNOWN-ISSUES.md) for more details on the testing strategy and known limitations.

## License

MIT