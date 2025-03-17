# PrimeOS Development Guide

## Build & Test Commands
- `npm run build` - Build all packages
- `npm run build:dev` - Development build
- `npm run build:prod` - Production build
- `npm run test` - Run all tests
- `npm test -- -t "test name"` - Run specific test by name
- `npm run test:integration` - Run integration tests
- `npm run lint` - Run ESLint
- `npm run format` - Run Prettier formatter

## Code Style Guidelines
- **Formatting**: 2-space indentation, Unix line endings, single quotes
- **Naming**: camelCase for variables/functions, PascalCase for classes/constructors
- **Imports**: CommonJS `require()` style, with named exports
- **Error Handling**: Use structured error hierarchy with PrimeError base class
- **Types**: Use JSDoc for type annotations
- **Architecture**: Module pattern with encapsulation, event-driven
- **Documentation**: JSDoc with descriptions for all public APIs
- **Testing**: Jest for unit tests, custom test runner for integration

## Best Practices
- Use Utils validation methods (isObject, isFunction, etc.)
- Handle errors with specific error classes
- Add coherence checks for mathematical operations
- Use EventBus for component communication
- Avoid direct console.log (use Logger)
- Implement the framework specification in javascript-spec.md