module.exports = {
    testEnvironment: 'jsdom',
    moduleFileExtensions: ['js'],
    transform: {
      '^.+\\.js$': 'babel-jest'
    },
    testMatch: [
      '**/tests/*-tests.js'
    ],
    testPathIgnorePatterns: [
      '/node_modules/',
      'tests/integration-tests.js',
      'tests/extreme-conditions-tests.js',
      'tests/uor-verification-tests.js'
    ],
    collectCoverage: true,
    coverageReporters: [
      'lcov',
      'text-summary'
    ],
    transformIgnorePatterns: [
      '/node_modules/',
      '\\.pnp\\.[^\\/]+$'
    ],
    moduleNameMapper: {
      // Add any module name mappings if needed
    }
  };