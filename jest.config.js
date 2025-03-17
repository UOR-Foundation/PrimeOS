module.exports = {
    testEnvironment: 'jsdom',
    moduleFileExtensions: ['js'],
    transform: {
      '^.+\\.js$': 'babel-jest'
    },
    testMatch: [
      '**/tests/*-tests.js'
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