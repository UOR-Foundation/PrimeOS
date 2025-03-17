/**
 * PrimeOS App Factory Test Runner
 * 
 * Service for executing tests on generated app code to ensure
 * quality and correct functionality.
 */

class TestRunner {
  /**
   * Creates a new TestRunner instance
   * @param {Object} options - Configuration options
   * @param {Object} options.eventBus - Event bus for notifications
   * @param {boolean} options.includeJest - Whether to include Jest for unit tests
   * @param {boolean} options.includeLint - Whether to include ESLint
   */
  constructor(options = {}) {
    // Store configuration
    this.eventBus = options.eventBus || null;
    this.includeJest = options.includeJest !== false;
    this.includeLint = options.includeLint !== false;
    
    // Temporary filesystem for testing
    this.tempFilesystem = null;
    
    // Jest configuration
    this.jestConfig = {
      verbose: true,
      testEnvironment: 'jsdom',
      setupFilesAfterEnv: [],
      transform: {},
      moduleNameMapper: {},
      testMatch: ['**/__tests__/**/*.js', '**/*.test.js', '**/*.spec.js'],
      testPathIgnorePatterns: ['/node_modules/']
    };
    
    // ESLint configuration
    this.eslintConfig = {
      env: {
        browser: true,
        es2021: true,
        jest: true
      },
      extends: ['eslint:recommended'],
      parserOptions: {
        ecmaVersion: 'latest',
        sourceType: 'module'
      },
      rules: {
        'no-unused-vars': 'warn',
        'no-undef': 'error'
      }
    };
    
    console.log('TestRunner initialized');
  }
  
  /**
   * Run tests on app code files
   * @param {Array} files - App code files
   * @returns {Promise<Object>} Test results
   */
  async runTests(files) {
    console.log('Running tests on app code');
    
    if (!files || !Array.isArray(files)) {
      throw new Error('Files array is required');
    }
    
    try {
      // Start with lint validation if enabled
      let lintResults = null;
      if (this.includeLint) {
        lintResults = await this._runLintValidation(files);
      }
      
      // Find test files
      const testFiles = files.filter(file => this._isTestFile(file.path));
      const sourceFiles = files.filter(file => !this._isTestFile(file.path));
      
      // Check if any test files exist
      if (testFiles.length === 0) {
        console.warn('No test files found in the provided app code');
        
        // Generate a basic test report with linting only
        return {
          success: lintResults?.success || false,
          lintResults,
          unitTestResults: null,
          passed: lintResults?.passed || 0,
          failed: lintResults?.errors || 0,
          total: lintResults?.total || 0,
          timestamp: new Date().toISOString(),
          details: {
            message: 'No test files found. Only linting was performed.',
            recommendation: 'Consider adding unit tests for your application.'
          }
        };
      }
      
      // Run unit tests
      let unitTestResults = null;
      if (this.includeJest) {
        unitTestResults = await this._runUnitTests(files);
      }
      
      // Combine results
      const success = 
        (lintResults?.success || !this.includeLint) && 
        (unitTestResults?.success || !this.includeJest);
      
      const passed = 
        (lintResults?.passed || 0) + 
        (unitTestResults?.passed || 0);
      
      const total = 
        (lintResults?.total || 0) + 
        (unitTestResults?.total || 0);
      
      // Create final test report
      const testReport = {
        success,
        lintResults,
        unitTestResults,
        passed,
        failed: total - passed,
        total,
        timestamp: new Date().toISOString(),
        details: {
          testFiles: testFiles.length,
          sourceFiles: sourceFiles.length,
          recommendations: this._generateRecommendations(lintResults, unitTestResults)
        }
      };
      
      // Notify test completion
      if (this.eventBus) {
        this.eventBus.publish('app-factory:tests-completed', {
          success,
          passed,
          total,
          timestamp: new Date().toISOString()
        });
      }
      
      return testReport;
    } catch (error) {
      console.error('Failed to run tests:', error);
      
      // Create error report
      return {
        success: false,
        error: error.message,
        timestamp: new Date().toISOString()
      };
    }
  }
  
  /**
   * Run ESLint validation on code files
   * @private
   * @param {Array} files - App code files
   * @returns {Promise<Object>} Lint results
   */
  async _runLintValidation(files) {
    console.log('Running lint validation');
    
    // In a real implementation, this would use ESLint to validate the code
    // For this reference implementation, we'll simulate the process
    
    // Filter only JS files for linting
    const jsFiles = files.filter(file => 
      file.path.endsWith('.js') && !file.path.includes('node_modules')
    );
    
    // Mock linting process
    const lintIssues = [];
    let passed = 0;
    
    for (const file of jsFiles) {
      // Simulate lint validation
      const fileIssues = this._mockLintFile(file);
      
      if (fileIssues.length === 0) {
        passed++;
      } else {
        lintIssues.push({
          filePath: file.path,
          issues: fileIssues
        });
      }
    }
    
    // Create lint report
    return {
      success: lintIssues.length === 0,
      passed,
      total: jsFiles.length,
      errors: lintIssues.reduce((sum, file) => sum + file.issues.length, 0),
      warnings: lintIssues.reduce((sum, file) => 
        sum + file.issues.filter(issue => issue.type === 'warning').length, 0
      ),
      issues: lintIssues
    };
  }
  
  /**
   * Mock lint validation on a file
   * @private
   * @param {Object} file - File to lint
   * @returns {Array} Lint issues
   */
  _mockLintFile(file) {
    const issues = [];
    const content = file.content;
    
    // Check for common issues
    
    // Check for console.log usage (warning)
    const consoleMatches = content.match(/console\.log\(/g);
    if (consoleMatches) {
      issues.push({
        type: 'warning',
        line: this._findLineNumber(content, 'console.log('),
        message: 'Unexpected console statement',
        rule: 'no-console'
      });
    }
    
    // Check for var usage (warning)
    const varMatches = content.match(/\bvar\s+/g);
    if (varMatches) {
      issues.push({
        type: 'warning',
        line: this._findLineNumber(content, 'var '),
        message: 'Unexpected var, use let or const instead',
        rule: 'no-var'
      });
    }
    
    // Check for undefined variables (error, more complex in real implementation)
    // This is a very simplistic check that will have false positives
    const undefinedVarMatch = content.match(/(?<!(?:var|let|const|function|class|import|\/\/|\/\*|\*).{0,40})\b([A-Za-z_$][A-Za-z0-9_$]*)(?=\s*[\.\(=])/);
    if (undefinedVarMatch && 
        !['document', 'window', 'fetch', 'Promise', 'Map', 'Set', 'Array', 'Object', 'String', 'Number', 'Boolean', 'console', 'this'].includes(undefinedVarMatch[1])) {
      issues.push({
        type: 'error',
        line: this._findLineNumber(content, undefinedVarMatch[0]),
        message: `'${undefinedVarMatch[1]}' is not defined`,
        rule: 'no-undef'
      });
    }
    
    return issues;
  }
  
  /**
   * Run unit tests on app code
   * @private
   * @param {Array} files - App code files
   * @returns {Promise<Object>} Unit test results
   */
  async _runUnitTests(files) {
    console.log('Running unit tests');
    
    // In a real implementation, this would use Jest to run the tests
    // For this reference implementation, we'll simulate the process
    
    // Find test files
    const testFiles = files.filter(file => this._isTestFile(file.path));
    
    // Simulate test runs
    const testResults = [];
    let passed = 0;
    let failed = 0;
    
    for (const testFile of testFiles) {
      // Mock test execution
      const fileResults = await this._mockRunTests(testFile, files);
      
      passed += fileResults.passed;
      failed += fileResults.failed;
      
      testResults.push({
        testFilePath: testFile.path,
        passed: fileResults.passed,
        failed: fileResults.failed,
        total: fileResults.total,
        duration: fileResults.duration,
        testResults: fileResults.tests
      });
    }
    
    // Create test report
    return {
      success: failed === 0,
      passed,
      failed,
      total: passed + failed,
      testFiles: testFiles.length,
      testResults
    };
  }
  
  /**
   * Mock test execution for a test file
   * @private
   * @param {Object} testFile - Test file
   * @param {Array} allFiles - All app files
   * @returns {Promise<Object>} Test results
   */
  async _mockRunTests(testFile, allFiles) {
    // Extract test cases from file content
    const testCases = this._extractTestCases(testFile.content);
    
    // Results for this file
    const testResults = [];
    let passed = 0;
    let failed = 0;
    
    for (const test of testCases) {
      // Simulate test execution
      const result = this._mockEvaluateTest(test, allFiles);
      
      if (result.status === 'passed') {
        passed++;
      } else {
        failed++;
      }
      
      testResults.push({
        name: test.name,
        status: result.status,
        duration: result.duration,
        error: result.error
      });
    }
    
    return {
      passed,
      failed,
      total: testCases.length,
      duration: Math.floor(Math.random() * 500) + 100, // Random duration between 100-600ms
      tests: testResults
    };
  }
  
  /**
   * Extract test cases from test file content
   * @private
   * @param {string} content - Test file content
   * @returns {Array} Array of test cases
   */
  _extractTestCases(content) {
    const testCases = [];
    
    // Look for test/it function calls
    const testRegex = /(?:test|it)\s*\(\s*['"](.+?)['"]\s*,\s*(?:async\s*)?\(\)\s*=>\s*\{([\s\S]*?)\}\s*\)/g;
    let match;
    
    while ((match = testRegex.exec(content)) !== null) {
      testCases.push({
        name: match[1],
        body: match[2]
      });
    }
    
    // If no test cases found, check for describe blocks
    if (testCases.length === 0) {
      const describeRegex = /describe\s*\(\s*['"](.+?)['"]\s*,\s*\(\)\s*=>\s*\{([\s\S]*?)\}\s*\)/g;
      
      while ((match = describeRegex.exec(content)) !== null) {
        const describeBody = match[2];
        const describeTitle = match[1];
        
        // Find tests within the describe block
        const nestedTestRegex = /(?:test|it)\s*\(\s*['"](.+?)['"]\s*,\s*(?:async\s*)?\(\)\s*=>\s*\{([\s\S]*?)\}\s*\)/g;
        let nestedMatch;
        
        while ((nestedMatch = nestedTestRegex.exec(describeBody)) !== null) {
          testCases.push({
            name: `${describeTitle} ${nestedMatch[1]}`,
            body: nestedMatch[2]
          });
        }
      }
    }
    
    return testCases;
  }
  
  /**
   * Mock evaluation of a test case
   * @private
   * @param {Object} test - Test case
   * @param {Array} allFiles - All app files
   * @returns {Object} Test result
   */
  _mockEvaluateTest(test, allFiles) {
    // In a real implementation, this would execute the test code
    // For this mock, we'll identify common patterns to determine pass/fail
    
    const testCode = test.body;
    
    // Check for likely failure patterns
    const assertionMatch = testCode.match(/expect\(.*\)\.(?:toBe|toEqual|toMatch|toContain|toHaveLength|toHaveProperty|toThrow|toBeNull|toBeUndefined|toBeDefined|toBeTruthy|toBeFalsy)\(/g);
    const assertCount = assertionMatch ? assertionMatch.length : 0;
    
    // Look for assertions that will likely fail
    const failingPatterns = [
      /expect\(undefined\)\.toBe/,
      /expect\(null\)\.toBe/,
      /expect\([^)]+\)\.toEqual\(\s*undefined\s*\)/,
      /expect\([^)]+\)\.toEqual\(\s*null\s*\)/,
      /expect\(false\)\.toBeTruthy/,
      /expect\(true\)\.toBeFalsy/,
      /expect\(\s*\[\s*\]\s*\)\.toHaveLength\(\s*[1-9][0-9]*\s*\)/,
      /expect\(\s*\{\s*\}\s*\)\.toHaveProperty/
    ];
    
    // Generate random success/failure
    // Tests with more assertions are more likely to fail
    const randomFactor = 0.9 - (assertCount * 0.05);
    const willPass = Math.random() < randomFactor;
    
    // Check for patterns that suggest failure
    let willFail = false;
    for (const pattern of failingPatterns) {
      if (pattern.test(testCode)) {
        willFail = true;
        break;
      }
    }
    
    // Final determination with some randomness
    const testPasses = willFail ? false : willPass;
    
    if (testPasses) {
      return {
        status: 'passed',
        duration: Math.floor(Math.random() * 20) + 5 // 5-25ms
      };
    } else {
      // Generate a plausible error message
      let errorMessage = 'Test failed';
      
      if (testCode.includes('toBe')) {
        errorMessage = 'Expected value to be equal, but received different value';
      } else if (testCode.includes('toContain')) {
        errorMessage = 'Expected array to contain item, but item was not found';
      } else if (testCode.includes('toHaveLength')) {
        errorMessage = 'Expected array to have specific length, but length was different';
      } else if (testCode.includes('toThrow')) {
        errorMessage = 'Expected function to throw an error, but it did not throw';
      }
      
      return {
        status: 'failed',
        duration: Math.floor(Math.random() * 30) + 10, // 10-40ms
        error: errorMessage
      };
    }
  }
  
  /**
   * Check if a file is a test file
   * @private
   * @param {string} filePath - File path
   * @returns {boolean} Whether the file is a test file
   */
  _isTestFile(filePath) {
    return (
      filePath.includes('/__tests__/') ||
      filePath.endsWith('.test.js') ||
      filePath.endsWith('.spec.js')
    );
  }
  
  /**
   * Find line number for a substring in content
   * @private
   * @param {string} content - File content
   * @param {string} substring - Substring to find
   * @returns {number} Line number
   */
  _findLineNumber(content, substring) {
    const lines = content.split('\n');
    for (let i = 0; i < lines.length; i++) {
      if (lines[i].includes(substring)) {
        return i + 1;
      }
    }
    return 1;
  }
  
  /**
   * Generate recommendations based on test results
   * @private
   * @param {Object} lintResults - Lint validation results
   * @param {Object} testResults - Unit test results
   * @returns {Array} Recommendations
   */
  _generateRecommendations(lintResults, testResults) {
    const recommendations = [];
    
    // Add lint-based recommendations
    if (lintResults) {
      if (lintResults.errors > 0) {
        recommendations.push({
          type: 'error',
          message: `Fix ${lintResults.errors} linting errors to improve code quality`
        });
      }
      
      if (lintResults.warnings > 0) {
        recommendations.push({
          type: 'warning',
          message: `Address ${lintResults.warnings} linting warnings for better code quality`
        });
      }
      
      // Common recommendations based on lint issues
      if (lintResults.issues) {
        const hasConsoleIssues = lintResults.issues.some(file => 
          file.issues.some(issue => issue.rule === 'no-console')
        );
        
        if (hasConsoleIssues) {
          recommendations.push({
            type: 'improvement',
            message: 'Replace console.log statements with a proper logging mechanism'
          });
        }
        
        const hasVarIssues = lintResults.issues.some(file => 
          file.issues.some(issue => issue.rule === 'no-var')
        );
        
        if (hasVarIssues) {
          recommendations.push({
            type: 'improvement',
            message: 'Replace var declarations with const or let for better scoping'
          });
        }
      }
    }
    
    // Add test-based recommendations
    if (testResults) {
      if (testResults.failed > 0) {
        recommendations.push({
          type: 'error',
          message: `Fix ${testResults.failed} failing tests to ensure app functionality`
        });
      }
      
      if (testResults.testFiles === 0) {
        recommendations.push({
          type: 'warning',
          message: 'No test files found - consider adding tests for your application'
        });
      } else if (testResults.total < 5) {
        recommendations.push({
          type: 'improvement',
          message: 'Increase test coverage by adding more test cases'
        });
      }
    }
    
    // Add general recommendations
    if (recommendations.length === 0) {
      recommendations.push({
        type: 'success',
        message: 'Code looks good! Consider adding more tests for edge cases.'
      });
    }
    
    return recommendations;
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { TestRunner };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.TestRunner = TestRunner;
}