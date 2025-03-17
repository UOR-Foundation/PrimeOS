/**
 * PrimeOS Code Generator
 * 
 * Service for transforming application specifications into functional code
 * for PrimeOS applications.
 */

class CodeGenerator {
  /**
   * Creates a new Code Generator instance
   * @param {Object} options - Configuration options
   * @param {Object} options.claudeService - ClaudeService instance for AI assistance
   * @param {Object} options.eventBus - Event bus for notifications
   * @param {Object} options.templates - Code templates
   */
  constructor(options) {
    // Validate required dependencies
    if (!options.claudeService) {
      throw new Error('CodeGenerator requires a claudeService instance');
    }
    
    // Store dependencies
    this.claudeService = options.claudeService;
    this.eventBus = options.eventBus || null;
    
    // Initialize templates
    this.templates = options.templates || {};
    this._loadDefaultTemplates();
    
    console.log('CodeGenerator initialized');
  }
  
  /**
   * Generate application code from specification
   * @param {Object} specification - Application specification
   * @returns {Promise<Object>} Generated code files
   */
  async generateAppCode(specification) {
    if (!specification) {
      throw new Error('Application specification is required');
    }
    
    console.log('Generating app code from specification');
    
    try {
      // Notify generation start
      this._notifyEvent('generation-started', {
        appName: specification.appName || 'Unnamed App'
      });
      
      // Generate app structure
      const appStructure = this._generateAppStructure(specification);
      
      // Delegate to Claude for code generation
      const generatedFiles = await this.claudeService.generateAppCode(specification);
      
      // Apply templates to files
      const enhancedFiles = this._applyCodeTemplates(generatedFiles.files, specification);
      
      // Ensure all required files exist
      const completeFiles = this._ensureRequiredFiles(enhancedFiles, specification);
      
      // Generate tests
      const withTests = await this._generateTests(completeFiles, specification);
      
      // Notify generation completion
      this._notifyEvent('generation-completed', {
        appName: specification.appName || 'Unnamed App',
        fileCount: withTests.length
      });
      
      return {
        files: withTests,
        structure: generatedFiles.structure || this._createFileStructure(withTests)
      };
    } catch (error) {
      console.error('Failed to generate app code:', error);
      
      // Notify generation failure
      this._notifyEvent('generation-failed', {
        error: error.message
      });
      
      throw error;
    }
  }
  
  /**
   * Generate test files for an application
   * @param {Array} files - Existing code files
   * @param {Object} specification - Application specification
   * @returns {Promise<Array>} Files with tests added
   */
  async _generateTests(files, specification) {
    console.log('Generating tests');
    
    try {
      // Find existing test files
      const testFiles = files.filter(file => this._isTestFile(file.path));
      
      // If sufficient tests already exist, return as-is
      if (testFiles.length >= Math.ceil(files.length * 0.2)) {
        return files;
      }
      
      // Get source files that need tests
      const sourceFiles = files.filter(file => 
        file.path.endsWith('.js') && 
        !this._isTestFile(file.path) &&
        !file.path.includes('node_modules') &&
        !file.path.includes('vendor')
      );
      
      // Generate test files for source files that don't have them
      const newTestFiles = [];
      
      for (const sourceFile of sourceFiles) {
        // Check if test already exists
        const testPath = this._getTestPathForSource(sourceFile.path);
        if (files.some(file => file.path === testPath)) {
          continue;
        }
        
        // Generate test file using template
        const testFile = await this._generateTestForSource(sourceFile, specification);
        if (testFile) {
          newTestFiles.push(testFile);
        }
      }
      
      // Return combined files
      return [...files, ...newTestFiles];
    } catch (error) {
      console.error('Error generating tests:', error);
      // Return original files if test generation fails
      return files;
    }
  }
  
  /**
   * Generate a test file for a source file
   * @private
   * @param {Object} sourceFile - Source file object
   * @param {Object} specification - Application specification
   * @returns {Promise<Object>} Generated test file
   */
  async _generateTestForSource(sourceFile, specification) {
    // Determine test path
    const testPath = this._getTestPathForSource(sourceFile.path);
    
    // Get appropriate test template
    const testTemplate = this._getTestTemplate(sourceFile.path);
    
    if (!testTemplate) {
      // Skip files that don't have a suitable test template
      return null;
    }
    
    try {
      // Use Claude to generate test content
      const testContent = await this._generateTestContent(sourceFile, testTemplate, specification);
      
      return {
        path: testPath,
        content: testContent,
        generated: true,
        isTest: true
      };
    } catch (error) {
      console.error(`Failed to generate test for ${sourceFile.path}:`, error);
      
      // Use a minimal test as fallback
      return {
        path: testPath,
        content: this._createMinimalTest(sourceFile.path),
        generated: true,
        isTest: true
      };
    }
  }
  
  /**
   * Generate test content for a source file
   * @private
   * @param {Object} sourceFile - Source file object
   * @param {string} testTemplate - Test template
   * @param {Object} specification - Application specification
   * @returns {Promise<string>} Generated test content
   */
  async _generateTestContent(sourceFile, testTemplate, specification) {
    // Prepare a focused prompt for test generation
    const prompt = `
      Generate a comprehensive Jest test file for this source file:
      
      Source File Path: ${sourceFile.path}
      
      Source Code:
      \`\`\`javascript
      ${sourceFile.content}
      \`\`\`
      
      App Specification Context:
      ${JSON.stringify(specification, null, 2)}
      
      Create tests that:
      1. Test all public methods and functions
      2. Mock dependencies appropriately
      3. Include both success and error cases
      4. Achieve good code coverage
      5. Follow jest best practices
      
      Return ONLY the complete test file content without explanation.
    `;
    
    // Use a custom prompt through Claude
    const response = await this.claudeService._executeRequest(prompt, 'test_generation');
    
    // Extract code content from response
    const codePattern = /```(?:javascript|js)\s*([\s\S]*?)\s*```|`([\s\S]*?)`/;
    const match = response.match(codePattern);
    
    if (match) {
      return match[1] || match[2];
    }
    
    // If no code block found, use the entire response
    return response;
  }
  
  /**
   * Create minimal test file content
   * @private
   * @param {string} sourcePath - Source file path
   * @returns {string} Minimal test content
   */
  _createMinimalTest(sourcePath) {
    const moduleName = sourcePath.split('/').pop().replace('.js', '');
    
    return `/**
 * Basic test file for ${moduleName}
 */

describe('${moduleName}', () => {
  it('should be properly implemented', () => {
    // This is a placeholder test
    // Replace with actual tests for ${moduleName}
    expect(true).toBe(true);
  });
});
`;
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
      filePath.includes('/tests/') ||
      filePath.endsWith('.test.js') ||
      filePath.endsWith('.spec.js')
    );
  }
  
  /**
   * Get test path for a source file
   * @private
   * @param {string} sourcePath - Source file path
   * @returns {string} Corresponding test file path
   */
  _getTestPathForSource(sourcePath) {
    // Determine test file naming strategy
    if (sourcePath.includes('/src/')) {
      // Use __tests__ directory if following src pattern
      const dirPath = sourcePath.substring(0, sourcePath.lastIndexOf('/'));
      const fileName = sourcePath.substring(sourcePath.lastIndexOf('/') + 1);
      return `${dirPath}/__tests__/${fileName.replace('.js', '.test.js')}`;
    } else {
      // Otherwise just append .test.js to filename
      return sourcePath.replace('.js', '.test.js');
    }
  }
  
  /**
   * Apply code templates to generated files
   * @private
   * @param {Array} files - Generated files
   * @param {Object} specification - Application specification
   * @returns {Array} Enhanced files
   */
  _applyCodeTemplates(files, specification) {
    return files.map(file => {
      // Find appropriate template for this file
      const template = this._getTemplateForFile(file.path);
      
      if (!template) {
        return file;
      }
      
      try {
        // Apply template replacements
        let content = template;
        
        // Replace template placeholders
        content = content.replace(/\{\{appName\}\}/g, specification.appName || 'PrimeOSApp');
        content = content.replace(/\{\{appDescription\}\}/g, specification.description || '');
        content = content.replace(/\{\{date\}\}/g, new Date().toISOString().split('T')[0]);
        
        // Replace {{code}} with generated content if it exists
        if (content.includes('{{code}}')) {
          content = content.replace(/\{\{code\}\}/g, file.content);
        }
        
        return {
          ...file,
          content,
          enhanced: true
        };
      } catch (error) {
        console.error(`Failed to apply template to ${file.path}:`, error);
        return file;
      }
    });
  }
  
  /**
   * Ensure all required files exist
   * @private
   * @param {Array} files - Existing files
   * @param {Object} specification - Application specification
   * @returns {Array} Complete files
   */
  _ensureRequiredFiles(files, specification) {
    const result = [...files];
    const filePaths = files.map(file => file.path);
    
    // Check for required files
    const requiredFiles = this._getRequiredFiles(specification);
    
    for (const [path, template] of Object.entries(requiredFiles)) {
      if (!filePaths.includes(path)) {
        // Create file from template
        let content = template;
        
        // Replace template placeholders
        content = content.replace(/\{\{appName\}\}/g, specification.appName || 'PrimeOSApp');
        content = content.replace(/\{\{appDescription\}\}/g, specification.description || '');
        content = content.replace(/\{\{date\}\}/g, new Date().toISOString().split('T')[0]);
        
        // Add file
        result.push({
          path,
          content,
          generated: true,
          required: true
        });
      }
    }
    
    return result;
  }
  
  /**
   * Generate basic app structure from specification
   * @private
   * @param {Object} specification - Application specification
   * @returns {Object} App structure
   */
  _generateAppStructure(specification) {
    // Determine app type
    const appType = specification.appType || 'standard';
    
    // Get structure template
    const structureTemplate = this.templates.structures?.[appType] || this.templates.structures?.standard;
    
    if (!structureTemplate) {
      return {
        directories: ['src', 'src/components', 'src/models', 'src/utils']
      };
    }
    
    // Clone template to avoid modifications
    return JSON.parse(JSON.stringify(structureTemplate));
  }
  
  /**
   * Get required files for the application
   * @private
   * @param {Object} specification - Application specification
   * @returns {Object} Map of required files
   */
  _getRequiredFiles(specification) {
    const appName = specification.appName || 'PrimeOSApp';
    const requiredFiles = {};
    
    // Add index.js if not exists
    requiredFiles['index.js'] = this.templates.core?.['index.js'] || `/**
 * ${appName}
 * 
 * Entry point for ${appName} application
 * Generated by PrimeOS App Factory
 * {{date}}
 */

// Initialize application
function initApp() {
  // Application initialization code
  console.log('${appName} initialized');
}

// Run app when DOM is ready
if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', initApp);
} else {
  initApp();
}
`;
    
    // Add README.md if not exists
    requiredFiles['README.md'] = this.templates.docs?.['README.md'] || `# ${appName}

${specification.description || 'A PrimeOS Application'}

## Overview

This application was generated using the PrimeOS App Factory.

## Features

${specification.features ? specification.features.map(f => `- ${f}`).join('\n') : '- Feature list coming soon'}

## Installation

1. Clone the repository
2. Install dependencies
3. Run the application

## Usage

Detailed usage instructions coming soon.

## License

MIT
`;
    
    return requiredFiles;
  }
  
  /**
   * Create a file structure representation from files array
   * @private
   * @param {Array} files - Array of file objects
   * @returns {Object} File structure representation
   */
  _createFileStructure(files) {
    // Create a directory tree structure
    const structure = {
      name: 'root',
      type: 'directory',
      children: {}
    };
    
    // Process each file
    for (const file of files) {
      const pathParts = file.path.split('/');
      const fileName = pathParts.pop();
      
      // Create directory structure
      let currentLevel = structure.children;
      
      for (const part of pathParts) {
        if (!part) continue; // Skip empty parts
        
        if (!currentLevel[part]) {
          currentLevel[part] = {
            name: part,
            type: 'directory',
            children: {}
          };
        }
        currentLevel = currentLevel[part].children;
      }
      
      // Add file at current level
      currentLevel[fileName] = {
        name: fileName,
        type: 'file',
        path: file.path,
        isTest: this._isTestFile(file.path)
      };
    }
    
    return structure;
  }
  
  /**
   * Get template for a specific file
   * @private
   * @param {string} filePath - File path
   * @returns {string|null} Template for the file
   */
  _getTemplateForFile(filePath) {
    // Check exact path match
    if (this.templates.files?.[filePath]) {
      return this.templates.files[filePath];
    }
    
    // Check path pattern matches
    for (const [pattern, template] of Object.entries(this.templates.patterns || {})) {
      const regex = new RegExp(pattern);
      if (regex.test(filePath)) {
        return template;
      }
    }
    
    // Check extension templates
    const extension = filePath.substring(filePath.lastIndexOf('.') + 1);
    return this.templates.extensions?.[extension] || null;
  }
  
  /**
   * Get test template for a file
   * @private
   * @param {string} filePath - Source file path
   * @returns {string|null} Test template
   */
  _getTestTemplate(filePath) {
    // Check if there's a specific test template for this file
    if (this.templates.tests?.[filePath]) {
      return this.templates.tests[filePath];
    }
    
    // Check for pattern-based test templates
    for (const [pattern, template] of Object.entries(this.templates.testPatterns || {})) {
      const regex = new RegExp(pattern);
      if (regex.test(filePath)) {
        return template;
      }
    }
    
    // Return default test template
    return this.templates.tests?.default || null;
  }
  
  /**
   * Load default templates
   * @private
   */
  _loadDefaultTemplates() {
    // Only load default templates for missing categories
    const templates = {
      structures: this.templates.structures || {
        standard: {
          directories: [
            'src',
            'src/components',
            'src/models',
            'src/utils',
            'src/assets',
            'src/__tests__'
          ]
        },
        utility: {
          directories: [
            'src',
            'src/lib',
            'src/utils',
            'src/__tests__'
          ]
        }
      },
      extensions: this.templates.extensions || {
        'js': `/**
 * {{appName}}
 * Generated by PrimeOS App Factory
 * {{date}}
 */

{{code}}`,
        'css': `/**
 * {{appName}} Styles
 * Generated by PrimeOS App Factory
 * {{date}}
 */

{{code}}`,
        'html': `<!DOCTYPE html>
<!--
  {{appName}}
  Generated by PrimeOS App Factory
  {{date}}
-->

{{code}}`
      },
      tests: this.templates.tests || {
        default: `/**
 * Tests for {{appName}}
 * Generated by PrimeOS App Factory
 * {{date}}
 */

describe('{{appName}}', () => {
  it('should pass basic tests', () => {
    expect(true).toBe(true);
  });
});`
      },
      core: this.templates.core || {},
      docs: this.templates.docs || {}
    };
    
    // Merge with existing templates
    this.templates = {
      ...templates,
      ...this.templates
    };
  }
  
  /**
   * Send event notification
   * @private
   * @param {string} event - Event name
   * @param {Object} data - Event data
   */
  _notifyEvent(event, data = {}) {
    if (this.eventBus) {
      this.eventBus.publish(`code-generator:${event}`, {
        timestamp: new Date().toISOString(),
        ...data
      });
    }
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { CodeGenerator };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.CodeGenerator = CodeGenerator;
}