/**
 * Template management for UOR model repository
 */

/**
 * Template for index.md with Obsidian note format and Gherkin syntax
 * @returns {string} The markdown template content
 */
function generateMarkdownTemplate() {
  return `# Feature: 

## Description

## Behavior Specifications

### Scenario: 
**Given** 
**When** 
**Then** 

### Scenario: 
**Given** 
**When** 
**Then** 

## Implementation Notes

## References
`;
}

/**
 * Template for test.json that aligns with Gherkin syntax
 * @returns {string} The JSON template content
 */
function generateTestJsonTemplate() {
  const template = {
    "feature": "",
    "description": "",
    "scenarios": []
  };
  
  return JSON.stringify(template, null, 2) + '\n';
}

/**
 * Template for empty index.json
 * @returns {string} The JSON template content
 */
function generateIndexJsonTemplate() {
  return '{}\n';
}

/**
 * Template for empty .model_namespace
 * @returns {string} Empty string
 */
function generateModelNamespaceTemplate() {
  return '';
}

/**
 * Required template files and their generator functions
 */
const REQUIRED_TEMPLATES = {
  'index.json': generateIndexJsonTemplate,
  'index.md': generateMarkdownTemplate,
  'test.json': generateTestJsonTemplate,
  '.model_namespace': generateModelNamespaceTemplate
};

/**
 * Get the list of required template file names
 * @returns {string[]} Array of required template file names
 */
function getRequiredTemplateFiles() {
  return Object.keys(REQUIRED_TEMPLATES);
}

/**
 * Generate content for a template file
 * @param {string} templateName - Name of the template file
 * @returns {string} Generated content
 * @throws {Error} If template name is not recognized
 */
function generateTemplateContent(templateName) {
  if (!REQUIRED_TEMPLATES[templateName]) {
    throw new Error(`Unknown template: ${templateName}`);
  }
  
  return REQUIRED_TEMPLATES[templateName]();
}

/**
 * Check if a file is a template file
 * @param {string} fileName - Name of the file to check
 * @returns {boolean} True if the file is a template file
 */
function isTemplateFile(fileName) {
  return Object.keys(REQUIRED_TEMPLATES).includes(fileName);
}

module.exports = {
  getRequiredTemplateFiles,
  generateTemplateContent,
  isTemplateFile,
  REQUIRED_TEMPLATES
};
