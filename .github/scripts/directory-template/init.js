#!/usr/bin/env node

const fs = require('fs');
const path = require('path');

// Get the directory path from command line arguments
const args = process.argv.slice(2);
if (args.length !== 1) {
  console.error('Usage: init <directory-path>');
  process.exit(1);
}

const dirPath = args[0];
const modelsRoot = path.resolve(__dirname, '../../../');
const targetPath = path.join(modelsRoot, dirPath);

// Check if directory already exists
if (fs.existsSync(targetPath)) {
  console.error(`Error: Directory '${dirPath}' already exists.`);
  process.exit(1);
}

// Template for index.md with Obsidian note format and Gherkin syntax
const obsidianTemplate = `# Feature: 

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

// Create empty test.json structure that aligns with the Gherkin syntax
const testJsonTemplate = {
  "feature": "",
  "description": "",
  "scenarios": []
};

// Create the directory
try {
  fs.mkdirSync(targetPath, { recursive: true });
  
  // Create empty index.json with empty object
  fs.writeFileSync(
    path.join(targetPath, 'index.json'),
    '{}\n'
  );
  
  // Create index.md file with the Obsidian template
  fs.writeFileSync(
    path.join(targetPath, 'index.md'),
    obsidianTemplate
  );
  
  // Create test.json file
  fs.writeFileSync(
    path.join(targetPath, 'test.json'),
    JSON.stringify(testJsonTemplate, null, 2) + '\n'
  );
  
  console.log(`Successfully initialized directory: ${dirPath}`);
} catch (error) {
  console.error(`Error creating directory: ${error.message}`);
  process.exit(1);
}
