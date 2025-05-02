# UOR Script Libraries

This directory contains shared utilities used by UOR Model Framework maintenance scripts. These libraries provide consistent functionality across the workflow scripts while keeping the codebase DRY (Don't Repeat Yourself).

## Available Libraries

### file-utils.js

A collection of file system utilities for working with the UOR model repository structure.

#### Key Functions:

- `walkDirectories(dir, options)`: Recursively traverses directories with filtering options
- `checkMissingFiles(dirPath, requiredFiles)`: Checks for missing required files in a directory
- `safeCreateFile(filePath, content)`: Creates a file only if it doesn't already exist
- `listDirectories(dirPath)`: Lists all directories in a given path

### template-manager.js

Manages templates for standard UOR model repository files.

#### Key Functions:

- `getRequiredTemplateFiles()`: Returns the list of required template files
- `generateTemplateContent(templateName)`: Generates content for a specific template
- `isTemplateFile(fileName)`: Checks if a file is a recognized template

#### Supported Templates:

- `index.json` - Empty JSON object 
- `index.md` - Markdown with Obsidian format and Gherkin syntax
- `test.json` - Test specification structure for BDD
- `.model_namespace` - Empty namespace marker

## Usage

These libraries are designed to be imported by scripts in the `workspace` directory or other maintenance tools:

```javascript
const fileUtils = require('../lib/file-utils');
const templateManager = require('../lib/template-manager');

// Example usage
const directories = fileUtils.walkDirectories('/path/to/models');
const requiredFiles = templateManager.getRequiredTemplateFiles();

for (const dir of directories) {
  const missingFiles = fileUtils.checkMissingFiles(dir, requiredFiles);
  // Process missing files...
}
```

## Design Principles

1. **Non-destructive operations**: Functions should never overwrite existing files or data
2. **Error handling**: All functions handle errors gracefully with appropriate messaging
3. **Pure functionality**: Libraries maintain separation of concerns without side effects
4. **Documentation**: All functions are documented with JSDoc comments
