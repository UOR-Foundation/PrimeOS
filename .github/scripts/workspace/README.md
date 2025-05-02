# UOR Workspace Scripts

This directory contains utilities for maintaining the UOR Model Framework repository structure. These scripts enforce the standardized structure and formatting required by the UOR Framework while respecting the "no scripts in repository" principle by being located in the `.github` directory.

## Available Scripts

### template-validator.js

This script validates and repairs the directory structure of the UOR model repository by ensuring all required template files exist in each directory.

#### Features:

- Scans all directories in the repository recursively
- Identifies missing template files based on the UOR Framework's standards
- Only adds missing files without modifying existing content
- Provides detailed reporting of actions taken

#### Required Files Checked:

- `index.json` - Empty JSON object template
- `index.md` - Markdown file with Obsidian-compatible format and Gherkin syntax
- `test.json` - Test specification structure compatible with BDD
- `.model_namespace` - Empty namespace marker file

#### Usage:

```bash
# Execute with default settings (will make changes)
./template-validator.js 

# Dry run - report issues without making changes
./template-validator.js --dry-run

# Verbose output with detailed information
./template-validator.js --verbose

# Only process directories matching a pattern
./template-validator.js --include-dir=schemas

# Skip directories matching a pattern
./template-validator.js --exclude-dir=\.git
```

#### Options:

- `--dry-run`: Report missing files without making changes
- `--verbose`: Show detailed information about each directory
- `--include-dir=pattern`: Only process directories matching pattern
- `--exclude-dir=pattern`: Skip directories matching pattern

Multiple include/exclude patterns can be provided. Patterns are treated as regular expressions.

## Common Libraries

The scripts utilize common utilities from the `../lib` directory:

- `file-utils.js` - File system operations and directory traversal
- `template-manager.js` - Template definitions and content generation
