#!/usr/bin/env node

/**
 * Template Validator for UOR Model Framework
 * 
 * This script scans the UOR model repository directories and ensures
 * that all required template files exist in each directory. It only adds
 * missing files and never modifies existing content.
 */

const fs = require('fs');
const path = require('path');
const fileUtils = require('../lib/file-utils');
const templateManager = require('../lib/template-manager');

// Process command line arguments
const args = process.argv.slice(2);
const options = {
  dryRun: args.includes('--dry-run'),
  verbose: args.includes('--verbose'),
  excludeDirs: [],
  includeDirs: []
};

// Process include/exclude patterns
args.forEach(arg => {
  if (arg.startsWith('--exclude-dir=')) {
    options.excludeDirs.push(new RegExp(arg.replace('--exclude-dir=', '')));
  }
  if (arg.startsWith('--include-dir=')) {
    options.includeDirs.push(new RegExp(arg.replace('--include-dir=', '')));
  }
});

// Find the models root directory
const scriptDir = path.dirname(require.main.filename);
const modelsRoot = path.resolve(scriptDir, '../../../');

// Initialize report object
const report = {
  fixed: [],
  complete: [],
  skipped: [],
  errors: []
};

/**
 * Check a directory for missing template files and add them if needed
 * @param {string} dirPath - Path to the directory to check
 * @returns {object} Report of actions taken
 */
function validateDirectory(dirPath) {
  const requiredFiles = templateManager.getRequiredTemplateFiles();
  const missingFiles = fileUtils.checkMissingFiles(dirPath, requiredFiles);
  
  if (missingFiles.length === 0) {
    if (options.verbose) {
      console.log(`✓ Directory is complete: ${dirPath}`);
    }
    report.complete.push(dirPath);
    return;
  }
  
  // Process each missing file
  for (const fileName of missingFiles) {
    const filePath = path.join(dirPath, fileName);
    
    if (options.dryRun) {
      console.log(`[DRY RUN] Would create: ${filePath}`);
      report.fixed.push(filePath);
      continue;
    }
    
    try {
      const created = fileUtils.safeCreateFile(
        filePath, 
        () => templateManager.generateTemplateContent(fileName)
      );
      
      if (created) {
        console.log(`+ Created: ${filePath}`);
        report.fixed.push(filePath);
      } else {
        console.log(`~ Skipped existing: ${filePath}`);
        report.skipped.push(filePath);
      }
    } catch (error) {
      console.error(`Error creating ${filePath}: ${error.message}`);
      report.errors.push({ path: filePath, error: error.message });
    }
  }
}

/**
 * Main function to validate all directories in the repository
 */
function validateAllDirectories() {
  console.log(`\nTemplate Validator for UOR Model Framework`);
  console.log(`${options.dryRun ? '[DRY RUN] ' : ''}Checking directories in: ${modelsRoot}\n`);
  
  // Get all directories to check
  let walkOptions = {};
  if (options.excludeDirs.length > 0) {
    walkOptions.exclude = new RegExp(options.excludeDirs.map(r => r.source).join('|'));
  }
  if (options.includeDirs.length > 0) {
    walkOptions.include = new RegExp(options.includeDirs.map(r => r.source).join('|'));
  }
  
  const directories = fileUtils.walkDirectories(modelsRoot, walkOptions);
  console.log(`Found ${directories.length} directories to check\n`);
  
  // Check each directory
  for (const dirPath of directories) {
    validateDirectory(dirPath);
  }
  
  // Print summary report
  console.log('\n--- Template Validation Summary ---');
  console.log(`Directories checked: ${directories.length}`);
  console.log(`Directories already complete: ${report.complete.length}`);
  console.log(`Files added: ${report.fixed.length}`);
  console.log(`Files skipped: ${report.skipped.length}`);
  console.log(`Errors: ${report.errors.length}`);
  
  if (options.dryRun) {
    console.log('\n[DRY RUN] No changes were made. Run without --dry-run to apply changes.');
  }
  
  if (report.errors.length > 0) {
    console.log('\nErrors:');
    report.errors.forEach(err => {
      console.log(`- ${err.path}: ${err.error}`);
    });
  }
}

// Execute the validation
validateAllDirectories();
