/**
 * Test Cleanup Script
 *
 * This script removes the old test files that have been migrated to the new test structure.
 */

const fs = require('fs');
const path = require('path');

// List of test files directly under tests/ that need to be removed
const oldTestFiles = [
  'attention-mechanism-tests.js',
  'coherence-tests.js',
  'coherence-validator-refactor-test.js',
  'coherence-verification-patched.js',
  'coherence-verification.js',
  'consciousness-integration-tests.js',
  'consciousness-module-tests.js',
  'consciousness-tests.js',
  'conv-memory-test.js',
  'core-tests.js',
  'distributed-coherence-benchmarks.js',
  'distributed-coherence-integration-tests.js',
  'distributed-coherence-mock-network.js',
  'distributed-integration-test.js',
  'distributed-pipeline-tests.js',
  'distributed-tests.js',
  'distributed-training-test.js',
  'extreme-conditions-basic-test.js',
  'extreme-conditions-tests.js',
  'framework-tests.js',
  'integration-tests.js',
  'manifold-operations-tests.js',
  'mathematics-tests.js',
  'matrix-edge-cases-tests.js',
  'matrix-extreme-values-svd-tests.js',
  'matrix-extreme-values-svd.js',
  'matrix-extreme-values-tests.js',
  'matrix-refactor-tests.js',
  'matrix-stability-test.js',
  'model-management-test.js',
  'neural-advanced-tests.js',
  'neural-distributed-test.js',
  'neural-model-test.js',
  'neural-refactor-test.js',
  'neural-tests.js',
  'pattern-recognition-tests.js',
  'prime-math-tests.js',
  'prime-os-verification-tests.js',
  'refactor-verification.js',
  'svd-basic-test.js',
  'uor-verification-tests.js',
  'vector-refactor-test.js'
];

// Storage test files to remove
const storageTestFiles = [
  'browser-matrix-storage-tests.js',
  'browser-storage-tests.js',
  'matrix-storage-integration.js',
  'neural-storage-tests.js',
  'node-storage-tests.js',
  'simple-test.js',
  'storage-integration-tests.js',
  'storage-provider-tests.js',
  'verify-matrix-storage.js',
  'simple/matrix-storage-test.js'
];

// Veneer test files to remove
const veneerTestFiles = [
  'coherence-boundaries-tests.js',
  'coherence-integration-tests.js',
  'coherence-manager-tests.js',
  'coherent-app-example-test.js',
  'core-tests.js',
  'loader-registry-integration.test.js',
  'loader-tests.js',
  'resources-manual-test.js',
  'resources.test.js',
];

// Function to remove file
function removeFile(filePath) {
  const testsDir = path.resolve(__dirname, '../tests');
  const fullPath = path.join(testsDir, filePath);
  
  if (!fs.existsSync(fullPath)) {
    console.log(`File does not exist: ${fullPath}`);
    return;
  }
  
  try {
    fs.unlinkSync(fullPath);
    console.log(`Removed: ${filePath}`);
  } catch (error) {
    console.error(`Error removing file ${filePath}:`, error);
  }
}

// Main function to remove all old test files
function main() {
  console.log('Removing old test files...');
  
  // Remove root test files
  for (const oldFile of oldTestFiles) {
    removeFile(oldFile);
  }
  
  // Remove storage test files
  for (const storageFile of storageTestFiles) {
    removeFile(path.join('storage', storageFile));
  }
  
  // Remove veneer test files
  for (const veneerFile of veneerTestFiles) {
    removeFile(path.join('veneer', veneerFile));
  }
  
  console.log('Done!');
}

// Run the script
main();