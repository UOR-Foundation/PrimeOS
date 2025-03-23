/**
 * Test Cleanup Script
 *
 * This script helps clean up the old test files that were part of the
 * previous test structure. It marks them as deprecated and reminds
 * users to use the new test structure instead.
 */

const fs = require("fs");
const path = require("path");

// List of test files directly under tests/ that need to be cleaned up
const oldTestFiles = [
  "attention-mechanism-tests.js",
  "coherence-tests.js",
  "coherence-validator-refactor-test.js",
  "coherence-verification-patched.js",
  "coherence-verification.js",
  "consciousness-integration-tests.js",
  "consciousness-module-tests.js",
  "consciousness-tests.js",
  "conv-memory-test.js",
  "core-tests.js",
  "distributed-coherence-benchmarks.js",
  "distributed-coherence-integration-tests.js",
  "distributed-coherence-mock-network.js",
  "distributed-integration-test.js",
  "distributed-pipeline-tests.js",
  "distributed-tests.js",
  "distributed-training-test.js",
  "extreme-conditions-basic-test.js",
  "extreme-conditions-tests.js",
  "framework-tests.js",
  "integration-tests.js",
  "manifold-operations-tests.js",
  "mathematics-tests.js",
  "matrix-edge-cases-tests.js",
  "matrix-extreme-values-svd-tests.js",
  "matrix-extreme-values-svd.js",
  "matrix-extreme-values-tests.js",
  "matrix-refactor-tests.js",
  "matrix-stability-test.js",
  "model-management-test.js",
  "neural-advanced-tests.js",
  "neural-distributed-test.js",
  "neural-model-test.js",
  "neural-refactor-test.js",
  "neural-tests.js",
  "pattern-recognition-tests.js",
  "prime-math-tests.js",
  "prime-os-verification-tests.js",
  "refactor-verification.js",
  "svd-basic-test.js",
  "uor-verification-tests.js",
  "vector-refactor-test.js",
];

// Mapping of old test files to their new locations
const migrationMap = {
  "attention-mechanism-tests.js": "unit/consciousness/attention.test.js",
  "coherence-tests.js": "unit/coherence/verification.test.js",
  "coherence-validator-refactor-test.js": "unit/coherence/validator.test.js",
  "coherence-verification-patched.js": "unit/coherence/verification.test.js",
  "coherence-verification.js": "unit/coherence/verification.test.js",
  "consciousness-integration-tests.js":
    "integration/consciousness/memory-temporal.test.js",
  "consciousness-module-tests.js": "unit/consciousness/module.test.js",
  "consciousness-tests.js": "unit/consciousness/module.test.js",
  "conv-memory-test.js": "unit/consciousness/memory.test.js",
  "core-tests.js": "unit/core/",
  "distributed-coherence-benchmarks.js": "performance/distributed/",
  "distributed-coherence-integration-tests.js":
    "integration/distributed/partition-coherence.test.js",
  "distributed-coherence-mock-network.js":
    "unit/distributed/communication.test.js",
  "distributed-integration-test.js":
    "integration/distributed/cluster-communication.test.js",
  "distributed-pipeline-tests.js":
    "integration/distributed/training-pipeline.test.js",
  "distributed-tests.js": "unit/distributed/",
  "distributed-training-test.js": "unit/distributed/training.test.js",
  "extreme-conditions-basic-test.js":
    "extreme/math/matrix-operations-extreme.test.js",
  "extreme-conditions-tests.js":
    "extreme/math/matrix-operations-extreme.test.js",
  "framework-tests.js": "unit/framework/",
  "integration-tests.js": "integration/",
  "manifold-operations-tests.js": "unit/math/lie-groups.test.js",
  "mathematics-tests.js": "unit/math/",
  "matrix-edge-cases-tests.js": "extreme/math/matrix-extreme.test.js",
  "matrix-extreme-values-svd-tests.js": "extreme/math/svd-extreme.test.js",
  "matrix-extreme-values-svd.js": "extreme/math/svd-extreme.test.js",
  "matrix-extreme-values-tests.js": "extreme/math/matrix-extreme.test.js",
  "matrix-refactor-tests.js": "unit/math/matrix.test.js",
  "matrix-stability-test.js": "extreme/math/matrix-operations-extreme.test.js",
  "model-management-test.js": "unit/neural/model.test.js",
  "neural-advanced-tests.js": "unit/neural/",
  "neural-distributed-test.js":
    "integration/distributed/training-pipeline.test.js",
  "neural-model-test.js": "unit/neural/model.test.js",
  "neural-refactor-test.js": "unit/neural/model.test.js",
  "neural-tests.js": "unit/neural/",
  "pattern-recognition-tests.js": "unit/framework/base1.test.js",
  "prime-math-tests.js": "unit/math/precision.test.js",
  "prime-os-verification-tests.js": "unit/core/",
  "refactor-verification.js": "unit/coherence/verification.test.js",
  "svd-basic-test.js": "unit/math/matrix.test.js",
  "uor-verification-tests.js": "unit/coherence/uor.test.js",
  "vector-refactor-test.js": "unit/math/vector.test.js",
};

// Add a deprecation notice to each file
const deprecationNotice = `
/**
 * @deprecated This test file has been migrated to the new test structure.
 * Please use the following file(s) instead:
 * {replacementPaths}
 * 
 * This file will be removed in a future release.
 * See tests/tests-refactor-plan.md for details on the test refactoring.
 */

// Original file content below:
`;

// Function to add deprecation notice to a file
function addDeprecationNotice(filePath, replacementPath) {
  const testsDir = path.resolve(__dirname);
  const fullPath = path.join(testsDir, filePath);

  if (!fs.existsSync(fullPath)) {
    console.log(`File does not exist: ${fullPath}`);
    return;
  }

  try {
    // Read original file content
    const content = fs.readFileSync(fullPath, "utf8");

    // Skip if already has deprecation notice
    if (content.includes("@deprecated")) {
      console.log(`File already has deprecation notice: ${filePath}`);
      return;
    }

    // Format replacement paths
    const replacements = replacementPath
      .split(",")
      .map((p) => `* - ${p.trim()}`)
      .join("\n");

    // Add deprecation notice
    const newContent =
      deprecationNotice.replace("{replacementPaths}", replacements) + content;

    // Write back to file
    fs.writeFileSync(fullPath, newContent, "utf8");
    console.log(`Added deprecation notice to: ${filePath}`);
  } catch (error) {
    console.error(`Error processing file ${filePath}:`, error);
  }
}

// Create a master deprecation index file
function createDeprecationIndex() {
  const testsDir = path.resolve(__dirname);
  const indexPath = path.join(testsDir, "DEPRECATED-TESTS.md");

  let content = `# Deprecated Test Files
  
This document lists all the deprecated test files from the old test structure
and their replacements in the new structure.

| Old Test File | Replacement(s) |
|---------------|---------------|
`;

  // Add each mapping
  for (const [oldFile, newFiles] of Object.entries(migrationMap)) {
    const replacements = newFiles
      .split(",")
      .map((p) => p.trim())
      .join("<br>");
    content += `| ${oldFile} | ${replacements} |\n`;
  }

  content += `
## Migration Status

All tests from the old structure have been migrated to the new structure.
The old test files are kept temporarily for reference but will be removed
in a future update.

For details on the test refactoring, see [tests-refactor-plan.md](tests-refactor-plan.md).
`;

  // Write the index file
  fs.writeFileSync(indexPath, content, "utf8");
  console.log(`Created deprecation index at: ${indexPath}`);
}

// Main function to process all files
function main() {
  console.log("Adding deprecation notices to old test files...");

  for (const oldFile of oldTestFiles) {
    const replacementPath = migrationMap[oldFile] || "unknown";
    addDeprecationNotice(oldFile, replacementPath);
  }

  createDeprecationIndex();

  console.log("Done!");
}

// Run the script
main();
