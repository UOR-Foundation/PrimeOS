/**
 * Comprehensive test runner for the PrimeOS Consciousness Module
 *
 * This script runs all tests related to the Consciousness Module to
 * ensure full test coverage of all components.
 */

// Run individual tests
const runTest = async (name, path) => {
  console.log(`\n=== Running ${name} ===`);
  const start = Date.now();
  try {
    const testModule = require(path);
    if (typeof testModule === "function") {
      await testModule();
    } else if (testModule && typeof testModule.runTests === "function") {
      await testModule.runTests();
    } else {
      // Testing module that self-executes
      console.log(`✓ ${name} tests completed (self-executed)`);
    }
    console.log(`✓ ${name} tests completed in ${Date.now() - start}ms`);
    return true;
  } catch (error) {
    console.error(`❌ ${name} tests failed: ${error.message}`);
    console.error(error.stack);
    return false;
  }
};

// Main test runner
const runAllTests = async () => {
  console.log("==================================================");
  console.log("Running PrimeOS Consciousness Module Tests");
  console.log("==================================================\n");

  const testCases = [
    { name: "Basic Consciousness Components", path: "./test-consciousness.js" },
    {
      name: "Consciousness Module Integration",
      path: "./tests/consciousness-integration-tests.js",
    },
    {
      name: "Consciousness Neural Integration",
      path: "./tests/consciousness-tests.js",
    },
  ];

  const results = [];

  for (const test of testCases) {
    const success = await runTest(test.name, test.path);
    results.push({ name: test.name, success });
  }

  // Print summary
  console.log("\n==================================================");
  console.log("Test Results Summary");
  console.log("==================================================");

  let failed = false;
  for (const result of results) {
    if (result.success) {
      console.log(`✓ ${result.name}: PASSED`);
    } else {
      console.log(`❌ ${result.name}: FAILED`);
      failed = true;
    }
  }

  console.log("\n==================================================");
  const passedCount = results.filter((r) => r.success).length;
  console.log(`${passedCount}/${results.length} test suites PASSED`);
  console.log(`OVERALL STATUS: ${failed ? "FAILURE" : "SUCCESS"}`);
  console.log("==================================================");

  // Return exit code
  process.exit(failed ? 1 : 0);
};

// Execute all tests
runAllTests().catch((error) => {
  console.error("Fatal error in test runner:", error);
  process.exit(1);
});
