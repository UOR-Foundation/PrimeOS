#!/usr/bin/env node

/**
 * PrimeOS Verification Test Runner
 *
 * This script runs the end-to-end verification tests that evaluate problems
 * only PrimeOS can solve, serving as the definitive verification of PrimeOS's
 * unique capabilities.
 *
 * These tests evaluate the actual implemented functionality of the PrimeOS
 * system and prove its capabilities for solving problems that traditional
 * computing systems cannot address effectively.
 */

const { runAllTests } = require("../../tests/prime-os-verification-tests");
const { performance } = require("perf_hooks");

// Parse command line arguments
const args = process.argv.slice(2);
const options = {
  verbosity: 1,
  seed: 42,
  timeout: 5 * 60 * 1000, // 5 minutes default
  testPattern: null,
};

// Process arguments
for (let i = 0; i < args.length; i++) {
  const arg = args[i];

  if (arg === "--verbose" || arg === "-v") {
    options.verbosity = 2;
  } else if (arg === "--quiet" || arg === "-q") {
    options.verbosity = 0;
  } else if (arg === "--seed" && i + 1 < args.length) {
    options.seed = parseInt(args[++i], 10);
  } else if (arg === "--timeout" && i + 1 < args.length) {
    options.timeout = parseInt(args[++i], 10) * 1000; // Convert to ms
  } else if (arg === "--json") {
    options.outputJson = true;
  } else if (arg === "--output" && i + 1 < args.length) {
    options.outputPath = args[++i];
  } else if (arg === "--help" || arg === "-h") {
    console.log("\nPrimeOS Verification Test Runner");
    console.log("Usage: node run-verification-tests.js [options]");
    console.log("\nOptions:");
    console.log("  --verbose, -v       Enable detailed output");
    console.log("  --quiet, -q         Suppress non-essential output");
    console.log("  --seed NUMBER       Set random seed (default: 42)");
    console.log(
      "  --timeout SECONDS   Set test timeout in seconds (default: 300)",
    );
    console.log("  --test PATTERN      Run tests matching pattern");
    console.log("  --json              Output results in JSON format");
    console.log("  --output PATH       Specify output path for JSON report");
    console.log("  --help, -h          Show this help message");
    process.exit(0);
  } else if (arg === "--test" && i + 1 < args.length) {
    options.testPattern = args[++i];
  }
}

// Configure test execution based on options
global.testConfig = {
  verbosity: options.verbosity,
  randomSeed: options.seed,
  maxTestTime: options.timeout,
  testPattern: options.testPattern,
};

// Print banner
console.log("=================================================");
console.log("|                                               |");
console.log("|      PrimeOS End-to-End Verification Suite    |");
console.log("|                                               |");
console.log("=================================================");
console.log(
  `Verbosity: ${options.verbosity === 0 ? "Quiet" : options.verbosity === 1 ? "Normal" : "Verbose"}`,
);
console.log(`Random seed: ${options.seed}`);
console.log(`Timeout: ${options.timeout / 1000} seconds`);
if (options.testPattern) {
  console.log(`Test pattern: ${options.testPattern}`);
}
console.log("-------------------------------------------------");

// Configure test execution based on options
if (options.outputJson) {
  if (!options.outputPath) {
    // Default output path
    options.outputPath = "test-results/verification-report.json";
  }

  // Ensure directory exists
  const fs = require("fs");
  const path = require("path");
  const dir = path.dirname(options.outputPath);

  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir, { recursive: true });
  }
}

// Run the tests and handle result
const startTime = performance.now();

runAllTests()
  .then((success) => {
    const endTime = performance.now();
    const duration = (endTime - startTime) / 1000;

    console.log("\n=================================================");
    console.log(`Total execution time: ${duration.toFixed(2)} seconds`);
    console.log("=================================================");

    if (success) {
      console.log(
        "\n✅ VERIFICATION SUCCESSFUL: PrimeOS has demonstrated its unique capabilities",
      );

      // Output JSON report if requested
      if (options.outputJson) {
        const fs = require("fs");
        const report = {
          success: true,
          timestamp: new Date().toISOString(),
          duration: duration,
          results: testResults ? testResults.details : {},
          summary: testResults
            ? {
                passed: testResults.passed,
                failed: testResults.failed,
                skipped: testResults.skipped,
                totalTime: testResults.totalTime,
              }
            : {},
        };

        fs.writeFileSync(options.outputPath, JSON.stringify(report, null, 2));
        console.log(`\nTest report written to ${options.outputPath}`);
      }

      // Ensure the process exits properly
      setTimeout(() => process.exit(0), 100);
    } else {
      console.log("\n❌ VERIFICATION INCOMPLETE: Some tests did not pass");

      // Output JSON report if requested
      if (options.outputJson) {
        const fs = require("fs");
        const report = {
          success: false,
          timestamp: new Date().toISOString(),
          duration: duration,
          results: testResults ? testResults.details : {},
          summary: testResults
            ? {
                passed: testResults.passed,
                failed: testResults.failed,
                skipped: testResults.skipped,
                totalTime: testResults.totalTime,
              }
            : {},
        };

        fs.writeFileSync(options.outputPath, JSON.stringify(report, null, 2));
        console.log(`\nTest report written to ${options.outputPath}`);
      }

      process.exit(1);
    }
  })
  .catch((error) => {
    console.error("\nFATAL ERROR IN TEST SUITE:");
    console.error(error);

    // Output error report if JSON requested
    if (options.outputJson) {
      const fs = require("fs");
      const report = {
        success: false,
        timestamp: new Date().toISOString(),
        error: error.message,
        stack: error.stack,
      };

      fs.writeFileSync(options.outputPath, JSON.stringify(report, null, 2));
      console.log(`\nError report written to ${options.outputPath}`);
    }

    process.exit(1);
  });
