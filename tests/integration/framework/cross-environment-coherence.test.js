/**
 * Cross-Environment Coherence Integration Tests for PrimeOS Framework
 *
 * These tests validate that framework components maintain coherence when
 * operating across different environments (Node.js and Browser).
 */

const assert = require("assert");
const { assertAdaptivePrecision } = require("../../utils/assertions");

// Import framework components
const Base0 = require("../../../src/framework/base0");
const Base1 = require("../../../src/framework/base1");
const Base2 = require("../../../src/framework/base2");
const Base3 = require("../../../src/framework/base3");
const FrameworkMath = require("../../../src/framework/math");

// Environment detection utility
const {
  detectEnvironment,
  createEnvironmentBridge,
} = require("../../utils/environments");

describe("Framework Cross-Environment Coherence", () => {
  // Test utilities
  let environmentBridge;
  let currentEnvironment;

  // Framework components
  let base0, base1, base2, base3;

  // Test data
  const testPatterns = [
    [1, 2, 3, 4, 5],
    [0.1, 0.2, 0.3, 0.4, 0.5],
    [10, 20, 30, 40, 50],
    [-1, -2, -3, -4, -5],
    [1.5, 2.5, 3.5, 4.5, 5.5],
  ];

  before(async function () {
    // Detect environment
    currentEnvironment = detectEnvironment();
    console.log(`Running in ${currentEnvironment} environment`);

    // Create environment bridge - allows sending data between environments
    environmentBridge = createEnvironmentBridge();

    // Initialize framework components
    base0 = new Base0();
    base1 = new Base1();
    base2 = new Base2();
    base3 = new Base3();

    // Skip tests if bridge creation failed
    if (!environmentBridge) {
      console.warn(
        "Environment bridge not available - skipping cross-environment tests",
      );
      this.skip();
    }
  });

  describe("Base0 Cross-Environment Coherence", () => {
    it("should produce consistent results across environments", async function () {
      // Process data in current environment
      const currentResults = testPatterns.map((pattern) =>
        base0.processData(pattern),
      );

      // Send patterns to other environment and get results
      const otherResults = await environmentBridge.runInOtherEnvironment(
        "frameworkBase0Test",
        { patterns: testPatterns },
      );

      // Skip test if other environment results not available
      if (!otherResults) {
        console.warn(
          "Could not get results from other environment - skipping test",
        );
        this.skip();
        return;
      }

      // Compare results between environments
      assert.strictEqual(
        currentResults.length,
        otherResults.length,
        "Result counts should match across environments",
      );

      // Check each result for consistency
      for (let i = 0; i < currentResults.length; i++) {
        // Results may not be identical due to floating point differences between environments,
        // but should be very close
        for (let j = 0; j < currentResults[i].length; j++) {
          assertAdaptivePrecision(
            currentResults[i][j],
            otherResults[i][j],
            1e-10,
            `Result mismatch for pattern ${i}, element ${j}`,
          );
        }
      }
    });
  });

  describe("Base1 Cross-Environment Coherence", () => {
    it("should maintain pattern recognition coherence across environments", async function () {
      // Generate test data
      const testData = testPatterns.map((pattern) => {
        // Add some noise to pattern
        return pattern.map((v) => v + Math.random() * 0.01);
      });

      // Process in current environment
      const currentRecognitions = testData.map((data) =>
        base1.recognizePattern(data),
      );

      // Process in other environment
      const otherRecognitions = await environmentBridge.runInOtherEnvironment(
        "frameworkBase1Test",
        { patterns: testData },
      );

      // Skip test if other environment results not available
      if (!otherRecognitions) {
        console.warn(
          "Could not get results from other environment - skipping test",
        );
        this.skip();
        return;
      }

      // Verify coherence across environments
      assert.strictEqual(
        currentRecognitions.length,
        otherRecognitions.length,
        "Recognition count should match across environments",
      );

      // Check recognition coherence
      for (let i = 0; i < currentRecognitions.length; i++) {
        // Check pattern type
        assert.strictEqual(
          currentRecognitions[i].patternType,
          otherRecognitions[i].patternType,
          `Pattern type should match for pattern ${i}`,
        );

        // Check confidence - allow small variation
        assertAdaptivePrecision(
          currentRecognitions[i].confidence,
          otherRecognitions[i].confidence,
          1e-6,
          `Confidence should be consistent for pattern ${i}`,
        );
      }
    });
  });

  describe("Base2 Integration Cross-Environment Coherence", () => {
    it("should maintain pattern integration coherence across environments", async function () {
      // Generate test patterns
      const patterns = [];
      for (let i = 0; i < 5; i++) {
        patterns.push(
          Array(10)
            .fill(0)
            .map((_, j) => Math.sin(j / 2 + i)),
        );
      }

      // Process in current environment
      const currentResult = base2.integratePatterns(patterns);

      // Process in other environment
      const otherResult = await environmentBridge.runInOtherEnvironment(
        "frameworkBase2Test",
        { patterns },
      );

      // Skip test if other environment results not available
      if (!otherResult) {
        console.warn(
          "Could not get results from other environment - skipping test",
        );
        this.skip();
        return;
      }

      // Verify coherence property
      assertAdaptivePrecision(
        currentResult.coherence,
        otherResult.coherence,
        1e-6,
        "Coherence should be consistent across environments",
      );

      // Verify integrated pattern structure
      assert.strictEqual(
        currentResult.integratedPattern.length,
        otherResult.integratedPattern.length,
        "Integrated pattern length should match",
      );

      // Check integrated pattern values
      for (let i = 0; i < currentResult.integratedPattern.length; i++) {
        assertAdaptivePrecision(
          currentResult.integratedPattern[i],
          otherResult.integratedPattern[i],
          1e-6,
          `Integrated pattern element ${i} should be consistent`,
        );
      }
    });
  });

  describe("Base3 Transformation Cross-Environment Coherence", () => {
    it("should maintain transformation coherence across environments", async function () {
      // Create test input
      const input = {
        patterns: [
          [1, 2, 3, 4, 5],
          [5, 4, 3, 2, 1],
        ],
        coherence: 0.85,
      };

      // Process in current environment
      const currentResult = base3.transformResult(input);

      // Process in other environment
      const otherResult = await environmentBridge.runInOtherEnvironment(
        "frameworkBase3Test",
        { input },
      );

      // Skip test if other environment results not available
      if (!otherResult) {
        console.warn(
          "Could not get results from other environment - skipping test",
        );
        this.skip();
        return;
      }

      // Verify transformation coherence
      assert.strictEqual(
        currentResult.transformationType,
        otherResult.transformationType,
        "Transformation type should match across environments",
      );

      // Verify transformation properties
      assertAdaptivePrecision(
        currentResult.transformationCoherence,
        otherResult.transformationCoherence,
        1e-6,
        "Transformation coherence should be consistent",
      );

      // Check transformed data
      assert.strictEqual(
        currentResult.transformed.length,
        otherResult.transformed.length,
        "Transformed data length should match",
      );

      // Compare transformation matrices
      if (
        currentResult.transformationMatrix &&
        otherResult.transformationMatrix
      ) {
        for (let i = 0; i < currentResult.transformationMatrix.length; i++) {
          for (
            let j = 0;
            j < currentResult.transformationMatrix[i].length;
            j++
          ) {
            assertAdaptivePrecision(
              currentResult.transformationMatrix[i][j],
              otherResult.transformationMatrix[i][j],
              1e-6,
              `Transformation matrix element [${i},${j}] should be consistent`,
            );
          }
        }
      }
    });
  });

  describe("Framework Math Cross-Environment Coherence", () => {
    it("should maintain coherence calculation consistency across environments", async function () {
      // Generate test vectors
      const vectors = Array(10)
        .fill(0)
        .map(() => {
          return Array(3)
            .fill(0)
            .map(() => Math.random() * 2 - 1);
        });

      // Calculate coherence in current environment
      const currentCoherence = FrameworkMath.calculateCoherence(vectors);

      // Calculate in other environment
      const otherCoherence = await environmentBridge.runInOtherEnvironment(
        "frameworkMathTest",
        { vectors },
      );

      // Skip test if other environment results not available
      if (otherCoherence === undefined) {
        console.warn(
          "Could not get results from other environment - skipping test",
        );
        this.skip();
        return;
      }

      // Verify coherence calculation consistency
      assertAdaptivePrecision(
        currentCoherence,
        otherCoherence,
        1e-10,
        "Coherence calculation should be consistent across environments",
      );
    });

    it("should maintain pattern recognition consistency across environments", async function () {
      // Generate test pattern
      const pattern = Array(50)
        .fill(0)
        .map((_, i) => Math.sin(i / 10) + Math.random() * 0.05);

      // Recognize pattern in current environment
      const currentResult = FrameworkMath.recognizePatterns(pattern);

      // Recognize in other environment
      const otherResult = await environmentBridge.runInOtherEnvironment(
        "frameworkPatternTest",
        { pattern },
      );

      // Skip test if other environment results not available
      if (!otherResult) {
        console.warn(
          "Could not get results from other environment - skipping test",
        );
        this.skip();
        return;
      }

      // Check primary pattern type
      assert.strictEqual(
        currentResult.primaryPattern,
        otherResult.primaryPattern,
        "Primary pattern type should match across environments",
      );

      // Check confidence scores
      Object.keys(currentResult.confidenceScores).forEach((patternType) => {
        assertAdaptivePrecision(
          currentResult.confidenceScores[patternType],
          otherResult.confidenceScores[patternType],
          1e-6,
          `Confidence score for pattern type ${patternType} should be consistent`,
        );
      });
    });
  });

  describe("End-to-End Framework Pipeline Cross-Environment Coherence", () => {
    it("should maintain end-to-end result coherence across environments", async function () {
      // Generate test data
      const testData = Array(3)
        .fill(0)
        .map(() =>
          Array(20)
            .fill(0)
            .map((_, i) => Math.sin(i / 5) + Math.random() * 0.01),
        );

      // Process through entire pipeline in current environment
      const currentResults = processEndToEnd(testData);

      // Process in other environment
      const otherResults = await environmentBridge.runInOtherEnvironment(
        "frameworkPipelineTest",
        { testData },
      );

      // Skip test if other environment results not available
      if (!otherResults) {
        console.warn(
          "Could not get results from other environment - skipping test",
        );
        this.skip();
        return;
      }

      // Verify overall coherence consistency
      assertAdaptivePrecision(
        currentResults.finalCoherence,
        otherResults.finalCoherence,
        1e-6,
        "Final coherence should be consistent across environments",
      );

      // Verify transformation consistency
      assert.strictEqual(
        currentResults.transformationType,
        otherResults.transformationType,
        "Transformation type should match across environments",
      );

      // Check final transformed result structure
      assert.strictEqual(
        currentResults.transformed.length,
        otherResults.transformed.length,
        "Transformed result length should match",
      );
    });
  });

  // Helper function to process data through the entire framework pipeline
  function processEndToEnd(inputData) {
    // Process through all layers
    const base0Results = inputData.map((data) => base0.processData(data));
    const base1Results = base0Results.map((result) =>
      base1.recognizePattern(result),
    );
    const base2Result = base2.integratePatterns(base1Results);
    const base3Result = base3.transformResult(base2Result);

    return {
      finalCoherence: base3Result.transformationCoherence,
      transformationType: base3Result.transformationType,
      transformed: base3Result.transformed,
    };
  }
});
