/**
 * Performance Benchmarks for PrimeOS Distributed Coherence
 * Measures coherence checking performance under different workloads
 */

// Import Prime with the Distributed module
const Prime = require("../src");

// Test data generation utilities
const generateRandomMatrix = (rows, cols) => {
  return Array.from({ length: rows }, () => 
    Array.from({ length: cols }, () => Math.random() * 2 - 1)
  );
};

const generateRandomVector = (size) => {
  return Array.from({ length: size }, () => Math.random() * 2 - 1);
};

const introduceNumericalInstability = (matrix, probability = 0.05) => {
  const result = JSON.parse(JSON.stringify(matrix)); // Deep copy
  
  for (let i = 0; i < result.length; i++) {
    for (let j = 0; j < result[i].length; j++) {
      if (Math.random() < probability) {
        // Introduce NaN or Infinity
        result[i][j] = Math.random() < 0.5 ? NaN : Infinity;
      }
    }
  }
  
  return result;
};

const createDataset = (sizes, configGenerator) => {
  const dataset = [];
  
  for (const size of sizes) {
    const config = configGenerator(size);
    dataset.push({
      size,
      ...config
    });
  }
  
  return dataset;
};

/**
 * Run coherence benchmarks
 */
const runCoherenceBenchmarks = async () => {
  console.log("=== Running Distributed Coherence Performance Benchmarks ===\n");
  
  // Create a benchmark suite
  const benchmarkSuite = new Prime.Distributed.Benchmark.BenchmarkSuite({
    id: 'distributed_coherence_benchmarks',
    options: {
      iterations: 20,
      warmupIterations: 5,
      reportProgress: true,
      captureMemory: true
    }
  });
  
  // Register coherence calculation benchmark for different matrix sizes
  benchmarkSuite.register('tensor_coherence', async (context) => {
    // Create matrix sizes to test
    const matrixSizes = [10, 50, 100, 200, 500, 1000];
    const size = matrixSizes[context.iteration % matrixSizes.length];
    
    // Create coherence manager
    const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
    
    // Create test layer
    const layer = {
      id: "benchmark_layer",
      config: {
        inputSize: size,
        outputSize: size
      },
      weights: generateRandomMatrix(size, size),
      biases: generateRandomVector(size)
    };
    
    // Measure coherence checking time
    const startTime = performance.now();
    const result = coherenceManager.checkLayerCoherence(layer);
    const endTime = performance.now();
    
    return {
      matrixSize: size,
      coherenceScore: result.coherenceScore,
      checkTime: endTime - startTime,
      dimensionsValid: result.dimensionsValid,
      violationCount: result.violations.length
    };
  }, {
    type: Prime.Distributed.Benchmark.BenchmarkType.COMPUTATION,
    description: 'Benchmark tensor coherence calculation performance',
    tags: ['coherence', 'tensor', 'calculation']
  });

  // Register coherence calculation benchmark for numerical instability detection
  benchmarkSuite.register('numerical_instability', async (context) => {
    // Create matrix sizes to test
    const matrixSizes = [10, 50, 100, 200, 500];
    const instabilityLevels = [0.01, 0.05, 0.1, 0.2];
    
    const size = matrixSizes[context.iteration % matrixSizes.length];
    const instabilityLevel = instabilityLevels[Math.floor(context.iteration / matrixSizes.length) % instabilityLevels.length];
    
    // Create coherence manager
    const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
    
    // Create unstable test layer
    const layer = {
      id: "unstable_layer",
      config: {
        inputSize: size,
        outputSize: size
      },
      weights: introduceNumericalInstability(generateRandomMatrix(size, size), instabilityLevel),
      biases: generateRandomVector(size)
    };
    
    // Measure coherence checking time
    const startTime = performance.now();
    const result = coherenceManager.checkLayerCoherence(layer);
    const endTime = performance.now();
    
    return {
      matrixSize: size,
      instabilityLevel,
      coherenceScore: result.coherenceScore,
      checkTime: endTime - startTime,
      violationCount: result.violations.length
    };
  }, {
    type: Prime.Distributed.Benchmark.BenchmarkType.COMPUTATION,
    description: 'Benchmark numerical instability detection performance',
    tags: ['coherence', 'numerical', 'instability']
  });

  // Register coherence correction benchmark
  benchmarkSuite.register('coherence_correction', async (context) => {
    // Create matrix sizes to test
    const matrixSizes = [10, 50, 100, 200, 500];
    const instabilityLevels = [0.05, 0.1, 0.2];
    
    const size = matrixSizes[context.iteration % matrixSizes.length];
    const instabilityLevel = instabilityLevels[Math.floor(context.iteration / matrixSizes.length) % instabilityLevels.length];
    
    // Create coherence manager
    const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
    
    // Create unstable test layer
    const layer = {
      id: "correction_layer",
      config: {
        inputSize: size,
        outputSize: size
      },
      weights: introduceNumericalInstability(generateRandomMatrix(size, size), instabilityLevel),
      biases: introduceNumericalInstability(generateRandomVector(size), instabilityLevel)
    };
    
    // Measure coherence checking and correction time
    const checkStartTime = performance.now();
    const checkResult = coherenceManager.checkLayerCoherence(layer);
    const checkEndTime = performance.now();
    
    const correctionStartTime = performance.now();
    const correctionResult = coherenceManager.applyCoherenceCorrection(
      layer, 
      checkResult.violations
    );
    const correctionEndTime = performance.now();
    
    // Verify correction with another check
    const verifyStartTime = performance.now();
    const verifyResult = coherenceManager.checkLayerCoherence(layer);
    const verifyEndTime = performance.now();
    
    return {
      matrixSize: size,
      instabilityLevel,
      initialCoherenceScore: checkResult.coherenceScore,
      finalCoherenceScore: verifyResult.coherenceScore,
      initialViolations: checkResult.violations.length,
      finalViolations: verifyResult.violations.length,
      checkTime: checkEndTime - checkStartTime,
      correctionTime: correctionEndTime - correctionStartTime,
      verifyTime: verifyEndTime - verifyStartTime,
      correctionApplied: correctionResult.applied,
      corrections: correctionResult.corrections
    };
  }, {
    type: Prime.Distributed.Benchmark.BenchmarkType.COMPUTATION,
    description: 'Benchmark coherence correction performance',
    tags: ['coherence', 'correction', 'performance']
  });

  // Register global coherence assessment benchmark
  benchmarkSuite.register('global_coherence', async (context) => {
    // Create node counts to test
    const nodeCounts = [2, 4, 8, 16, 32];
    const nodeCount = nodeCounts[context.iteration % nodeCounts.length];
    
    // Create coherence manager
    const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
    
    // Create node coherence results
    const nodeResults = [];
    
    // Some nodes have good coherence
    for (let i = 0; i < Math.ceil(nodeCount * 0.7); i++) {
      nodeResults.push({
        nodeId: `node_${i}`,
        coherenceScore: 0.9 + (Math.random() * 0.1),
        isCoherent: true,
        violations: []
      });
    }
    
    // Some nodes have marginal coherence
    for (let i = Math.ceil(nodeCount * 0.7); i < Math.ceil(nodeCount * 0.9); i++) {
      nodeResults.push({
        nodeId: `node_${i}`,
        coherenceScore: 0.6 + (Math.random() * 0.2),
        isCoherent: Math.random() > 0.5,
        violations: Math.random() > 0.5 ? [] : [
          {
            type: Prime.Distributed.Coherence.CoherenceViolationType.SYNCHRONIZATION,
            severity: Prime.Distributed.Coherence.ViolationSeverity.LOW,
            message: "Minor synchronization issue"
          }
        ]
      });
    }
    
    // Some nodes have poor coherence
    for (let i = Math.ceil(nodeCount * 0.9); i < nodeCount; i++) {
      nodeResults.push({
        nodeId: `node_${i}`,
        coherenceScore: 0.2 + (Math.random() * 0.3),
        isCoherent: false,
        violations: [
          {
            type: Prime.Distributed.Coherence.CoherenceViolationType.NUMERICAL,
            severity: Prime.Distributed.Coherence.ViolationSeverity.HIGH,
            message: "Numerical instability detected"
          },
          {
            type: Prime.Distributed.Coherence.CoherenceViolationType.SYNCHRONIZATION,
            severity: Prime.Distributed.Coherence.ViolationSeverity.MEDIUM,
            message: "Parameters out of sync"
          }
        ]
      });
    }
    
    // Measure global coherence assessment time
    const startTime = performance.now();
    const result = coherenceManager.assessGlobalCoherence(nodeResults);
    const endTime = performance.now();
    
    return {
      nodeCount,
      globalCoherenceScore: result.score,
      globalCoherentStatus: result.isCoherent,
      coherentNodeRatio: result.coherentNodeRatio,
      assessmentTime: endTime - startTime,
      recommendedRecovery: result.recovery?.strategy || "none"
    };
  }, {
    type: Prime.Distributed.Benchmark.BenchmarkType.SYSTEM,
    description: 'Benchmark global coherence assessment performance',
    tags: ['coherence', 'global', 'assessment']
  });

  // Register synchronization coherence benchmark
  benchmarkSuite.register('sync_coherence', async (context) => {
    // Create matrix sizes to test
    const matrixSizes = [10, 50, 100, 200, 500];
    const deviationLevels = [0.01, 0.05, 0.1, 0.5, 1.0];
    
    const size = matrixSizes[context.iteration % matrixSizes.length];
    const deviationLevel = deviationLevels[Math.floor(context.iteration / matrixSizes.length) % deviationLevels.length];
    
    // Create coherence manager
    const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager({
      thresholds: {
        synchronization: 0.05
      }
    });
    
    // Create global parameters
    const globalParams = {
      weights: generateRandomMatrix(size, size),
      biases: generateRandomVector(size)
    };
    
    // Create local parameters with deviations
    const localParams = {
      weights: JSON.parse(JSON.stringify(globalParams.weights)),
      biases: JSON.parse(JSON.stringify(globalParams.biases))
    };
    
    // Apply deviations
    for (let i = 0; i < localParams.weights.length; i++) {
      for (let j = 0; j < localParams.weights[i].length; j++) {
        localParams.weights[i][j] += deviationLevel * (Math.random() * 2 - 1);
      }
    }
    
    for (let i = 0; i < localParams.biases.length; i++) {
      localParams.biases[i] += deviationLevel * (Math.random() * 2 - 1);
    }
    
    // Create layer for testing
    const layer = {
      id: "sync_layer",
      config: {
        inputSize: size,
        outputSize: size
      },
      weights: localParams.weights,
      biases: localParams.biases
    };
    
    // Measure sync coherence checking time
    const startTime = performance.now();
    const result = coherenceManager.checkLayerCoherence(layer, {
      isDistributed: true,
      globalParams
    });
    const endTime = performance.now();
    
    // Check if we have synchronization results
    let syncCoherence = null;
    let syncViolation = null;
    
    if (result.checks && result.checks.synchronization) {
      syncCoherence = result.checks.synchronization.coherence;
    }
    
    if (result.violations) {
      syncViolation = result.violations.find(v => 
        v.type === Prime.Distributed.Coherence.CoherenceViolationType.SYNCHRONIZATION
      );
    }
    
    return {
      matrixSize: size,
      deviationLevel,
      syncCoherence: syncCoherence,
      overallCoherence: result.coherenceScore,
      checkTime: endTime - startTime,
      hasSyncViolation: !!syncViolation,
      violationSeverity: syncViolation ? syncViolation.severity : 'none'
    };
  }, {
    type: Prime.Distributed.Benchmark.BenchmarkType.COMPUTATION,
    description: 'Benchmark parameter synchronization coherence performance',
    tags: ['coherence', 'synchronization', 'performance']
  });

  // Register scaling benchmark for coherence checking
  Prime.Distributed.Benchmark.CoherenceBenchmarks.registerTo(benchmarkSuite, {
    matrixSizes: [10, 50, 100, 200, 500, 1000]
  });
  
  // Measure scaling performance
  console.log("Measuring scaling performance for coherence calculation...");
  const scalingResult = await benchmarkSuite.measureScaling('tensor_coherence', {
    nodeCounts: [1, 2, 4, 8],
    iterations: 10
  });
  
  console.log(`Optimal node count: ${scalingResult.optimalNodeCount}`);
  
  // Run all benchmarks
  console.log("Running all coherence benchmarks...");
  const results = await benchmarkSuite.runAll();
  
  // Generate report
  const report = benchmarkSuite.generateReport({
    format: 'text',
    sortBy: 'duration'
  });
  
  console.log("\n=== Benchmark Report ===\n");
  console.log(report);
  
  return {
    benchmarkSuite,
    results,
    scalingResult
  };
};

// Run the benchmarks
try {
  runCoherenceBenchmarks().catch(error => {
    console.error("Benchmark failed:", error.message);
    console.error(error.stack);
    process.exit(1);
  });
} catch (error) {
  console.error("Benchmark setup failed:", error.message);
  console.error(error.stack);
  process.exit(1);
}