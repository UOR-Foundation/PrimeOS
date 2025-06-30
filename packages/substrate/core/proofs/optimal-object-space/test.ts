// Comprehensive Test Suite for Optimal Object Space Proof
// Outputs detailed JSON diagnostics for analysis

import * as fs from 'fs';
import * as path from 'path';
import { 
  createOptimalObjectSpaceProof, 
  runAllTests, 
  testDataGenerators,
  EncoderOptions
} from './index';

interface TestResult {
  testName: string;
  passed: boolean;
  duration: number;
  compressionRatio: number;
  matchRate: number;
  details: any;
}

interface TestSummary {
  timestamp: string;
  totalTests: number;
  passed: number;
  failed: number;
  averageCompression: number;
  averageMatchRate: number;
  configurations: TestConfiguration[];
}

interface TestConfiguration {
  name: string;
  options: Partial<EncoderOptions>;
  results: TestResult[];
}

async function runTestConfiguration(
  name: string, 
  options: Partial<EncoderOptions>
): Promise<TestConfiguration> {
  console.log(`\n=== Running Test Configuration: ${name} ===`);
  
  const results: TestResult[] = [];
  const proof = createOptimalObjectSpaceProof(options);
  
  for (const generator of testDataGenerators) {
    const startTime = Date.now();
    console.log(`Testing ${generator.name}...`);
    
    try {
      const testData = generator.generate();
      const result = await proof.runProof(testData, options);
      
      const testResult: TestResult = {
        testName: generator.name,
        passed: result.valid,
        duration: Date.now() - startTime,
        compressionRatio: result.encoderDiagnostics.compressionRatio,
        matchRate: result.encoderDiagnostics.matches.percentage,
        details: {
          encoder: result.encoderDiagnostics,
          decoder: result.decoderDiagnostics,
          metadata: result.encoded.metadata
        }
      };
      
      results.push(testResult);
      
      // Write individual test diagnostics
      const diagnosticsDir = path.join(__dirname, 'diagnostics', name);
      if (!fs.existsSync(diagnosticsDir)) {
        fs.mkdirSync(diagnosticsDir, { recursive: true });
      }
      
      fs.writeFileSync(
        path.join(diagnosticsDir, `${generator.name}.json`),
        JSON.stringify({
          generator: {
            name: generator.name,
            description: generator.description,
            expectedMatchRate: generator.expectedMatchRate
          },
          result: testResult
        }, null, 2)
      );
      
      console.log(`  ✓ ${generator.name}: ${result.valid ? 'PASSED' : 'FAILED'}`);
      console.log(`    Compression: ${testResult.compressionRatio.toFixed(2)}x`);
      console.log(`    Match rate: ${testResult.matchRate.toFixed(1)}%`);
      
    } catch (error) {
      console.error(`  ✗ ${generator.name}: ERROR - ${error}`);
      results.push({
        testName: generator.name,
        passed: false,
        duration: Date.now() - startTime,
        compressionRatio: 0,
        matchRate: 0,
        details: { error: String(error) }
      });
    }
  }
  
  return { name, options, results };
}

async function runComprehensiveTests() {
  console.log('=== Optimal Object Space Proof - Comprehensive Test Suite ===');
  console.log(`Starting at: ${new Date().toISOString()}`);
  
  const configurations: TestConfiguration[] = [];
  
  // Test Configuration 1: Full features
  configurations.push(await runTestConfiguration('full-features', {
    useBase768: true,
    useFull12288: true,
    useDomainPatterns: true,
    useResonanceDict: true,
    useConservationCheck: true,
    enableLearning: true,
    learningThreshold: 3,
    maxGroupSearchDepth: 100,
    cacheSize: 1000
  }));
  
  // Test Configuration 2: Base 768 only
  configurations.push(await runTestConfiguration('base-768-only', {
    useBase768: true,
    useFull12288: false,
    useDomainPatterns: false,
    useResonanceDict: true,
    useConservationCheck: true,
    enableLearning: false,
    learningThreshold: 3,
    maxGroupSearchDepth: 0,
    cacheSize: 0
  }));
  
  // Test Configuration 3: With domain patterns but no group transforms
  configurations.push(await runTestConfiguration('domain-patterns-only', {
    useBase768: true,
    useFull12288: false,
    useDomainPatterns: true,
    useResonanceDict: true,
    useConservationCheck: true,
    enableLearning: true,
    learningThreshold: 2,
    maxGroupSearchDepth: 0,
    cacheSize: 500
  }));
  
  // Test Configuration 4: Full 12,288 without domain patterns
  configurations.push(await runTestConfiguration('full-12288-no-domain', {
    useBase768: true,
    useFull12288: true,
    useDomainPatterns: false,
    useResonanceDict: true,
    useConservationCheck: true,
    enableLearning: false,
    learningThreshold: 5,
    maxGroupSearchDepth: 200,
    cacheSize: 2000
  }));
  
  // Calculate summary statistics
  let totalTests = 0;
  let passedTests = 0;
  let totalCompression = 0;
  let totalMatchRate = 0;
  
  for (const config of configurations) {
    for (const result of config.results) {
      totalTests++;
      if (result.passed) passedTests++;
      totalCompression += result.compressionRatio;
      totalMatchRate += result.matchRate;
    }
  }
  
  const summary: TestSummary = {
    timestamp: new Date().toISOString(),
    totalTests,
    passed: passedTests,
    failed: totalTests - passedTests,
    averageCompression: totalCompression / totalTests,
    averageMatchRate: totalMatchRate / totalTests,
    configurations
  };
  
  // Write summary
  const diagnosticsDir = path.join(__dirname, 'diagnostics');
  if (!fs.existsSync(diagnosticsDir)) {
    fs.mkdirSync(diagnosticsDir, { recursive: true });
  }
  
  fs.writeFileSync(
    path.join(diagnosticsDir, 'summary.json'),
    JSON.stringify(summary, null, 2)
  );
  
  // Generate performance comparison
  const performanceComparison = configurations.map(config => ({
    configuration: config.name,
    features: config.options,
    performance: {
      averageCompression: 
        config.results.reduce((sum, r) => sum + r.compressionRatio, 0) / config.results.length,
      averageMatchRate: 
        config.results.reduce((sum, r) => sum + r.matchRate, 0) / config.results.length,
      totalDuration: 
        config.results.reduce((sum, r) => sum + r.duration, 0)
    },
    testBreakdown: config.results.map(r => ({
      test: r.testName,
      compression: r.compressionRatio.toFixed(2),
      matchRate: r.matchRate.toFixed(1),
      passed: r.passed
    }))
  }));
  
  fs.writeFileSync(
    path.join(diagnosticsDir, 'performance-comparison.json'),
    JSON.stringify(performanceComparison, null, 2)
  );
  
  // Generate pattern analysis
  const patternAnalysis: any = {};
  
  for (const config of configurations) {
    patternAnalysis[config.name] = {};
    
    for (const result of config.results) {
      if (result.details?.encoder?.patternFrequencies) {
        patternAnalysis[config.name][result.testName] = {
          uniquePatterns: result.details.encoder.patternFrequencies.size,
          topPatterns: result.details.encoder.topPatterns,
          resonanceDistribution: Array.from(
            result.details.encoder.resonanceDistribution.entries()
          ).sort((a, b) => b[1] - a[1]).slice(0, 10)
        };
      }
    }
  }
  
  fs.writeFileSync(
    path.join(diagnosticsDir, 'pattern-analysis.json'),
    JSON.stringify(patternAnalysis, null, 2)
  );
  
  // Console summary
  console.log('\n=== Test Summary ===');
  console.log(`Total Tests: ${totalTests}`);
  console.log(`Passed: ${passedTests}`);
  console.log(`Failed: ${totalTests - passedTests}`);
  console.log(`Average Compression: ${summary.averageCompression.toFixed(2)}x`);
  console.log(`Average Match Rate: ${summary.averageMatchRate.toFixed(1)}%`);
  
  console.log('\n=== Configuration Comparison ===');
  for (const perf of performanceComparison) {
    console.log(`\n${perf.configuration}:`);
    console.log(`  Average Compression: ${perf.performance.averageCompression.toFixed(2)}x`);
    console.log(`  Average Match Rate: ${perf.performance.averageMatchRate.toFixed(1)}%`);
    console.log(`  Total Duration: ${perf.performance.totalDuration}ms`);
  }
  
  console.log('\n=== Diagnostics Written ===');
  console.log(`Location: ${diagnosticsDir}`);
  console.log('Files:');
  console.log('  - summary.json');
  console.log('  - performance-comparison.json');
  console.log('  - pattern-analysis.json');
  console.log('  - [configuration]/[test].json (individual test results)');
  
  return summary;
}

// Run tests if this file is executed directly
if (require.main === module) {
  runComprehensiveTests()
    .then(summary => {
      console.log('\n✓ All tests completed successfully');
      process.exit(summary.failed > 0 ? 1 : 0);
    })
    .catch(error => {
      console.error('\n✗ Test suite failed:', error);
      process.exit(1);
    });
}

export { runComprehensiveTests, runTestConfiguration };