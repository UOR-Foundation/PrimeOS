#!/usr/bin/env node
// Comprehensive verification of all research scripts

const { execSync } = require('child_process');
const fs = require('fs');
const path = require('path');

console.log('=== COMPREHENSIVE SCRIPT VERIFICATION ===\n');

// Get all JS files in current directory
const scripts = fs.readdirSync('.')
  .filter(f => f.endsWith('.js'))
  .filter(f => f !== 'verify-all-scripts.js')
  .sort();

const results = {
  passed: [],
  failed: [],
  warnings: []
};

// Common issues to check for
const codeIssues = {
  // Mathematical errors
  'slice(48, 48)': 'Empty slice operation - will return empty array',
  'Math.random\\(\\) \\* 256\\) \\| 0': 'Should use Math.floor() for safer integer conversion',
  '=== a && .* === b': 'Incorrect identity check in group operations',
  
  // Arbitrary thresholds without justification
  'threshold = 0\\.1(?!\\d)': 'Arbitrary threshold 0.1 without justification',
  'threshold = 0\\.5(?!\\d)': 'Arbitrary threshold 0.5 without justification', 
  'tolerance = 0\\.9(?!\\d)': 'Arbitrary tolerance 0.9 without justification',
  
  // Incomplete implementations
  'TODO': 'Incomplete implementation marked with TODO',
  'FIXME': 'Known issue marked with FIXME',
  '// Only check.*specific': 'Non-exhaustive analysis',
  'for speed': 'Computational shortcut that may miss results',
  
  // Conceptual issues
  'Dirichlet character': 'Check if actual Dirichlet character properties are satisfied',
  'L-function': 'Check if actual L-function properties are satisfied',
  'modular form': 'Check if actual modular form properties are satisfied',
  
  // Performance issues
  'for \\(let .* = 0; .* < 12288': 'Iterating over full space - consider optimization',
  '\\.slice\\(0, \\d+\\)(?!.*\\.forEach)': 'Limiting results without showing all'
};

console.log(`Verifying ${scripts.length} scripts...\n`);

scripts.forEach(script => {
  console.log(`\nChecking: ${script}`);
  console.log('─'.repeat(50));
  
  const scriptPath = path.join('.', script);
  const content = fs.readFileSync(scriptPath, 'utf8');
  const issues = [];
  
  // 1. Check if script runs without errors
  try {
    execSync(`node ${script}`, { 
      stdio: 'pipe',
      timeout: 30000 // 30 second timeout
    });
    console.log('✓ Runs without errors');
  } catch (error) {
    console.log('✗ Runtime error:', error.message.split('\n')[0]);
    issues.push('Runtime error: ' + error.message.split('\n')[0]);
  }
  
  // 2. Check for code issues
  Object.entries(codeIssues).forEach(([pattern, description]) => {
    const regex = new RegExp(pattern, 'gi');
    const matches = content.match(regex);
    if (matches) {
      const lineNumbers = [];
      const lines = content.split('\n');
      lines.forEach((line, idx) => {
        if (regex.test(line)) {
          lineNumbers.push(idx + 1);
        }
      });
      console.log(`⚠ ${description} (lines: ${lineNumbers.join(', ')})`);
      issues.push(`${description} at lines ${lineNumbers.join(', ')}`);
    }
  });
  
  // 3. Check for mathematical correctness
  
  // Check if resonance calculation is consistent
  if (content.includes('calculateResonance')) {
    const resonanceRegex = /function calculateResonance[^{]*{([^}]+)}/;
    const match = content.match(resonanceRegex);
    if (match && !match[1].includes('for (let i = 0; i < 8; i++)')) {
      console.log('⚠ Non-standard resonance calculation');
      issues.push('Non-standard resonance calculation');
    }
  }
  
  // Check for proper error handling
  if (!content.includes('try') && !content.includes('catch')) {
    console.log('⚠ No error handling (try/catch blocks)');
    issues.push('No error handling');
  }
  
  // Check for proper constant definitions
  if (content.includes('FIELD_CONSTANTS') && !content.includes('const FIELD_CONSTANTS')) {
    console.log('⚠ Uses FIELD_CONSTANTS without defining them');
    issues.push('Missing FIELD_CONSTANTS definition');
  }
  
  // 4. Check for specific known issues
  
  // Unity calculation issues
  if (script.includes('unity') && content.includes('resonance === 1')) {
    console.log('⚠ Exact equality check for floating point (use tolerance)');
    issues.push('Exact floating point equality check');
  }
  
  // Group theory issues  
  if (script.includes('automorphism') || script.includes('group')) {
    if (content.includes('order') && !content.includes('=== 1')) {
      console.log('⚠ Group order calculation may not check for identity');
      issues.push('Group order calculation issue');
    }
  }
  
  // Complexity analysis issues
  if (script.includes('complexity')) {
    if (content.includes('O(2^n)') && content.includes('polynomial')) {
      console.log('⚠ Possible confusion about exponential vs polynomial time');
      issues.push('Complexity class confusion');
    }
  }
  
  // 5. Check for incomplete proofs
  if (content.includes('Proof:') || content.includes('Theorem:')) {
    if (!content.includes('∎') && !content.includes('QED') && !content.includes('proven')) {
      console.log('⚠ Proof appears incomplete (no conclusion marker)');
      issues.push('Incomplete proof');
    }
  }
  
  // Record results
  if (issues.length === 0) {
    results.passed.push(script);
    console.log('\n✅ PASSED - No issues found');
  } else if (issues.some(i => i.includes('Runtime error'))) {
    results.failed.push({ script, issues });
    console.log(`\n❌ FAILED - ${issues.length} issues found`);
  } else {
    results.warnings.push({ script, issues });
    console.log(`\n⚠️  WARNING - ${issues.length} issues found`);
  }
});

// Summary report
console.log('\n\n=== VERIFICATION SUMMARY ===\n');
console.log(`Total scripts: ${scripts.length}`);
console.log(`✅ Passed: ${results.passed.length}`);
console.log(`⚠️  Warnings: ${results.warnings.length}`);
console.log(`❌ Failed: ${results.failed.length}`);

if (results.failed.length > 0) {
  console.log('\n\nFAILED SCRIPTS:');
  results.failed.forEach(({ script, issues }) => {
    console.log(`\n${script}:`);
    issues.forEach(issue => console.log(`  - ${issue}`));
  });
}

if (results.warnings.length > 0) {
  console.log('\n\nSCRIPTS WITH WARNINGS:');
  results.warnings.forEach(({ script, issues }) => {
    console.log(`\n${script}:`);
    issues.forEach(issue => console.log(`  - ${issue}`));
  });
}

console.log('\n\nRECOMMENDATIONS:');
console.log('1. Fix all runtime errors in failed scripts');
console.log('2. Address arbitrary thresholds with theoretical justification');
console.log('3. Complete any TODOs or partial implementations');
console.log('4. Add error handling to scripts without try/catch');
console.log('5. Verify mathematical claims match implementations');

// Write detailed report
const report = {
  timestamp: new Date().toISOString(),
  summary: {
    total: scripts.length,
    passed: results.passed.length,
    warnings: results.warnings.length,
    failed: results.failed.length
  },
  results
};

fs.writeFileSync('verification-report.json', JSON.stringify(report, null, 2));
console.log('\nDetailed report written to verification-report.json');