// Working example of projection operator π: ℝ^64 → ℝ^48
// Demonstrates dimensional reduction and information preservation

console.log('=== PROJECTION OPERATOR π: ℝ^64 → ℝ^48 EXAMPLE ===\n');

// Field constants
const FIELD_CONSTANTS = [
  1.0, 1.8392867552141612, 1.6180339887498950, 0.5,
  0.15915494309189535, 6.283185307179586, 0.199612, 0.014134725
];

// 1. Basic projection operation
console.log('1. Basic Projection Operation\n');

// Define projection
function project(vector64) {
  return vector64.slice(0, 48);
}

// Define lifting (pseudoinverse)
function lift(vector48) {
  return [...vector48, ...new Array(16).fill(0)];
}

// Example vector
const example64 = Array.from({length: 64}, (_, i) => Math.sin(i * 0.1));
const projected = project(example64);
const lifted = lift(projected);

console.log('Example projection:');
console.log(`  Original vector: 64D with norm ${Math.sqrt(example64.reduce((a,b) => a+b*b, 0)).toFixed(4)}`);
console.log(`  Projected: 48D with norm ${Math.sqrt(projected.reduce((a,b) => a+b*b, 0)).toFixed(4)}`);
console.log(`  Lifted back: 64D with norm ${Math.sqrt(lifted.reduce((a,b) => a+b*b, 0)).toFixed(4)}`);

// Information loss
const hidden = example64.slice(48);
const hiddenNorm = Math.sqrt(hidden.reduce((a,b) => a+b*b, 0));
console.log(`  Lost information (hidden norm): ${hiddenNorm.toFixed(4)}\n`);

// 2. Field pattern transformation
console.log('2. Field Pattern Transformation Under Projection\n');

function calculateResonance(fieldBits) {
  let resonance = 1.0;
  for (let i = 0; i < 8; i++) {
    if ((fieldBits >> i) & 1) {
      resonance *= FIELD_CONSTANTS[i];
    }
  }
  return resonance;
}

function projectFieldPattern(pattern) {
  // Clear fields 6,7 (projection effect)
  return pattern & 0x3F;
}

// Analyze transformation
const transformationMap = new Map();
let preservedCount = 0;

for (let pattern = 0; pattern < 256; pattern++) {
  const original = calculateResonance(pattern);
  const projectedPattern = projectFieldPattern(pattern);
  const projected = calculateResonance(projectedPattern);
  const ratio = projected / original;
  
  if (Math.abs(ratio - 1) < 1e-10) preservedCount++;
  
  const key = ratio.toFixed(6);
  if (!transformationMap.has(key)) {
    transformationMap.set(key, { ratio, count: 0, example: pattern });
  }
  transformationMap.get(key).count++;
}

console.log(`Field patterns preserved exactly: ${preservedCount}/256 (${(preservedCount/256*100).toFixed(1)}%)`);
console.log('\nResonance transformation ratios:');
Array.from(transformationMap.values()).forEach(t => {
  const binary = t.example.toString(2).padStart(8, '0');
  console.log(`  Ratio ${t.ratio.toFixed(6)}: ${t.count} patterns (example: ${binary})`);
});

// 3. Spectral properties
console.log('\n3. Spectral Analysis of π^T π\n');

// For demonstration, show the structure
console.log('Eigenvalue spectrum of π^T π:');
console.log('  λ₁, ..., λ₄₈ = 1 (preserved dimensions)');
console.log('  λ₄₉, ..., λ₆₄ = 0 (projected out)');
console.log('  Spectral gap = 1 - 0 = 1 (maximal)');
console.log('  Condition number = 1 (perfect conditioning)\n');

// 4. Geometric properties
console.log('4. Geometric Properties\n');

// Test distance preservation
function distance(v1, v2) {
  return Math.sqrt(v1.reduce((sum, x, i) => sum + (x - v2[i])**2, 0));
}

const v1 = Array.from({length: 64}, (_, i) => Math.cos(i * 0.1));
const v2 = Array.from({length: 64}, (_, i) => Math.sin(i * 0.1));

const dist64 = distance(v1, v2);
const dist48 = distance(project(v1), project(v2));

console.log('Distance preservation test:');
console.log(`  ||v₁ - v₂||₆₄ = ${dist64.toFixed(4)}`);
console.log(`  ||π(v₁) - π(v₂)||₄₈ = ${dist48.toFixed(4)}`);
console.log(`  Ratio: ${(dist48/dist64).toFixed(4)} ≤ 1 (non-expansive) ✓\n`);

// 5. Fiber bundle structure
console.log('5. Fiber Bundle Visualization\n');

// Show fiber over a point
const basePoint = Array.from({length: 48}, (_, i) => i / 48);
console.log('Fiber over a point in ℝ^48:');
console.log(`  Base point: 48D vector with components [0, 1/48, 2/48, ...]`);
console.log(`  Fiber: All 64D vectors of form:`);
console.log(`    (basePoint, x₄₈, x₄₉, ..., x₆₃) where xᵢ ∈ ℝ`);
console.log(`  Fiber dimension: 16`);
console.log(`  Fiber topology: ℝ^16 (before compactification)\n`);

// 6. Information theory
console.log('6. Information Theoretic Analysis\n');

// Calculate information capacities
const bitsPerFloat = 32;
const full64 = 64 * bitsPerFloat;
const proj48 = 48 * bitsPerFloat;
const hidden16 = 16 * bitsPerFloat;

console.log('Information capacity (32-bit floats):');
console.log(`  Full 64D space: ${full64} bits`);
console.log(`  Projected 48D: ${proj48} bits (${(proj48/full64*100).toFixed(1)}%)`);
console.log(`  Hidden 16D: ${hidden16} bits (${(hidden16/full64*100).toFixed(1)}%)`);
console.log(`  Ratio: ${proj48}:${hidden16} = 3:1\n`);

// 7. Page structure interaction
console.log('7. Interaction with Page Structure\n');

// Analyze how pages map under projection
const pageSize = 48;
console.log('Page mapping under projection:');
for (let page = 0; page <= 3; page++) {
  const start = page * pageSize;
  const end = start + pageSize - 1;
  
  if (end < 48) {
    console.log(`  Page ${page} (dims ${start}-${end}): Preserved exactly`);
  } else if (start < 48) {
    console.log(`  Page ${page} (dims ${start}-${end}): Partially preserved (up to dim 47)`);
  } else {
    console.log(`  Page ${page} (dims ${start}-${end}): Completely in hidden space`);
  }
}

// 8. Reconstruction example
console.log('\n8. Optimal Reconstruction\n');

// Show minimal norm reconstruction
const data48 = Array.from({length: 48}, (_, i) => Math.exp(-i/10));
const minimalLift = lift(data48);

// Add non-minimal reconstruction
const nonMinimalLift = [...data48, ...Array.from({length: 16}, () => Math.random())];

const minNorm = Math.sqrt(minimalLift.reduce((a,b) => a+b*b, 0));
const nonMinNorm = Math.sqrt(nonMinimalLift.reduce((a,b) => a+b*b, 0));

console.log('Reconstruction comparison:');
console.log(`  Original 48D norm: ${Math.sqrt(data48.reduce((a,b) => a+b*b, 0)).toFixed(4)}`);
console.log(`  Minimal lift norm: ${minNorm.toFixed(4)} (using π^T)`);
console.log(`  Non-minimal lift norm: ${nonMinNorm.toFixed(4)} (with random hidden)`);
console.log(`  Minimal is optimal: ${minNorm < nonMinNorm ? 'YES' : 'NO'} ✓\n`);

// 9. Projection invariants
console.log('9. Quantities Invariant Under Projection\n');

// Test various quantities
function testInvariant(name, compute64, compute48) {
  const vec64 = Array.from({length: 64}, (_, i) => Math.sin(i * 0.2) * Math.exp(-i/30));
  const vec48 = project(vec64);
  
  const val64 = compute64(vec64);
  const val48 = compute48(vec48);
  const preserved = Math.abs(val64 - val48) < 1e-10;
  
  return { name, val64, val48, preserved };
}

const invariantTests = [
  {
    name: 'First 48 components sum',
    compute64: v => v.slice(0, 48).reduce((a,b) => a+b, 0),
    compute48: v => v.reduce((a,b) => a+b, 0)
  },
  {
    name: 'L² norm of first 48',
    compute64: v => Math.sqrt(v.slice(0, 48).reduce((a,b) => a+b*b, 0)),
    compute48: v => Math.sqrt(v.reduce((a,b) => a+b*b, 0))
  },
  {
    name: 'Total L² norm',
    compute64: v => Math.sqrt(v.reduce((a,b) => a+b*b, 0)),
    compute48: v => Math.sqrt(v.reduce((a,b) => a+b*b, 0))
  }
];

console.log('Invariance tests:');
invariantTests.forEach(test => {
  const result = testInvariant(test.name, test.compute64, test.compute48);
  console.log(`  ${result.name}:`);
  console.log(`    64D: ${result.val64.toFixed(6)}, 48D: ${result.val48.toFixed(6)}`);
  console.log(`    Preserved: ${result.preserved ? 'YES ✓' : 'NO ✗'}`);
});

// 10. Practical application
console.log('\n10. Practical Application: Dimensionality Reduction\n');

// Simulate high-dimensional data
function generateData(n, dims) {
  return Array.from({length: n}, () => 
    Array.from({length: dims}, () => Math.random() * 2 - 1)
  );
}

const dataset64 = generateData(100, 64);
const dataset48 = dataset64.map(project);

// Calculate preservation statistics
let totalVar64 = 0;
let totalVar48 = 0;

dataset64.forEach((vec, i) => {
  totalVar64 += vec.reduce((a,b) => a+b*b, 0);
  totalVar48 += dataset48[i].reduce((a,b) => a+b*b, 0);
});

const varPreserved = totalVar48 / totalVar64;

console.log('Dataset dimensionality reduction:');
console.log(`  Original: 100 samples × 64 dimensions`);
console.log(`  Reduced: 100 samples × 48 dimensions`);
console.log(`  Variance preserved: ${(varPreserved * 100).toFixed(1)}%`);
console.log(`  Memory saved: ${((1 - 48/64) * 100).toFixed(1)}%`);
console.log(`  Information loss: bounded and predictable`);

// Export results
const projectionResults = {
  operator: {
    domain: 64,
    codomain: 48,
    kernel: 16,
    type: 'Orthogonal projection'
  },
  spectral: {
    eigenvalues: '48 ones, 16 zeros',
    spectralGap: 1,
    conditionNumber: 1
  },
  fieldPatterns: {
    preserved: preservedCount,
    total: 256,
    preservationRate: preservedCount / 256,
    transformationRatios: Array.from(transformationMap.values())
  },
  information: {
    dimensionalReduction: 0.25,
    preservedCapacity: 0.75,
    hiddenDimensions: 16
  },
  geometric: {
    nonExpansive: true,
    optimalReconstruction: 'π^T',
    fiberDimension: 16
  }
};

console.log('\n=== SUMMARY ===');
console.log('The projection operator π: ℝ^64 → ℝ^48:');
console.log('1. Perfectly conditioned with maximal spectral gap');
console.log('2. Preserves exactly 25% of field patterns');
console.log('3. Creates trivial ℝ^16 fiber bundle structure');
console.log('4. Provides optimal (minimal norm) reconstruction');
console.log('5. Non-expansive: never increases distances');

require('fs').writeFileSync('/workspaces/PrimeOS/research/examples/projection-operator-results.json', 
  JSON.stringify(projectionResults, null, 2));