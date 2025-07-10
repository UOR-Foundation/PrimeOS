// Find minimal generating set for Aut(ℤ/48ℤ × ℤ/256ℤ)
// This script optimizes the representation of the 2048 automorphisms

console.log('=== MINIMAL GENERATING SET FOR Aut(G) ===\n');

// Utility functions
function gcd(a, b) {
  while (b !== 0) {
    [a, b] = [b, a % b];
  }
  return a;
}

function modPow(base, exp, mod) {
  let result = 1;
  base = base % mod;
  while (exp > 0) {
    if (exp % 2 === 1) result = (result * base) % mod;
    exp = Math.floor(exp / 2);
    base = (base * base) % mod;
  }
  return result;
}

function multiplicativeOrder(a, n) {
  if (gcd(a, n) !== 1) return 0;
  let order = 1;
  let pow = a % n;
  while (pow !== 1) {
    pow = (pow * a) % n;
    order++;
    if (order > n) return 0;
  }
  return order;
}

// 1. ANALYZE GROUP STRUCTURE
console.log('1. GROUP STRUCTURE ANALYSIS\n');

// Aut(G) ≅ U(48) × U(256)
console.log('Aut(ℤ/48ℤ × ℤ/256ℤ) ≅ U(48) × U(256)');

// Analyze U(48)
// 48 = 16 × 3 = 2^4 × 3
// φ(48) = φ(16) × φ(3) = 8 × 2 = 16
// U(48) ≅ U(16) × U(3) ≅ (ℤ/2ℤ × ℤ/2ℤ × ℤ/2ℤ × ℤ/2ℤ) × ℤ/2ℤ

console.log('\nU(48) analysis:');
console.log('  48 = 2^4 × 3');
console.log('  φ(48) = 16');
console.log('  U(48) ≅ ℤ/2ℤ × ℤ/2ℤ × ℤ/2ℤ × ℤ/2ℤ × ℤ/2ℤ');

// Analyze U(256)
// 256 = 2^8
// φ(256) = 128 = 2^7
// U(256) ≅ ℤ/2ℤ × ℤ/2ℤ × ... × ℤ/2ℤ (7 times)

console.log('\nU(256) analysis:');
console.log('  256 = 2^8');
console.log('  φ(256) = 128');
console.log('  U(256) ≅ ℤ/2ℤ × ℤ/2ℤ × ... × ℤ/2ℤ (7 times)');

// 2. FIND GENERATORS FOR U(48)
console.log('\n2. GENERATORS FOR U(48)\n');

const units48 = [];
for (let a = 1; a < 48; a++) {
  if (gcd(a, 48) === 1) units48.push(a);
}

// For U(48), we need to find independent generators
// Since U(48) ≅ (ℤ/2ℤ)^5, we need 5 generators

// First, separate into odd units (coprime to 2) and units ≡ 1 (mod 3)
const oddUnits48 = units48.filter(u => u % 2 === 1);
const mod3Units48 = units48.filter(u => u % 3 === 1);

console.log(`All units mod 48: [${units48.join(', ')}]`);
console.log(`Odd units: [${oddUnits48.join(', ')}]`);

// Find a minimal set of generators
function findGeneratorsU48() {
  // We need generators that span U(48)
  // U(48) has order 16 = 2^4, but structure is (Z/2)^4 × Z/2 (from the Z/3 part)
  
  const generators = [];
  const generated = new Set([1]);
  
  function addGenerator(g) {
    const newGenerated = new Set();
    for (const elem of generated) {
      newGenerated.add(elem);
      let prod = elem;
      // Generate all powers of g times elem
      for (let i = 0; i < multiplicativeOrder(g, 48); i++) {
        prod = (prod * g) % 48;
        newGenerated.add(prod);
      }
    }
    return newGenerated;
  }
  
  // Start with -1 (generates the Z/2 from the Z/3 component)
  let newSet = addGenerator(47);
  console.log(`Adding generator 47: ${generated.size} → ${newSet.size} elements`);
  generated.clear();
  for (const elem of newSet) generated.add(elem);
  generators.push(47);
  
  // Now find generators for the remaining structure
  // We need generators that together with 47 generate all 16 elements
  const candidates = [5, 7, 17, 31, 11, 13];
  
  for (const g of candidates) {
    if (generated.size === 16) break;
    
    const testSet = addGenerator(g);
    if (testSet.size > generated.size) {
      console.log(`Adding generator ${g}: ${generated.size} → ${testSet.size} elements`);
      generated.clear();
      for (const elem of testSet) generated.add(elem);
      generators.push(g);
    }
  }
  
  return generators;
}

const generatorsU48 = findGeneratorsU48();
console.log(`\nMinimal generators for U(48): [${generatorsU48.join(', ')}]`);
console.log(`Number of generators: ${generatorsU48.length}`);

// 3. FIND GENERATORS FOR U(256)
console.log('\n3. GENERATORS FOR U(256)\n');

// U(256) = U(2^8) has a well-known structure
// U(2^n) ≅ ℤ/2ℤ × ℤ/2^(n-2)ℤ for n ≥ 3
// So U(256) ≅ ℤ/2ℤ × ℤ/64ℤ

console.log('U(256) ≅ ℤ/2ℤ × ℤ/64ℤ');
console.log('We need exactly 2 generators:');

// Find generators: -1 and a primitive root mod 2^8
const generatorsU256 = [];

// -1 generates the ℤ/2ℤ component
generatorsU256.push(255); // -1 mod 256

// Find a generator for ℤ/64ℤ component
// We need an element of order 64 in U(256)
// 3 is a primitive root modulo 2^n for n ≥ 3
let order3 = multiplicativeOrder(3, 256);
console.log(`Order of 3 in U(256): ${order3}`);

if (order3 === 64) {
  generatorsU256.push(3);
} else {
  // Find another generator
  for (let g = 3; g < 256; g += 2) {
    if (multiplicativeOrder(g, 256) === 64) {
      generatorsU256.push(g);
      break;
    }
  }
}

console.log(`Minimal generators for U(256): [${generatorsU256.join(', ')}]`);

// 4. COMBINE TO GET GENERATORS FOR Aut(G)
console.log('\n4. GENERATORS FOR Aut(G)\n');

const autGenerators = [];

// Add U(48) generators (acting on first component)
generatorsU48.forEach(g => {
  autGenerators.push({
    matrix: [[g, 0], [0, 1]],
    description: `U(48) generator: ${g}`,
    component: 'first'
  });
});

// Add U(256) generators (acting on second component)
generatorsU256.forEach(g => {
  autGenerators.push({
    matrix: [[1, 0], [0, g]],
    description: `U(256) generator: ${g}`,
    component: 'second'
  });
});

console.log(`Total generators for Aut(G): ${autGenerators.length}`);
console.log('\nGenerator list:');
autGenerators.forEach((gen, idx) => {
  console.log(`  ${idx + 1}. ${gen.description}`);
  console.log(`     Matrix: [[${gen.matrix[0][0]}, ${gen.matrix[0][1]}], [${gen.matrix[1][0]}, ${gen.matrix[1][1]}]]`);
});

// 5. VERIFY GENERATION
console.log('\n5. VERIFICATION OF GENERATION\n');

// Generate all automorphisms from our generators
function generateAllAutomorphisms(generators) {
  const generated = new Set();
  
  // Add identity
  generated.add('1,1');
  
  // BFS to generate all elements
  const queue = ['1,1'];
  const seen = new Set(['1,1']);
  
  while (queue.length > 0 && generated.size < 2048) {
    const current = queue.shift();
    const [a, d] = current.split(',').map(Number);
    
    // Apply each generator
    for (const gen of generators) {
      const [[g_a, _], [__, g_d]] = gen.matrix;
      const new_a = (a * g_a) % 48;
      const new_d = (d * g_d) % 256;
      const key = `${new_a},${new_d}`;
      
      if (!seen.has(key) && gcd(new_a, 48) === 1 && gcd(new_d, 256) === 1) {
        seen.add(key);
        queue.push(key);
        generated.add(key);
      }
    }
  }
  
  return generated;
}

console.log('Generating all automorphisms from minimal set...');
const generatedAuts = generateAllAutomorphisms(autGenerators);
console.log(`Generated ${generatedAuts.size} automorphisms`);
console.log(`Expected: 2048`);
console.log(`Complete generation: ${generatedAuts.size === 2048 ? 'YES ✓' : 'NO ✗'}`);

// 6. ALTERNATIVE MINIMAL SETS
console.log('\n6. ALTERNATIVE MINIMAL GENERATING SETS\n');

// There are multiple minimal generating sets
// Let's find another one using different choices

console.log('Alternative set 1 (using different U(48) generators):');
const altGeneratorsU48 = [47, 5, 11, 13, 17]; // Different choice
console.log(`  U(48): [${altGeneratorsU48.join(', ')}]`);
console.log(`  U(256): [${generatorsU256.join(', ')}] (same)`);

console.log('\nAlternative set 2 (using 5 as generator for U(256)):');
const order5 = multiplicativeOrder(5, 256);
console.log(`  Order of 5 in U(256): ${order5}`);
if (order5 === 64) {
  console.log('  U(48): Same as original');
  console.log('  U(256): [255, 5]');
}

// 7. REPRESENTATION EFFICIENCY
console.log('\n7. REPRESENTATION EFFICIENCY\n');

console.log('Storage comparison:');
console.log(`  Storing all 2048 automorphisms: ${2048 * 2} bytes`);
console.log(`  Storing ${autGenerators.length} generators: ${autGenerators.length * 2} bytes`);
console.log(`  Compression ratio: ${(2048 * 2) / (autGenerators.length * 2)}:1`);

console.log('\nComputational trade-offs:');
console.log('  - Generators: Minimal storage, but need computation to apply');
console.log('  - Full list: Fast lookup, but more storage');
console.log('  - Hybrid: Store frequently used automorphisms + generators');

// 8. GENERATOR RELATIONS
console.log('\n8. GENERATOR RELATIONS\n');

// Compute orders and relations
console.log('Generator orders:');
autGenerators.forEach((gen, idx) => {
  const [[a, _], [__, d]] = gen.matrix;
  const order = Math.max(multiplicativeOrder(a, 48), multiplicativeOrder(d, 256));
  console.log(`  Generator ${idx + 1}: order ${order}`);
});

console.log('\nKey relations:');
console.log('  All U(48) generators (except possibly one) have order ≤ 4');
console.log('  U(256) has one generator of order 2 and one of order 64');
console.log('  Generators commute between components');

// 9. APPLICATIONS
console.log('\n9. APPLICATIONS OF MINIMAL GENERATORS\n');

console.log('1. Efficient automorphism representation:');
console.log('   - Express any automorphism as product of generators');
console.log('   - Maximum word length: ~11 (number of generators)');

console.log('\n2. Random automorphism generation:');
console.log('   - Choose random exponents for each generator');
console.log('   - Uniform distribution over Aut(G)');

console.log('\n3. Subgroup generation:');
console.log('   - Any subset of generators generates a subgroup');
console.log('   - Easy to construct specific subgroups');

// 10. EXPORT RESULTS
console.log('\n10. EXPORTING RESULTS\n');

const results = {
  metadata: {
    group: 'Aut(ℤ/48ℤ × ℤ/256ℤ)',
    totalElements: 2048,
    structure: 'U(48) × U(256)',
    timestamp: new Date().toISOString()
  },
  groupDecomposition: {
    U48: {
      order: 16,
      structure: '(ℤ/2ℤ)^5',
      generators: generatorsU48
    },
    U256: {
      order: 128,
      structure: 'ℤ/2ℤ × ℤ/64ℤ',
      generators: generatorsU256
    }
  },
  minimalGenerators: {
    count: autGenerators.length,
    generators: autGenerators.map((gen, idx) => ({
      id: idx,
      matrix: gen.matrix,
      description: gen.description,
      component: gen.component
    }))
  },
  alternativeSets: [
    {
      description: 'Alternative U(48) generators',
      U48: altGeneratorsU48,
      U256: generatorsU256
    }
  ],
  efficiency: {
    storageReduction: `${(2048 * 2) / (autGenerators.length * 2)}:1`,
    generatorCount: autGenerators.length,
    fullStorageBytes: 2048 * 2,
    generatorStorageBytes: autGenerators.length * 2
  },
  verification: {
    generatesAll: generatedAuts.size === 2048,
    elementCount: generatedAuts.size
  }
};

const fs = require('fs');
fs.writeFileSync('/workspaces/PrimeOS/research/examples/automorphism-minimal-generators-results.json',
  JSON.stringify(results, null, 2));

console.log('Results saved to automorphism-minimal-generators-results.json');
console.log('\n=== MINIMAL GENERATOR ANALYSIS COMPLETE ===');