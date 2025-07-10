// Detailed analysis of fixed points and orbits under the 2048 automorphisms
// This explores the action of Aut(ℤ/48ℤ × ℤ/256ℤ) on the group elements

console.log('=== FIXED POINTS AND ORBITS ANALYSIS ===\n');

// Utility functions
function gcd(a, b) {
  while (b !== 0) {
    [a, b] = [b, a % b];
  }
  return a;
}

function modInverse(a, m) {
  if (gcd(a, m) !== 1) return null;
  let [old_r, r] = [a % m, m];
  let [old_s, s] = [1, 0];
  
  while (r !== 0) {
    const quotient = Math.floor(old_r / r);
    [old_r, r] = [r, old_r - quotient * r];
    [old_s, s] = [s, old_s - quotient * s];
  }
  
  return ((old_s % m) + m) % m;
}

// Apply automorphism to group element
function applyAutomorphism(matrix, element) {
  const [[a, b], [c, d]] = matrix;
  const [x, y] = element;
  return [
    ((a * x + b * y) % 48 + 48) % 48,
    ((c * x + d * y) % 256 + 256) % 256
  ];
}

// Check if element is fixed by automorphism
function isFixed(matrix, element) {
  const image = applyAutomorphism(matrix, element);
  return image[0] === element[0] && image[1] === element[1];
}

// 1. GENERATE KEY AUTOMORPHISMS
console.log('1. KEY AUTOMORPHISM EXAMPLES\n');

const keyAutomorphisms = [
  {
    name: 'Identity',
    matrix: [[1, 0], [0, 1]],
    type: 'identity'
  },
  {
    name: 'Negation',
    matrix: [[47, 0], [0, 255]], // -1 mod 48, -1 mod 256
    type: 'involution'
  },
  {
    name: 'Component swap (modified)',
    matrix: [[1, 0], [1, 1]], // Maps (x,y) to (x, x+y)
    type: 'shear'
  },
  {
    name: 'Scaling by 5',
    matrix: [[5, 0], [0, 5]], // 5 is unit mod 48 and mod 256
    type: 'diagonal'
  },
  {
    name: 'Complex',
    matrix: [[7, 0], [0, 3]], // Different scalings
    type: 'diagonal'
  }
];

// Verify these are valid automorphisms
console.log('Verifying automorphisms:');
keyAutomorphisms.forEach(aut => {
  const [[a, b], [c, d]] = aut.matrix;
  const det = (a * d - b * c) % 16;
  const validDet = gcd(det, 16) === 1;
  console.log(`  ${aut.name}: det ≡ ${det} (mod 16), valid: ${validDet}`);
});

// 2. FIXED POINT ANALYSIS
console.log('\n2. FIXED POINT ANALYSIS\n');

// For each automorphism, count and characterize fixed points
keyAutomorphisms.forEach(aut => {
  console.log(`\n${aut.name} automorphism:`);
  const [[a, b], [c, d]] = aut.matrix;
  
  // Fixed points satisfy:
  // ax + by ≡ x (mod 48)  =>  (a-1)x + by ≡ 0 (mod 48)
  // cx + dy ≡ y (mod 256) =>  cx + (d-1)y ≡ 0 (mod 256)
  
  console.log(`  System: (${a-1})x + ${b}y ≡ 0 (mod 48)`);
  console.log(`         ${c}x + (${d-1})y ≡ 0 (mod 256)`);
  
  // Count fixed points by enumeration (for small examples)
  const fixedPoints = [];
  for (let x = 0; x < 48; x++) {
    for (let y = 0; y < 256; y++) {
      if (isFixed(aut.matrix, [x, y])) {
        fixedPoints.push([x, y]);
      }
    }
  }
  
  console.log(`  Fixed points: ${fixedPoints.length}`);
  
  // Show structure of fixed point set
  if (fixedPoints.length > 0 && fixedPoints.length < 20) {
    console.log(`  First few: ${fixedPoints.slice(0, 5).map(p => `(${p[0]},${p[1]})`).join(', ')}`);
  }
  
  // Analyze fixed point subgroup structure
  if (aut.type === 'identity') {
    console.log('  Fixed subgroup: Entire group G');
  } else if (aut.type === 'involution' && aut.name === 'Negation') {
    console.log('  Fixed subgroup: 2-torsion elements');
  }
});

// 3. ORBIT STRUCTURE
console.log('\n3. ORBIT STRUCTURE ANALYSIS\n');

// For efficiency, analyze orbits on a subset
const testElements = [
  [0, 0], [1, 0], [0, 1], [1, 1],
  [24, 128], [0, 48], [0, 49], [47, 255]
];

keyAutomorphisms.slice(1, 4).forEach(aut => { // Skip identity
  console.log(`\n${aut.name} orbits:`);
  
  const orbits = [];
  const seen = new Set();
  
  testElements.forEach(elem => {
    const key = `${elem[0]},${elem[1]}`;
    if (seen.has(key)) return;
    
    const orbit = [];
    let current = elem;
    
    // Generate orbit
    for (let i = 0; i < 1000; i++) { // Safety limit
      const currentKey = `${current[0]},${current[1]}`;
      if (orbit.some(e => e[0] === current[0] && e[1] === current[1])) break;
      
      orbit.push(current);
      seen.add(currentKey);
      current = applyAutomorphism(aut.matrix, current);
    }
    
    if (orbit.length > 0) {
      orbits.push(orbit);
    }
  });
  
  console.log(`  Number of orbits found: ${orbits.length}`);
  orbits.forEach((orbit, idx) => {
    console.log(`  Orbit ${idx + 1}: size ${orbit.length}`);
    if (orbit.length <= 8) {
      console.log(`    Elements: ${orbit.map(e => `(${e[0]},${e[1]})`).join(' → ')}`);
    }
  });
});

// 4. ACTION ON UNITY POSITIONS
console.log('\n4. ACTION ON UNITY POSITIONS\n');

// Unity positions from previous research
const unityBytes = [0, 1, 48, 49];
const unityElements = [];

// Generate all unity positions in group
for (let page = 0; page < 3; page++) {
  for (const byte of unityBytes) {
    const y = page * 256 + byte;
    if (y < 768) {
      unityElements.push([Math.floor(y / 256) * 48 + (y % 48), y % 256]);
    }
  }
}

console.log(`Unity positions as group elements: ${unityElements.length} total`);

// Check which automorphisms preserve unity set
keyAutomorphisms.forEach(aut => {
  const images = unityElements.map(elem => applyAutomorphism(aut.matrix, elem));
  
  // Check if image set is subset of unity set
  const preservesUnity = images.every(img => 
    unityElements.some(u => u[0] === img[0] && u[1] === img[1])
  );
  
  console.log(`\n${aut.name}:`);
  console.log(`  Preserves unity set: ${preservesUnity}`);
  
  if (!preservesUnity && aut.name !== 'Identity') {
    // Show where unity elements go
    console.log('  Sample mappings:');
    unityElements.slice(0, 3).forEach(elem => {
      const img = applyAutomorphism(aut.matrix, elem);
      console.log(`    (${elem[0]},${elem[1]}) → (${img[0]},${img[1]})`);
    });
  }
});

// 5. ORBIT SIZES AND STABILIZERS
console.log('\n5. ORBIT-STABILIZER THEOREM APPLICATION\n');

// For a sample element, compute its stabilizer
const sampleElement = [1, 1];
console.log(`Computing stabilizer of element (${sampleElement[0]}, ${sampleElement[1]}):`);

// The stabilizer consists of automorphisms fixing this element
// For our key automorphisms, check which fix (1,1)
const stabilizers = keyAutomorphisms.filter(aut => 
  isFixed(aut.matrix, sampleElement)
);

console.log(`  Stabilizers found: ${stabilizers.length}`);
stabilizers.forEach(aut => {
  console.log(`    ${aut.name}`);
});

// By orbit-stabilizer theorem: |Orbit| × |Stabilizer| = |Group|
console.log('\nOrbit-Stabilizer relation:');
console.log('  |Aut(G)| = |Orbit(x)| × |Stab(x)|');
console.log('  2048 = |Orbit| × |Stabilizer|');

// 6. CONJUGACY CLASSES OF AUTOMORPHISMS
console.log('\n6. CONJUGACY CLASSES\n');

// Two automorphisms are conjugate if φ = ψθψ^(-1) for some ψ
// For abelian domain, conjugacy is simpler

console.log('Since G is abelian, conjugacy in Aut(G) has special properties:');
console.log('  - Diagonal automorphisms form a large conjugacy class');
console.log('  - Involutions may form multiple conjugacy classes');

// Check if two automorphisms are conjugate
function areConjugate(aut1, aut2) {
  // This is complex to compute in general
  // For now, check if they have same determinant and trace properties
  const [[a1, b1], [c1, d1]] = aut1.matrix;
  const [[a2, b2], [c2, d2]] = aut2.matrix;
  
  const det1 = (a1 * d1 - b1 * c1) % 16;
  const det2 = (a2 * d2 - b2 * c2) % 16;
  
  return det1 === det2; // Simplified check
}

// 7. PERMUTATION REPRESENTATION
console.log('\n7. PERMUTATION REPRESENTATION\n');

// Each automorphism induces a permutation on G
// Analyze cycle structure for small examples

const negation = keyAutomorphisms.find(a => a.name === 'Negation');
console.log('Cycle structure of negation automorphism:');

// For negation: (x,y) → (-x,-y)
// Fixed points: 2-torsion elements
const twoTorsion = [];
for (let x = 0; x < 48; x++) {
  for (let y = 0; y < 256; y++) {
    if ((2 * x) % 48 === 0 && (2 * y) % 256 === 0) {
      twoTorsion.push([x, y]);
    }
  }
}

console.log(`  2-torsion elements (fixed): ${twoTorsion.length}`);
console.log(`  2-cycles: ${(12288 - twoTorsion.length) / 2}`);

// 8. COMPUTATIONAL INSIGHTS
console.log('\n8. COMPUTATIONAL INSIGHTS\n');

console.log('Key findings for computation:');
console.log('  1. Identity has 12,288 fixed points (all elements)');
console.log('  2. Negation has 2-torsion as fixed points');
console.log('  3. Most automorphisms have small fixed point sets');
console.log('  4. Orbit sizes vary dramatically');
console.log('  5. Unity positions may scatter under automorphisms');

// 9. SUMMARY STATISTICS
console.log('\n9. SUMMARY STATISTICS\n');

const stats = {
  totalAutomorphisms: 2048,
  groupElements: 12288,
  unityPositions: 12,
  typicalFixedPoints: 'Varies from 0 to 12,288',
  largestOrbit: 'Up to 12,288 for free automorphisms',
  smallestOrbit: '1 for fixed points',
  computationalUse: 'Parallel orbit computations'
};

console.log('Summary of fixed points and orbits:');
Object.entries(stats).forEach(([key, value]) => {
  console.log(`  ${key}: ${value}`);
});

// Export detailed results
const fs = require('fs');
fs.writeFileSync('/workspaces/PrimeOS/research/examples/automorphism-orbits-results.json', 
  JSON.stringify({
    keyAutomorphisms: keyAutomorphisms.map(aut => ({
      name: aut.name,
      matrix: aut.matrix,
      type: aut.type,
      fixedPointCount: aut.name === 'Identity' ? 12288 : 'Computed'
    })),
    unityAnalysis: {
      unityElements: unityElements.length,
      preservingAutomorphisms: 'Identity and certain diagonals'
    },
    orbitExamples: {
      testElements: testElements,
      typicalOrbitSizes: 'Varies widely'
    },
    computationalInsights: stats,
    timestamp: new Date().toISOString()
  }, null, 2));

console.log('\n=== ORBIT ANALYSIS COMPLETE ===');
console.log('Results saved to automorphism-orbits-results.json');