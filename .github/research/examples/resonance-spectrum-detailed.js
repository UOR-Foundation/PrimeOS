// Detailed resonance spectrum analysis with corrected calculations
console.log('=== DETAILED RESONANCE SPECTRUM ANALYSIS ===\n');

// Field constants
const FIELD_CONSTANTS = [
  1.0,                    // α0: Identity
  1.8392867552141612,     // α1: Tribonacci
  1.6180339887498950,     // α2: Golden ratio
  0.5,                    // α3: Half
  0.15915494309189535,    // α4: 1/2π
  6.283185307179586,      // α5: 2π
  0.199612,               // α6: Phase
  0.014134725             // α7: Quantum
];

// Calculate resonance for a byte
function calculateResonance(byte) {
  let resonance = 1.0;
  for (let i = 0; i < 8; i++) {
    if ((byte >> i) & 1) {
      resonance *= FIELD_CONSTANTS[i];
    }
  }
  return resonance;
}

// Build complete spectrum
const resonanceMap = new Map();
for (let byte = 0; byte < 256; byte++) {
  const resonance = calculateResonance(byte);
  const key = resonance.toFixed(10);
  
  if (!resonanceMap.has(key)) {
    resonanceMap.set(key, {
      value: resonance,
      bytes: [],
      activeFields: []
    });
  }
  
  const entry = resonanceMap.get(key);
  entry.bytes.push(byte);
  
  // Record active fields
  const activeFields = [];
  for (let f = 0; f < 8; f++) {
    if ((byte >> f) & 1) activeFields.push(f);
  }
  if (entry.activeFields.length === 0) {
    entry.activeFields = activeFields;
  }
}

const spectrum = Array.from(resonanceMap.values())
  .sort((a, b) => a.value - b.value);

console.log(`Total unique resonances: ${spectrum.length}\n`);

// 1. SPECIAL VALUES WITH EXACT MATCHES
console.log('1. EXACT SPECIAL VALUE MATCHES\n');

const specialMatches = [];
spectrum.forEach((res, idx) => {
  // Check for π
  if (Math.abs(res.value - Math.PI) < 1e-10) {
    specialMatches.push({
      index: idx,
      value: res.value,
      name: 'π',
      bytes: res.bytes,
      fields: res.activeFields
    });
  }
  // Check for φ
  if (Math.abs(res.value - ((1 + Math.sqrt(5)) / 2)) < 1e-10) {
    specialMatches.push({
      index: idx,
      value: res.value,
      name: 'φ',
      bytes: res.bytes,
      fields: res.activeFields
    });
  }
  // Check for e
  if (Math.abs(res.value - Math.E) < 1e-10) {
    specialMatches.push({
      index: idx,
      value: res.value,
      name: 'e',
      bytes: res.bytes,
      fields: res.activeFields
    });
  }
  // Check for unity
  if (Math.abs(res.value - 1.0) < 1e-10) {
    specialMatches.push({
      index: idx,
      value: res.value,
      name: '1',
      bytes: res.bytes,
      fields: res.activeFields
    });
  }
});

specialMatches.forEach(match => {
  console.log(`${match.name} appears at position #${match.index + 1}:`);
  console.log(`  Value: ${match.value}`);
  console.log(`  Active fields: ${match.fields.length === 0 ? 'none (α0)' : match.fields.map(f => `α${f}`).join(' × ')}`);
  console.log(`  Byte examples: ${match.bytes.slice(0, 4).join(', ')}\n`);
});

// 2. FIELD ACTIVATION ANALYSIS
console.log('2. CORRECTED FIELD ACTIVATION ANALYSIS\n');

const fieldCounts = new Array(8).fill(0);
for (let byte = 0; byte < 256; byte++) {
  for (let f = 0; f < 8; f++) {
    if ((byte >> f) & 1) {
      fieldCounts[f]++;
    }
  }
}

console.log('Field activation frequency:');
fieldCounts.forEach((count, field) => {
  console.log(`  Field ${field}: ${count}/256 = ${(count/256*100).toFixed(1)}%`);
});

// Note about field 0
console.log('\nNote: Field 0 (α0=1) is implicitly always active as the multiplicative identity.');
console.log('When no bits are set (byte=0), the resonance is 1.0 (pure α0).\n');

// 3. RESONANCE CLUSTERING
console.log('3. RESONANCE CLUSTERING ANALYSIS\n');

// Find natural clusters
const clusterThreshold = 0.1; // Resonances within 0.1 of each other
const clusters = [];
let currentCluster = [spectrum[0]];

for (let i = 1; i < spectrum.length; i++) {
  if (spectrum[i].value - spectrum[i-1].value < clusterThreshold) {
    currentCluster.push(spectrum[i]);
  } else {
    if (currentCluster.length > 1) {
      clusters.push({
        size: currentCluster.length,
        min: currentCluster[0].value,
        max: currentCluster[currentCluster.length - 1].value,
        center: (currentCluster[0].value + currentCluster[currentCluster.length - 1].value) / 2
      });
    }
    currentCluster = [spectrum[i]];
  }
}

console.log(`Found ${clusters.length} resonance clusters`);
clusters.slice(0, 5).forEach((cluster, idx) => {
  console.log(`  Cluster ${idx + 1}: ${cluster.size} values from ${cluster.min.toFixed(4)} to ${cluster.max.toFixed(4)}`);
});

// 4. MULTIPLICATIVE STRUCTURE
console.log('\n4. MULTIPLICATIVE STRUCTURE\n');

// Find all multiplicative relationships
const multRelations = new Map();

for (let i = 0; i < spectrum.length; i++) {
  for (let j = 0; j < spectrum.length; j++) {
    const product = spectrum[i].value * spectrum[j].value;
    
    // Check if product is another resonance
    for (let k = 0; k < spectrum.length; k++) {
      if (Math.abs(product - spectrum[k].value) < 1e-6) {
        const key = `${i},${j}→${k}`;
        multRelations.set(key, {
          a: i,
          b: j,
          c: k,
          equation: `R${i+1} × R${j+1} = R${k+1}`
        });
      }
    }
  }
}

console.log(`Found ${multRelations.size} multiplicative relationships`);
console.log('Sample equations:');
let count = 0;
multRelations.forEach(rel => {
  if (count++ < 5) {
    console.log(`  ${rel.equation}: ${spectrum[rel.a].value.toFixed(4)} × ${spectrum[rel.b].value.toFixed(4)} = ${spectrum[rel.c].value.toFixed(4)}`);
  }
});

// 5. EXTREMA AND OUTLIERS
console.log('\n5. EXTREMA AND OUTLIERS\n');

console.log('Smallest 5 resonances:');
spectrum.slice(0, 5).forEach((res, idx) => {
  console.log(`  #${idx + 1}: ${res.value.toFixed(6)} (fields: ${res.activeFields.join(',')})`);
});

console.log('\nLargest 5 resonances:');
spectrum.slice(-5).forEach((res, idx) => {
  console.log(`  #${spectrum.length - 4 + idx}: ${res.value.toFixed(6)} (fields: ${res.activeFields.join(',')})`);
});

// Calculate outliers using IQR method
const q1Index = Math.floor(spectrum.length * 0.25);
const q3Index = Math.floor(spectrum.length * 0.75);
const q1 = spectrum[q1Index].value;
const q3 = spectrum[q3Index].value;
const iqr = q3 - q1;
const lowerBound = q1 - 1.5 * iqr;
const upperBound = q3 + 1.5 * iqr;

const outliers = spectrum.filter(res => res.value < lowerBound || res.value > upperBound);
console.log(`\nOutliers (beyond 1.5×IQR): ${outliers.length}`);

// 6. SYMMETRY AND DUALITY
console.log('\n6. SYMMETRY AND DUALITY ANALYSIS\n');

// Check for complement duality
let complementPairs = 0;
const complementMap = new Map();

for (let byte = 0; byte < 128; byte++) {
  const complement = 255 - byte; // Bitwise complement
  const res1 = calculateResonance(byte);
  const res2 = calculateResonance(complement);
  
  const product = res1 * res2;
  const ratio = res1 / res2;
  
  if (Math.abs(product - 1.0) < 1e-6) {
    complementPairs++;
  }
  
  const key = product.toFixed(6);
  if (!complementMap.has(key)) {
    complementMap.set(key, 0);
  }
  complementMap.set(key, complementMap.get(key) + 1);
}

console.log(`Complement pairs with product = 1: ${complementPairs}`);
console.log('\nMost common complement products:');
const sortedProducts = Array.from(complementMap.entries())
  .sort((a, b) => b[1] - a[1])
  .slice(0, 5);

sortedProducts.forEach(([product, count]) => {
  console.log(`  Product ${product}: occurs ${count} times`);
});

// 7. SUMMARY STATISTICS
console.log('\n7. COMPREHENSIVE SUMMARY\n');

const totalResonance = spectrum.reduce((sum, res) => sum + res.value * res.bytes.length, 0);
console.log(`Total resonance over all 256 bytes: ${totalResonance.toFixed(6)}`);
console.log(`Average resonance per byte: ${(totalResonance / 256).toFixed(6)}`);

// Conservation check for 768-cycle
const expected768Total = 687.110133;
const actual768Total = totalResonance * 3; // 768 = 3 × 256
console.log(`\n768-cycle total (3×256): ${actual768Total.toFixed(6)}`);
console.log(`Expected from research: ${expected768Total}`);
console.log(`Match: ${Math.abs(actual768Total - expected768Total) < 0.001 ? 'YES' : 'NO'}`);

console.log('\n=== DETAILED ANALYSIS COMPLETE ===');