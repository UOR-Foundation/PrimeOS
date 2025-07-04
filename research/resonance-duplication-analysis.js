/**
 * Resonance Duplication Analysis
 * ==============================
 * 
 * This script analyzes which bit patterns produce identical resonance values,
 * explaining why there are only 96 unique values among 256 possibilities.
 */

// Import field constants
const fieldConstants = {
  α0: 1.0,
  α1: 1.8392867552141612,
  α2: 1.618033988749895,
  α3: 0.5,
  α4: 0.15915494309189535,
  α5: 6.283185307179586,
  α6: 0.19961197478400414,
  α7: 0.014134725141734694
};

console.log("=== RESONANCE DUPLICATION ANALYSIS ===\n");

// Function to compute resonance for a given byte value
function computeResonance(n) {
  let product = 1.0;
  for (let i = 0; i < 8; i++) {
    if ((n >> i) & 1) {
      product *= fieldConstants[`α${i}`];
    }
  }
  return product;
}

// Compute all 256 resonance values
const resonances = new Map();
const byResonance = new Map();

for (let n = 0; n < 256; n++) {
  const r = computeResonance(n);
  resonances.set(n, r);
  
  if (!byResonance.has(r)) {
    byResonance.set(r, []);
  }
  byResonance.get(r).push(n);
}

console.log(`Total positions: 256`);
console.log(`Unique resonance values: ${byResonance.size}`);
console.log();

// Analyze duplication patterns
const countByFrequency = new Map();
for (const [resonance, positions] of byResonance) {
  const freq = positions.length;
  if (!countByFrequency.has(freq)) {
    countByFrequency.set(freq, 0);
  }
  countByFrequency.set(freq, countByFrequency.get(freq) + 1);
}

console.log("=== DUPLICATION PATTERN ===");
for (const [freq, count] of [...countByFrequency].sort((a, b) => a[0] - b[0])) {
  console.log(`${count} resonance values appear exactly ${freq} times`);
}

// Find specific patterns that cause duplication
console.log("\n=== RESONANCE COLLISIONS ===");
console.log("Analyzing why certain bit patterns give the same resonance...\n");

// Check the unity product α₄ × α₅ = 1
console.log("1. Unity Product Collision:");
console.log("   Since α₄ × α₅ = 1, swapping bits 4 and 5 doesn't change resonance");
console.log("   Example:");
const example1a = 0b00010000; // bit 4 set
const example1b = 0b00100000; // bit 5 set
console.log(`   Byte ${example1a} (bit 4): resonance = ${computeResonance(example1a)}`);
console.log(`   Byte ${example1b} (bit 5): resonance = ${computeResonance(example1b)}`);
console.log(`   But when both are set:`);
const example1c = 0b00110000; // bits 4,5 set
const example1d = 0b00000000; // neither set
console.log(`   Byte ${example1c} (bits 4,5): resonance = ${computeResonance(example1c)}`);
console.log(`   Byte ${example1d} (no bits): resonance = ${computeResonance(example1d)}`);

// Find all pairs that produce same resonance
console.log("\n2. Finding Collision Patterns:");
let collisionCount = 0;
const collisionPatterns = new Map();

for (let i = 0; i < 256; i++) {
  for (let j = i + 1; j < 256; j++) {
    if (Math.abs(resonances.get(i) - resonances.get(j)) < 1e-10) {
      collisionCount++;
      const xor = i ^ j;
      if (!collisionPatterns.has(xor)) {
        collisionPatterns.set(xor, []);
      }
      collisionPatterns.get(xor).push([i, j]);
    }
  }
}

console.log(`   Total collision pairs: ${collisionCount}`);
console.log("\n   XOR patterns causing collisions:");
const sortedPatterns = [...collisionPatterns].sort((a, b) => b[1].length - a[1].length);
for (const [xor, pairs] of sortedPatterns.slice(0, 5)) {
  console.log(`   XOR = ${xor} (binary: ${xor.toString(2).padStart(8, '0')}): ${pairs.length} pairs`);
  if (pairs.length <= 3) {
    for (const [a, b] of pairs) {
      console.log(`      ${a} ↔ ${b}`);
    }
  }
}

// Analyze the mathematical reason for 96 unique values
console.log("\n=== MATHEMATICAL STRUCTURE ===");
console.log("The 96 unique values arise from:");
console.log("1. Unity relation α₄ × α₅ = 1 reduces combinations");
console.log("2. Field constant relationships create equivalences");
console.log("3. Specific bit patterns produce identical products");

// Export findings
console.log("\n=== KEY FINDINGS FOR PROOF ===");
console.log(`Confirmed: Exactly ${byResonance.size} unique resonance values`);
console.log(`Pattern: ${countByFrequency.get(2) || 0} values appear 2x, ${countByFrequency.get(4) || 0} values appear 4x`);

// Save detailed results
const fs = require('fs');
const results = {
  uniqueCount: byResonance.size,
  duplicationPattern: Object.fromEntries(countByFrequency),
  collisionXORs: Object.fromEntries(
    [...collisionPatterns].map(([k, v]) => [k, v.length])
  )
};
fs.writeFileSync('resonance-duplication-results.json', JSON.stringify(results, null, 2));