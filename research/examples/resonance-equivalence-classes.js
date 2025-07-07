/**
 * Resonance Equivalence Classes
 * =============================
 * 
 * Correctly partitioning the 256 positions into equivalence classes
 */

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

function computeResonance(n) {
  let product = 1.0;
  for (let i = 0; i < 8; i++) {
    if ((n >> i) & 1) {
      product *= fieldConstants[`α${i}`];
    }
  }
  return product;
}

console.log("=== RESONANCE EQUIVALENCE CLASSES ===\n");

// Build equivalence classes based on resonance equality
const resonanceMap = new Map();
const classes = [];

for (let n = 0; n < 256; n++) {
  const r = computeResonance(n);
  let found = false;
  
  for (const cls of classes) {
    if (Math.abs(computeResonance(cls[0]) - r) < 1e-10) {
      cls.push(n);
      found = true;
      break;
    }
  }
  
  if (!found) {
    classes.push([n]);
  }
}

// Analyze class sizes
const sizeCount = new Map();
for (const cls of classes) {
  const size = cls.length;
  sizeCount.set(size, (sizeCount.get(size) || 0) + 1);
}

console.log(`Total equivalence classes: ${classes.length}`);
console.log("\nClass size distribution:");
for (const [size, count] of [...sizeCount].sort((a, b) => a[0] - b[0])) {
  console.log(`  ${count} classes of size ${size}`);
}

// Analyze what makes classes of different sizes
console.log("\n=== ANALYZING CLASS STRUCTURE ===");

// Check classes of size 2
console.log("\nClasses of size 2:");
const size2Classes = classes.filter(cls => cls.length === 2);
console.log(`Found ${size2Classes.length} classes of size 2`);
if (size2Classes.length > 0) {
  console.log("Examples:");
  for (const cls of size2Classes.slice(0, 5)) {
    const xor = cls[0] ^ cls[1];
    console.log(`  ${cls}: XOR = ${xor} (${xor.toString(2).padStart(8, '0')})`);
  }
}

// Check classes of size 4
console.log("\nClasses of size 4:");
const size4Classes = classes.filter(cls => cls.length === 4);
console.log(`Found ${size4Classes.length} classes of size 4`);
if (size4Classes.length > 0) {
  console.log("Examples:");
  for (const cls of size4Classes.slice(0, 5)) {
    cls.sort((a, b) => a - b);
    console.log(`  ${cls}`);
    // Check XOR patterns within the class
    const xors = new Set();
    for (let i = 0; i < cls.length; i++) {
      for (let j = i + 1; j < cls.length; j++) {
        xors.add(cls[i] ^ cls[j]);
      }
    }
    console.log(`    XOR patterns: ${[...xors].sort((a, b) => a - b)}`);
  }
}

// The key insight
console.log("\n=== KEY INSIGHT ===");
console.log("The equivalence relation is determined by:");
console.log("1. Bit 0 doesn't affect resonance (α₀ = 1)");
console.log("2. Bits 4,5 together don't affect resonance (α₄ × α₅ = 1)");
console.log("\nThis creates equivalence classes where n ~ m if:");
console.log("- They differ only in bit 0, OR");
console.log("- They differ only in bits 4 and 5 together, OR");
console.log("- They differ in combinations of the above");

// Check specific positions to understand the pattern
console.log("\n=== PATTERN VERIFICATION ===");
for (let base = 0; base < 8; base += 2) {
  const group = [base, base^1, base^48, base^49];
  console.log(`\nBase ${base} group: ${group}`);
  for (const n of group) {
    if (n < 256) {
      console.log(`  ${n}: ${computeResonance(n).toFixed(6)}`);
    }
  }
}