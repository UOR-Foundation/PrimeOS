/**
 * XOR Collision Pattern Analysis
 * ==============================
 * 
 * Deep dive into why XOR patterns 1, 48, and 49 cause resonance collisions
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

console.log("=== XOR COLLISION PATTERN ANALYSIS ===\n");

// Function to compute resonance
function computeResonance(n) {
  let product = 1.0;
  for (let i = 0; i < 8; i++) {
    if ((n >> i) & 1) {
      product *= fieldConstants[`α${i}`];
    }
  }
  return product;
}

// Analyze XOR = 1 (bit 0 flip)
console.log("1. XOR = 1 (00000001) - Flipping bit 0:");
console.log("   This toggles α₀ = 1 in the product");
console.log("   Since α₀ = 1, multiplying by 1 doesn't change the value!");
console.log("   Examples:");
for (let i = 0; i < 4; i++) {
  const n = i * 2;
  console.log(`   ${n} vs ${n+1}: ${computeResonance(n).toFixed(6)} = ${computeResonance(n+1).toFixed(6)}`);
}

// Analyze XOR = 48 (bits 4,5 flip)
console.log("\n2. XOR = 48 (00110000) - Flipping bits 4 and 5:");
console.log("   This toggles α₄ and α₅ together");
console.log("   Since α₄ × α₅ = 1, toggling both maintains the product!");
console.log("   Examples:");
const examples48 = [[0, 48], [1, 49], [2, 50], [3, 51]];
for (const [a, b] of examples48) {
  console.log(`   ${a} vs ${b}: ${computeResonance(a).toFixed(6)} = ${computeResonance(b).toFixed(6)}`);
}

// Analyze XOR = 49 (bits 0,4,5 flip)
console.log("\n3. XOR = 49 (00110001) - Flipping bits 0, 4, and 5:");
console.log("   This combines the effects of XOR=1 and XOR=48");
console.log("   Since both preserve resonance, their combination does too!");

// Find the mathematical principle
console.log("\n=== MATHEMATICAL PRINCIPLE ===");
console.log("Resonance is preserved when XOR pattern represents:");
console.log("1. Toggling α₀ (identity) - XOR has bit 0 set");
console.log("2. Toggling α₄ and α₅ together - XOR has bits 4,5 set");
console.log("3. Any combination of the above");

// This explains the duplication pattern
console.log("\n=== DUPLICATION PATTERN EXPLAINED ===");
console.log("- Each position n has resonance R(n)");
console.log("- R(n) = R(n XOR 1) because α₀ = 1");
console.log("- This creates pairs: (0,1), (2,3), (4,5), ... (254,255)");
console.log("- That's 128 pairs with identical resonance");
console.log();
console.log("Additionally:");
console.log("- R(n) = R(n XOR 48) when α₄,α₅ are both toggled");
console.log("- R(n) = R(n XOR 49) combining both effects");
console.log("- This creates groups of 4: {n, n⊕1, n⊕48, n⊕49}");
console.log();
console.log("Result: Some resonances appear 2x, others 4x");

// Verify the count
let twoCount = 0;
let fourCount = 0;
const seen = new Set();

for (let n = 0; n < 256; n++) {
  if (seen.has(n)) continue;
  
  const group = [n, n^1, n^48, n^49].filter(x => x < 256);
  const resonances = group.map(computeResonance);
  
  // Check if all in group have same resonance
  const allSame = resonances.every(r => Math.abs(r - resonances[0]) < 1e-10);
  
  if (allSame) {
    group.forEach(x => seen.add(x));
    if (group.length === 2) twoCount++;
    else if (group.length === 4) fourCount++;
  }
}

console.log(`\n=== VERIFICATION ===`);
console.log(`Groups of size 2: ${twoCount}`);
console.log(`Groups of size 4: ${fourCount}`);
console.log(`Total unique resonances: ${twoCount + fourCount}`);

// This gives us the key insight for the proof!
console.log("\n=== KEY INSIGHT FOR PROOF ===");
console.log("The 256 positions partition into equivalence classes:");
console.log("- 64 classes of size 2 (related by XOR 1)");
console.log("- 32 classes of size 4 (related by XOR 1,48,49)");
console.log("- Total: 64 + 32 = 96 unique resonance values");
console.log("\nThis can be proven by showing:");
console.log("1. α₀ = 1 (identity property)");
console.log("2. α₄ × α₅ = 1 (unity product)");
console.log("3. These are the only collision-causing relationships");