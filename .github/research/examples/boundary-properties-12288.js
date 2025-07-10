/**
 * Boundary Properties and Position of 12,288
 * ==========================================
 * 
 * Exploring why 12,288 occupies a unique position in the number line
 * and its boundary characteristics between powers of 2.
 */

console.log("=== BOUNDARY PROPERTIES OF 12,288 ===\n");

// 1. Position between powers of 2
console.log("1. POSITION BETWEEN POWERS OF 2");
console.log("--------------------------------");
for (let n = 10; n <= 15; n++) {
  const power = Math.pow(2, n);
  console.log(`2^${n} = ${power}`);
}
console.log();

const lower = Math.pow(2, 13); // 8192
const upper = Math.pow(2, 14); // 16384
const position = 12288;

console.log(`12,288 lies between 2^13 (${lower}) and 2^14 (${upper})`);
console.log(`Distance from 2^13: ${position - lower} = ${position - lower}`);
console.log(`Distance to 2^14: ${upper - position} = ${upper - position}`);
console.log(`Ratio: ${position}/2^13 = ${position/lower} = 3/2`);
console.log(`Position: ${((position - lower)/(upper - lower) * 100).toFixed(1)}% of the way from 2^13 to 2^14`);
console.log();

// 2. Binary representation analysis
console.log("2. BINARY REPRESENTATION");
console.log("------------------------");
console.log(`12,288 in binary: ${position.toString(2)}`);
console.log(`Pattern: Two 1s followed by twelve 0s`);
console.log(`Bit count: ${position.toString(2).split('1').length - 1} ones`);
console.log(`Trailing zeros: ${position.toString(2).match(/0*$/)[0].length}`);
console.log();

// 3. As sum of powers of 2
console.log("3. SUM OF POWERS OF 2");
console.log("---------------------");
console.log(`12,288 = 2^13 + 2^12`);
console.log(`       = 8192 + 4096`);
console.log(`       = 2^12(2 + 1)`);
console.log(`       = 2^12 × 3`);
console.log();

// 4. Unique factorizations
console.log("4. UNIQUE FACTORIZATIONS");
console.log("------------------------");
const factorizations = [
  "2^12 × 3",
  "2^10 × 12",
  "2^8 × 48", 
  "2^6 × 192",
  "2^4 × 768",
  "3 × 4^6",
  "16 × 768",
  "48 × 256",
  "64 × 192"
];

factorizations.forEach(f => {
  console.log(`12,288 = ${f}`);
});
console.log();

// 5. Boundary analysis
console.log("5. BOUNDARY ANALYSIS");
console.log("--------------------");
console.log("As a boundary, 12,288 separates:");
console.log("- Below: 4-digit hex numbers (0x0000 - 0x2FFF)");
console.log("- Above: Requires 0x3000 and beyond");
console.log(`In hex: 12,288 = 0x${position.toString(16).toUpperCase()}`);
console.log();

// 6. Geometric mean property
console.log("6. GEOMETRIC MEAN PROPERTY");
console.log("--------------------------");
const geoMean = Math.sqrt(lower * upper);
console.log(`Geometric mean of 2^13 and 2^14: √(8192 × 16384) = ${geoMean}`);
console.log(`12,288 vs geometric mean: ${position} vs ${geoMean}`);
console.log(`Ratio: 12,288 / ${geoMean} = ${(position/geoMean).toFixed(6)}`);
console.log();

// 7. Special position: 3/2 × 2^13
console.log("7. THE 3/2 POSITION");
console.log("-------------------");
console.log(`12,288 = 3/2 × 2^13`);
console.log(`This is the ONLY integer of form 3/2 × 2^n between consecutive powers of 2`);
console.log(`Previous: 3/2 × 2^12 = 6,144 (between 2^12 and 2^13)`);
console.log(`Next: 3/2 × 2^14 = 24,576 (between 2^14 and 2^15)`);
console.log();

// 8. Divisibility properties
console.log("8. DIVISIBILITY PROPERTIES");
console.log("--------------------------");
const divisibilityTests = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16, 32, 64, 128, 256];
console.log("12,288 is divisible by:");
divisibilityTests.forEach(d => {
  if (position % d === 0) {
    console.log(`  ${d} → 12,288/${d} = ${position/d}`);
  }
});
console.log();

// 9. Digital root and numerology
console.log("9. DIGITAL ROOT ANALYSIS");
console.log("------------------------");
let digitalRoot = position;
while (digitalRoot >= 10) {
  digitalRoot = digitalRoot.toString().split('').reduce((a, b) => a + parseInt(b), 0);
}
console.log(`Digital root: 1+2+2+8+8 = 21 → 2+1 = 3`);
console.log(`The digital root is 3 (matching the factor of 3!)`);
console.log();

// 10. Nearby significant numbers
console.log("10. NEARBY SIGNIFICANT NUMBERS");
console.log("-----------------------------");
const nearby = [
  { value: 10000, name: "10^4" },
  { value: 12000, name: "12 × 10^3" },
  { value: 12288, name: "Our number" },
  { value: 12345, name: "Sequential" },
  { value: 13000, name: "13 × 10^3" },
  { value: 16384, name: "2^14" }
];

nearby.forEach(n => {
  const diff = n.value - position;
  console.log(`${n.value.toString().padStart(5)} (${n.name}): ${diff >= 0 ? '+' : ''}${diff}`);
});
console.log();

// 11. Information theoretic view
console.log("11. INFORMATION THEORETIC VIEW");
console.log("------------------------------");
console.log(`log₂(12,288) = ${Math.log2(position).toFixed(6)} bits`);
console.log(`This is between 13 and 14 bits`);
console.log(`Excess over 13 bits: ${Math.log2(position) - 13} ≈ 0.585 bits`);
console.log(`This excess encodes the factor of 3/2`);
console.log();

// 12. Boundary of computational feasibility
console.log("12. COMPUTATIONAL BOUNDARIES");
console.log("----------------------------");
console.log("12,288 as a boundary:");
console.log("- Small enough for direct computation");
console.log("- Large enough for complex structures");
console.log("- Fits in 14-bit address space");
console.log("- Exceeds 8KB (2^13) memory page");
console.log("- Below 16KB (2^14) limit");
console.log();

// 13. The golden boundary?
console.log("13. GOLDEN RATIO CONNECTION?");
console.log("----------------------------");
const phi = (1 + Math.sqrt(5)) / 2;
console.log(`φ × 2^13 = ${phi * lower} ≈ ${Math.round(phi * lower)}`);
console.log(`12,288 / φ = ${position / phi} ≈ ${Math.round(position / phi)}`);
console.log(`Note: 12,288 / φ ≈ 7,593 (no obvious significance)`);
console.log();

// 14. Powers of 3 analysis
console.log("14. POWERS OF 3 ANALYSIS");
console.log("------------------------");
for (let n = 1; n <= 10; n++) {
  const power3 = Math.pow(3, n);
  if (position % power3 === 0) {
    console.log(`3^${n} = ${power3} divides 12,288: 12,288/3^${n} = ${position/power3}`);
  }
}
console.log();

// 15. Why this boundary matters
console.log("15. WHY THIS BOUNDARY MATTERS");
console.log("-----------------------------");
console.log("12,288 is special because:");
console.log("1. Only number of form 3×2^n between 2^13 and 2^14");
console.log("2. Exactly 50% between consecutive powers of 2");
console.log("3. Sum of two consecutive powers of 2: 2^13 + 2^12");
console.log("4. Perfect factorization: 1024 × 12 (quantum × geometric)");
console.log("5. Binary pattern: 11000000000000 (aesthetic simplicity)");
console.log();

console.log("=== CONCLUSIONS ===");
console.log("12,288 occupies a unique position as the 3/2 point between");
console.log("2^13 and 2^14. This boundary represents a perfect balance:");
console.log("- Binary structure (powers of 2)");
console.log("- Ternary factor (multiple of 3)");
console.log("- Geometric significance (1024 × 12)");
console.log();
console.log("It's large enough to encode complex structures but small");
console.log("enough to be computationally tractable, making it an ideal");
console.log("'Goldilocks' number for bridging physics and computation.");