// Study of resonance current dynamics and their physical meaning
// Analyzes how resonance flows through the 768-cycle

console.log('=== RESONANCE CURRENT DYNAMICS ANALYSIS ===\n');

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

// Calculate resonance for a position
function calculateResonance(position) {
  const byte = position & 0xFF;
  let resonance = 1.0;
  for (let i = 0; i < 8; i++) {
    if ((byte >> i) & 1) {
      resonance *= FIELD_CONSTANTS[i];
    }
  }
  return resonance;
}

// 1. COMPUTE RESONANCE FLOW
console.log('1. COMPUTING RESONANCE FLOW THROUGH 768-CYCLE\n');

const resonances = [];
const currents = [];
const accelerations = [];

// Calculate resonances
for (let i = 0; i < 768; i++) {
  resonances.push(calculateResonance(i));
}

// Calculate currents (first derivative)
for (let i = 0; i < 768; i++) {
  const next = (i + 1) % 768;
  const current = resonances[next] - resonances[i];
  currents.push(current);
}

// Calculate accelerations (second derivative)
for (let i = 0; i < 768; i++) {
  const next = (i + 1) % 768;
  const acceleration = currents[next] - currents[i];
  accelerations.push(acceleration);
}

// Find extrema
const maxCurrent = Math.max(...currents);
const minCurrent = Math.min(...currents);
const maxAccel = Math.max(...accelerations);
const minAccel = Math.min(...accelerations);

const maxCurrentPos = currents.indexOf(maxCurrent);
const minCurrentPos = currents.indexOf(minCurrent);

console.log('Current extrema:');
console.log(`  Maximum: ${maxCurrent.toFixed(6)} at position ${maxCurrentPos}`);
console.log(`  Minimum: ${minCurrent.toFixed(6)} at position ${minCurrentPos}`);
console.log(`  Range: ${(maxCurrent - minCurrent).toFixed(6)}`);

console.log('\nAcceleration extrema:');
console.log(`  Maximum: ${maxAccel.toFixed(6)}`);
console.log(`  Minimum: ${minAccel.toFixed(6)}`);

// 2. ANALYZE FLOW PATTERNS
console.log('\n2. FLOW PATTERN ANALYSIS\n');

// Count zero crossings
let zeroCrossings = 0;
let positivePeriods = [];
let negativePeriods = [];
let currentPeriod = [];
let isPositive = currents[0] > 0;

for (let i = 0; i < 768; i++) {
  const current = currents[i];
  
  if ((current > 0) !== isPositive) {
    // Zero crossing detected
    zeroCrossings++;
    if (currentPeriod.length > 0) {
      if (isPositive) {
        positivePeriods.push(currentPeriod.length);
      } else {
        negativePeriods.push(currentPeriod.length);
      }
    }
    currentPeriod = [];
    isPositive = current > 0;
  }
  
  currentPeriod.push(i);
}

console.log(`Zero crossings: ${zeroCrossings}`);
console.log(`Average positive period: ${positivePeriods.reduce((a,b) => a+b, 0) / positivePeriods.length || 0}`);
console.log(`Average negative period: ${negativePeriods.reduce((a,b) => a+b, 0) / negativePeriods.length || 0}`);

// 3. FIELD TRANSITIONS ANALYSIS
console.log('\n3. FIELD TRANSITION ANALYSIS\n');

// Analyze which field transitions cause largest currents
const transitionMap = new Map();

for (let i = 0; i < 768; i++) {
  const curr = i & 0xFF;
  const next = (i + 1) & 0xFF;
  const diff = curr ^ next; // XOR shows which bits changed
  
  // Count active transitions
  let transitionKey = '';
  for (let f = 0; f < 8; f++) {
    if ((diff >> f) & 1) {
      transitionKey += f;
    }
  }
  
  if (transitionKey) {
    if (!transitionMap.has(transitionKey)) {
      transitionMap.set(transitionKey, {
        count: 0,
        totalCurrent: 0,
        maxCurrent: -Infinity,
        positions: []
      });
    }
    
    const entry = transitionMap.get(transitionKey);
    entry.count++;
    entry.totalCurrent += Math.abs(currents[i]);
    entry.maxCurrent = Math.max(entry.maxCurrent, Math.abs(currents[i]));
    if (entry.positions.length < 5) entry.positions.push(i);
  }
}

console.log('Most impactful field transitions:');
const sortedTransitions = Array.from(transitionMap.entries())
  .sort((a, b) => b[1].maxCurrent - a[1].maxCurrent)
  .slice(0, 10);

sortedTransitions.forEach(([key, data]) => {
  const fields = key.split('').map(Number);
  console.log(`  Fields ${fields.join(',')}: max current = ${data.maxCurrent.toFixed(4)}, count = ${data.count}`);
});

// 4. CONSERVATION ANALYSIS
console.log('\n4. CONSERVATION AND CIRCULATION\n');

// Total circulation (should be 0 for conservation)
const totalCirculation = currents.reduce((sum, c) => sum + c, 0);
console.log(`Total circulation: ${totalCirculation.toFixed(10)} (should be ≈0)`);

// Check conservation over different scales
const scales = [8, 16, 32, 48, 64, 96, 128, 192, 256, 384, 768];
console.log('\nCirculation at different scales:');

scales.forEach(scale => {
  if (768 % scale === 0) {
    let maxLocalCirculation = 0;
    const periods = 768 / scale;
    
    for (let p = 0; p < periods; p++) {
      let localCirculation = 0;
      for (let i = 0; i < scale; i++) {
        localCirculation += currents[p * scale + i];
      }
      maxLocalCirculation = Math.max(maxLocalCirculation, Math.abs(localCirculation));
    }
    
    console.log(`  Scale ${scale}: max local circulation = ${maxLocalCirculation.toFixed(6)}`);
  }
});

// 5. FOURIER ANALYSIS
console.log('\n5. FREQUENCY ANALYSIS OF CURRENT\n');

// Simple DFT for dominant frequencies
function computeDFT(signal, maxFreq = 10) {
  const N = signal.length;
  const frequencies = [];
  
  for (let k = 0; k < maxFreq; k++) {
    let real = 0, imag = 0;
    
    for (let n = 0; n < N; n++) {
      const angle = -2 * Math.PI * k * n / N;
      real += signal[n] * Math.cos(angle);
      imag += signal[n] * Math.sin(angle);
    }
    
    const magnitude = Math.sqrt(real * real + imag * imag) / N;
    frequencies.push({ freq: k, magnitude, phase: Math.atan2(imag, real) });
  }
  
  return frequencies;
}

const spectrum = computeDFT(currents, 20);
console.log('Dominant frequencies in resonance current:');
spectrum
  .sort((a, b) => b.magnitude - a.magnitude)
  .slice(0, 10)
  .forEach(({ freq, magnitude }) => {
    if (magnitude > 0.1) {
      console.log(`  Frequency ${freq}: magnitude = ${magnitude.toFixed(4)}, period = ${freq > 0 ? (768/freq).toFixed(1) : 'Inf'}`);
    }
  });

// 6. PHASE SPACE ANALYSIS
console.log('\n6. PHASE SPACE DYNAMICS\n');

// Create phase space plot data (resonance vs current)
const phaseSpace = [];
for (let i = 0; i < 768; i++) {
  phaseSpace.push({
    position: i,
    resonance: resonances[i],
    current: currents[i],
    acceleration: accelerations[i]
  });
}

// Find attractors and repellers
const attractors = [];
const repellers = [];

for (let i = 1; i < 767; i++) {
  // Attractor: current changes sign from - to + (local minimum)
  if (currents[i-1] < 0 && currents[i+1] > 0) {
    attractors.push({
      position: i,
      resonance: resonances[i],
      strength: Math.abs(currents[i+1] - currents[i-1])
    });
  }
  
  // Repeller: current changes sign from + to - (local maximum)
  if (currents[i-1] > 0 && currents[i+1] < 0) {
    repellers.push({
      position: i,
      resonance: resonances[i],
      strength: Math.abs(currents[i+1] - currents[i-1])
    });
  }
}

console.log(`Found ${attractors.length} attractors and ${repellers.length} repellers`);

console.log('\nStrongest attractors:');
attractors
  .sort((a, b) => b.strength - a.strength)
  .slice(0, 5)
  .forEach(a => {
    console.log(`  Position ${a.position}: resonance = ${a.resonance.toFixed(4)}, strength = ${a.strength.toFixed(4)}`);
  });

// 7. PHYSICAL INTERPRETATION
console.log('\n7. PHYSICAL INTERPRETATIONS\n');

console.log('Current as Energy Flow:');
console.log('- Positive current: energy flowing forward in cycle');
console.log('- Negative current: energy flowing backward');
console.log('- Zero crossings: equilibrium points');
console.log(`- ${zeroCrossings} equilibrium points in full cycle`);

console.log('\nCurrent as Information Flow:');
console.log('- High current: rapid information transfer');
console.log('- Low current: stable information state');
console.log(`- Maximum information flux: ${maxCurrent.toFixed(4)} bits/step`);

console.log('\nQuantum Interpretation:');
console.log('- Current represents probability flow');
console.log('- Attractors are stable quantum states');
console.log('- Repellers are unstable transition states');

// 8. COMPUTATIONAL IMPLICATIONS
console.log('\n8. COMPUTATIONAL IMPLICATIONS\n');

// Find stable regions (low current)
const stableRegions = [];
let inStable = false;
let stableStart = 0;

for (let i = 0; i < 768; i++) {
  const isStable = Math.abs(currents[i]) < 0.5; // Threshold
  
  if (isStable && !inStable) {
    inStable = true;
    stableStart = i;
  } else if (!isStable && inStable) {
    stableRegions.push({
      start: stableStart,
      end: i - 1,
      length: i - stableStart
    });
    inStable = false;
  }
}

console.log(`Found ${stableRegions.length} stable regions`);
console.log('Longest stable regions:');
stableRegions
  .sort((a, b) => b.length - a.length)
  .slice(0, 5)
  .forEach(r => {
    console.log(`  Positions ${r.start}-${r.end} (length ${r.length})`);
  });

console.log('\nOptimization strategies:');
console.log('1. Cache computations in stable regions');
console.log('2. Use high-current positions for random access');
console.log('3. Exploit periodicity for parallel processing');
console.log('4. Align data structures with equilibrium points');

console.log('\n=== RESONANCE CURRENT ANALYSIS COMPLETE ===');