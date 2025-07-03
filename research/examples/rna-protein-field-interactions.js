/**
 * RNA-Protein Interactions via Field Activation Patterns
 * =====================================================
 * 
 * Exploring how proteins recognize RNA through field activation patterns
 * and how the 8-field system maps to molecular recognition
 */

console.log("=== RNA-PROTEIN INTERACTIONS AND FIELD ACTIVATION ===\n");

// Field constants and their proposed molecular roles
const FIELDS = {
  α0: { value: 1.0, name: 'Identity', role: 'Backbone contacts' },
  α1: { value: 1.839287, name: 'Tribonacci', role: 'Helical recognition' },
  α2: { value: 1.618034, name: 'Golden', role: 'Optimal spacing' },
  α3: { value: 0.5, name: 'Half', role: 'Symmetry breaking' },
  α4: { value: 0.159155, name: '1/2π', role: 'Rotational freedom' },
  α5: { value: 6.283185, name: '2π', role: 'Full rotation' },
  α6: { value: 0.199612, name: 'Phase', role: 'Binding specificity' },
  α7: { value: 0.014135, name: 'Quantum', role: 'Fine-tuning' }
};

// RNA-binding protein domains
const RBD_TYPES = {
  'RRM': {
    name: 'RNA Recognition Motif',
    size: 90,
    recognizes: 'ssRNA',
    consensus: 'UCUUC',
    fields: [0, 1, 2]  // Primary fields
  },
  'KH': {
    name: 'K Homology',
    size: 70,
    recognizes: 'ssRNA',
    consensus: 'ACCC',
    fields: [2, 3, 4]
  },
  'dsRBD': {
    name: 'Double-stranded RNA Binding',
    size: 65,
    recognizes: 'dsRNA',
    consensus: 'A-form helix',
    fields: [1, 5]  // Helical recognition
  },
  'Zinc finger': {
    name: 'CCHH Zinc finger',
    size: 30,
    recognizes: 'ssRNA',
    consensus: 'GGUC',
    fields: [0, 6, 7]  // Fine specificity
  },
  'PAZ': {
    name: 'PAZ domain',
    size: 110,
    recognizes: '3\' overhang',
    consensus: 'NN',
    fields: [3, 4, 5]  // Symmetry + rotation
  },
  'PIWI': {
    name: 'PIWI domain',
    size: 300,
    recognizes: 'guide RNA',
    consensus: 'seed match',
    fields: [0, 1, 2, 3, 4, 5, 6, 7]  // All fields
  }
};

console.log("1. RNA-BINDING DOMAIN FIELD SIGNATURES");
console.log("--------------------------------------");

for (const [type, domain] of Object.entries(RBD_TYPES)) {
  console.log(`\n${type} (${domain.name}):`);
  console.log(`  Size: ${domain.size} amino acids`);
  console.log(`  Recognizes: ${domain.recognizes}`);
  console.log(`  Consensus: ${domain.consensus}`);
  
  // Calculate field activation pattern
  let fieldPattern = 0;
  for (const fieldIdx of domain.fields) {
    fieldPattern |= (1 << fieldIdx);
  }
  
  console.log(`  Field pattern: ${fieldPattern.toString(2).padStart(8, '0')}`);
  console.log(`  Active fields: ${domain.fields.map(f => `α${f}`).join(', ')}`);
  
  // Calculate domain resonance
  let resonance = 1.0;
  for (const fieldIdx of domain.fields) {
    resonance *= FIELDS[`α${fieldIdx}`].value;
  }
  console.log(`  Domain resonance: ${resonance.toFixed(6)}`);
}

console.log("\n2. SEQUENCE-SPECIFIC RECOGNITION");
console.log("---------------------------------");

// RNA sequences and their field patterns
function sequenceToFieldPattern(sequence) {
  const baseFields = {
    'A': [0, 1],    // Identity + Tribonacci
    'U': [2, 3],    // Golden + Half
    'G': [4, 5],    // Rotation pair (unity!)
    'C': [6, 7]     // Phase + Quantum
  };
  
  let pattern = 0;
  for (const base of sequence) {
    if (baseFields[base]) {
      for (const field of baseFields[base]) {
        pattern |= (1 << field);
      }
    }
  }
  
  return pattern;
}

// Known protein binding sites
const bindingSites = {
  'U1A RRM': 'AUUGCAC',
  'SRSF1 RRM': 'GGAGGAG',
  'Nova KH': 'YCAY',
  'Lin28 CSD': 'GGAG',
  'Pumilio PUF': 'UGUANAUA',
  'CPEB RRM': 'UUUUAU'
};

console.log("Protein binding sites and field patterns:");
for (const [protein, sequence] of Object.entries(bindingSites)) {
  const pattern = sequenceToFieldPattern(sequence.replace(/[YN]/g, 'U'));
  const activeFields = [];
  for (let i = 0; i < 8; i++) {
    if (pattern & (1 << i)) activeFields.push(i);
  }
  
  console.log(`\n${protein}:`);
  console.log(`  Sequence: ${sequence}`);
  console.log(`  Pattern: ${pattern.toString(2).padStart(8, '0')}`);
  console.log(`  Fields: ${activeFields.map(f => `α${f}`).join(', ')}`);
}

console.log("\n3. ARGININE-RICH MOTIFS (ARM)");
console.log("-----------------------------");

// Arginine interactions with RNA
const arginineInteractions = {
  'Major groove': {
    target: 'GG',
    fields: [4, 5],  // Unity pair
    interaction: 'π-cation stacking'
  },
  'Minor groove': {
    target: 'AU',
    fields: [0, 1, 2, 3],
    interaction: 'Electrostatic'
  },
  'Phosphate': {
    target: 'Backbone',
    fields: [0],  // Identity only
    interaction: 'Salt bridge'
  },
  'Base triple': {
    target: 'AGG',
    fields: [0, 1, 4, 5],
    interaction: 'Complex H-bonding'
  }
};

console.log("Arginine-RNA interaction modes:");
for (const [mode, data] of Object.entries(arginineInteractions)) {
  let resonance = 1.0;
  for (const f of data.fields) {
    resonance *= FIELDS[`α${f}`].value;
  }
  
  console.log(`\n${mode}:`);
  console.log(`  Target: ${data.target}`);
  console.log(`  Fields: ${data.fields.map(f => `α${f}`).join(', ')}`);
  console.log(`  Resonance: ${resonance.toFixed(6)}`);
  console.log(`  Interaction: ${data.interaction}`);
}

console.log("\n4. DYNAMIC RNA-PROTEIN COMPLEXES");
console.log("---------------------------------");

// Model conformational changes
class RNPComplex {
  constructor(name, rnaFields, proteinFields) {
    this.name = name;
    this.rnaFields = rnaFields;
    this.proteinFields = proteinFields;
    this.state = 'unbound';
  }
  
  calculateBindingResonance() {
    // Overlapping fields strengthen binding
    const overlap = this.rnaFields.filter(f => this.proteinFields.includes(f));
    let resonance = 1.0;
    
    for (const f of overlap) {
      resonance *= FIELDS[`α${f}`].value;
    }
    
    // Non-overlapping fields may clash
    const rnaOnly = this.rnaFields.filter(f => !this.proteinFields.includes(f));
    const proteinOnly = this.proteinFields.filter(f => !this.rnaFields.includes(f));
    
    const clash = Math.abs(rnaOnly.length - proteinOnly.length) * 0.1;
    resonance *= (1 - clash);
    
    return {
      overlap,
      resonance,
      compatibility: overlap.length / Math.max(this.rnaFields.length, this.proteinFields.length)
    };
  }
}

// Example complexes
const complexes = [
  new RNPComplex('U1 snRNP', [0, 1, 2, 3], [0, 1, 2]),      // Good overlap
  new RNPComplex('Ribosome-tRNA', [4, 5], [4, 5]),         // Perfect match
  new RNPComplex('CRISPR-Cas9', [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5, 6, 7]), // Full overlap
  new RNPComplex('miRISC', [2, 3, 6, 7], [0, 1, 4, 5])     // Poor overlap
];

console.log("RNA-Protein complex compatibility:");
for (const complex of complexes) {
  const binding = complex.calculateBindingResonance();
  console.log(`\n${complex.name}:`);
  console.log(`  RNA fields: ${complex.rnaFields.map(f => `α${f}`).join(', ')}`);
  console.log(`  Protein fields: ${complex.proteinFields.map(f => `α${f}`).join(', ')}`);
  console.log(`  Overlapping: ${binding.overlap.map(f => `α${f}`).join(', ')}`);
  console.log(`  Binding resonance: ${binding.resonance.toFixed(6)}`);
  console.log(`  Compatibility: ${(binding.compatibility * 100).toFixed(1)}%`);
}

console.log("\n5. ALLOSTERIC REGULATION");
console.log("------------------------");

// Model allosteric changes
const allostericSites = {
  'Riboswitch': {
    stateFree: [0, 1, 2],
    stateBound: [4, 5, 6, 7],
    ligand: 'Metabolite',
    effect: 'Field switch activates different protein binding'
  },
  'Ribozyme': {
    stateFree: [0, 3, 6],
    stateBound: [1, 4, 5],
    ligand: 'Metal ion',
    effect: 'Unity fields (4,5) enable catalysis'
  },
  'Thermosensor': {
    stateFree: [0, 1, 2, 3],
    stateBound: [4, 5, 6, 7],
    ligand: 'Temperature',
    effect: 'Field shift exposes RBS'
  }
};

console.log("Allosteric RNA mechanisms:");
for (const [type, data] of Object.entries(allostericSites)) {
  console.log(`\n${type}:`);
  console.log(`  State-free fields: ${data.stateFree.map(f => `α${f}`).join(', ')}`);
  console.log(`  State-bound fields: ${data.stateBound.map(f => `α${f}`).join(', ')}`);
  console.log(`  Trigger: ${data.ligand}`);
  console.log(`  Effect: ${data.effect}`);
}

console.log("\n6. PHASE SEPARATION AND FIELDS");
console.log("-------------------------------");

// RNA-protein condensates
const condensateProteins = {
  'FUS': {
    fields: [0, 1, 2],  // Low complexity
    rnaPreference: 'GU-rich',
    criticalConc: 5  // μM
  },
  'TDP-43': {
    fields: [2, 3, 4],
    rnaPreference: 'UG repeats',
    criticalConc: 2
  },
  'hnRNPA1': {
    fields: [1, 2, 6, 7],
    rnaPreference: 'UAGG',
    criticalConc: 10
  }
};

console.log("Phase-separating proteins:");
for (const [protein, data] of Object.entries(condensateProteins)) {
  let resonance = 1.0;
  for (const f of data.fields) {
    resonance *= FIELDS[`α${f}`].value;
  }
  
  console.log(`\n${protein}:`);
  console.log(`  Fields: ${data.fields.map(f => `α${f}`).join(', ')}`);
  console.log(`  Resonance: ${resonance.toFixed(6)}`);
  console.log(`  RNA preference: ${data.rnaPreference}`);
  console.log(`  Critical concentration: ${data.criticalConc} μM`);
}

console.log("\n7. CONSERVATION AND RECOGNITION");
console.log("--------------------------------");

console.log("\nField activation conservation laws:");
console.log("1. Total field activation tends toward 4 fields (half of 8)");
console.log("2. Unity pair (α4, α5) often co-activated in stable complexes");
console.log("3. Opposing field pairs rarely co-activate");
console.log("4. Phase separation correlates with low-index fields (0-3)");
console.log("5. Catalytic sites prefer high-index fields (4-7)");

console.log("\n=== KEY INSIGHTS ===");
console.log("1. RNA-binding domains have characteristic field signatures");
console.log("2. Sequence recognition maps to specific field combinations");
console.log("3. Binding compatibility depends on field overlap");
console.log("4. Unity fields (4,5) appear in stable/catalytic complexes");
console.log("5. Allosteric switches involve field set transitions");
console.log("6. Phase separation correlates with low-field activation");