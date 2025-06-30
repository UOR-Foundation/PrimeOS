// Type definitions for Optimal Object Space Proof
// Demonstrates full 12,288-element pre-computed object space with domain patterns

export interface FieldConstants {
  α0: number; // Identity = 1.0
  α1: number; // Tribonacci = 1.8392867552141612
  α2: number; // Golden ratio = 1.6180339887498950
  α3: number; // Half = 0.5
  α4: number; // 1/2π = 0.15915494309189535
  α5: number; // 2π = 6.283185307179586
  α6: number; // Phase = 0.199612
  α7: number; // Quantum = 0.014134725
}

export interface PageCoordinates {
  pageIndex: number;          // Position in stream (0-based)
  hypercube: number;         // Which of 12 hypercubes (0-11)
  phase: [boolean, boolean]; // [field6_active, field7_active]
  resonance: number;         // Resonance value (one of 96)
  symmetryTransform?: GroupElement; // Optional G-element
}

export interface GroupElement {
  pageShift: number;  // 0-47 (Z/48Z component)
  byteAdd: number;    // 0-255 (Z/256Z component)
}

export interface ObjectSpaceReference {
  pageIndex: number;
  coordinates: PageCoordinates;
  matchType: 'direct' | 'transformed' | 'domain-pattern';
  patternId?: string; // For domain patterns
}

export interface BlockSpacePage {
  pageIndex: number;
  data: Uint8Array;
  resonance: number;
}

export interface EncodedObject {
  version: 3; // Version 3 includes full 12,288 + domain patterns
  algorithm: 'primeos-optimal-object-space';
  
  objectSpaceRefs: ObjectSpaceReference[];
  blockSpacePages: BlockSpacePage[];
  
  metadata: {
    originalSize: number;
    totalPages: number;
    objectSpaceMatches: number;
    blockSpacePages: number;
    compressionRatio: number;
    
    // Match breakdown
    matchTypes: {
      direct: number;          // Direct 768 matches
      transformed: number;     // 12,288 group transforms
      domainPattern: number;   // Domain-specific patterns
    };
    
    // Features used
    features: {
      base768: boolean;
      full12288: boolean;
      domainPatterns: boolean;
      resonanceDict: boolean;
      conservationCheck: boolean;
    };
  };
}

export interface DomainPattern {
  id: string;
  name: string;
  pattern: Uint8Array; // 48 bytes
  frequency?: number;  // For adaptive learning
  source: 'builtin' | 'learned';
}

export interface OptimalObjectSpace {
  // Mathematical spaces
  base768: Uint8Array;
  resonanceDict: Map<string, number>;
  unityPositions: number[];
  
  // Domain patterns
  domainPatterns: Map<string, DomainPattern>;
  
  // Group operations
  applyGroupElement(page: Uint8Array, element: GroupElement): Uint8Array;
  inverseGroupElement(element: GroupElement): GroupElement;
  
  // Pattern matching
  findMatch(page: Uint8Array): ObjectSpaceReference | null;
  
  // Coordinate calculation
  calculateCoordinates(pageIndex: number, page: Uint8Array): PageCoordinates;
  
  // Reconstruction
  reconstructPage(coordinates: PageCoordinates): Uint8Array;
}

export interface EncoderOptions {
  // Object space features
  useBase768: boolean;
  useFull12288: boolean;
  useDomainPatterns: boolean;
  
  // Mathematical features
  useResonanceDict: boolean;
  useConservationCheck: boolean;
  
  // Domain pattern learning
  enableLearning: boolean;
  learningThreshold: number; // Min frequency to add pattern
  
  // Performance tuning
  maxGroupSearchDepth: number; // Limit group element search
  cacheSize: number;           // Transform cache size
}

export interface EncoderDiagnostics {
  timestamp: string;
  inputFile: string;
  inputSize: number;
  
  // Encoding results
  totalPages: number;
  encodingTime: number;
  
  // Match analysis
  matches: {
    total: number;
    percentage: number;
    byType: {
      direct: number;
      transformed: number;
      domainPattern: number;
    };
  };
  
  // Pattern analysis
  patternFrequencies: Map<string, number>;
  topPatterns: Array<{
    pattern: string;
    count: number;
    bytes: string; // Hex representation
  }>;
  
  // Resonance analysis
  resonanceDistribution: Map<number, number>;
  averageResonance: number;
  conservationValid: boolean;
  
  // Group transform analysis
  transformsUsed: Map<string, number>; // "shift,add" -> count
  mostCommonTransforms: Array<{
    element: GroupElement;
    count: number;
  }>;
  
  // Compression metrics
  originalBytes: number;
  encodedBytes: number;
  compressionRatio: number;
  theoreticalLimit: number; // If all pages matched
  
  // Performance metrics
  encodingRate: number; // pages/second
  matchingTime: number; // ms spent in pattern matching
  cacheHitRate: number;
}

export interface DecoderDiagnostics {
  timestamp: string;
  
  // Decoding results
  totalPages: number;
  decodingTime: number;
  
  // Reconstruction analysis
  pagesFromObjectSpace: number;
  pagesFromBlockSpace: number;
  
  // Validation
  resonanceChecks: {
    passed: number;
    failed: number;
  };
  conservationValid: boolean;
  
  // Performance
  decodingRate: number; // pages/second
  cacheHitRate: number;
}

// Test data generators
export interface TestDataGenerator {
  name: string;
  description: string;
  generate(): Uint8Array;
  expectedMatchRate: number; // 0-1
}

// Main proof interface
export interface OptimalObjectSpaceProof {
  encoder: ObjectSpaceEncoder;
  decoder: ObjectSpaceDecoder;
  objectSpace: OptimalObjectSpace;
  
  // Run complete proof with diagnostics
  runProof(testData: Uint8Array, options: EncoderOptions): Promise<{
    encoded: EncodedObject;
    decoded: Uint8Array;
    encoderDiagnostics: EncoderDiagnostics;
    decoderDiagnostics: DecoderDiagnostics;
    valid: boolean;
  }>;
}

export interface ObjectSpaceEncoder {
  constructor(objectSpace: OptimalObjectSpace, options: EncoderOptions);
  
  encode(data: Uint8Array): Promise<EncodedObject>;
  generateDiagnostics(): EncoderDiagnostics;
  
  // Learning interface
  learnPatterns(data: Uint8Array): void;
  getLearnedPatterns(): DomainPattern[];
}

export interface ObjectSpaceDecoder {
  constructor(objectSpace: OptimalObjectSpace);
  
  decode(encoded: EncodedObject): Promise<Uint8Array>;
  generateDiagnostics(): DecoderDiagnostics;
  
  // Validation
  validateResonance(encoded: EncodedObject): boolean;
  validateConservation(data: Uint8Array): boolean;
}