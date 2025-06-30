// Optimal Object Space Proof Index
// Connects encoder, decoder, and object space for complete proof system

import { ObjectSpaceEncoder } from './encoder';
import { ObjectSpaceDecoder } from './decoder';
import { OptimalObjectSpace } from './object-space';

import {
  EncoderOptions,
  EncodedObject,
  EncoderDiagnostics,
  DecoderDiagnostics,
  OptimalObjectSpaceProof as IOptimalObjectSpaceProof,
  TestDataGenerator
} from './types';

export * from './types';
export { ObjectSpaceEncoder } from './encoder';
export { ObjectSpaceDecoder } from './decoder';
export { OptimalObjectSpace } from './object-space';

export class OptimalObjectSpaceProof implements IOptimalObjectSpaceProof {
  encoder: ObjectSpaceEncoder;
  decoder: ObjectSpaceDecoder;
  objectSpace: OptimalObjectSpace;
  
  constructor(options?: Partial<EncoderOptions>) {
    // Initialize object space
    this.objectSpace = new OptimalObjectSpace();
    
    // Default encoder options
    const defaultOptions: EncoderOptions = {
      useBase768: true,
      useFull12288: true,
      useDomainPatterns: true,
      useResonanceDict: true,
      useConservationCheck: true,
      enableLearning: true,
      learningThreshold: 3,
      maxGroupSearchDepth: 100,
      cacheSize: 1000
    };
    
    const encoderOptions = { ...defaultOptions, ...options };
    
    // Initialize encoder and decoder
    this.encoder = new ObjectSpaceEncoder(this.objectSpace, encoderOptions);
    this.decoder = new ObjectSpaceDecoder(this.objectSpace);
  }
  
  async runProof(testData: Uint8Array, options?: Partial<EncoderOptions>): Promise<{
    encoded: EncodedObject;
    decoded: Uint8Array;
    encoderDiagnostics: EncoderDiagnostics;
    decoderDiagnostics: DecoderDiagnostics;
    valid: boolean;
  }> {
    // Update encoder options if provided
    if (options) {
      this.encoder = new ObjectSpaceEncoder(this.objectSpace, {
        ...this.encoder['options'],
        ...options
      });
    }
    
    // Encode data
    console.log(`Encoding ${testData.length} bytes...`);
    const encoded = await this.encoder.encode(testData);
    const encoderDiagnostics = this.encoder.generateDiagnostics();
    
    // Decode data
    console.log(`Decoding...`);
    const decoded = await this.decoder.decode(encoded);
    const decoderDiagnostics = this.decoder.generateDiagnostics();
    
    // Validate
    const valid = this.validateProof(testData, decoded, encoded);
    
    return {
      encoded,
      decoded,
      encoderDiagnostics,
      decoderDiagnostics,
      valid
    };
  }
  
  private validateProof(original: Uint8Array, decoded: Uint8Array, encoded: EncodedObject): boolean {
    // Check length
    if (original.length !== decoded.length) {
      console.error(`Length mismatch: ${original.length} vs ${decoded.length}`);
      return false;
    }
    
    // Check content
    for (let i = 0; i < original.length; i++) {
      if (original[i] !== decoded[i]) {
        console.error(`Byte mismatch at position ${i}: ${original[i]} vs ${decoded[i]}`);
        return false;
      }
    }
    
    // Validate resonance
    const resonanceValid = this.decoder.validateResonance(encoded);
    if (!resonanceValid) {
      console.error('Resonance validation failed');
      return false;
    }
    
    // Validate conservation
    const conservationValid = this.decoder.validateConservation(decoded);
    if (!conservationValid) {
      console.error('Conservation validation failed');
      return false;
    }
    
    return true;
  }
}

// Test data generators
export const testDataGenerators: TestDataGenerator[] = [
  {
    name: 'sequential',
    description: 'Sequential counter pattern (0-767)',
    generate(): Uint8Array {
      const data = new Uint8Array(768);
      for (let i = 0; i < data.length; i++) {
        data[i] = i & 0xFF;
      }
      return data;
    },
    expectedMatchRate: 1.0
  },
  
  {
    name: 'shifted-sequential',
    description: 'Sequential pattern shifted by 100',
    generate(): Uint8Array {
      const data = new Uint8Array(768);
      for (let i = 0; i < data.length; i++) {
        data[i] = (i + 100) & 0xFF;
      }
      return data;
    },
    expectedMatchRate: 1.0
  },
  
  {
    name: 'text-lorem',
    description: 'Lorem ipsum text pattern',
    generate(): Uint8Array {
      const text = 'Lorem ipsum dolor sit amet, consectetur adipiscing elit. '.repeat(20);
      const data = new Uint8Array(768);
      for (let i = 0; i < data.length; i++) {
        data[i] = text.charCodeAt(i % text.length);
      }
      return data;
    },
    expectedMatchRate: 0.15
  },
  
  {
    name: 'json-data',
    description: 'JSON structure pattern',
    generate(): Uint8Array {
      const json = '{"id":12345,"name":"test","values":[1,2,3,4,5],"active":true} ';
      const data = new Uint8Array(768);
      for (let i = 0; i < data.length; i++) {
        data[i] = json.charCodeAt(i % json.length);
      }
      return data;
    },
    expectedMatchRate: 0.20
  },
  
  {
    name: 'log-entries',
    description: 'Server log pattern',
    generate(): Uint8Array {
      const logs = [
        '2024-01-01 12:00:00 INFO [server] Request received\n',
        '2024-01-01 12:00:01 DEBUG [auth] User authenticated\n',
        '2024-01-01 12:00:02 INFO [api] Processing request\n'
      ];
      const fullLog = logs.join('').repeat(5);
      const data = new Uint8Array(768);
      for (let i = 0; i < data.length; i++) {
        data[i] = fullLog.charCodeAt(i % fullLog.length);
      }
      return data;
    },
    expectedMatchRate: 0.25
  },
  
  {
    name: 'binary-mixed',
    description: 'Mixed binary pattern',
    generate(): Uint8Array {
      const data = new Uint8Array(768);
      // First quarter: sequential
      for (let i = 0; i < 192; i++) {
        data[i] = i & 0xFF;
      }
      // Second quarter: zeros
      for (let i = 192; i < 384; i++) {
        data[i] = 0;
      }
      // Third quarter: alternating
      for (let i = 384; i < 576; i++) {
        data[i] = i % 2 ? 0xFF : 0x00;
      }
      // Fourth quarter: random-like
      for (let i = 576; i < 768; i++) {
        data[i] = (i * 7 + 13) & 0xFF;
      }
      return data;
    },
    expectedMatchRate: 0.50
  },
  
  {
    name: 'multimedia-header',
    description: 'Simulated multimedia file header',
    generate(): Uint8Array {
      const data = new Uint8Array(768);
      // PNG-like header
      data.set([0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A], 0);
      // IHDR chunk
      data.set([0x00, 0x00, 0x00, 0x0D, 0x49, 0x48, 0x44, 0x52], 8);
      // Dimensions
      data.set([0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x03, 0x00], 16);
      // Rest is structured data
      for (let i = 24; i < 768; i++) {
        data[i] = (i % 16 === 0) ? 0x00 : (i & 0xFF);
      }
      return data;
    },
    expectedMatchRate: 0.30
  },
  
  {
    name: 'csv-data',
    description: 'CSV formatted data',
    generate(): Uint8Array {
      const header = 'id,timestamp,value,status,description\n';
      const row = '123,2024-01-01T12:00:00Z,42.5,active,"Test data"\n';
      const csv = header + row.repeat(15);
      const data = new Uint8Array(768);
      for (let i = 0; i < data.length; i++) {
        data[i] = csv.charCodeAt(i % csv.length);
      }
      return data;
    },
    expectedMatchRate: 0.20
  }
];

// Utility function to run all test generators
export async function runAllTests(options?: Partial<EncoderOptions>): Promise<Map<string, any>> {
  const proof = new OptimalObjectSpaceProof(options);
  const results = new Map<string, any>();
  
  for (const generator of testDataGenerators) {
    console.log(`\nTesting: ${generator.name}`);
    const testData = generator.generate();
    const result = await proof.runProof(testData);
    
    results.set(generator.name, {
      ...result,
      generator: generator,
      matchRateAchieved: result.encoderDiagnostics.matches.percentage / 100,
      matchRateExpected: generator.expectedMatchRate,
      compressionRatio: result.encoderDiagnostics.compressionRatio
    });
  }
  
  return results;
}

// Export convenience function for creating proof instance
export function createOptimalObjectSpaceProof(options?: Partial<EncoderOptions>): OptimalObjectSpaceProof {
  return new OptimalObjectSpaceProof(options);
}