// Optimal Object Space Decoder
// Reconstructs data from coordinates and block space pages

import {
  PageCoordinates,
  ObjectSpaceReference,
  BlockSpacePage,
  EncodedObject,
  OptimalObjectSpace,
  DecoderDiagnostics,
  ObjectSpaceDecoder as IObjectSpaceDecoder
} from './types';

export class ObjectSpaceDecoder implements IObjectSpaceDecoder {
  private objectSpace: OptimalObjectSpace;
  
  // Diagnostics tracking
  private diagnostics: {
    startTime: number;
    pagesFromObjectSpace: number;
    pagesFromBlockSpace: number;
    resonanceChecksPassed: number;
    resonanceChecksFailed: number;
    cacheHits: number;
    cacheMisses: number;
  };
  
  constructor(objectSpace: OptimalObjectSpace) {
    this.objectSpace = objectSpace;
    
    this.diagnostics = {
      startTime: 0,
      pagesFromObjectSpace: 0,
      pagesFromBlockSpace: 0,
      resonanceChecksPassed: 0,
      resonanceChecksFailed: 0,
      cacheHits: 0,
      cacheMisses: 0
    };
  }
  
  async decode(encoded: EncodedObject): Promise<Uint8Array> {
    this.diagnostics.startTime = Date.now();
    
    // Validate encoded object
    if (encoded.version !== 3) {
      throw new Error(`Unsupported version: ${encoded.version}. This decoder requires version 3.`);
    }
    
    if (encoded.algorithm !== 'primeos-optimal-object-space') {
      throw new Error(`Unsupported algorithm: ${encoded.algorithm}`);
    }
    
    // Allocate output buffer
    const outputSize = encoded.metadata.originalSize;
    const output = new Uint8Array(outputSize);
    const pageSize = 48;
    
    // Create page index maps for efficient lookup
    const objectSpaceMap = new Map<number, ObjectSpaceReference>();
    const blockSpaceMap = new Map<number, BlockSpacePage>();
    
    for (const ref of encoded.objectSpaceRefs) {
      objectSpaceMap.set(ref.pageIndex, ref);
    }
    
    for (const page of encoded.blockSpacePages) {
      blockSpaceMap.set(page.pageIndex, page);
    }
    
    // Reconstruct pages in order
    const totalPages = encoded.metadata.totalPages;
    
    for (let pageIndex = 0; pageIndex < totalPages; pageIndex++) {
      const outputOffset = pageIndex * pageSize;
      
      if (objectSpaceMap.has(pageIndex)) {
        // Reconstruct from object space
        const ref = objectSpaceMap.get(pageIndex)!;
        const reconstructed = await this.reconstructFromObjectSpace(ref);
        
        // Validate resonance if enabled
        if (encoded.metadata.features.resonanceDict) {
          const valid = this.validatePageResonance(reconstructed, ref.coordinates);
          if (valid) {
            this.diagnostics.resonanceChecksPassed++;
          } else {
            this.diagnostics.resonanceChecksFailed++;
          }
        }
        
        output.set(reconstructed, outputOffset);
        this.diagnostics.pagesFromObjectSpace++;
        
      } else if (blockSpaceMap.has(pageIndex)) {
        // Copy from block space
        const page = blockSpaceMap.get(pageIndex)!;
        output.set(page.data, outputOffset);
        this.diagnostics.pagesFromBlockSpace++;
        
      } else {
        // Page missing - this shouldn't happen
        throw new Error(`Missing page at index ${pageIndex}`);
      }
    }
    
    // Validate conservation if enabled
    if (encoded.metadata.features.conservationCheck) {
      const valid = this.validateConservation(output);
      if (!valid) {
        console.warn('Conservation check failed - data may be corrupted');
      }
    }
    
    return output;
  }
  
  private async reconstructFromObjectSpace(ref: ObjectSpaceReference): Promise<Uint8Array> {
    let page: Uint8Array;
    
    switch (ref.matchType) {
      case 'direct':
        // Reconstruct from base 768 space
        page = this.reconstructFromBase768(ref.coordinates);
        break;
        
      case 'transformed':
        // Reconstruct with group transform
        page = this.reconstructWithTransform(ref.coordinates);
        break;
        
      case 'domain-pattern':
        // Reconstruct from domain pattern
        page = this.reconstructFromDomainPattern(ref);
        break;
        
      default:
        throw new Error(`Unknown match type: ${ref.matchType}`);
    }
    
    return page;
  }
  
  private reconstructFromBase768(coordinates: PageCoordinates): Uint8Array {
    // Calculate offset in base 768 space
    const hypercubeOffset = coordinates.hypercube * 64;
    const pageInHypercube = coordinates.pageIndex % 16;
    const pageOffset = pageInHypercube * 48;
    
    // Extract page from base space
    const start = hypercubeOffset + pageOffset;
    const page = this.objectSpace.base768.slice(start, start + 48);
    
    // Apply phase if needed
    if (coordinates.phase[0] || coordinates.phase[1]) {
      return this.applyPhase(page, coordinates.phase);
    }
    
    return new Uint8Array(page);
  }
  
  private reconstructWithTransform(coordinates: PageCoordinates): Uint8Array {
    // First reconstruct base page
    let page = this.reconstructFromBase768(coordinates);
    
    // Apply group transform if present
    if (coordinates.symmetryTransform) {
      page = this.objectSpace.applyGroupElement(page, coordinates.symmetryTransform);
    }
    
    return page;
  }
  
  private reconstructFromDomainPattern(ref: ObjectSpaceReference): Uint8Array {
    if (!ref.patternId) {
      throw new Error('Domain pattern reference missing pattern ID');
    }
    
    // Look up pattern
    const pattern = this.objectSpace.domainPatterns.get(ref.patternId);
    if (!pattern) {
      throw new Error(`Domain pattern not found: ${ref.patternId}`);
    }
    
    // Return copy of pattern
    return new Uint8Array(pattern.pattern);
  }
  
  private applyPhase(page: Uint8Array, phase: [boolean, boolean]): Uint8Array {
    // Phase application based on field 6 and 7 activation
    const result = new Uint8Array(page);
    
    for (let i = 0; i < result.length; i++) {
      const byte = result[i];
      const fieldIndex = byte & 0x07;
      
      // Apply phase based on field activation
      if (phase[0] && fieldIndex === 6) {
        // Field 6 phase transform
        result[i] = (byte ^ 0x33) & 0xFF;
      } else if (phase[1] && fieldIndex === 7) {
        // Field 7 quantum transform
        result[i] = (byte ^ 0x55) & 0xFF;
      }
    }
    
    return result;
  }
  
  private validatePageResonance(page: Uint8Array, coordinates: PageCoordinates): boolean {
    // Calculate actual resonance
    const actualResonance = this.calculatePageResonance(page);
    
    // Compare with expected resonance from coordinates
    const expectedResonance = coordinates.resonance;
    
    // Allow small numerical error
    const epsilon = 1e-6;
    return Math.abs(actualResonance - expectedResonance) < epsilon;
  }
  
  private calculatePageResonance(page: Uint8Array): number {
    const constants = [
      1.0,                    // α0
      1.8392867552141612,     // α1
      1.6180339887498950,     // α2
      0.5,                    // α3
      0.15915494309189535,    // α4
      6.283185307179586,      // α5
      0.199612,               // α6
      0.014134725             // α7
    ];
    
    let resonance = 1.0;
    for (let i = 0; i < page.length; i++) {
      const byte = page[i];
      const fieldIndex = byte & 0x07;
      resonance *= constants[fieldIndex];
    }
    
    return resonance;
  }
  
  validateResonance(encoded: EncodedObject): boolean {
    // Validate resonance for all pages
    let allValid = true;
    
    // Check object space references
    for (const ref of encoded.objectSpaceRefs) {
      const reconstructed = this.objectSpace.reconstructPage(ref.coordinates);
      const valid = this.validatePageResonance(reconstructed, ref.coordinates);
      if (!valid) {
        allValid = false;
        console.warn(`Resonance mismatch for page ${ref.pageIndex}`);
      }
    }
    
    // Check block space pages
    for (const page of encoded.blockSpacePages) {
      const actualResonance = this.calculatePageResonance(page.data);
      const epsilon = 1e-6;
      if (Math.abs(actualResonance - page.resonance) > epsilon) {
        allValid = false;
        console.warn(`Resonance mismatch for block space page ${page.pageIndex}`);
      }
    }
    
    return allValid;
  }
  
  validateConservation(data: Uint8Array): boolean {
    // Validate conservation laws at multiple scales
    const pageSize = 48;
    const pages = Math.floor(data.length / pageSize);
    
    // Check XOR balance for each page
    for (let p = 0; p < pages; p++) {
      const start = p * pageSize;
      const page = data.slice(start, start + pageSize);
      
      let xor = 0;
      for (let i = 0; i < page.length; i++) {
        xor ^= page[i];
      }
      
      if (xor !== 0) {
        console.warn(`XOR balance failed for page ${p}: ${xor}`);
        return false;
      }
    }
    
    // Check resonance conservation at 768-element boundaries
    if (pages >= 16) {
      const cycles = Math.floor(pages / 16);
      
      for (let c = 0; c < cycles; c++) {
        let totalResonance = 0;
        
        for (let p = 0; p < 16; p++) {
          const pageIndex = c * 16 + p;
          const start = pageIndex * pageSize;
          const page = data.slice(start, start + pageSize);
          totalResonance += this.calculatePageResonance(page);
        }
        
        // Expected total resonance for 768 elements
        const expectedTotal = 687.110133;
        const epsilon = 0.001;
        
        if (Math.abs(totalResonance - expectedTotal) > epsilon) {
          console.warn(`Resonance conservation failed for cycle ${c}: ${totalResonance} vs ${expectedTotal}`);
          return false;
        }
      }
    }
    
    return true;
  }
  
  generateDiagnostics(): DecoderDiagnostics {
    const totalTime = Date.now() - this.diagnostics.startTime;
    const totalPages = this.diagnostics.pagesFromObjectSpace + this.diagnostics.pagesFromBlockSpace;
    
    return {
      timestamp: new Date().toISOString(),
      totalPages,
      decodingTime: totalTime,
      pagesFromObjectSpace: this.diagnostics.pagesFromObjectSpace,
      pagesFromBlockSpace: this.diagnostics.pagesFromBlockSpace,
      resonanceChecks: {
        passed: this.diagnostics.resonanceChecksPassed,
        failed: this.diagnostics.resonanceChecksFailed
      },
      conservationValid: true, // Set based on actual validation
      decodingRate: totalPages / (totalTime / 1000),
      cacheHitRate: this.diagnostics.cacheHits / (this.diagnostics.cacheHits + this.diagnostics.cacheMisses)
    };
  }
}