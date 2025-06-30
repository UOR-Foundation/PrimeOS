# @primeos/substrate Package Specification

## Overview

`@primeos/substrate` is the foundational data coordination layer for PrimeOS. It provides resonance-based addressing, attestation-driven knowledge representation, and multiple view representations for data access.

## Package Structure

```
@primeos/substrate/
├── src/
│   ├── core/           # Universal digest implementation
│   ├── statements/     # Statement system
│   ├── views/          # View ADLs (graph, object, stream, etc.)
│   ├── mutations/      # Write operations
│   ├── queries/        # Read operations
│   └── types/          # Shared TypeScript interfaces
├── test/
├── docs/
└── package.json
```

## Core Components

### 1. Object Space and Block Space

**Object Space**: The pre-calculable coordinate space derived from the 64-dimensional Mathematical Universe. Pages that fall within the client's object space can be computed deterministically and need not be stored.

**Block Space**: The storage space for pages that fall outside the client's object space. Only these non-calculable pages are written as IPLD statement blocks.

```typescript
interface ObjectSpace {
  // 768-element super-cycle decomposed as 12 × 64D hypercubes
  superCycle: Uint8Array; // [0...767] precalculated patterns
  
  // Resonance lookup table (96 unique values)
  resonanceDict: Map<string, number>;
  
  // Symmetry group G = Z/48Z × Z/256Z
  symmetryGroup: {
    pageModulus: 48;
    fieldModulus: 256;
    order: 12288; // 48 × 256
  };
  
  // Check if a page falls within calculable object space
  isCalculable(pageData: Uint8Array): boolean;
  
  // Calculate page from coordinates (if in object space)
  calculatePage(coordinates: PageCoordinates): Uint8Array | null;
}

interface PageCoordinates {
  position: number;        // Position in stream (0-based)
  hypercube: number;      // Which of 12 hypercubes (0-11)
  phase: [boolean, boolean]; // [field6_active, field7_active]
  resonance: number;      // Resonance value (quantized)
  symmetryTransform?: [number, number]; // Optional G-element
}
```

### 2. Universal Digest (Layer 0)

**Purpose**: Convert arbitrary data into navigable coordinates in Mathematical Universe space, separating calculable (object space) from non-calculable (block space) content.

```typescript
interface UniversalDigest {
  version: 2; // Updated for object/block space
  pageSize: 48;
  
  // Compact coordinates for calculable pages
  objectSpaceRefs: ObjectSpaceReference[];
  
  // Full blocks for non-calculable pages  
  blockSpacePages: BlockSpacePage[];
  
  metadata: {
    totalBytes: number;
    totalPages: number;
    objectSpacePages: number;
    blockSpacePages: number;
    compressionRatio: number;
    checksum: number;
  };
}

interface ObjectSpaceReference {
  pageIndex: number;
  coordinates: PageCoordinates;
  length: number; // Bytes in page (1-48)
}

interface BlockSpacePage {
  pageIndex: number;
  data: Uint8Array; // Actual page data (1-48 bytes)
  resonance: number; // For verification
  cid?: CID; // IPLD block CID if stored
}

class UniversalDigestADL {
  constructor(objectSpace: ObjectSpace);
  
  // Enhanced encoder that separates object/block space
  encode(data: Uint8Array): Promise<UniversalDigest>;
  
  // Decoder that reconstructs from coordinates + blocks
  decode(digest: UniversalDigest): Promise<Uint8Array>;
  
  // Streaming support with object space optimization
  createEncoder(options?: EncoderOptions): TransformStream<Uint8Array, EncodedChunk>;
  createDecoder(): TransformStream<EncodedChunk, Uint8Array>;
}

interface EncoderOptions {
  // Compression features from research
  useResonanceDict?: boolean;      // 96 unique values
  useXorBalance?: boolean;          // Hypercube XOR = 0
  useGSymmetry?: boolean;           // Full G-symmetry
  useTorusPeriodicity?: boolean;    // T^16 modeling
  
  // Object space threshold (% match required)
  objectSpaceThreshold?: number;    // Default: 0.9 (90%)
}

interface EncodedChunk {
  type: 'object-ref' | 'block-data';
  pageIndex: number;
  
  // For object space references
  coordinates?: PageCoordinates;
  
  // For block space data
  data?: Uint8Array;
  statement?: Statement; // IPLD statement for this block
}
```

**Field Constants** (from mathematical research):
```typescript
const FIELD_CONSTANTS = {
  α0: 1.0,                    // Identity/Time
  α1: 1.8392867552141612,     // Tribonacci constant (growth)
  α2: 1.6180339887498950,     // Golden ratio (proportion)
  α3: 0.5,                    // One-half (symmetry)
  α4: 0.15915494309189535,    // 1/2π (angular/compactification)
  α5: 6.283185307179586,      // 2π (cyclic/rotation)
  α6: 0.199612,               // θ (phase/modulation)
  α7: 0.014134725             // ζ (quantum/fine structure)
};

// Key mathematical relationships
const UNITY_RESONANCE = FIELD_CONSTANTS.α4 * FIELD_CONSTANTS.α5; // = 1.0
const COMPACTIFICATION_RADIUS = FIELD_CONSTANTS.α4; // T^16 torus radius
```

### 3. Statement System (Layer 1)

**Purpose**: Create semantic relationships between data through triple statements. For encoded multimedia streams, special "coordinates" statements contain the compact representation needed to reconstruct the original data.

```typescript
interface Statement {
  subject: CID;           // What we're making a claim about
  predicate: string;      // The relationship type
  object: CID | string;   // The target of the relationship
}

// Special statement types for substrate encoding
interface CoordinatesStatement extends Statement {
  predicate: 'coordinates';
  object: CID; // CID of the coordinates object
}

interface CoordinatesObject {
  version: 2;
  algorithm: 'primeos-substrate';
  
  // Object space references (compact)
  objectSpace: {
    refs: ObjectSpaceReference[];
    matchRate: number; // Percentage in object space
  };
  
  // Block space pages (as CIDs)
  blockSpace: {
    pages: Array<{
      index: number;
      cid: CID;
      length: number;
    }>;
  };
  
  // Reconstruction metadata
  metadata: {
    originalSize: number;
    totalPages: number;
    compressionRatio: number;
    features: {
      resonanceDict: boolean;
      xorBalance: boolean;
      gSymmetry: boolean;
      torusPeriodicity: boolean;
    };
  };
}

class StatementADL {
  // Create statement
  state(statement: Statement): Promise<CID>;
  
  // Create coordinates statement for encoded data
  stateCoordinates(dataCID: CID, coords: CoordinatesObject): Promise<CID>;
  
  // Query statements
  findBySubject(subject: CID): Promise<Statement[]>;
  findByPredicate(predicate: string): Promise<Statement[]>;
  findByObject(object: CID): Promise<Statement[]>;
  
  // Get coordinates for reconstruction
  getCoordinates(dataCID: CID): Promise<CoordinatesObject | null>;
  
  // Revoke statement
  revoke(statementCID: CID): Promise<void>;
}
```

### 3. View ADLs (Layer 2)

**Purpose**: Interpret statements through different access patterns.

#### Graph View
```typescript
interface GraphNode {
  cid: CID;
  data: any;
  edges: GraphEdge[];
}

interface GraphEdge {
  from: CID;
  to: CID;
  predicate: string;
  weight?: number;
}

class GraphADL {
  buildView(statements: Statement[]): GraphView;
  traverse(start: CID, depth: number): GraphNode[];
  findPath(from: CID, to: CID): CID[];
}
```

#### Object View
```typescript
interface ObjectView {
  [key: string]: any;
}

class ObjectADL {
  buildView(statements: Statement[]): ObjectView;
  get(key: string): any;
  set(key: string, value: any): void;
}
```

#### Stream View
```typescript
interface StreamEvent {
  cid: CID;
  timestamp: number;
  data: any;
}

class StreamADL {
  buildView(statements: Statement[]): AsyncIterable<StreamEvent>;
  subscribe(filter: StreamFilter): AsyncIterable<StreamEvent>;
}
```

#### Column View
```typescript
interface ColumnView {
  columns: Map<string, any[]>;
  rows: number;
}

class ColumnADL {
  buildView(statements: Statement[]): ColumnView;
  query(sql: string): any[];
  aggregate(column: string, operation: AggregateOp): number;
}
```

## API Specification

### Mutation API

```typescript
interface MutationAPI {
  // Data operations
  createDigest(data: Uint8Array, options?: DigestOptions): Promise<CID>;
  
  // Statement operations
  state(statement: Statement): Promise<CID>;
  stateBatch(statements: Statement[]): Promise<CID[]>;
  revokeStatement(cid: CID): Promise<void>;
}
```

### Query API

```typescript
interface QueryAPI {
  // Raw data access
  getDigest(cid: CID): Promise<UniversalDigest>;
  getData(cid: CID): Promise<Uint8Array>;
  
  // View access
  getView(cid: CID, viewType: ViewType): Promise<any>;
  
  // GraphQL interface
  graphql(query: string, variables?: any): Promise<any>;
  
  // Statement queries
  getStatements(filter: StatementFilter): Promise<Statement[]>;
}
```

### GraphQL Schema

```graphql
type Query {
  # Get data with specific view
  data(cid: ID!, view: ViewType!): ViewResult
  
  # Graph traversal
  node(cid: ID!): GraphNode
  path(from: ID!, to: ID!): [ID!]
  
  # Statement queries
  statements(
    subject: ID
    predicate: String
    object: ID
    limit: Int
  ): [Statement!]
}

type Mutation {
  # Create data
  createDigest(data: String!): ID!
  
  # Create statement
  state(
    subject: ID!
    predicate: String!
    object: ID!
  ): ID!
}

enum ViewType {
  GRAPH
  OBJECT
  STREAM
  COLUMN
  TENSOR
}
```

## Storage Interface

The substrate package is storage-agnostic but requires:

```typescript
interface StorageAdapter {
  put(cid: CID, data: Uint8Array): Promise<void>;
  get(cid: CID): Promise<Uint8Array>;
  has(cid: CID): Promise<boolean>;
  delete(cid: CID): Promise<void>;
}
```

Default implementation uses IPFS, but can use any CID-addressable storage.

## Usage Examples

### Basic Usage

```typescript
import { Substrate } from '@primeos/substrate';

const substrate = new Substrate({
  storage: new IPFSAdapter(ipfs)
});

// Store data
const data = new TextEncoder().encode('Hello, World!');
const cid = await substrate.mutations.createDigest(data);

// Create statement
const statementCID = await substrate.mutations.state({
  subject: cid,
  predicate: 'type',
  object: 'greeting'
});

// State who created it
await substrate.mutations.state({
  subject: statementCID,
  predicate: 'createdBy',
  object: 'alice'
});

// State when created
await substrate.mutations.state({
  subject: statementCID,
  predicate: 'createdAt',
  object: '2024-01-15T10:00:00Z'
});

// Query as graph
const graph = await substrate.queries.getView(cid, 'graph');
```

### Streaming Multimedia with Object Space

```typescript
// Initialize substrate with object space
const objectSpace = new ObjectSpace();
const substrate = new Substrate({
  storage: new IPFSAdapter(ipfs),
  objectSpace: objectSpace
});

// Create encoder with all optimizations
const encoder = substrate.createEncoder({
  useResonanceDict: true,
  useXorBalance: true,
  useGSymmetry: true,
  useTorusPeriodicity: true,
  objectSpaceThreshold: 0.9
});

// Stream video file
const readStream = fs.createReadStream('video.mp4');
const encodedStream = readStream.pipeThrough(encoder);

const blockCIDs = [];
const objectRefs = [];

// Process encoded chunks
for await (const chunk of encodedStream) {
  if (chunk.type === 'object-ref') {
    // Page matched object space - just store coordinates
    objectRefs.push({
      index: chunk.pageIndex,
      coords: chunk.coordinates
    });
    console.log(`Page ${chunk.pageIndex}: IN object space (${chunk.coordinates.resonance})`);
  } else {
    // Page didn't match - store as block
    const cid = await substrate.storage.put(
      chunk.statement.subject,
      chunk.data
    );
    blockCIDs.push({
      index: chunk.pageIndex,
      cid: cid,
      length: chunk.data.length
    });
    console.log(`Page ${chunk.pageIndex}: NOT in object space, stored as ${cid}`);
  }
}

// Create coordinates object
const coordinates: CoordinatesObject = {
  version: 2,
  algorithm: 'primeos-substrate',
  objectSpace: {
    refs: objectRefs,
    matchRate: objectRefs.length / (objectRefs.length + blockCIDs.length)
  },
  blockSpace: {
    pages: blockCIDs
  },
  metadata: {
    originalSize: /* file size */,
    totalPages: objectRefs.length + blockCIDs.length,
    compressionRatio: /* calculated */,
    features: {
      resonanceDict: true,
      xorBalance: true,
      gSymmetry: true,
      torusPeriodicity: true
    }
  }
};

// Store coordinates and create statement
const coordsCID = await substrate.storage.put(coordinates);
const videoCID = /* CID representing the video */;

await substrate.mutations.stateCoordinates(videoCID, coordinates);

console.log(`Video encoded:`);
console.log(`  Object space pages: ${objectRefs.length} (${(coordinates.objectSpace.matchRate * 100).toFixed(1)}%)`);
console.log(`  Block space pages: ${blockCIDs.length}`);
console.log(`  Compression ratio: ${coordinates.metadata.compressionRatio.toFixed(2)}×`);
```

### Reconstructing from Coordinates

```typescript
// Get coordinates for a file
const coords = await substrate.queries.getCoordinates(videoCID);

if (!coords) {
  throw new Error('No coordinates found for this CID');
}

// Create decoder
const decoder = substrate.createDecoder();

// Reconstruct pages
const pages = [];

// Process in order
for (let i = 0; i < coords.metadata.totalPages; i++) {
  // Check object space first
  const objRef = coords.objectSpace.refs.find(r => r.index === i);
  
  if (objRef) {
    // Calculate from object space
    const page = objectSpace.calculatePage(objRef.coords);
    pages.push(page);
  } else {
    // Fetch from block space
    const blockRef = coords.blockSpace.pages.find(p => p.index === i);
    if (blockRef) {
      const blockData = await substrate.storage.get(blockRef.cid);
      pages.push(blockData);
    }
  }
}

// Decode pages back to original data
const reconstructed = await decoder.decode(pages);
```

### GraphQL Queries

```typescript
const result = await substrate.queries.graphql(`
  query {
    node(cid: "${cid}") {
      data
      edges {
        predicate
        to {
          data
        }
      }
    }
  }
`);
```

## Configuration

```typescript
interface SubstrateConfig {
  storage: StorageAdapter;
  enableCache?: boolean;      // Default: true
  cacheSize?: number;        // Default: 1000 entries
}
```

## Error Handling

```typescript
class SubstrateError extends Error {
  code: ErrorCode;
}

enum ErrorCode {
  INVALID_DIGEST = 'INVALID_DIGEST',
  ATTESTATION_NOT_FOUND = 'ATTESTATION_NOT_FOUND',
  INVALID_VIEW_TYPE = 'INVALID_VIEW_TYPE',
  STORAGE_ERROR = 'STORAGE_ERROR'
}
```

## Performance Considerations

1. **Page-aligned operations**: Process data in 48-byte chunks for optimal performance
2. **Batch statements**: Use `stateBatch` for multiple statements
3. **View caching**: Views are cached by default to avoid recomputation
4. **Streaming**: Use streaming APIs for large files
5. **Object space optimization**: 
   - Text files typically achieve 18-27% object space match
   - Structured data can achieve up to 80% object space match
   - Binary/compressed data typically < 2% object space match
   - Each object space match saves 48 bytes of storage + 1 CID
6. **Compression ratios** (from research):
   - Pattern-following data: up to 50× compression
   - Symmetric data with G-symmetry: up to 100× compression
   - General text: 2-4× compression
   - Random data: 1.6× compression
7. **Mathematical optimizations**:
   - Resonance dictionary: 96 unique values reduce entropy
   - XOR balance: Save 1 byte per 64-byte hypercube
   - T^16 periodicity: Model hidden dimensions efficiently
   - Conservation laws: Built-in error detection

## Security Considerations

1. **No built-in encryption**: Data is stored as-is
2. **Statement trust**: Trust is established through statement source
3. **Access control**: Implement at application layer
4. **Content validation**: The substrate doesn't validate content semantics

## Migration Guide

From raw IPFS:
```typescript
// Before
const cid = await ipfs.add(data);

// After  
const cid = await substrate.mutations.createDigest(data);
```

From traditional database:
```typescript
// Before
db.insert({ id: 123, name: 'Alice' });

// After
const cid = await substrate.mutations.createDigest(data);
await substrate.mutations.state({
  subject: cid,
  predicate: 'type',
  object: 'user'
});
```

## Roadmap

- [ ] v1.0: Core functionality with object/block space separation
- [ ] v1.1: Full mathematical optimizations (G-symmetry, T^16 periodicity)
- [ ] v1.2: Additional view types (Tensor, TimeSeries)
- [ ] v1.3: Distributed object space consensus
- [ ] v2.0: Native WASM implementation

## Mathematical Foundation

The substrate is built on rigorous mathematical research:

1. **64-48-16 Dimensional Structure**: Reality is 64D with 48D observable and 16D compactified
2. **768-Element Super-Cycle**: Decomposes as 12 × 64D hypercubes
3. **Symmetry Group G = ℤ/48ℤ × ℤ/256ℤ**: Order 12,288 encoding transformations
4. **96 Unique Resonance Values**: Complete spectrum for pattern matching
5. **Conservation Laws**: Perfect at 8k-dimensional scales
6. **Unity Resonance**: α₄ × α₅ = 1 creates special 48-byte pages

See `/research` directory for complete mathematical proofs and analysis.

## License

MIT