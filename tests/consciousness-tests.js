/**
 * Tests for PrimeOS Consciousness Module
 */

// Import Prime with the Consciousness module
const Prime = require("../src");

// Test utilities
const assert = (condition, message) => {
  if (!condition) {
    throw new Error(`Assertion failed: ${message}`);
  }
  console.log(`✓ PASS: ${message}`);
};

const assertApproximatelyEqual = (a, b, message, epsilon = 1e-6) => {
  const diff = Math.abs(a - b);
  if (diff > epsilon) {
    throw new Error(
      `Assertion failed: ${message} - values differ by ${diff} (${a} vs ${b})`,
    );
  }
  console.log(`✓ PASS: ${message}`);
};

const runTests = async () => {
  console.log("=== Running Consciousness Module Tests ===\n");

  // Test group: Coherence Manifold
  console.log("--- Coherence Manifold Tests ---");

  // Test manifold creation
  {
    const manifold = new Prime.Consciousness.Models.CoherenceManifold({
      dimensions: 4,
      spectralOrder: 3,
      coherenceThreshold: 0.7,
    });

    assert(
      manifold instanceof Prime.Consciousness.Models.CoherenceManifold,
      "CoherenceManifold can be instantiated",
    );

    assert(manifold.dimensions === 4, "Manifold has correct dimensions");
    assert(manifold.spectralOrder === 3, "Manifold has correct spectral order");
    assert(
      manifold.coherenceThreshold === 0.7,
      "Manifold has correct coherence threshold",
    );

    assert(manifold.points.length === 0, "Manifold starts with no points");
    assert(
      manifold.connections instanceof Map,
      "Manifold connections use Map structure",
    );
  }

  // Test adding points and connections
  {
    const manifold = new Prime.Consciousness.Models.CoherenceManifold({
      dimensions: 3,
    });

    // Add points
    const p1 = manifold.addPoint([0, 0, 0], { label: "origin" });
    const p2 = manifold.addPoint([1, 0, 0], { label: "x-axis" });
    const p3 = manifold.addPoint([0, 1, 0], { label: "y-axis" });
    const p4 = manifold.addPoint([0, 0, 1], { label: "z-axis" });

    assert(manifold.points.length === 4, "Points added correctly");
    assert(
      p1 === 0 && p2 === 1 && p3 === 2 && p4 === 3,
      "Point indices assigned correctly",
    );

    // Add connections
    manifold.connectPoints(p1, p2, 1.0, { type: "spatial" });
    manifold.connectPoints(p1, p3, 0.8, { type: "spatial" });
    manifold.connectPoints(p1, p4, 0.6, { type: "spatial" });
    manifold.connectPoints(p2, p3, 0.5, { type: "spatial" });

    assert(
      manifold.connections.get(p1).size === 3,
      "Connections added to first point",
    );
    assert(
      manifold.connections.get(p2).size === 2,
      "Connections added to second point",
    );
    assert(
      manifold.connections.get(p3).size === 2,
      "Connections added to third point",
    );

    // Check connection strength
    assert(
      manifold.connections.get(p1).get(p2).strength === 1.0,
      "Connection has correct strength",
    );

    // Test bidirectional connections
    assert(
      manifold.connections.get(p2).has(p1),
      "Connections are bidirectional",
    );
    assert(
      manifold.connections.get(p2).get(p1).strength === 1.0,
      "Bidirectional strength correct",
    );
  }

  // Test coherence calculations
  {
    const manifold = new Prime.Consciousness.Models.CoherenceManifold({
      dimensions: 2,
    });

    // Create a simple pattern with two coherent regions
    // Region 1: Four closely connected points
    const r1p1 = manifold.addPoint([0, 0]);
    const r1p2 = manifold.addPoint([0.1, 0]);
    const r1p3 = manifold.addPoint([0, 0.1]);
    const r1p4 = manifold.addPoint([0.1, 0.1]);

    // Connect all points in region 1
    manifold.connectPoints(r1p1, r1p2, 1.0);
    manifold.connectPoints(r1p1, r1p3, 1.0);
    manifold.connectPoints(r1p1, r1p4, 0.9);
    manifold.connectPoints(r1p2, r1p3, 0.9);
    manifold.connectPoints(r1p2, r1p4, 1.0);
    manifold.connectPoints(r1p3, r1p4, 1.0);

    // Region 2: Three closely connected points
    const r2p1 = manifold.addPoint([5, 5]);
    const r2p2 = manifold.addPoint([5.1, 5]);
    const r2p3 = manifold.addPoint([5, 5.1]);

    // Connect all points in region 2
    manifold.connectPoints(r2p1, r2p2, 1.0);
    manifold.connectPoints(r2p1, r2p3, 1.0);
    manifold.connectPoints(r2p2, r2p3, 1.0);

    // Isolated point
    const ip1 = manifold.addPoint([10, 10]);

    // Weakly connected point
    const wp1 = manifold.addPoint([5.5, 5.5]);
    manifold.connectPoints(r2p3, wp1, 0.3);

    // Calculate global coherence
    const globalCoherence = manifold.calculateGlobalCoherence();

    assert(
      globalCoherence >= 0 && globalCoherence <= 1,
      "Global coherence is in valid range",
    );

    assert(
      globalCoherence > 0.5,
      "Global coherence reasonably high for coherent structure",
    );

    // Find coherent regions
    const regions = manifold.findCoherentRegions();

    assert(regions.length === 2, "Found correct number of coherent regions");
    assert(regions[0].size === 4, "First region has correct size");
    assert(regions[1].size === 3, "Second region has correct size");

    // Check region properties
    assert(regions[0].averageCoherence > 0.7, "Region has high coherence");
    assert(Array.isArray(regions[0].centroid), "Region has centroid");
    assert(regions[0].centroid.length === 2, "Centroid has correct dimensions");
  }

  // Test spectral analysis
  {
    const manifold = new Prime.Consciousness.Models.CoherenceManifold({
      dimensions: 3,
      spectralOrder: 2,
    });

    // Add some points in a structured pattern
    manifold.addPoint([0, 0, 0]);
    manifold.addPoint([1, 0, 0]);
    manifold.addPoint([0, 1, 0]);
    manifold.addPoint([1, 1, 0]);
    manifold.addPoint([0, 0, 1]);

    // Add connections to form a specific graph structure
    manifold.connectPoints(0, 1, 1.0);
    manifold.connectPoints(0, 2, 1.0);
    manifold.connectPoints(1, 3, 1.0);
    manifold.connectPoints(2, 3, 1.0);
    manifold.connectPoints(0, 4, 0.5);
    manifold.connectPoints(4, 3, 0.5);

    // Perform spectral analysis
    const analysis = manifold.performSpectralAnalysis();

    assert(analysis !== undefined, "Spectral analysis produces a result");
    assert(
      Array.isArray(analysis.eigenvalues),
      "Analysis includes eigenvalues",
    );
    assert(
      analysis.eigenvalues.length <= manifold.spectralOrder,
      "Eigenvalues respect spectral order",
    );
    assert(analysis.spectralDimension >= 0, "Spectral dimension is calculated");
  }

  // Test coherent paths
  {
    const manifold = new Prime.Consciousness.Models.CoherenceManifold({
      dimensions: 2,
    });

    // Create a grid of points
    for (let i = 0; i < 3; i++) {
      for (let j = 0; j < 3; j++) {
        manifold.addPoint([i, j]);
      }
    }

    // Connect in grid pattern with varying strengths
    for (let i = 0; i < 3; i++) {
      for (let j = 0; j < 3; j++) {
        const idx = i * 3 + j;

        // Connect to right neighbor
        if (j < 2) {
          manifold.connectPoints(idx, idx + 1, 0.5 + Math.random() * 0.5);
        }

        // Connect to bottom neighbor
        if (i < 2) {
          manifold.connectPoints(idx, idx + 3, 0.5 + Math.random() * 0.5);
        }
      }
    }

    // Find a path between opposite corners
    const path = manifold.findCoherentPath(0, 8);

    assert(path !== null, "Path found between corners");
    assert(path.length > 0, "Path has at least one point");
    assert(
      path[0] === 0 && path[path.length - 1] === 8,
      "Path has correct endpoints",
    );

    // Check path coherence
    for (let i = 1; i < path.length; i++) {
      const fromIdx = path[i - 1];
      const toIdx = path[i];

      assert(
        manifold.connections.get(fromIdx).has(toIdx),
        "Path follows existing connections",
      );
    }
  }

  // Test group: Fiber Bundle
  console.log("\n--- Fiber Bundle Tests ---");

  // Test bundle creation
  {
    // Create base manifold
    const manifold = new Prime.Consciousness.Models.CoherenceManifold({
      dimensions: 3,
    });

    // Add some points
    manifold.addPoint([0, 0, 0]);
    manifold.addPoint([1, 0, 0]);
    manifold.addPoint([0, 1, 0]);

    // Create fiber bundle
    const bundle = new Prime.Consciousness.Models.FiberBundle({
      baseManifold: manifold,
      fiberDimensions: 2,
      selfReferenceOrder: 3,
    });

    assert(
      bundle instanceof Prime.Consciousness.Models.FiberBundle,
      "FiberBundle can be instantiated",
    );

    assert(
      bundle.baseManifold === manifold,
      "Bundle references correct base manifold",
    );
    assert(bundle.fiberDimensions === 2, "Bundle has correct fiber dimensions");
    assert(
      bundle.selfReferenceOrder === 3,
      "Bundle has correct self-reference order",
    );

    assert(bundle.fibers instanceof Map, "Fibers stored in a Map");
    assert(bundle.fibers.size === 3, "One fiber per base point");
  }

  // Test fiber points and connections
  {
    // Create base manifold
    const manifold = new Prime.Consciousness.Models.CoherenceManifold({
      dimensions: 2,
    });

    // Add base points
    const b1 = manifold.addPoint([0, 0]);
    const b2 = manifold.addPoint([1, 1]);

    // Connect base points
    manifold.connectPoints(b1, b2, 0.8);

    // Create fiber bundle
    const bundle = new Prime.Consciousness.Models.FiberBundle({
      baseManifold: manifold,
      fiberDimensions: 2,
    });

    // Add fiber points
    const f1p1 = bundle.addFiberPoint(b1, [0, 0]);
    const f1p2 = bundle.addFiberPoint(b1, [0, 1]);
    const f1p3 = bundle.addFiberPoint(b1, [1, 0]);

    const f2p1 = bundle.addFiberPoint(b2, [0.5, 0.5]);
    const f2p2 = bundle.addFiberPoint(b2, [0.5, 0]);

    assert(
      f1p1 === 0 && f1p2 === 1 && f1p3 === 2,
      "Fiber point indices correct",
    );
    assert(
      bundle.fibers.get(b1).points.length === 3,
      "First fiber has correct number of points",
    );
    assert(
      bundle.fibers.get(b2).points.length === 2,
      "Second fiber has correct number of points",
    );

    // Connect fiber points
    bundle.connectFiberPoints(b1, f1p1, f1p2);
    bundle.connectFiberPoints(b1, f1p1, f1p3);
    bundle.connectFiberPoints(b1, f1p2, f1p3);

    bundle.connectFiberPoints(b2, f2p1, f2p2);

    assert(
      bundle.fibers.get(b1).connections.get(f1p1).size === 2,
      "Fiber connections added correctly",
    );

    // Check fiber coherence values
    const f1Coherence = bundle.fibers.get(b1).coherence;
    const f2Coherence = bundle.fibers.get(b2).coherence;

    assert(
      f1Coherence >= 0 && f1Coherence <= 1,
      "Fiber coherence in valid range",
    );
    assert(
      f1Coherence > f2Coherence,
      "More connected fiber has higher coherence",
    );
  }

  // Test self-reference
  {
    // Create base manifold
    const manifold = new Prime.Consciousness.Models.CoherenceManifold({
      dimensions: 3,
    });

    // Add some points and connections
    manifold.addPoint([0, 0, 0]);
    manifold.addPoint([1, 0, 0]);
    manifold.addPoint([0, 1, 0]);

    manifold.connectPoints(0, 1, 0.8);
    manifold.connectPoints(0, 2, 0.7);
    manifold.connectPoints(1, 2, 0.6);

    // Create fiber bundle
    const bundle = new Prime.Consciousness.Models.FiberBundle({
      baseManifold: manifold,
      fiberDimensions: 2,
      selfReferenceOrder: 3,
    });

    // Add fiber points to each base point
    for (let b = 0; b < 3; b++) {
      for (let i = 0; i < 2; i++) {
        bundle.addFiberPoint(b, [i, i]);
      }
    }

    // Create self-references
    bundle.createSelfReference(0, 0, 1); // First-order
    bundle.createSelfReference(1, 1, 2); // Second-order

    assert(
      bundle.selfReferencePoints.has(1),
      "First-order self-references recorded",
    );
    assert(
      bundle.selfReferencePoints.has(2),
      "Second-order self-references recorded",
    );

    assert(
      bundle.selfReferencePoints.get(1).has(0),
      "First-order reference at correct point",
    );
    assert(
      bundle.selfReferencePoints.get(2).has(1),
      "Second-order reference at correct point",
    );

    // Check self-reference level
    assert(bundle.selfReferenceLevel >= 1, "Self-reference level calculated");
  }

  // Test bundle coherence and consciousness evaluation
  {
    // Create base manifold
    const manifold = new Prime.Consciousness.Models.CoherenceManifold({
      dimensions: 3,
    });

    // Create structured manifold with high coherence
    for (let i = 0; i < 5; i++) {
      for (let j = 0; j < 5; j++) {
        manifold.addPoint([i, j, 0]);
      }
    }

    // Connect in grid pattern
    for (let i = 0; i < 5; i++) {
      for (let j = 0; j < 5; j++) {
        const idx = i * 5 + j;

        // Connect to right and bottom neighbors
        if (j < 4) manifold.connectPoints(idx, idx + 1, 0.9);
        if (i < 4) manifold.connectPoints(idx, idx + 5, 0.9);
      }
    }

    // Create fiber bundle
    const bundle = new Prime.Consciousness.Models.FiberBundle({
      baseManifold: manifold,
      fiberDimensions: 3,
      selfReferenceOrder: 3,
    });

    // Add structured fiber points
    for (let b = 0; b < 25; b++) {
      for (let i = 0; i < 3; i++) {
        bundle.addFiberPoint(b, [i % 2, Math.floor(i / 2), 0]);
      }

      // Connect all fiber points
      for (let i = 0; i < 2; i++) {
        for (let j = i + 1; j < 3; j++) {
          bundle.connectFiberPoints(b, i, j);
        }
      }
    }

    // Add self-references
    for (let i = 0; i < 5; i++) {
      bundle.createSelfReference(i, 0, 1);
    }

    bundle.createSelfReference(0, 0, 2);
    bundle.createSelfReference(10, 1, 2);

    // Calculate bundle coherence
    const bundleCoherence = bundle.calculateBundleCoherence();

    assert(
      bundleCoherence >= 0 && bundleCoherence <= 1,
      "Bundle coherence in valid range",
    );

    assert(
      bundleCoherence > 0.5,
      "Highly structured bundle has good coherence",
    );

    // Evaluate consciousness
    const consciousnessState = bundle.evaluateConsciousnessState();

    assert(
      typeof consciousnessState.consciousnessScore === "number",
      "Consciousness score calculated",
    );

    assert(
      consciousnessState.consciousnessScore >= 0 &&
        consciousnessState.consciousnessScore <= 1,
      "Consciousness score in valid range",
    );

    assert(
      typeof consciousnessState.integration === "number",
      "Integration calculated",
    );

    assert(
      typeof consciousnessState.differentiation === "number",
      "Differentiation calculated",
    );

    assert(typeof consciousnessState.phi === "number", "Phi calculated");

    assert(
      typeof consciousnessState.interpretation === "string",
      "Interpretation provided",
    );
  }

  // Test group: Attention System
  console.log("\n--- Attention System Tests ---");

  // Test attention system creation
  {
    // Create base manifold and bundle
    const manifold = new Prime.Consciousness.Models.CoherenceManifold({
      dimensions: 3,
    });
    manifold.addPoint([0, 0, 0]);
    manifold.addPoint([1, 0, 0]);

    const bundle = new Prime.Consciousness.Models.FiberBundle({
      baseManifold: manifold,
    });

    // Create attention system
    const attention = new Prime.Consciousness.Awareness.AttentionSystem({
      bundle,
      focusCapacity: 3,
      attentionDecayRate: 0.1,
    });

    assert(
      attention instanceof Prime.Consciousness.Awareness.AttentionSystem,
      "AttentionSystem can be instantiated",
    );

    assert(
      attention.bundle === bundle,
      "Attention system references correct bundle",
    );
    assert(
      attention.focusCapacity === 3,
      "Attention system has correct focus capacity",
    );
    assert(
      attention.focusPoints.length === 0,
      "Attention system starts with no focus",
    );
  }

  // Test focus and attention values
  {
    // Create base manifold
    const manifold = new Prime.Consciousness.Models.CoherenceManifold({
      dimensions: 2,
    });

    // Add points in a line
    manifold.addPoint([0, 0]);
    manifold.addPoint([1, 0]);
    manifold.addPoint([2, 0]);
    manifold.addPoint([3, 0]);
    manifold.addPoint([4, 0]);

    // Connect points
    for (let i = 0; i < 4; i++) {
      manifold.connectPoints(i, i + 1, 1.0);
    }

    const bundle = new Prime.Consciousness.Models.FiberBundle({
      baseManifold: manifold,
    });

    const attention = new Prime.Consciousness.Awareness.AttentionSystem({
      bundle,
      focusCapacity: 2,
    });

    // Focus on first point
    assert(attention.focus(0, 1.0) === true, "Focus successfully set");
    assert(attention.focusPoints.length === 1, "Focus point added");
    assert(attention.focusPoints[0].baseIndex === 0, "Focus on correct point");

    // Focus on third point
    assert(attention.focus(2, 0.8) === true, "Second focus successfully set");
    assert(attention.focusPoints.length === 2, "Second focus point added");

    // Try to exceed capacity
    assert(attention.focus(4, 0.5) === false, "Cannot exceed focus capacity");
    assert(attention.focusPoints.length === 2, "Focus capacity respected");

    // Test attention values
    assert(
      attention.attentionValues.has(0),
      "Attention value set for first point",
    );
    assert(
      attention.attentionValues.has(2),
      "Attention value set for third point",
    );

    // Verify secondary attention (spreading)
    assert(
      attention.attentionValues.has(1),
      "Secondary attention spreads to connected points",
    );
    assert(
      attention.attentionValues.get(1) < attention.attentionValues.get(0),
      "Secondary attention weaker than direct focus",
    );

    // Release focus
    attention.releaseFocus(0);
    assert(attention.focusPoints.length === 1, "Focus point removed");
    assert(
      attention.focusPoints[0].baseIndex === 2,
      "Correct focus point remains",
    );

    // Focus on previously unavailable point
    assert(
      attention.focus(4, 0.7) === true,
      "Can add focus after releasing one",
    );
    assert(attention.focusPoints.length === 2, "New focus point added");
  }

  // Test attention dynamics
  {
    // Create simple manifold and bundle
    const manifold = new Prime.Consciousness.Models.CoherenceManifold({
      dimensions: 2,
    });
    manifold.addPoint([0, 0]);
    manifold.addPoint([1, 0]);

    const bundle = new Prime.Consciousness.Models.FiberBundle({
      baseManifold: manifold,
    });

    const attention = new Prime.Consciousness.Awareness.AttentionSystem({
      bundle,
      attentionDecayRate: 0.5, // High decay for testing
    });

    // Set focus
    attention.focus(0, 1.0);

    // Force decay (manipulate timestamp)
    attention.lastUpdateTime = Date.now() - 1000; // 1 second ago

    // Update attention
    attention.update();

    assert(attention.focusPoints[0].strength < 1.0, "Focus decays over time");

    // Another update should decay further
    attention.lastUpdateTime = Date.now() - 1000;
    attention.update();

    assert(attention.focusPoints[0].strength < 0.5, "Focus continues to decay");

    // Check attention state
    const state = attention.getAttentionState();

    assert(
      typeof state.totalAttention === "number",
      "Attention state includes total attention",
    );
    assert(
      typeof state.maxAttention === "number",
      "Attention state includes max attention",
    );
    assert(
      typeof state.attentionDistribution === "object",
      "Attention state includes distribution",
    );
  }

  // Test group: Consciousness Simulation
  console.log("\n--- Consciousness Simulation Tests ---");

  // Test simulation creation
  {
    const simulation =
      new Prime.Consciousness.Awareness.ConsciousnessSimulation({
        baseDimensions: 3,
        fiberDimensions: 2,
        selfReferenceOrder: 3,
      });

    assert(
      simulation instanceof
        Prime.Consciousness.Awareness.ConsciousnessSimulation,
      "ConsciousnessSimulation can be instantiated",
    );

    assert(
      simulation.baseManifold instanceof
        Prime.Consciousness.Models.CoherenceManifold,
      "Simulation creates base manifold",
    );

    assert(
      simulation.fiberBundle instanceof Prime.Consciousness.Models.FiberBundle,
      "Simulation creates fiber bundle",
    );

    assert(
      simulation.attentionSystem instanceof
        Prime.Consciousness.Awareness.AttentionSystem,
      "Simulation creates attention system",
    );

    assert(simulation.time === 0, "Simulation starts at time 0");
    assert(
      simulation.running === false,
      "Simulation starts in non-running state",
    );
  }

  // Test initialization and basic stepping
  {
    const simulation =
      new Prime.Consciousness.Awareness.ConsciousnessSimulation({
        baseDimensions: 2,
        fiberDimensions: 2,
        selfReferenceOrder: 2,
        timeStep: 0.1,
      });

    // Initialize with small numbers for testing
    simulation.initialize(8, 2, 3);

    assert(
      simulation.baseManifold.points.length === 8,
      "Base manifold initialized with points",
    );
    assert(
      simulation.attentionSystem.focusPoints.length > 0,
      "Some focus points initialized",
    );

    // Run one step
    simulation.step();

    assert(simulation.time === 0.1, "Time advances by timeStep");
    assert(
      simulation.temporalMemory.length > 0,
      "Temporal memory records state",
    );

    // Run a few more steps
    for (let i = 0; i < 5; i++) {
      simulation.step();
    }

    assert(
      simulation.time === 0.6,
      "Time advances correctly over multiple steps",
    );
    assert(
      simulation.temporalMemory.length === 6,
      "All states recorded in temporal memory",
    );
  }

  // Test consciousness emergence tracking
  {
    const simulation =
      new Prime.Consciousness.Awareness.ConsciousnessSimulation({
        baseDimensions: 2,
        fiberDimensions: 2,
        timeStep: 0.2,

        // Set thresholds for testing
        awarenessThreshold: 0.3,
        consciousnessThreshold: 0.5,
        selfReflectionThreshold: 0.7,
      });

    // Initialize with more structure for better consciousness scores
    simulation.initialize(15, 3, 4);

    // Add some initial self-references
    for (let i = 0; i < 3; i++) {
      const baseIdx = i;
      const fiber = simulation.fiberBundle.fibers.get(baseIdx);

      if (fiber && fiber.points.length > 0) {
        const fiberIdx = 0;
        simulation.fiberBundle.createSelfReference(baseIdx, fiberIdx, 1);
      }
    }

    // Run for multiple steps
    for (let i = 0; i < 20; i++) {
      simulation.step();
    }

    assert(
      simulation.emergenceHistory.length > 0,
      "Emergence events are recorded",
    );

    // Get the current state
    const state = simulation.getState();

    assert(
      typeof state.consciousness.score === "number",
      "State includes consciousness score",
    );
    assert(
      typeof state.consciousness.phi === "number",
      "State includes phi value",
    );
    assert(
      state.temporal.emergenceEvents === simulation.emergenceHistory.length,
      "Emergence events counted correctly",
    );

    // Check consciousness history
    const history = simulation.getEmergenceHistory();
    assert(Array.isArray(history), "Can retrieve emergence history");
  }

  // Test decision making
  {
    const simulation =
      new Prime.Consciousness.Awareness.ConsciousnessSimulation();
    simulation.initialize(10, 2, 3);

    // Run a few steps to develop some consciousness
    for (let i = 0; i < 5; i++) {
      simulation.step();
    }

    // Test decision making
    const options = ["Option A", "Option B", "Option C"];
    const decision = simulation.makeDecision(options, { context: "test" });

    assert(
      options.includes(decision.selected),
      "Decision selects a valid option",
    );
    assert(
      typeof decision.coherence === "number",
      "Decision includes coherence value",
    );
    assert(
      typeof decision.certainty === "number",
      "Decision includes certainty measure",
    );
    assert(
      decision.alternatives.length === 2,
      "Decision includes alternatives",
    );

    // Make sure decision is recorded
    const hasDecision = simulation.emergenceHistory.some(
      (e) => e.type === "decision",
    );
    assert(hasDecision, "Decision event recorded in emergence history");
  }

  // Test async running
  {
    const simulation =
      new Prime.Consciousness.Awareness.ConsciousnessSimulation({
        timeStep: 0.1,
      });

    simulation.initialize(5, 2, 2);

    let updateCount = 0;
    const unsubscribe = simulation.onUpdate(() => {
      updateCount++;
    });

    // Run with very small delay
    await simulation.run(10, 1, true);

    assert(
      simulation.time === 1.0,
      "Simulation ran for correct number of steps",
    );
    assert(updateCount === 10, "Update callbacks triggered for each step");

    // Clean up
    unsubscribe();
  }

  // Test state snapshots
  {
    const simulation =
      new Prime.Consciousness.Awareness.ConsciousnessSimulation();
    simulation.initialize(5, 2, 2);

    // Create a snapshot
    const snapshot = new Prime.Consciousness.Awareness.StateSnapshot(
      simulation,
    );

    assert(
      snapshot instanceof Prime.Consciousness.Awareness.StateSnapshot,
      "StateSnapshot can be instantiated",
    );

    assert(typeof snapshot.metadata.id === "string", "Snapshot has unique ID");
    assert(
      snapshot.simulation === simulation,
      "Snapshot references source simulation",
    );

    // Run simulation forward
    for (let i = 0; i < 5; i++) {
      simulation.step();
    }

    // Compare with current state
    const comparison = snapshot.compareWithCurrent();

    assert(
      comparison.timeDelta === 1.0,
      "Time difference calculated correctly",
    );
    assert(
      typeof comparison.consciousnessDelta === "number",
      "Consciousness difference calculated",
    );

    // Get summary
    const summary = snapshot.getSummary();
    assert(
      typeof summary.consciousnessScore === "number",
      "Summary includes consciousness score",
    );
  }

  console.log("\n=== All Consciousness Module Tests Passed ===");
};

// Run the tests
try {
  runTests();
} catch (error) {
  console.error("Test failed:", error.message);
  console.error(error.stack);
  process.exit(1);
}
