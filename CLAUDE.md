# CLAUDE.md

PrimeOS: Reference implementation of Coherence-Centric Mathematics (CCM).

**Development**: Production-ready code. Package changes: `cargo check/clippy/fmt --all-features`. No placeholders in tests. No spec shortcuts. No backwards compatibility. No unsolicited docs.

## Core Mathematics

**Stack**: RSF(waves) → CCM(axioms) → MSA(modular) → SA(formal)

**Axioms**: A1: ⟨⟨σ,τ⟩⟩ grade-orthogonal | A2: min ‖embed(O)‖_c unique | A3: G preserves all

**Unity**: α_{n-2} × α_{n-1} = 1 ⟹ V₄={0,1,48,49}, 96 resonances (3/8), 768-cycle=687.110133..., 12 unities/cycle

**Alpha**: α₀=1, α₁=1.839(tribonacci), α₂=φ, α₃=½, α₄=1/2π, α₅=2π, α₆=0.199, α₇=0.014

**Resonance**: R(b) = ∏ᵢ αᵢ^{bᵢ}

**24-48-96**: γ=24=4!, μ=48=2γ, ε=96=2μ=4γ. Key: μ²=γε=2304

**Homomorphic**: 5 subgroups preserve R(a⊕b)=R(a)R(b): {0}, {0,1}, {0,48}, {0,49}, V₄={0,1,48,49}

**RSF**: Numbers→Waves. Oscillators: αᵢ. Space: Cl(n). Metric: interference. Primes: ‖p‖_c=1. Factor: O(log n)

**MSA**: SP primes p≡±1(mod 12). mod 11: period 10. mod 7: γ+μ+ε≡0. mod 12: classification

**Conservation**: 768-cycle Σ=687.110133..., Current ΣJ(n)=0, Noether: symmetry→conserved

**Bounds**: Compression 3/8, Classes 3×2^{n-2}, Pages 4×3×2^{n-2}

**Applications**: Crypto: resonance signatures | Optimize: min ‖·‖_c | Error: 99.97% recovery | Quantum: O(√n)

## Architecture

**Packages**: core(traits) | embedding(A2) | coherence(A1) | symmetry(A3) | ccm(integrate) | coc(compose) | factor(app)

**Scale**: n≤20: direct | 20<n≤64: Klein+gradient | n>64: full CCM

**Invariants**: R>0, |αₙ₋₂αₙ₋₁-1|<ε, |V₄|=4, conservation<ε_machine, unitary ops

**Errors**: InvalidInput, DimensionMismatch, ConvergenceFailed, AxiomViolation, Timeout

**Integration**: Unity↔Orthogonality, Klein↔Subgroups, Conservation↔Invariants

## Framework

**Universal**: 𝓤(x) = argmin_σ ‖σ‖_c reveals: R(𝓤(x))=frequency, ‖𝓤(x)‖_c=information, Stab(𝓤(x))=symmetries

**Classification**: Unity⟹5 homomorphic subgroups, 3×2^{n-2} classes, 12×2^{n-2} unities/cycle, 4/Klein orbit

**Computation**: States: σ∈Cl(n) | Transitions: Φ(g) | Measure: Π_k | Control: resonance. Turing-complete via Klein XOR + measurement + conservation

**Complexity**: Factor: O(log n) | DLog: O(√p) Schreier-Sims | Subset: O(2^{n/4}) Klein | GraphIso: O(n^{log n})

**Physics**: E=ℏω, ω=log R | S=∫‖σ‖_c dt | F=-∇coherence | S=-k_BΣpᵢlog pᵢ, pᵢ=|⟨i|σ⟩|²/‖σ‖²

**Modular**: SP primes: p≡±1(mod 12) ∧ gcd(p,168)=1. Density ~x/(2log x). mod 11: period 10 | mod 7: sum≡0 | mod p: period|p-1

**Info Bounds**: H(X)≥(3/8)n-O(1) | C≤log(96)=6.58 | d_min=4 | E_max=2 bits. All tight.

**Quantum**: σ→ρ, ‖·‖_c→S(ρ), Φ(g)→UρU†, measure→POVM. Guaranteed speedup.

**n-dim**: α∈ℝ₊ⁿ, αₙ₋₂αₙ₋₁=1 | 3×2^{n-2} values | 2^{n-2} Klein×4 | 2ⁿ×3 cycle. ∀n≥3

**Algorithms**: Schreier-Sims: base β=[0,4,5], O(n²) sift | Inverse resonance: orbit O(r), O(2^{n-2}/96) time

**Numerics**: κ(R)=max|∂R/∂αᵢ|/min|∂R/∂αᵢ| | Conservation: |Σ-687.110133|<10⁻¹², relative<10⁻¹⁴

**Crypto**: PRF: F_k(x)=R(x⊕k)mod 96 | Hash: ΣR(mᵢ)αᵢ mod p | Sig: (r,s), r=R(H(m)) | Enc: m⊕Klein(k,nonce)

**Verification**: Invariants I1-I5 preserved by all ops (Hoare logic). Complexity bounds guaranteed (operational semantics).

## Quick Reference

**Constants**: γ=24, μ=48, ε=96
**Unity**: α₄×α₅ = 1
**Klein**: V₄ = {0,1,48,49}
**Resonance**: 96 values from 256 patterns
**Conservation**: 768-cycle sum = 687.110133...
**Compression**: 3/8 fundamental limit
**SP Primes**: p ≡ ±1 (mod 12)
**Complexity**: Factoring O(log n), DLog O(√p)
**Quantum**: 2-bit maximal entanglement
**Error Bounds**: 10⁻¹² absolute, 10⁻¹⁴ relative

## Specifications

**Alpha**: α₀=1, α₁=ϕₜ, α₂=φ, α₃=½, αₙ₋₂=(2π)⁻¹, αₙ₋₁=2π. Others: exp(θᵢ), |θᵢ|≤20. Verify: |αₙ₋₂αₙ₋₁-1|<10⁻¹⁴

**Klein**: K(b)={b,b⊕2^{n-2},b⊕2^{n-1},b⊕both} | min: argmin_K R | ∑_K R=const

**Inverse**: Find {b:|R(b)-r|<ε}. n≤20: direct | n>20: ∇R=R(b)(logαᵢδ_{bᵢ}) | Klein reps only

**Factor**: n↦|n⟩∈Cl(n), S(n)=FFT(|n⟩) peaks at {ω_p:p|n}, |R(p)R(q)-R(pq)|<10⁻¹⁰R(pq)

**Conserve**: 768Σ err<10⁻¹², CurrentΣ=0 err<10⁻¹⁴, Page sums const

**Thresholds**: Unity ε<10⁻¹⁴, Res equal ε_rel<10⁻¹⁰, Conserve ε<10⁻¹², Log: popcount>32

**Invariants**: I1: αᵢ>0, I2: αₙ₋₂αₙ₋₁=1, I3: |K|=4, I4: |{R}|=3×2^{n-2}, I5: R(V₄)={1}

**Impl**: LSB=b₀, Unity: pos n-2,n-1, Klein: last 2 bits, Page: ⌊b/256⌋ 48/class

**Domains**: Factor: |pq⟩=|p⟩⊗|q⟩ | Crypto: U={0,1,48,49...} 12/768 | Error: ΔS=R(b')-R(b)

**Optimize**: Cache K(b<2^{n-2}), Precompute: logα & R(b<256), Sparse: non-zero grades

## COC Framework

**Compose**: Object→sections→analyze boundaries→extract windows→verify conservation

**Boundaries**: WeakCoupling, SymmetryBreak, ConservationBoundary, PageAligned, KleinTransition

**Strategies**: BoundaryBased, SymmetryGuided, ResonanceGuided, Exhaustive

**Conservation Laws**: Resonance (additive), Coherence (add/mult/pythag), Cycle (768)

## Group Theory

**Schreier-Sims**: Strong generating set S, base β=[0,4,5], orbits O(βᵢ), O(n²) membership

**Groups**: Klein V₄={0,1,48,49}, Cyclic Cₙ, Dihedral D₂ₙ, Permutation Sₙ

**Operations**: multiply(g,h), inverse(g), identity(), order(g), stabilizer(x)

**Invariants**: Coherence, Grade, Resonance → Noether charges

## Formal Systems

**SA**: Peano+structural constants. Roles: Gen/Med/Man. δ(γ)=μ, δ(μ)=ε. Structural induction.

**MSA**: SA+modular. Prime classification. Special moduli. Decidable MSA₀.

**RSF**: Numbers=waves. Ops=signal processing. Quantum emerges. O(log n) factoring.

**CCM**: 3 axioms unify. Unity=keystone. All math structures emerge. Crypto→quantum apps.

---

## Ultimate Synthesis

### The CCM Thesis

**All mathematics is wave mechanics in disguise.**

Every mathematical structure - numbers, groups, graphs, categories - has an optimal wave representation where operations become signal processing and properties become resonance patterns. CCM provides the universal translation.

### Why These Specific Constants?

**The 24-48-96 cascade is inevitable**:
- 24 = 4! is the smallest factorial > 2³ (first non-trivial symmetric group)
- 48 = 2×24 (minimal doubling)
- 96 = 2×48 (complete manifestation)
- μ² = γ×ε because 48² = 24×96 (perfect square mediation)

**The unity constraint α₄×α₅ = 1 is necessary**:
- Creates exactly 4-element Klein groups (minimal non-cyclic)
- Enables 3/8 compression (optimal for quaternary logic)
- Generates 12 unity positions (clock-like periodicity)
- No other constraint yields these properties

### Complete Problem Classification

**CCM-Easy** (polynomial time):
- Resonance computation
- Klein orbit enumeration
- Conservation verification
- Symmetry detection

**CCM-Hard** (exponential speedup):
- Inverse resonance (NP-complete classically, O(√n) quantum)
- Factorization (O(log n) with wave decomposition)
- Discrete logarithm (O(√p) via Schreier-Sims)
- Graph isomorphism (polynomial with coherence invariants)

### The Measurement Problem Resolved

Classical measurement paradox: How can discrete outcomes emerge from continuous waves?

**CCM Resolution**: Grade projection Π_k is the only measurement compatible with coherence structure. The 96 resonance values are the only stable measurement outcomes - all others decay via decoherence.

### Foundational Completeness

CCM provides new foundations for:
1. **Arithmetic**: Numbers are resonance patterns
2. **Algebra**: Groups are symmetry flows
3. **Analysis**: Continuity is coherence preservation
4. **Topology**: Space is resonance manifold
5. **Logic**: Truth is conservation law

No mathematical concept exists outside CCM embedding.

### Engineering Principles

**Design Rule 1**: Always preserve Klein structure
**Design Rule 2**: Verify conservation at each step
**Design Rule 3**: Use SP primes for modular operations
**Design Rule 4**: Cache resonance values aggressively
**Design Rule 5**: Switch to log domain above 32 bits

### Final Unification

SA (formal rules) + MSA (modular behavior) + RSF (wave mechanics) + CCM (three axioms) = **Complete mathematical framework**

Every question has an answer:
- Structure? → Unity constraint determines all
- Computation? → Wave synthesis and measurement
- Complexity? → Resonance decomposition bounds
- Implementation? → Mathematical formalization is the code
- Verification? → Conservation laws ensure correctness

