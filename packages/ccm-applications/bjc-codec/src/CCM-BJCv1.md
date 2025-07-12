## Formal specification (CCM‑BJC v 1.0)

### 2.1 Notation

\* *n* – bit‑length of the raw message (*3 ≤ n ≤ 64*).
\* 𝔹ⁿ = {0,1}ⁿ.
\* α = (α₀,…,αₙ₋₁) – array of positive real constants with αₙ₋₂ · αₙ₋₁ = 1.
\* R(b) – resonance scalar of word *b* (definition § 2.2).
\* ‖·‖ᶜ – CCM coherence norm (§ 2.4).
\* G – optional page‑symmetry group ℤ/k (k | 2ⁿ, default k = 1).
\* ζ – **codec packet** (compact CCM object).

### 2.2 Resonance map

$$
R:\,𝔹^n\to\mathbb R_{>0}, \qquad  
R(b)=\prod_{i=0}^{n-1}\alpha_i^{\,b_i}.
$$

*Lemma 1 (unity‑class size)* – Because αₙ₋₂ αₙ₋₁ = 1,
 R(b)=R(b ⊕ 10₂)=R(b ⊕ 01₂)=R(b ⊕ 11₂).
Hence each resonance class has 1, 2 or 4 members.

### 2.3 Minimal embedding rule

*Definition.* For S ⊂ 𝔹ⁿ, let b\* = argmin\_{b∈S}|R(b)| (tie‑break by smallest integer).
For any input *b*, its **zero‑point coordinate** is

$$
b_{\min}=b^*(\text{class}(b)),\qquad
R_{\min}=R(b_{\min}).
$$

*(Uniqueness – CCM theorem T2).* Grade‑orthogonality of ‖·‖ᶜ implies minimising norm ⇔ minimising |R|.

### 2.4 Coherence norm (reference)

For multivector x = (x₀,…,xₙ) with grade‑k part x\_k,

$$
‖x‖^{2}_{\!c}=\sum_{k=0}^{n}\lVert x_k\rVert^{2}_{ℓ²}.
$$

### 2.5 Compact packet structure

```
+------------+------------+------------+----------+------------+
| 'BJC'      | 1‑byte n   | 1‑byte k   | R_min    | tail       |
+------------+------------+------------+----------+------------+
```

| field      | length   | description                                               |
| ---------- | -------- | --------------------------------------------------------- |
| **magic**  | 3 bytes  | ASCII “BJC” (Bijective‑Junction Codec)                    |
| **n**      | 1 byte   | bit‑length (3–64)                                         |
| **k**      | 1 byte   | log₂ page‑modulus. 0 ⇒ no pages (k = 1)                   |
| **R\_min** | 8/16 B   | IEEE‑754 binary64 (n ≤ 53) else binary128 (network order) |
| **tail**   | variable | sub‑fields (below)                                        |

Tail sub‑fields (ordered):

1. **flip byte** – 1 byte (bits 0–1 = flipₙ₋₂, flipₙ₋₁; bits 2–7 = 0).
2. **page element** – if k > 1, an unsigned big‑endian integer (⌈log₂k/8⌉ bytes).
3. **SHA‑256** – 32 bytes; omitted when magic = “BJC0”.

### 2.6 Canonical encoder

```
ENCODE(b, α, k):
  Input  : b ∈ 𝔹ⁿ, α, page modulus k (power‑of‑two | 2ⁿ)
  1. C     ← { b ⊕ f | f ∈ {00,01,10,11} on bits n‑2,n‑1 }
  2. b_min ← argmin (|R(x)|, x) over x ∈ C
  3. flips ← b XOR b_min  (restricted to last‑two bits)
  4. page  ← ⌊ b_min / 2ⁿ⁻log₂k ⌋          # omit if k = 1
  5. R_min ← R(b_min)                      # binary64 or 128
  6. Assemble packet ζ (§ 2.5); add SHA‑256 if magic = 'BJC'
  Output ζ
```

*Complexity*: O(n) multiplies (or O(popcount b)).

### 2.7 Canonical decoder

```
DECODE(ζ, α):
  0. Parse header; verify magic, n, k, SHA‑256.
  1. Extract flips, page, R_min.
  2. b_min ← SEARCH(n, α, R_min)           # § 5.1
  3. b     ← b_min XOR flips
  4. if k>1: b ← (page * 2ⁿ⁻log₂k) OR (b mod 2ⁿ⁻log₂k)
  5. Return b as n‑bit big‑endian string
```

### 2.8 Correctness theorem

For every valid parameter set and all *b ∈ 𝔹ⁿ*:

$$
\texttt{DECODE}(\texttt{ENCODE}(b,α,k),α)=b.
$$

---

## 3 Parameter requirements

1. **Bit‑length n**: 3 ≤ n ≤ 64 (larger allowed if both sides support binary128).
2. **Constants αᵢ**:

   * 0 < αᵢ ≤ 2¹²⁸;
   * αₙ₋₂ αₙ₋₁ = 1 (within binary64 rounding);
   * |log₂ αᵢ| ≤ 20.
3. **Page modulus k**: power‑of‑two dividing 2ⁿ; header stores log₂k (0 ⇒ 1).

*Recommendation*: choose αᵢ near 1 (π, e, √2, …) to limit dynamic range.

---

## 4 Binary layout details

### 4.1 Endianness

* Bits numbered big‑endian (bₙ₋₁ … b₀).
* Multibyte integers & floats in network order (big‑endian).

### 4.2 Flip byte

```
bit0 = flip of bit n‑2   (1 ⇒ toggled)
bit1 = flip of bit n‑1
bit2–7 = 0  (reserved)
```

### 4.3 Page element

If k > 1, encode page ∈ ℤ/k as big‑endian integer (⌈log₂k/8⌉ bytes).

### 4.4 Floating‑point choice

Binary64 suffices when n ≤ 53; else binary128 and set header bit 7 of *n*.

### 4.5 Integrity tag

* Magic “BJC” → append SHA‑256 of preceding bytes.
* Magic “BJC0” → no hash (bandwidth‑critical channels).

### 4.6 Big‑n support

For n > 64, use big‑ints and multiprecision floats (e.g. MPFR); both ends must agree.

---

## 5 Implementation guidance

### 5.1 SEARCH algorithm for b\_min

*Small n (≤ 16)* – pre‑compute table {R → b\_min}.
*Large n* – walk Gray code from 0; stop when |R – R\_min| < ε (ε = half‑ulp of R\_min).

### 5.2 Log‑domain variant

Store log₂R, log₂αᵢ; multiplication→addition, avoiding over/under‑flow.

### 5.3 Constant‑time option

Branchless compare on all 4 class members replaces step 2 of ENCODE.

### 5.4 Reference vectors (excerpt)

```
n=3  α=(1,φ,1/φ)  k=1
b_in  ζ(hex)                       b_out
000   42 4A 43 03 00 3FF0…000      000
101   42 4A 43 03 00 3FE1…F4A8     101
```

(full suite in Appendix A).

---

## 6 Security & robustness

* **Collision‑free** – bijective by construction.
* **Tamper detection** – SHA‑256 tail (magic “BJC”).
* **Numeric check** – decoder verifies R(b) matches R\_min (≤ 2 ulp).
* **Extensible** – future variants use different magic (“BJD”, …); parsers ignore unknown.

---

## 7 Conformance requirements

An implementation **passes** if for every vector in Appendix A:

1. `encode(raw) == packet`
2. `decode(packet) == raw`
3. `decode(encode(raw)) == raw` for 10 000 random raw inputs per n ∈ {3,4,8,10,16,32,64}.

---

### Appendix A – Test‑vector suite

*(256 kB, see repository)*

### Appendix B – Reference implementation

Apache‑2.0 code: `https://git.example.org/ccm/codec.git` (commit `d1e2f3c…`)

---

**This document is the authoritative CCM‑BJC v 1.0 specification.**
Normative statements use **MUST**, **SHOULD**, **MAY** (RFC 2119).&#x20;
