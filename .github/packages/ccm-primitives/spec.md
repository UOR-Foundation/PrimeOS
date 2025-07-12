# **Rust CCM Primitives Specification**

*(Normative, version 1.0, July 2025)*

> **Purpose** — This document defines the public Rust crate **`ccm-primitives`**.
> The crate exposes *all* low‑level building‑blocks required by any Coherence‑Centric‑Mathematics (CCM) implementation, including—but not limited to—the BJC‑1.0 codec described earlier. The spec is exhaustive; implementations **MUST** follow it to claim conformance.

---

## 1 Scope & non‑goals

|                              | In scope                      | Out of scope                    |
| ---------------------------- | ----------------------------- | ------------------------------- |
| Resonance algebra (R map)    | ✔︎                            | —                               |
| CCM coherence norm           | ✔︎                            | Visualisation/plotting          |
| BJC‑1.0 (encode/decode)      | ✔︎                            | Other packet formats (BJD, BJE) |
| α‑vector enumeration tools   | ✔︎ (library helpers)          | Network registry client         |
| Cryptographic tags (SHA‑256) | ✔︎                            | Post‑quantum hashes             |
| `#![no_std]` support         | ✔︎                            | WASI I/O plumbing               |
| Unsafe Rust                  | ✖︎ (*MUST NOT* in safe build) | •                               |

---

## 2 Crate metadata (`Cargo.toml`)

```toml
[package]
name            = "ccm-primitives"
version         = "1.0.0"
edition         = "2021"
license         = "MIT"
description     = "Core primitives for Coherence‑Centric Mathematics (CCM)."
repository      = "https://github.com/UOR-Foundation/PrimeOS"

[features]
default   = ["std", "sha2"]
std       = []                # pulls in std::vec, std::error, etc.
alloc     = []                # for no_std + alloc
bigint    = ["num-bigint"]    # α beyond 128‑bit mantissa
binary128 = ["rug"]           # quad‑precision floats
ct        = ["subtle"]        # constant‑time comparisons
sha2      = ["sha2"]          # SHA‑256 integrity tags
```

*Implementation **MUST** build* with `--no-default-features --features alloc` on `#![no_std]` targets.

---

## 3 Module layout

```
crate
 ├─ alpha        // α‑vector representation & validation
 ├─ bitword      // fixed‑/variable‑length bit‑vectors
 ├─ resonance    // R(b) implementation
 ├─ coherence    // ‖·‖ᶜ generic norm
 ├─ codec
 │   ├─ bjc      // BJC‑1.0 encoder/decoder
 │   └─ search   // generic b_min search back‑end
 ├─ page         // page‑symmetry helpers
 ├─ hash         // SHA‑256 wrappers
 ├─ error        // unified error enum
 ├─ math         // internal math utils (log‑domain ops)
 └─ tests        // conformance suite (Appendix A)
```

Each top‑level module **MUST** be `pub mod`.

---

## 4 Core data‑types

### 4.1 `AlphaVec`

```rust
/// Positive real constants α₀ … αₙ₋₁ with αₙ₋₂·αₙ₋₁ ≈ 1.
pub struct AlphaVec<P: Float> {
    pub values: Box<[P]>,   // length = n
}
```

*Constraints*

* `3 ≤ n ≤ 64` for `P = f64`; up to 512 if `binary128` feature enabled.
* `0 < αᵢ ≤ 2^128`.
* `alpha[n-2] * alpha[n-1] == 1` within `P::EPSILON` relative tolerance.

### 4.2 `BitWord`

*Compile‑time length (`const N: usize`) variant* and *heap variant* (`BitWordDyn`).
Both **MUST** provide:

```rust
fn xor(&self, rhs: &Self) -> Self;
fn popcount(&self) -> u32;
fn to_usize(&self) -> usize;          // N ≤ 64
```

### 4.3 `Resonance`

```rust
pub trait Resonance<P: Float> {
    fn r(&self, alpha: &AlphaVec<P>) -> P;           // R(b)
    fn class_members(&self) -> [Self; 4];            // up to 4 variants
}
```

### 4.4 `Coherence`

```rust
pub trait Coherence<P: Float> {
    fn coherence_norm_sq(&self) -> P;
}
```

*Default blanket impl* via grade decomposition for multivectors that
implement `GradeN`.

### 4.5 `BjcPacket`

```rust
pub struct BjcPacket {
    pub n_bits: u8,          // header n (bit‑7 ⇒ binary128)
    pub log2_k: u8,
    pub r_min: Vec<u8>,      // 8 or 16 bytes
    pub flips: u8,
    pub page: Vec<u8>,       // empty when k = 1
    pub hash: Option<[u8;32]>
}
```

---

## 5 Public API surface (`lib.rs`)

```rust
pub use alpha::{AlphaVec, AlphaError};
pub use bitword::{BitWord, BitWordDyn};
pub use resonance::{Resonance};
pub use coherence::{Coherence};
pub use codec::bjc::{encode_bjc, decode_bjc, BjcPacket};
pub use codec::search::{search_b_min};
pub use page::{page_of, inject_page};
pub use error::CcmError;
```

All items **MUST** be documented with `///` comments.
Missing/inaccurate docs is a spec violation.

---

## 6 Algorithms (normative)

### 6.1 Resonance map

```rust
R(b) = Π α_i^{b_i}            // power by 0/1 selection
```

Implementations **MUST** provide both:

* **Direct product** (`feature = "std"`) – multiply in *ascending index order*.
  Overflow/underflow **MUST** be detected; trigger `CcmError::FpRange`.

* **Log‑domain** (`math::log_r`) – sum log₂αᵢ·bᵢ; final value via `exp2`.
  Used automatically when `popcount > 32` or `|log₂R| > 1024`.

### 6.2 BJC encoding

*Exactly* the 6‑step algorithm (§ 2.6 of the user spec), with the
following edge rules:

| Step | Corner case              | Required behaviour                           |
| ---- | ------------------------ | -------------------------------------------- |
| 1    | `n < 2`                  | return `Err(CcmError::InvalidLength)`        |
| 2    | ties                     | choose numerically smallest `x` (big‑endian) |
| 3    | —                        | restrict XOR to last two bits only           |
| 4    | `k=1`                    | omit page field entirely                     |
| 5    | n>53 without `binary128` | return `CcmError::UnsupportedPrecision`      |
| 6    | `magic == "BJC0"`        | skip hash field                              |

Encoder **MUST NOT** allocate on the heap in `const N ≤ 64` builds
unless `feature = "bigint"` is active.

### 6.3 BJC decoding

Steps mirror § 2.7; additional checks:

* `R(b_min)` **MUST** match stored `r_min` within `≤ 2 ulp` (f64) or
  `≤ 1 ulp` (binary128).
* SHA‑256 **MUST** be verified when present; failure ⇒ `Err(CcmError::HashMismatch)`.
* Unknown `magic` ⇒ `Err(CcmError::UnknownMagic)`.

### 6.4 Constant‑time feature

When crate feature `ct` is enabled, **ALL** comparisons in Steps 2 & 3
must use `subtle::Choice` and avoid early returns.

---

## 7 Error handling (`enum CcmError`)

```rust
pub enum CcmError {
    InvalidLength,
    AlphaConstraint,
    UnsupportedPrecision,
    FpRange,
    HashMismatch,
    UnknownMagic,
    SearchExhausted,
    IoError(core::fmt::Error),          // only when std
    Custom(&'static str),
}
```

`std::error::Error` impl **MUST** be present when `std` feature enabled.

---

## 8 Inter‑operability rules

*Crate version `1.y.z`* **MUST** maintain semver compatibility for all public
items documented herein.
Breaking changes bump the *major* (`2.0.0`).

`BjcPacket` produced by any compliant encoder **MUST** decode successfully
with any compliant decoder of the *same major* version.

---

## 9 Security considerations

| Threat               | Mitigation                                                                        |
| -------------------- | --------------------------------------------------------------------------------- |
| **Packet tampering** | SHA‑256 verification mandatory except for “BJC0”.                                 |
| **Timing attacks**   | Enable `ct` on sensitive channels; provides branch‑free path.                     |
| **Float poisoning**  | All FP ops guarded by finite/normal asserts.                                      |
| **DoS via big n**    | Hard cap `MAX_N = 512`; search aborts after 2ⁿ iterations with `SearchExhausted`. |

---

## 10 Testing & conformance

*Directory `tests/`* **MUST** contain:

1. **`vectors.rs`** – exhaustive tests for Appendix A (256 kB fixture in `tests/data`).
2. **`property.rs`** – `proptest` round‑trip for random `(n, α, k, b)`.
3. **`no_std.rs`** – builds crate with `--no-default-features --features alloc`.

Continuous integration **MUST** execute:

```bash
cargo test --all-features
cargo test --no-default-features --features alloc
```

Success criteria exactly match § 7 of the user spec (encode = vector,
decode = raw, 10 k randoms per nominated n).

---

## 11 Examples (non‑normative)

```rust
use ccm_primitives::{
    AlphaVec, BitWord, encode_bjc, decode_bjc
};

// PrimeOS (n = 8)
let alpha = AlphaVec::<f64>::try_from(vec![1.0, 1.61803398875, 1.0/1.61803398875,
                                           1.41421, 0.707106, 1.0, 0.5, 2.0])?;
let raw = BitWord::<8>::from(0b1011_0010);
let packet = encode_bjc(&raw, &alpha, 1, true)?;      // k = 1, include hash
let decoded = decode_bjc(&packet, &alpha)?;
assert_eq!(raw, decoded);
```

---

## 12 License & governance

Licensed **MIT**.
All pull‑requests **MUST** pass the conformance suite.
The UOR Foundation oversees change control; open an issue and
request a “spec‑impact label” to signal proposed breaking changes.

---

### **End of Rust CCM Primitives Specification v 1.0**
