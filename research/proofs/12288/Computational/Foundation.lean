/-!
# Computational Foundations for PrimeOS 12288 Proofs

This layer establishes the core mappings between positions, bytes, and field activation.
It provides the foundational computational interface that was missing in earlier proof attempts.
-/

import PrimeOS12288.Basic.Types
import PrimeOS12288.Constants.All
import PrimeOS12288.Axioms.Page

namespace PrimeOS12288.Computational

open PrimeOS12288

/-- Interface for computational foundations -/
class Foundation where
  /-- Core function: map position to byte value -/
  positionToByte : Position → ByteValue

  /-- Core function: check if field is active for byte -/
  isFieldActive : ByteValue → FieldIndex → Bool

  /-- Axiom: position to byte mapping is periodic with period 256 -/
  position_byte_periodic : ∀ (n : Position),
    positionToByte n = ⟨n.val % ByteSize, by
      simp [ByteSize]
      exact Nat.mod_lt n.val (by norm_num : 0 < 256)⟩

  /-- Axiom: field activation is determined by bit testing -/
  field_active_bit : ∀ (b : ByteValue) (i : FieldIndex),
    isFieldActive b i = b.val.testBit i.val

variable [Foundation]

/-- Given the foundation, derive the set of active fields for a position -/
def activeFields (n : Position) : Finset FieldIndex :=
  Finset.filter (fun i => isFieldActive (positionToByte n) i) Finset.univ

/-- Extract page index from position -/
def pageIndex (n : Position) : PageIndex :=
  ⟨n.val / PageSize, by
    simp [PageIndex, NumPages, PageSize, TotalSize] at *
    have h : n.val < TotalSize := n.isLt
    simp [TotalSize] at h
    omega⟩

/-- Extract offset within page from position -/
def pageOffset (n : Position) : PageOffset :=
  ⟨n.val % PageSize, by
    simp [PageOffset, PageSize]
    exact Nat.mod_lt n.val (by norm_num : 0 < 48)⟩

/-- Resonance computation using active fields -/
noncomputable def resonance (n : Position) : ℝ :=
  (activeFields n).prod (fun i => fieldConstant i)

/-- Basic property: position decomposes into page and offset -/
theorem position_decompose (n : Position) :
  n.val = (pageIndex n).val * PageSize + (pageOffset n).val := by
  simp [pageIndex, pageOffset]
  exact Nat.div_add_mod n.val PageSize

end PrimeOS12288.Computational
