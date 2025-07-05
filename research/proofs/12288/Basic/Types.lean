import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

namespace PrimeOS12288

/-! ## Basic Type Aliases -/

/-- The number of field constants -/
abbrev NumFields : ℕ := 8

/-- The byte size (field period) -/
abbrev ByteSize : ℕ := 256

/-- The total size of the structure -/
abbrev TotalSize : ℕ := 12288

/-- The page size -/
abbrev PageSize : ℕ := 48

/-- The number of pages -/
abbrev NumPages : ℕ := 256

/-- The cycle size -/
abbrev CycleSize : ℕ := 768

/-! ## Finite Type Definitions -/

/-- Field index type (0 to 7) -/
abbrev FieldIndex := Fin NumFields

/-- Byte value type (0 to 255) -/
abbrev ByteValue := Fin ByteSize

/-- Position in the full structure (0 to 12287) -/
abbrev Position := Fin TotalSize

/-- Page index type (0 to 255) -/
abbrev PageIndex := Fin NumPages

/-- Offset within a page (0 to 47) -/
abbrev PageOffset := Fin PageSize

/-- Position within a cycle (0 to 767) -/
abbrev CyclePosition := Fin CycleSize

/-! ## Basic Lemmas about Sizes -/

lemma total_size_eq : TotalSize = PageSize * NumPages := by norm_num

lemma cycle_size_eq : CycleSize = PageSize * 16 := by norm_num

lemma page_count_eq : NumPages = ByteSize := by norm_num

end PrimeOS12288
