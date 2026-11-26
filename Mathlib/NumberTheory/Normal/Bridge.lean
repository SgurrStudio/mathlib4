/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Imported.NormalNumbers.Counting
public import Mathlib.Imported.NormalNumbers.RealDefs
public import Mathlib.NumberTheory.Normal.Basic

/-!
# Morris's normality and `Real.IsNormalIn`

The files imported from Trevor Morris's `normal-numbers` project (`Mathlib/Imported/NormalNumbers`)
state normality as `NormalNumbers.IsNormal b x`: the digit sequence of `Int.fract x` is a normal
sequence, with blocks given as lists of naturals and counted by `NormalNumbers.countOccurrences`.
We show that this is the same as `Real.IsNormalIn b x`, so that each imported theorem becomes a
statement about `Real.IsNormalIn` in one line.

## Main statements

* `Real.digitOf_fract`: Morris's digit map on `Int.fract x` is `Real.digit`.
* `Real.isNormalIn_iff_isNormal`: the two notions of normality agree.
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

theorem digitOf_fract (b : ℕ) (x : ℝ) (i : ℕ) :
    NormalNumbers.digitOf b (Int.fract x) i = digit b x i := by
  rw [← digit_fract, digit, NormalNumbers.digitOf,
    Int.toNat_emod (Int.floor_nonneg.2 (mul_nonneg (Int.fract_nonneg x) (by positivity)))
      (by positivity)]
  simp

/-- Morris's occurrence count of a nonempty block differs from `blockCount` by at most the block
length (occurrences overlapping the end of the prefix are counted only by `blockCount`). -/
theorem countOccurrences_le_blockCount {k : ℕ} (hk : 0 < k) (w : Fin k → Fin b)
    (N : ℕ) :
    NormalNumbers.countOccurrences (List.ofFn fun j ↦ (w j : ℕ))
        ((List.range N).map (NormalNumbers.digitOf b (Int.fract x))) ≤ blockCount b x w N ∧
      blockCount b x w N ≤ NormalNumbers.countOccurrences (List.ofFn fun j ↦ (w j : ℕ))
        ((List.range N).map (NormalNumbers.digitOf b (Int.fract x))) + k := by
  sorry

/-- **The bridge**: Morris's `NormalNumbers.IsNormal` is `Real.IsNormalIn`. -/
theorem isNormalIn_iff_isNormal (b : ℕ) (x : ℝ) :
    IsNormalIn b x ↔ NormalNumbers.IsNormal b x := by
  sorry

end Real
