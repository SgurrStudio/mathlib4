/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Normal numbers

A real number `x` is *normal in base `b`* if, in its base-`b` expansion, every block of `k` digits
occurs with asymptotic frequency `b⁻ᵏ`. It is *absolutely normal* if it is normal in every base
`b ≥ 2`. These notions were introduced by É. Borel in 1909.

## Main definitions

* `Real.digit b x n`: the `n`-th digit (counted from `0`) after the radix point of the base-`b`
  expansion of `x`, i.e. `⌊x * b ^ (n + 1)⌋ mod b`. This is the expansion of the fractional part
  of `x` that does not end in an infinite string of `b - 1`s.
* `Real.blockCount b x w N`: the number of positions `i < N` at which the block `w` of digits
  occurs in the base-`b` expansion of `x`.
* `Real.IsSimplyNormalIn b x`: every digit occurs with frequency `1 / b`.
* `Real.IsNormalIn b x`: every block of `k` digits occurs with frequency `b⁻ᵏ`.
* `Real.IsAbsolutelyNormal x`: `x` is normal in every base `b ≥ 2`.

## Main statements

* `Real.IsNormalIn.isSimplyNormalIn`: normal numbers are simply normal.
* `Real.isNormalIn_add_intCast_iff`: normality only depends on the fractional part.
* `Real.IsNormalIn.irrational`: a number normal in some base `b ≥ 2` is irrational.

Borel's conjecture, that every irrational algebraic number is absolutely normal, is stated in
`Wanted/NumberTheory/Normal/Basic.lean`.

## References

* [É. Borel, *Les probabilités dénombrables et leurs applications arithmétiques*][Borel1909]
* [Y. Bugeaud, *Distribution modulo one and Diophantine approximation*][Bugeaud2012]
-/

@[expose] public section

open Filter Topology

namespace Real

/-- The `n`-th digit (counted from `0`) after the radix point of the base-`b` expansion of `x`,
namely `⌊x * b ^ (n + 1)⌋ mod b`. For `x ∈ [0, 1)` this agrees with `Real.digits x b n`. -/
noncomputable def digit (b : ℕ) (x : ℝ) (n : ℕ) : ℕ :=
  (⌊x * (b : ℝ) ^ (n + 1)⌋ % (b : ℤ)).toNat

/-- The number of positions `i < N` such that the block of digits of `x` (in base `b`) starting at
position `i` is the word `w`. -/
noncomputable def blockCount (b : ℕ) (x : ℝ) {k : ℕ} (w : Fin k → Fin b) (N : ℕ) : ℕ :=
  open Classical in
  ((Finset.range N).filter fun i ↦ ∀ j : Fin k, digit b x (i + j) = w j).card

/-- A real number `x` is *simply normal in base `b`* if each of the `b` digits occurs in the
base-`b` expansion of `x` with asymptotic frequency `1 / b`. -/
def IsSimplyNormalIn (b : ℕ) (x : ℝ) : Prop :=
  ∀ d : Fin b, Tendsto (fun N : ℕ ↦ (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N) atTop
    (𝓝 (b : ℝ)⁻¹)

/-- A real number `x` is *normal in base `b`* if every block `w` of `k` digits occurs in the
base-`b` expansion of `x` with asymptotic frequency `b⁻ᵏ`. -/
def IsNormalIn (b : ℕ) (x : ℝ) : Prop :=
  ∀ (k : ℕ) (w : Fin k → Fin b), Tendsto (fun N : ℕ ↦ (blockCount b x w N : ℝ) / N) atTop
    (𝓝 ((b : ℝ) ^ k)⁻¹)

/-- A real number is *absolutely normal* if it is normal in every base `b ≥ 2`. -/
def IsAbsolutelyNormal (x : ℝ) : Prop :=
  ∀ b : ℕ, 2 ≤ b → IsNormalIn b x

variable {b : ℕ} {x : ℝ}

theorem digit_lt (hb : 0 < b) (x : ℝ) (n : ℕ) : digit b x n < b := by
  sorry

@[simp]
theorem digit_add_intCast (b : ℕ) (x : ℝ) (m : ℤ) (n : ℕ) :
    digit b (x + m) n = digit b x n := by
  sorry

@[simp]
theorem blockCount_add_intCast (b : ℕ) (x : ℝ) (m : ℤ) {k : ℕ} (w : Fin k → Fin b) (N : ℕ) :
    blockCount b (x + m) w N = blockCount b x w N := by
  sorry

theorem blockCount_le (b : ℕ) (x : ℝ) {k : ℕ} (w : Fin k → Fin b) (N : ℕ) :
    blockCount b x w N ≤ N := by
  sorry

theorem IsNormalIn.isSimplyNormalIn (h : IsNormalIn b x) : IsSimplyNormalIn b x := by
  sorry

@[simp]
theorem isNormalIn_add_intCast_iff (m : ℤ) : IsNormalIn b (x + m) ↔ IsNormalIn b x := by
  sorry

@[simp]
theorem isAbsolutelyNormal_add_intCast_iff (m : ℤ) :
    IsAbsolutelyNormal (x + m) ↔ IsAbsolutelyNormal x := by
  sorry

/-- A rational number is not normal in any base `b ≥ 2`: its expansion only contains finitely
many distinct blocks of each length, so long enough blocks are missing. -/
theorem IsNormalIn.irrational (hb : 2 ≤ b) (h : IsNormalIn b x) : Irrational x := by
  sorry

theorem IsAbsolutelyNormal.irrational (h : IsAbsolutelyNormal x) : Irrational x :=
  (h 2 le_rfl).irrational le_rfl

end Real
