/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.CopelandErdos

/-!
# Normality of digits along an arithmetic progression

If `x` is normal in base `b ≥ 2`, then for every offset `a` and step `m ≥ 1`, the digit subsequence
`n ↦ Real.digit b x (a + m * n)` is normal in base `b`, and the real number formed from these
digits via `Real.ofDigits` is normal in base `b`.

## Main statements

* `Real.IsNormalIn.isNormalSeq_arithmeticProgression`: if `IsNormalIn b x` (`2 ≤ b`) and `0 < m`,
  then `IsNormalSeq b (fun n ↦ digit b x (a + m * n))`.
* `Real.IsNormalIn.ofDigits_arithmeticProgression`: the real number with base-`b` digits
  `n ↦ digit b x (a + m * n)` is normal in base `b`.

## References

* D. D. Wall, *Normal numbers*, PhD thesis, University of California, Berkeley, 1949.
* L. Kuipers and H. Niederreiter, *Uniform Distribution of Sequences*, Ch. 1 §8.
-/

@[expose] public section

namespace Real

/-- **Wall (1949)**: the base-`b` digits of a base-`b` normal number sampled along any arithmetic
progression `a + m * n` (`m ≥ 1`) form a base-`b` normal sequence. -/
theorem IsNormalIn.isNormalSeq_arithmeticProgression {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (hx : IsNormalIn b x) (a : ℕ) {m : ℕ} (hm : 0 < m) :
    IsNormalSeq b (fun n ↦ digit b x (a + m * n)) := by
  sorry

/-- The real number whose base-`b` digits are `n ↦ Real.digit b x (a + m * n)` is normal in
base `b` whenever `x` is normal in base `b` (`2 ≤ b`) and `0 < m`. -/
theorem IsNormalIn.ofDigits_arithmeticProgression {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (hx : IsNormalIn b x) (a : ℕ) {m : ℕ} (hm : 0 < m) :
    IsNormalIn b (ofDigits fun n ↦ ⟨digit b x (a + m * n), digit_lt (by omega) x _⟩) := by
  sorry

end Real
