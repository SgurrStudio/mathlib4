/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.NumberTheory.Normal.Basic
public import Mathlib.Probability.StrongLaw

/-!
# Borel's normal number theorem

We prove **Borel's normal number theorem** (É. Borel, 1909): Lebesgue-almost every real number is
absolutely normal. In particular absolutely normal numbers exist.

## Strategy

1. Under the uniform probability measure on `[0, 1)`, the events `{x | digit b x n = a}`
   (`n : ℕ`) are mutually independent and each has probability `1 / b`
   (`Real.iIndepSet_digit_eq`, `Real.volume_restrict_digit_eq`). This is a counting argument:
   the first `n` digits of `x` are determined by `⌊x * b ^ n⌋₊`, which is uniformly distributed
   on `{0, …, b ^ n - 1}`.
2. The strong law of large numbers applied to the indicators of these events shows that almost
   every `x ∈ [0, 1)` is simply normal in base `b`; since digits are invariant under integer
   translation this holds almost everywhere on `ℝ` (`Real.ae_isSimplyNormalIn`).
3. Splitting the positions `i` according to `i mod k`, a block of `k` base-`b` digits of `x`
   starting at position `r + m * k` is a single base-`b ^ k` digit of `x * b ^ r`. Hence if
   `x * b ^ r` is simply normal in base `b ^ k` for all `0 ≤ r < k`, then every block of length `k`
   has frequency `b⁻ᵏ` in base `b` (`Real.isNormalIn_of_isSimplyNormalIn_pow`).
4. Multiplication by `b ^ r` preserves null sets, and there are countably many bases, which gives
   `Real.ae_isAbsolutelyNormal`.

## References

* [É. Borel, *Les probabilités dénombrables et leurs applications arithmétiques*][Borel1909]
-/

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Real

variable {b : ℕ} {x : ℝ}

@[simp]
theorem isSimplyNormalIn_add_intCast_iff (m : ℤ) :
    IsSimplyNormalIn b (x + m) ↔ IsSimplyNormalIn b x := by
  sorry

@[fun_prop]
theorem measurable_digit (b n : ℕ) : Measurable fun x : ℝ ↦ digit b x n := by
  sorry

/-- Under the uniform measure on `[0, 1)`, each base-`b` digit takes each value `a < b` with
probability `1 / b`. -/
theorem volume_restrict_digit_eq (hb : 0 < b) (n : ℕ) {a : ℕ} (ha : a < b) :
    volume.restrict (Ico (0 : ℝ) 1) {x | digit b x n = a} = (b : ℝ≥0∞)⁻¹ := by
  sorry

/-- Under the uniform measure on `[0, 1)`, the events "the `n`-th digit is `a`" are mutually
independent. -/
theorem iIndepSet_digit_eq (hb : 0 < b) {a : ℕ} (ha : a < b) :
    iIndepSet (fun n ↦ {x : ℝ | digit b x n = a}) (volume.restrict (Ico (0 : ℝ) 1)) := by
  sorry

/-- **Borel's theorem on simply normal numbers**: almost every real number is simply normal in
base `b`. -/
theorem ae_isSimplyNormalIn (hb : 0 < b) : ∀ᵐ x : ℝ, IsSimplyNormalIn b x := by
  sorry

/-- If `x * b ^ r` is simply normal in base `b ^ k` for all `0 ≤ r < k`, for every `k ≥ 1`, then
`x` is normal in base `b`. -/
theorem isNormalIn_of_isSimplyNormalIn_pow (hb : 0 < b)
    (h : ∀ k, 0 < k → ∀ r < k, IsSimplyNormalIn (b ^ k) (x * (b : ℝ) ^ r)) :
    IsNormalIn b x := by
  sorry

/-- Almost every real number is normal in base `b`. -/
theorem ae_isNormalIn (hb : 0 < b) : ∀ᵐ x : ℝ, IsNormalIn b x := by
  sorry

/-- **Borel's normal number theorem**: almost every real number is absolutely normal. -/
theorem ae_isAbsolutelyNormal : ∀ᵐ x : ℝ, IsAbsolutelyNormal x := by
  sorry

/-- Absolutely normal numbers exist. -/
theorem exists_isAbsolutelyNormal : ∃ x : ℝ, IsAbsolutelyNormal x := by
  sorry

/-- The set of real numbers that are not absolutely normal is a Lebesgue null set. -/
theorem volume_setOf_not_isAbsolutelyNormal : volume {x : ℝ | ¬ IsAbsolutelyNormal x} = 0 := by
  sorry

end Real
