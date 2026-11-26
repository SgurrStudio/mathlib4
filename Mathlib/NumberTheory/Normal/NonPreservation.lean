/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Imported.NormalNumbers.CantorLiouvilleAll
public import Mathlib.Imported.NormalNumbers.VisitDeviationB
public import Mathlib.NumberTheory.Normal.BasePow
public import Mathlib.NumberTheory.Normal.Bridge
public import Mathlib.NumberTheory.Normal.QuarterCantorDecay

/-!
# Squaring, inversion and the exponential do not preserve normality

Let `y` run over the quarter-Cantor set (`NormalNumbers.CantorSelfSimilar.cantorReal`): its
base-`4` digits are all `1` or `2`, so `y` is not normal in any base `2 ^ k`. For `G` one of
`√`, `x ↦ x⁻¹`, `log`, the second derivative of `G` is bounded away from `0` on `[1/2, 1]`, so the
pushforward of the quarter-Cantor law under `G` has polynomial Fourier decay
(`NormalNumbers.QuarterCantorDecay.polyDecay`), and almost every `x = G y` is absolutely normal
(Davenport–Erdős–LeVeque in every base). Then `x` is absolutely normal while `x ^ 2 = y`,
`x⁻¹ = y`, or `exp x = y` is not normal in base `2 ^ k`.

## Main statements

* `NormalNumbers.QuarterCantorDecay.ae_isAbsolutelyNormal_of_polyDecay`
* `NormalNumbers.QuarterCantorDecay.polyDecay_sqrt`, `polyDecay_inv`, `polyDecay_log`
* `NormalNumbers.QuarterCantorDecay.exists_computable_isNormal_sqrt`: an unconditional computable
  witness for the `√` case of Manai's Theorem 2.
* `Real.exists_isAbsolutelyNormal_not_isAbsolutelyNormal_sq`, `..._inv`, `..._exp`
* `Real.exists_isNormalIn_two_pow_not_isNormalIn_sq`, `..._inv`, `..._exp`: bases `b = 2 ^ k`

## References

* R. Kaufman, *On the theorem of Jarník and Besicovitch*, Acta Arith. 39 (1981).
* C. A. Mosquera, P. S. Shmerkin, *Self-similar measures: asymptotic bounds for the dimension and
  Fourier decay of smooth images*, Ann. Acad. Sci. Fenn. Math. 43 (2018).
* M. Manai, arXiv:2609.24665, Theorem 2.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology

namespace NormalNumbers.QuarterCantorDecay

open ExplicitSquare CantorSelfSimilar DecayAeNormal

/-- **Polynomial decay ⇒ `F(y)` is absolutely normal for almost every quarter-Cantor `y`.** -/
theorem ae_isAbsolutelyNormal_of_polyDecay {F : ℝ → ℝ} (hF : Measurable F) (hd : PolyDecay F) :
    ∀ᵐ ω ∂coinMeasure, Real.IsAbsolutelyNormal (F (cantorReal ω)) := by
  sorry

/-- **`√` has polynomial decay**: this proves the `√` case of `BakerBanajiQuarterCantor`. -/
theorem polyDecay_sqrt : PolyDecay Real.sqrt := by
  sorry

theorem polyDecay_inv : PolyDecay fun t => t⁻¹ := by
  sorry

theorem polyDecay_log : PolyDecay Real.log := by
  sorry

/-- An unconditional computable quarter-Cantor `y` with `√y` normal in base 2 (Manai
2609.24665, Theorem 2, the `√` case), via
`ExplicitSquare.exists_computable_isNormal_sqrt_of_polyDecay`. -/
theorem exists_computable_isNormal_sqrt :
    ∃ e : ℕ → Bool, Computable e ∧ IsNormal 2 (Real.sqrt (cantorReal e)) := by
  sorry

end NormalNumbers.QuarterCantorDecay

namespace Real

open NormalNumbers.QuarterCantorDecay

/-- An absolutely normal number whose square is not normal in any base `2 ^ k`. -/
theorem exists_isAbsolutelyNormal_forall_not_isNormalIn_two_pow_sq :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ∀ k : ℕ, 0 < k → ¬ IsNormalIn (2 ^ k) (x ^ 2) := by
  sorry

/-- An absolutely normal number whose inverse is not normal in any base `2 ^ k`. -/
theorem exists_isAbsolutelyNormal_forall_not_isNormalIn_two_pow_inv :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ∀ k : ℕ, 0 < k → ¬ IsNormalIn (2 ^ k) x⁻¹ := by
  sorry

/-- An absolutely normal number whose exponential is not normal in any base `2 ^ k`. -/
theorem exists_isAbsolutelyNormal_forall_not_isNormalIn_two_pow_exp :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ∀ k : ℕ, 0 < k → ¬ IsNormalIn (2 ^ k) (Real.exp x) := by
  sorry

/-- Squaring does not preserve absolute normality. -/
theorem exists_isAbsolutelyNormal_not_isAbsolutelyNormal_sq :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ¬ IsAbsolutelyNormal (x ^ 2) := by
  sorry

/-- Inversion does not preserve absolute normality. -/
theorem exists_isAbsolutelyNormal_not_isAbsolutelyNormal_inv :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ¬ IsAbsolutelyNormal x⁻¹ := by
  sorry

/-- The exponential does not preserve absolute normality. -/
theorem exists_isAbsolutelyNormal_not_isAbsolutelyNormal_exp :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ¬ IsAbsolutelyNormal (Real.exp x) := by
  sorry

/-- Squaring does not preserve normality in base `2 ^ k`. -/
theorem exists_isNormalIn_two_pow_not_isNormalIn_sq {k : ℕ} (hk : 0 < k) :
    ∃ x : ℝ, IsNormalIn (2 ^ k) x ∧ ¬ IsNormalIn (2 ^ k) (x ^ 2) := by
  sorry

/-- Inversion does not preserve normality in base `2 ^ k`. -/
theorem exists_isNormalIn_two_pow_not_isNormalIn_inv {k : ℕ} (hk : 0 < k) :
    ∃ x : ℝ, IsNormalIn (2 ^ k) x ∧ ¬ IsNormalIn (2 ^ k) x⁻¹ := by
  sorry

/-- The exponential does not preserve normality in base `2 ^ k`. -/
theorem exists_isNormalIn_two_pow_not_isNormalIn_exp {k : ℕ} (hk : 0 < k) :
    ∃ x : ℝ, IsNormalIn (2 ^ k) x ∧ ¬ IsNormalIn (2 ^ k) (Real.exp x) := by
  sorry

end Real
