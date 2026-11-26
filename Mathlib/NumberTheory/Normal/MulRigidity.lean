/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.NumberTheory.Normal.Borel
public import Mathlib.NumberTheory.Normal.NonPreservation
public import Mathlib.NumberTheory.Normal.Rational

/-!
# Multiplicative rigidity of normality in a fixed base

A real number `γ` preserves base-`b` normality under multiplication if and only if `γ` is a
nonzero rational (Dayan–Ganguly–Weiss). The reverse implication is Wall's theorem. For the
forward implication we follow the probabilistic proof of Manai (arXiv:2609.24665, §2): if
`θ` is irrational, then `θ Y` is normal in base `b ≥ 3` for almost every point `Y` of the base-`b`
Cantor law (digits in `{0, 1}`), while `Y` itself is never normal. Applying this with
`θ = γ⁻¹` and `B = b ^ 2` gives a base-`b` normal `x = γ⁻¹ Y` with `γ x = Y` not normal.

The almost sure normality is a martingale argument. Write `f_n = e(θ b^n Y)` and let `E_m`
average over all coins after the first `m` (`condE`). Then
`f_{K+t} = (f_{K+t} - E_{t+K+L} f_{K+t}) + ∑_{i < K+L} (E_{t+i+1} - E_{t+i}) f_{K+t} + E_t f_{K+t}`.
The first term is `O(|θ| b^{-L})`, the last has modulus `∏_{r<K} |cos(π θ b^r)|`, which tends to
`0` because `θ` is irrational, and for each `i` the middle terms are orthogonal bounded increments,
so their averages tend to `0` almost surely.

## Main statements

* `NormalNumbers.MulRigidity.ae_isNormal_mul_bReal`: `θ Y` is normal for a.e. Cantor point `Y`.
* `Real.exists_isNormalIn_not_isNormalIn_mul`: for irrational `γ` some base-`b` normal `x` has
  `γ x` not normal in base `b`.
* `Real.preserves_isNormalIn_mul_iff`: multiplication by `γ` preserves base-`b` normality iff
  `γ` is a nonzero rational.

## References

* Y. Dayan, A. Ganguly, B. Weiss, *Random walks on tori and normal numbers in self-similar sets*.
* C. Manai, *On normality preserving operations*, arXiv:2609.24665, §2.
-/

@[expose] public noncomputable section

namespace Real

/-- **Multiplication by an irrational breaks normality**: for every base `b ≥ 2` and irrational
`γ`, some base-`b` normal `x` has `γ x` not normal in base `b`. -/
theorem exists_isNormalIn_not_isNormalIn_mul {b : ℕ} (hb : 2 ≤ b) {γ : ℝ} (hγ : Irrational γ) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalIn b (γ * x) := by
  sorry

/-- **Multiplicative rigidity in a fixed base** (Dayan–Ganguly–Weiss; Manai, arXiv:2609.24665):
multiplication by `α` preserves base-`b` normality (`b ≥ 2`) if and only if `α` is a nonzero
rational. -/
theorem preserves_isNormalIn_mul_iff {b : ℕ} (hb : 2 ≤ b) {α : ℝ} :
    (∀ x : ℝ, IsNormalIn b x → IsNormalIn b (α * x)) ↔ ∃ q : ℚ, q ≠ 0 ∧ (q : ℝ) = α := by
  sorry

end Real
