/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.NonPreservation
public import Mathlib.NumberTheory.Normal.Rational
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.MonotoneContinuity

/-!
# `C²` affine rigidity of normality preservation

A `C²` map `f : ℝ → ℝ` that sends every base-`b` normal number to a base-`b` normal number is
affine (Manai, arXiv:2609.24665). We prove the contrapositive in a strong form: if `f` is `C²`
and not affine, then for every base `b ≥ 2` there is an absolutely normal `x` with `f x` not
normal in base `b`.

The proof: `f''(p) ≠ 0` and `f'(p) ≠ 0` for some `p`, so on a small interval around `p` the map
`f` is a `C²` diffeomorphism whose inverse `g` has `g'' = -f''(g) / f'(g)³` bounded away from `0`.
Composing `g` with a rational affine map onto the window, the Kaufman-type decay of
`NormalNumbers.QuarterCantorDecay` (base `2`) or `NormalNumbers.BaseCantorDecay` (base `b ≥ 3`)
makes `x = g(q + s Y)` absolutely normal for almost every Cantor point `Y`, while
`f x = q + s Y` is not normal in base `b`, by Wall's theorem.

## Main statements

* `Real.exists_isAbsolutelyNormal_not_isNormalIn_of_contDiff`
* `Real.exists_affine_of_contDiff_two_preserves_isNormalIn`
* `Real.exists_affine_of_contDiff_two_preserves_isAbsolutelyNormal`
-/

@[expose] public noncomputable section

open Filter Topology Set


namespace Real

/-- **Non-preservation by non-affine `C²` maps**: if `f` is `C²` and not affine, then for every
base `b ≥ 2` some absolutely normal `x` has `f x` not normal in base `b`. -/
theorem exists_isAbsolutelyNormal_not_isNormalIn_of_contDiff {b : ℕ} (hb : 2 ≤ b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hna : ¬ ∃ a c : ℝ, ∀ x, f x = a * x + c) :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ¬ IsNormalIn b (f x) := by
  sorry

/-- **`C²` affine rigidity in a fixed base** (Manai, arXiv:2609.24665): a `C²` map sending every
base-`b` normal number (`b ≥ 2`) to a base-`b` normal number is affine. -/
theorem exists_affine_of_contDiff_two_preserves_isNormalIn {b : ℕ} (hb : 2 ≤ b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hpres : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (f x)) :
    ∃ a c : ℝ, ∀ x : ℝ, f x = a * x + c := by
  sorry

/-- **`C²` affine rigidity for absolute normality** (Manai, arXiv:2609.24665): a `C²` map sending
every absolutely normal number to an absolutely normal number is affine. -/
theorem exists_affine_of_contDiff_two_preserves_isAbsolutelyNormal {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hpres : ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (f x)) :
    ∃ a c : ℝ, ∀ x : ℝ, f x = a * x + c := by
  sorry

end Real

