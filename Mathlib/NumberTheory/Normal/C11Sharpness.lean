/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.NumberTheory.Normal.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Sharpness of `C²` affine rigidity: non-affine `C^{1,1}` normality-preserving diffeomorphisms

In `Mathlib.NumberTheory.Normal.Rigidity`, it is shown that every `C²` map `f : ℝ → ℝ` preserving
normality in any fixed base `b ≥ 2` (or absolute normality) must be affine. We prove **Manai's
Theorem 1.4** (arXiv:2609.24665, §4.2), showing that the `C²` regularity hypothesis is sharp and
cannot be weakened to `C^{1,1}` (continuously differentiable with globally Lipschitz derivative):

There exists a non-affine, strictly increasing `C^{1,1}` diffeomorphism `e : ℝ ≃ ℝ` (with both
`deriv e` and `deriv e.symm` globally Lipschitz) that preserves base-`b` normality for *every*
integer base `b ≥ 2`, and hence preserves absolute normality.

## Main statements

* `Real.exists_nonAffine_C11_diffeomorph_preserves_isNormalIn`: Manai's Theorem 1.4.
* `Real.exists_nonAffine_C11_diffeomorph_preserves_isAbsolutelyNormal_forward`: absolute-normality
  corollary.

## References

* C. Manai, *On normality preserving operations*, arXiv:2609.24665, §4.2 (Theorem 1.4).
-/

@[expose] public section

namespace Real

/-- **Manai's Theorem 1.4 (`C^{1,1}` sharpness of `C²` affine rigidity)**:
there exists a non-affine, strictly increasing `C^{1,1}` diffeomorphism `e : ℝ ≃ ℝ` (with both
`deriv e` and `deriv e.symm` globally Lipschitz) that preserves base-`b` normality for *every*
integer base `b ≥ 2`, and hence preserves absolute normality. -/
theorem exists_nonAffine_C11_diffeomorph_preserves_isNormalIn :
    ∃ e : ℝ ≃ ℝ, StrictMono e ∧ ContDiff ℝ 1 e ∧ ContDiff ℝ 1 e.symm ∧
      (∃ C : NNReal, LipschitzWith C (deriv e)) ∧
      (∃ C : NNReal, LipschitzWith C (deriv e.symm)) ∧
      (¬ ∃ a c : ℝ, ∀ x : ℝ, e x = a * x + c) ∧
      (∀ b : ℕ, 2 ≤ b → ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (e x)) ∧
      (∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (e x)) := by
  sorry

/-- Corollary: there exists a non-affine `C^{1,1}` diffeomorphism of `ℝ` (with globally Lipschitz
derivative) preserving absolute normality. -/
theorem exists_nonAffine_C11_diffeomorph_preserves_isAbsolutelyNormal_forward :
    ∃ e : ℝ ≃ ℝ, ContDiff ℝ 1 e ∧ ContDiff ℝ 1 e.symm ∧ LocallyLipschitz (deriv e) ∧
      (¬ ∃ a c : ℝ, ∀ x : ℝ, e x = a * x + c) ∧
      (∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (e x)) := by
  sorry

end Real
