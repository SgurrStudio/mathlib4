/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.NumberTheory.Normal.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Open problems and deep rigidity theorems on normality-preserving maps

This file states (using `proof_wanted`) deep theorems and open conjectures concerning which maps
preserve normality in a fixed base `b ≥ 2` or absolute normality:

* Multiplicative rigidity for absolute normality (Hochman–Shmerkin; arXiv:2609.24665).
* Two-sided sharpness of `C²` rigidity: existence of a non-affine `C^{1,1}` diffeomorphism of `ℝ`
  whose forward *and* inverse maps both preserve absolute normality (strengthening Manai's
  forward `C^{1,1}` sharpness theorem proved in `Mathlib.NumberTheory.Normal.C11Sharpness`).

Non-preservation under squaring, inversion, the exponential and Möbius maps, in every base and
for absolute normality, is proved in `Mathlib.NumberTheory.Normal.NonPreservation`, `C²`
affine rigidity in `Mathlib.NumberTheory.Normal.Rigidity`, forward `C^{1,1}` sharpness in every
base and for absolute normality in `Mathlib.NumberTheory.Normal.C11Sharpness`
(`Real.exists_nonAffine_C11_diffeomorph_preserves_isNormalIn`), and multiplicative rigidity in a
fixed base in `Mathlib.NumberTheory.Normal.MulRigidity` (`Real.preserves_isNormalIn_mul_iff`).
-/

namespace Real

/-! ### Multiplicative rigidity -/

/-- **Multiplicative rigidity for absolute normality**: a real number `α` preserves absolute
normality under multiplication if and only if `α` is a nonzero rational number.

The fixed-base version is `Real.preserves_isNormalIn_mul_iff`; the absolute version needs the
Hochman–Shmerkin equidistribution theorem for bases multiplicatively independent of `2`. -/
proof_wanted preserves_isAbsolutelyNormal_mul_iff {α : ℝ} :
    (∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (α * x)) ↔
      ∃ q : ℚ, q ≠ 0 ∧ (q : ℝ) = α

/-! ### Two-sided sharpness of `C²` rigidity -/

/-- **Two-sided sharpness of `C²` rigidity** (strengthening of Manai, arXiv:2609.24665,
Theorem 1.4): there exists a non-affine `C^{1,1}` diffeomorphism of `ℝ` (i.e. a bijection
`e : ℝ ≃ ℝ` with `e` and `e.symm` of class `C¹` and locally Lipschitz derivative `deriv e`) that
preserves absolute normality in *both* directions.

Forward preservation in every base `b ≥ 2` and for absolute normality is proved in
`Real.exists_nonAffine_C11_diffeomorph_preserves_isNormalIn`
(`Mathlib.NumberTheory.Normal.C11Sharpness`). -/
proof_wanted exists_nonAffine_C11_diffeomorph_preserves_isAbsolutelyNormal :
    ∃ e : ℝ ≃ ℝ, ContDiff ℝ 1 e ∧ ContDiff ℝ 1 e.symm ∧ LocallyLipschitz (deriv e) ∧
      (¬ ∃ a c : ℝ, ∀ x : ℝ, e x = a * x + c) ∧
      (∀ x : ℝ, IsAbsolutelyNormal x ↔ IsAbsolutelyNormal (e x))

end Real
