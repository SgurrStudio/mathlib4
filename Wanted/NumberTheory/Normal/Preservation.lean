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

* Multiplicative rigidity for fixed base `b ≥ 2` and for absolute normality
  (Dayan–Ganguly–Weiss; Hochman–Shmerkin; arXiv:2609.24665).
* Sharpness of `C²` rigidity: existence of a non-affine `C^{1,1}` diffeomorphism of `ℝ`
  preserving absolute normality (arXiv:2609.24665).

Non-preservation under squaring, inversion, the exponential and Möbius maps, in every base and
for absolute normality, is proved in `Mathlib.NumberTheory.Normal.NonPreservation`, and `C²`
affine rigidity in `Mathlib.NumberTheory.Normal.Rigidity`.
-/

namespace Real

/-! ### Multiplicative rigidity -/

/-- **Multiplicative rigidity in a fixed base**: a real number `α` preserves base-`b` normality
under multiplication (`b ≥ 2`) if and only if `α` is a nonzero rational number.

The reverse implication is Wall's theorem (`Real.isNormalIn_mul_add_ratCast_iff`). The forward
implication is a deep rigidity theorem (Dayan–Ganguly–Weiss; Hochman–Shmerkin; arXiv:2609.24665). -/
proof_wanted preserves_isNormalIn_mul_iff {b : ℕ} (hb : 2 ≤ b) {α : ℝ} :
    (∀ x : ℝ, IsNormalIn b x → IsNormalIn b (α * x)) ↔ ∃ q : ℚ, q ≠ 0 ∧ (q : ℝ) = α

/-- **Multiplicative rigidity for absolute normality**: a real number `α` preserves absolute
normality under multiplication if and only if `α` is a nonzero rational number. -/
proof_wanted preserves_isAbsolutelyNormal_mul_iff {α : ℝ} :
    (∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (α * x)) ↔
      ∃ q : ℚ, q ≠ 0 ∧ (q : ℝ) = α

/-! ### Sharpness of `C²` rigidity -/

/-- **Sharpness of `C²` rigidity** (arXiv:2609.24665): there exists a non-affine `C^{1,1}`
diffeomorphism of `ℝ` (i.e. a bijection `e : ℝ ≃ ℝ` with `e` and `e.symm` of class `C¹` and
locally Lipschitz derivative `deriv e`) that preserves absolute normality. -/
proof_wanted exists_nonAffine_C11_diffeomorph_preserves_isAbsolutelyNormal :
    ∃ e : ℝ ≃ ℝ, ContDiff ℝ 1 e ∧ ContDiff ℝ 1 e.symm ∧ LocallyLipschitz (deriv e) ∧
      (¬ ∃ a c : ℝ, ∀ x : ℝ, e x = a * x + c) ∧
      (∀ x : ℝ, IsAbsolutelyNormal x ↔ IsAbsolutelyNormal (e x))

end Real
