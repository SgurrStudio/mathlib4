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
* `C²` affine rigidity: every `C²` map preserving base-`b` normality or absolute normality is
  affine-linear (arXiv:2609.24665).
* Non-preservation of normality in a general base under squaring, inversion, the exponential
  map, and non-degenerate Möbius transformations with `c ≠ 0`.
* Sharpness of `C²` rigidity: existence of a non-affine `C^{1,1}` diffeomorphism of `ℝ`
  preserving absolute normality (arXiv:2609.24665).
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

/-! ### Smooth (`C²`) affine rigidity -/

/-- **`C²` affine rigidity in a fixed base** (arXiv:2609.24665): any `C²` function `f : ℝ → ℝ`
that maps every base-`b` normal number (`b ≥ 2`) to a base-`b` normal number is affine-linear. -/
proof_wanted exists_affine_of_contDiff_two_preserves_isNormalIn {b : ℕ} (hb : 2 ≤ b)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hpres : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (f x)) :
    ∃ a c : ℝ, ∀ x : ℝ, f x = a * x + c

/-- **`C²` affine rigidity for absolute normality** (arXiv:2609.24665): any `C²` function
`f : ℝ → ℝ` that maps every absolutely normal number to an absolutely normal number is
affine-linear. -/
proof_wanted exists_affine_of_contDiff_two_preserves_isAbsolutelyNormal {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hpres : ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (f x)) :
    ∃ a c : ℝ, ∀ x : ℝ, f x = a * x + c

/-! ### Non-preservation under standard nonlinear operations

The absolute-normality versions, and the base-`b` versions for `b = 2 ^ k`, are proved in
`Mathlib.NumberTheory.Normal.NonPreservation`
(`Real.exists_isAbsolutelyNormal_not_isAbsolutelyNormal_sq` and its `inv`, `exp`, `mobius`
siblings).
The general base `b` needs a base-`b` analogue of the quarter-Cantor set. -/

/-- Squaring does not preserve base-`b` normality (`b ≥ 2`). -/
proof_wanted exists_isNormalIn_not_isNormalIn_sq {b : ℕ} (hb : 2 ≤ b) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalIn b (x ^ 2)

/-- Inversion `x ↦ x⁻¹` does not preserve base-`b` normality (`b ≥ 2`). -/
proof_wanted exists_isNormalIn_not_isNormalIn_inv {b : ℕ} (hb : 2 ≤ b) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalIn b x⁻¹

/-- The exponential map `x ↦ Real.exp x` does not preserve base-`b` normality (`b ≥ 2`). -/
proof_wanted exists_isNormalIn_not_isNormalIn_exp {b : ℕ} (hb : 2 ≤ b) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalIn b (Real.exp x)

/-- No non-degenerate Möbius transformation `x ↦ (a₁ * x + a₂) / (c * x + d)` with `c ≠ 0`
preserves base-`b` normality (`b ≥ 2`). -/
proof_wanted exists_isNormalIn_not_isNormalIn_mobius {b : ℕ} (hb : 2 ≤ b)
    (a₁ a₂ c d : ℝ) (hc : c ≠ 0) (hdet : a₁ * d - a₂ * c ≠ 0) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalIn b ((a₁ * x + a₂) / (c * x + d))

/-! ### Sharpness of `C²` rigidity -/

/-- **Sharpness of `C²` rigidity** (arXiv:2609.24665): there exists a non-affine `C^{1,1}`
diffeomorphism of `ℝ` (i.e. a bijection `e : ℝ ≃ ℝ` with `e` and `e.symm` of class `C¹` and
locally Lipschitz derivative `deriv e`) that preserves absolute normality. -/
proof_wanted exists_nonAffine_C11_diffeomorph_preserves_isAbsolutelyNormal :
    ∃ e : ℝ ≃ ℝ, ContDiff ℝ 1 e ∧ ContDiff ℝ 1 e.symm ∧ LocallyLipschitz (deriv e) ∧
      (¬ ∃ a c : ℝ, ∀ x : ℝ, e x = a * x + c) ∧
      (∀ x : ℝ, IsAbsolutelyNormal x ↔ IsAbsolutelyNormal (e x))

end Real
