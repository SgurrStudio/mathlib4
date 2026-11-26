/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.Normal.Basic
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

/-!
# Invariance and non-invariance of normality under transformations

This file establishes both positive invariance theorems and sharp obstructions for operations on
normal numbers:

* **Rational affine invariance for absolute normality** (Wall 1949): `x ↦ q * x + r` (`q ∈ ℚ×`,
  `r ∈ ℚ`) preserves `Real.IsAbsolutelyNormal`.
* **Cesàro-zero / sparse-digit translations** (Aistleitner 2011; explicit subgroup of Rauzy 1976):
  translating `x` by any `y` whose fractional orbits `Int.fract (y * b ^ n)` have Cesàro mean `0`
  — in particular any `y` whose nonzero base-`b` digits have asymptotic density `0`, or
  Mathlib's `liouvilleNumber b` — preserves `Real.IsNormalIn b`.
* **Rotational rigidity in `ℝ²`**: rotating `(x, y)` by angle `θ` preserves coordinatewise base-`b`
  normality (or absolute normality) for all normal pairs `(x, y)` if and only if
  `sin θ = 0 ∨ cos θ = 0` (i.e., `θ` is a multiple of `π / 2`).
* **Universal normal decompositions**: every real number is the sum of two absolutely normal
  numbers, and every nonzero real number is the product of two absolutely normal numbers.

## Main statements

* `Real.isAbsolutelyNormal_mul_add_ratCast_iff`: `q * x + r` is absolutely normal iff `x` is.
* `Real.isNormalIn_add_iff_of_tendsto_cesaro_fract`: Cesàro-zero fractional-orbit translations
  preserve base-`b` normality.
* `Real.isNormalIn_add_iff_of_density_zero`: **Aistleitner (2011)**, translations by numbers with
  density-`0` nonzero base-`b` digits preserve base-`b` normality.
* `Real.isNormalIn_add_liouvilleNumber_iff`: adding `liouvilleNumber b` preserves base-`b`
  normality.
* `Real.rotation_preserves_isNormalIn_iff`, `Real.rotation_preserves_isAbsolutelyNormal_iff`:
  exact characterization of normality-preserving planar rotations.
* `Real.exists_isAbsolutelyNormal_add_eq`, `Real.exists_isAbsolutelyNormal_mul_eq`:
  every real (resp. nonzero real) is a sum (resp. product) of two absolutely normal numbers.

## References

* D. D. Wall, *Normal numbers*, PhD thesis, University of California, Berkeley, 1949.
* G. Rauzy, *Nombres normaux et processus déterministes*, Acta Arith. 29 (1976), 211–225.
* C. Aistleitner, *Normal numbers and the digits of their sums*,
  Unif. Distrib. Theory 6 (2011), no. 2, 49–58.
-/

@[expose] public section

open Filter Topology

namespace Real

/-- Negation preserves absolute normality. -/
theorem IsAbsolutelyNormal.neg {x : ℝ} (h : IsAbsolutelyNormal x) : IsAbsolutelyNormal (-x) := by
  sorry

/-- Multiplying by a nonzero rational preserves absolute normality. -/
theorem IsAbsolutelyNormal.mul_ratCast {x : ℝ} (h : IsAbsolutelyNormal x) {q : ℚ} (hq : q ≠ 0) :
    IsAbsolutelyNormal (q * x) := by
  sorry

/-- Adding a rational preserves absolute normality. -/
theorem IsAbsolutelyNormal.add_ratCast {x : ℝ} (h : IsAbsolutelyNormal x) (r : ℚ) :
    IsAbsolutelyNormal (x + r) := by
  sorry

/-- **Wall (1949)** for absolute normality: `q * x + r` is absolutely normal iff `x` is, for
every nonzero rational `q` and rational `r`. -/
theorem isAbsolutelyNormal_mul_add_ratCast_iff {x : ℝ} {q : ℚ} (hq : q ≠ 0) (r : ℚ) :
    IsAbsolutelyNormal (q * x + r) ↔ IsAbsolutelyNormal x := by
  sorry

/-- If the fractional parts `Int.fract (y * b ^ n)` have Cesàro mean `0`, then translating by `y`
preserves base-`b` normality. -/
theorem isNormalIn_add_iff_of_tendsto_cesaro_fract {b : ℕ} (hb : 2 ≤ b) {x y : ℝ}
    (hy : Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N, Int.fract (y * (b : ℝ) ^ n)) / N)
      atTop (𝓝 0)) :
    IsNormalIn b (x + y) ↔ IsNormalIn b x := by
  sorry

/-- **Aistleitner (2011)** (special case of Rauzy 1976): if the nonzero base-`b` digits of `y`
have asymptotic density `0`, then adding `y` preserves base-`b` normality. -/
theorem isNormalIn_add_iff_of_density_zero {b : ℕ} (hb : 2 ≤ b) {x y : ℝ}
    (hy : Tendsto (fun N : ℕ ↦ (((Finset.range N).filter fun n ↦ digit b y n ≠ 0).card : ℝ) / N)
      atTop (𝓝 0)) :
    IsNormalIn b (x + y) ↔ IsNormalIn b x := by
  sorry

/-- Translating by Liouville's constant `liouvilleNumber b` preserves base-`b` normality,
exhibiting an explicit transcendental rotation in Rauzy's invariance group. -/
theorem isNormalIn_add_liouvilleNumber_iff {b : ℕ} (hb : 2 ≤ b) (x : ℝ) :
    IsNormalIn b (x + liouvilleNumber b) ↔ IsNormalIn b x := by
  sorry

/-- **Rotational rigidity in `ℝ²`** (base `b`): rotating `(x, y)` by angle `θ` preserves
coordinatewise base-`b` normality for all base-`b` normal pairs `(x, y)` if and only if
`sin θ = 0 ∨ cos θ = 0`. -/
theorem rotation_preserves_isNormalIn_iff {b : ℕ} (hb : 2 ≤ b) (θ : ℝ) :
    (∀ x y : ℝ, IsNormalIn b x → IsNormalIn b y →
      IsNormalIn b (x * cos θ - y * sin θ) ∧ IsNormalIn b (x * sin θ + y * cos θ)) ↔
      sin θ = 0 ∨ cos θ = 0 := by
  sorry

/-- **Rotational rigidity in `ℝ²`** (absolute normality): rotating `(x, y)` by angle `θ`
preserves coordinatewise absolute normality for all absolutely normal pairs `(x, y)` if and only
if `sin θ = 0 ∨ cos θ = 0`. -/
theorem rotation_preserves_isAbsolutelyNormal_iff (θ : ℝ) :
    (∀ x y : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal y →
      IsAbsolutelyNormal (x * cos θ - y * sin θ) ∧
      IsAbsolutelyNormal (x * sin θ + y * cos θ)) ↔
      sin θ = 0 ∨ cos θ = 0 := by
  sorry

/-- Every real number is the sum of two absolutely normal numbers. -/
theorem exists_isAbsolutelyNormal_add_eq (y : ℝ) :
    ∃ x₁ x₂ : ℝ, IsAbsolutelyNormal x₁ ∧ IsAbsolutelyNormal x₂ ∧ x₁ + x₂ = y := by
  sorry

/-- Every nonzero real number is the product of two absolutely normal numbers. -/
theorem exists_isAbsolutelyNormal_mul_eq {y : ℝ} (hy : y ≠ 0) :
    ∃ x₁ x₂ : ℝ, IsAbsolutelyNormal x₁ ∧ IsAbsolutelyNormal x₂ ∧ x₁ * x₂ = y := by
  sorry

end Real
