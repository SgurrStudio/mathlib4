/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.NumberTheory.Normal.DigitOperations
public import Mathlib.NumberTheory.Normal.Preservation
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

/-!
# Uncountable and transcendental additive normality preservers

We prove that for every base `b ≥ 2`, the additive subgroup `Real.normalAddPreservers hb` of real
numbers `t` such that `x ↦ x + t` preserves base-`b` normality is uncountable — in fact has
cardinality `Cardinal.continuum` — contains explicit transcendental numbers (in particular
Mathlib's `liouvilleNumber b`), and is closed under rational scalar multiplication.

## Main statements

* `Real.isNormalIn_add_sparseSeries`: sparse base-`b` series preserve base-`b` normality under
  addition.
* `Real.liouvilleNumber_mem_normalAddPreservers`: `liouvilleNumber b ∈ normalAddPreservers hb`.
* `Real.exists_transcendental_mem_normalAddPreservers`: existence of a transcendental additive
  normality preserver in every base `b ≥ 2`.
* `Real.cardinalMk_normalAddPreservers`, `Real.uncountable_normalAddPreservers`:
  `normalAddPreservers hb` has cardinality `Cardinal.continuum` and is uncountable.
* `Real.ratCast_mul_mem_normalAddPreservers`: `normalAddPreservers hb` is closed under
  multiplication by rationals `q : ℚ`.
-/

@[expose] public section

open Filter Topology
open scoped Cardinal

namespace Real

variable {b : ℕ} {x t : ℝ}

/-- A sparse base-`b` series with bit coefficients `c : ℕ → Bool` at digit positions `a k`. -/
noncomputable def sparseSeries (b : ℕ) (a : ℕ → ℕ) (c : ℕ → Bool) : ℝ :=
  ∑' k : ℕ, if c k then ((b : ℝ) ^ (a k + 1))⁻¹ else 0

/-- Adding any sparse base-`b` series with `a k / a (k + 1) → 0` preserves base-`b` normality. -/
theorem isNormalIn_add_sparseSeries (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a)
    (hratio : Tendsto (fun k : ℕ ↦ (a k : ℝ) / (a (k + 1) : ℝ)) atTop (𝓝 0))
    (c : ℕ → Bool) (hx : IsNormalIn b x) :
    IsNormalIn b (x + sparseSeries b a c) := by
  sorry

/-- Mathlib's base-`b` Liouville constant `liouvilleNumber b` preserves base-`b` normality under
addition. -/
theorem liouvilleNumber_mem_normalAddPreservers (hb : 2 ≤ b) :
    liouvilleNumber (b : ℝ) ∈ normalAddPreservers hb := by
  sorry

/-- In every base `b ≥ 2`, there exists a transcendental (in particular irrational) real number
whose translation preserves base-`b` normality. -/
theorem exists_transcendental_mem_normalAddPreservers (hb : 2 ≤ b) :
    ∃ t : ℝ, Transcendental ℤ t ∧ t ∈ normalAddPreservers hb := by
  sorry

/-- The additive subgroup `normalAddPreservers hb` has cardinality `Cardinal.continuum`. -/
theorem cardinalMk_normalAddPreservers (hb : 2 ≤ b) :
    #(normalAddPreservers hb) = 𝔠 := by
  sorry

/-- In every base `b ≥ 2`, there are uncountably many real numbers whose translation preserves
base-`b` normality. -/
theorem uncountable_normalAddPreservers (hb : 2 ≤ b) :
    Uncountable (normalAddPreservers hb) := by
  sorry

/-- The additive normality preservers in base `b ≥ 2` are closed under rational scaling. -/
theorem ratCast_mul_mem_normalAddPreservers (hb : 2 ≤ b) (q : ℚ)
    {α : ℝ} (hα : α ∈ normalAddPreservers hb) :
    (q : ℝ) * α ∈ normalAddPreservers hb := by
  sorry

end Real
