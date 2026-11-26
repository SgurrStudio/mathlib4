/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.NumberTheory.Normal.Borel
public import Mathlib.NumberTheory.Normal.Rational

/-!
# Preservation and non-preservation of normality under maps

We study which translations, dilations, and smooth maps preserve normality in a fixed base `b ≥ 2`
or absolute normality, both from an algebraic and from a metric (Lebesgue measure) perspective.

## Main statements

* `Real.not_preserves_isNormalIn_add_of_isNormalIn`: no normal number `α` preserves normality under
  translation `x ↦ x + α` (witnessed by `x = -α`).
* `Real.not_preserves_isNormalIn_mul_of_isNormalIn_inv`: if `α ≠ 0` and `α⁻¹` is normal, then
  `x ↦ α * x` does not preserve normality (witnessed by `x = α⁻¹`).
* `Real.volume_setOf_preserves_isNormalIn_add_eq_zero`,
  `Real.volume_setOf_preserves_isAbsolutelyNormal_add_eq_zero`: the set of additive normality
  preservers has Lebesgue measure zero.
* `Real.ae_isAbsolutelyNormal_inv`, `Real.ae_isAbsolutelyNormal_pow`,
  `Real.ae_isAbsolutelyNormal_exp`, `Real.ae_isAbsolutelyNormal_aeval_rat_poly`: for
  Lebesgue-almost every `x : ℝ`, `x⁻¹`, `x ^ k` (`k ≥ 1`), `Real.exp x`, and `Polynomial.aeval x p`
  (simultaneously for every non-constant `p : Polynomial ℚ`) are absolutely normal.
* `Real.volume_setOf_preserves_isNormalIn_mul_eq_zero`,
  `Real.volume_setOf_preserves_isAbsolutelyNormal_mul_eq_zero`: the set of multiplicative normality
  preservers has Lebesgue measure zero.
* `Real.normalAddPreservers`, `Real.absolutelyNormalAddPreservers`: additive normality preservers
  form an `AddSubgroup ℝ` containing `ℚ`.
* `Real.normalMulPreservers`, `Real.absolutelyNormalMulPreservers`,
  `Real.normalMulEquivPreservers`, `Real.absolutelyNormalMulEquivPreservers`: multiplicative
  normality preservers form a `Submonoid ℝ` containing `ℚ \ {0}`, and two-sided multiplicative
  preservers form a `Subgroup ℝˣ`.
-/

@[expose] public section

open Filter MeasureTheory Polynomial Set Topology
open scoped ENNReal

namespace Real

variable {b : ℕ} {x α β : ℝ}

/-! ### Rational invariance helpers -/


/-! ### Elementary non-preservation witnesses -/

/-- If `α` is normal in base `b ≥ 2`, then translation by `α` does not preserve base-`b`
normality: `-α` is normal in base `b`, whereas `-α + α = 0` is rational. -/
theorem not_preserves_isNormalIn_add_of_isNormalIn (hb : 2 ≤ b) (hα : IsNormalIn b α) :
    ¬ ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + α) := by sorry
/-- If `α` is absolutely normal, then translation by `α` does not preserve absolute normality. -/
theorem not_preserves_isAbsolutelyNormal_add_of_isAbsolutelyNormal (hα : IsAbsolutelyNormal α) :
    ¬ ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + α) := by sorry
/-- If `α ≠ 0` and `α⁻¹` is normal in base `b ≥ 2`, then multiplication by `α` does not preserve
base-`b` normality: `α * α⁻¹ = 1` is rational. -/
theorem not_preserves_isNormalIn_mul_of_isNormalIn_inv (hb : 2 ≤ b) (hα0 : α ≠ 0)
    (hα : IsNormalIn b α⁻¹) : ¬ ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (α * x) := by sorry
/-- If `α ≠ 0` and `α⁻¹` is absolutely normal, then multiplication by `α` does not preserve
absolute normality. -/
theorem not_preserves_isAbsolutelyNormal_mul_of_isAbsolutelyNormal_inv (hα0 : α ≠ 0)
    (hα : IsAbsolutelyNormal α⁻¹) :
    ¬ ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (α * x) := by sorry
/-- Any multiplicative preserver of base-`b` normality (`b ≥ 2`) is nonzero. -/
theorem ne_zero_of_preserves_isNormalIn_mul (hb : 2 ≤ b)
    (h : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (α * x)) : α ≠ 0 := by sorry
/-- Any multiplicative preserver of absolute normality is nonzero. -/
theorem ne_zero_of_preserves_isAbsolutelyNormal_mul
    (h : ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (α * x)) : α ≠ 0 := by sorry

/-! ### Measure-zero sets of additive preservers -/

/-- The set of real numbers `α` whose translation `x ↦ x + α` preserves base-`b` normality
has Lebesgue measure zero. -/
theorem volume_setOf_preserves_isNormalIn_add_eq_zero (hb : 2 ≤ b) :
    volume {α : ℝ | ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + α)} = 0 := by sorry
/-- The set of real numbers `α` whose translation `x ↦ x + α` preserves absolute normality
has Lebesgue measure zero. -/
theorem volume_setOf_preserves_isAbsolutelyNormal_add_eq_zero :
    volume {α : ℝ | ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + α)} = 0 := by sorry

/-! ### Null-set pullbacks under locally `C¹` maps with non-vanishing derivative -/

/-- If `f` is `C¹` with non-vanishing derivative on an open set `U ⊆ ℝ` of full Lebesgue measure,
then preimages of Lebesgue null sets under `f` are null. -/
theorem volume_preimage_eq_zero_of_hasDerivAt_ne_zero {U t : Set ℝ} {f f' : ℝ → ℝ}
    (hU : IsOpen U) (hUc : volume Uᶜ = 0) (hf : ∀ x ∈ U, HasDerivAt f (f' x) x)
    (hf'c : ContinuousOn f' U) (hf'_ne : ∀ x ∈ U, f' x ≠ 0) (ht : volume t = 0) :
    volume (f ⁻¹' t) = 0 := by sorry
/-- If `P` holds Lebesgue-almost everywhere and `f` is `C¹` with non-vanishing derivative on an
open set of full measure, then `P (f x)` holds for Lebesgue-almost every `x`. -/
theorem ae_comp_of_hasDerivAt_ne_zero {U : Set ℝ} {f f' : ℝ → ℝ} {P : ℝ → Prop}
    (hU : IsOpen U) (hUc : volume Uᶜ = 0) (hf : ∀ x ∈ U, HasDerivAt f (f' x) x)
    (hf'c : ContinuousOn f' U) (hf'_ne : ∀ x ∈ U, f' x ≠ 0) (hP : ∀ᵐ y : ℝ, P y) :
    ∀ᵐ x : ℝ, P (f x) := by sorry

/-! ### Almost-everywhere absolute normality of smooth images -/

/-- For Lebesgue-almost every `x : ℝ`, `x⁻¹` is absolutely normal. -/
theorem ae_isAbsolutelyNormal_inv : ∀ᵐ x : ℝ, IsAbsolutelyNormal x⁻¹ := by sorry
/-- For Lebesgue-almost every `x : ℝ` and any `k ≥ 1`, `x ^ k` is absolutely normal. -/
theorem ae_isAbsolutelyNormal_pow {k : ℕ} (hk : 1 ≤ k) :
    ∀ᵐ x : ℝ, IsAbsolutelyNormal (x ^ k) := by sorry
/-- For Lebesgue-almost every `x : ℝ`, `Real.exp x` is absolutely normal. -/
theorem ae_isAbsolutelyNormal_exp : ∀ᵐ x : ℝ, IsAbsolutelyNormal (Real.exp x) := by sorry
/-- For a fixed non-constant rational polynomial `p`, `Polynomial.aeval x p` is absolutely normal
for Lebesgue-almost every `x : ℝ`. -/
theorem ae_isAbsolutelyNormal_aeval_rat_poly_single (p : ℚ[X]) (hp : 1 ≤ p.natDegree) :
    ∀ᵐ x : ℝ, IsAbsolutelyNormal (Polynomial.aeval x p) := by sorry
/-- For Lebesgue-almost every `x : ℝ`, `Polynomial.aeval x p` is absolutely normal simultaneously
for every non-constant rational polynomial `p : Polynomial ℚ`. -/
theorem ae_isAbsolutelyNormal_aeval_rat_poly :
    ∀ᵐ x : ℝ, ∀ p : ℚ[X], 1 ≤ p.natDegree → IsAbsolutelyNormal (Polynomial.aeval x p) := by sorry

/-! ### Measure-zero sets of multiplicative preservers -/

/-- The set of real numbers `α` whose multiplication `x ↦ α * x` preserves base-`b` normality
has Lebesgue measure zero. -/
theorem volume_setOf_preserves_isNormalIn_mul_eq_zero (hb : 2 ≤ b) :
    volume {α : ℝ | ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (α * x)} = 0 := by sorry
/-- The set of real numbers `α` whose multiplication `x ↦ α * x` preserves absolute normality
has Lebesgue measure zero. -/
theorem volume_setOf_preserves_isAbsolutelyNormal_mul_eq_zero :
    volume {α : ℝ | ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (α * x)} = 0 := by sorry

/-! ### Algebraic structure of additive and multiplicative preservers -/

theorem preserves_isNormalIn_add_zero :
    ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + 0) := by sorry
theorem preserves_isNormalIn_add_add
    (hα : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + α))
    (hβ : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + β)) :
    ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + (α + β)) := by sorry
theorem preserves_isNormalIn_add_neg (hb : 2 ≤ b)
    (hα : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + α)) :
    ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + -α) := by sorry
theorem preserves_isNormalIn_add_sub (hb : 2 ≤ b)
    (hα : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + α))
    (hβ : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + β)) :
    ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + (α - β)) := by sorry
theorem preserves_isNormalIn_add_ratCast (hb : 2 ≤ b) (r : ℚ) :
    ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + (r : ℝ)) := by sorry
/-- Forward preservation of base-`b` normality under translation is equivalent to two-sided
preservation, because `-x` is normal iff `x` is normal. -/
theorem preserves_isNormalIn_add_iff_forall_iff (hb : 2 ≤ b) :
    (∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + α)) ↔
      (∀ x : ℝ, IsNormalIn b x ↔ IsNormalIn b (x + α)) := by sorry
/-- The additive subgroup of `ℝ` consisting of all translations preserving base-`b` normality
(`b ≥ 2`). -/
def normalAddPreservers (hb : 2 ≤ b) : AddSubgroup ℝ where
  carrier := {α : ℝ | ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + α)}
  zero_mem' := preserves_isNormalIn_add_zero
  add_mem' := preserves_isNormalIn_add_add
  neg_mem' := preserves_isNormalIn_add_neg hb

theorem ratCast_mem_normalAddPreservers (hb : 2 ≤ b) (r : ℚ) :
    (r : ℝ) ∈ normalAddPreservers hb := by sorry
theorem preserves_isAbsolutelyNormal_add_zero :
    ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + 0) := by sorry
theorem preserves_isAbsolutelyNormal_add_add
    (hα : ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + α))
    (hβ : ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + β)) :
    ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + (α + β)) := by sorry
theorem preserves_isAbsolutelyNormal_add_neg
    (hα : ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + α)) :
    ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + -α) := by sorry
theorem preserves_isAbsolutelyNormal_add_iff_forall_iff :
    (∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + α)) ↔
      (∀ x : ℝ, IsAbsolutelyNormal x ↔ IsAbsolutelyNormal (x + α)) := by sorry
/-- The additive subgroup of `ℝ` consisting of all translations preserving absolute normality. -/
def absolutelyNormalAddPreservers : AddSubgroup ℝ where
  carrier := {α : ℝ | ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + α)}
  zero_mem' := preserves_isAbsolutelyNormal_add_zero
  add_mem' := preserves_isAbsolutelyNormal_add_add
  neg_mem' := preserves_isAbsolutelyNormal_add_neg

theorem ratCast_mem_absolutelyNormalAddPreservers (r : ℚ) :
    (r : ℝ) ∈ absolutelyNormalAddPreservers := by sorry
theorem preserves_isNormalIn_mul_one :
    ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (1 * x) := by sorry
theorem preserves_isNormalIn_mul_mul
    (hα : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (α * x))
    (hβ : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (β * x)) :
    ∀ x : ℝ, IsNormalIn b x → IsNormalIn b ((α * β) * x) := by sorry
theorem preserves_isNormalIn_mul_ratCast (hb : 2 ≤ b) {q : ℚ} (hq : q ≠ 0) :
    ∀ x : ℝ, IsNormalIn b x → IsNormalIn b ((q : ℝ) * x) := by sorry
/-- The multiplicative submonoid of `ℝ` consisting of all dilations preserving base-`b`
normality. -/
def normalMulPreservers (b : ℕ) : Submonoid ℝ where
  carrier := {α : ℝ | ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (α * x)}
  one_mem' := preserves_isNormalIn_mul_one
  mul_mem' := preserves_isNormalIn_mul_mul

theorem ratCast_mem_normalMulPreservers (hb : 2 ≤ b) {q : ℚ} (hq : q ≠ 0) :
    (q : ℝ) ∈ normalMulPreservers b := by sorry
/-- The multiplicative subgroup of `ℝˣ` consisting of all two-sided multiplicative preservers of
base-`b` normality. -/
def normalMulEquivPreservers (b : ℕ) : Subgroup ℝˣ where
  carrier := {α : ℝˣ | ∀ x : ℝ, IsNormalIn b x ↔ IsNormalIn b ((α : ℝ) * x)}
  one_mem' := fun x ↦ by simp
  mul_mem' := fun hα hβ x ↦ by
    rw [Units.val_mul, mul_assoc]
    exact (hβ x).trans (hα _)
  inv_mem' := fun {u} hu x ↦ by
    simpa [Units.val_inv_eq_inv_val] using (hu ((u : ℝ)⁻¹ * x)).symm

theorem preserves_isAbsolutelyNormal_mul_one :
    ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (1 * x) := by sorry
theorem preserves_isAbsolutelyNormal_mul_mul
    (hα : ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (α * x))
    (hβ : ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (β * x)) :
    ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal ((α * β) * x) := by sorry
/-- The multiplicative submonoid of `ℝ` consisting of all dilations preserving absolute
normality. -/
def absolutelyNormalMulPreservers : Submonoid ℝ where
  carrier := {α : ℝ | ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (α * x)}
  one_mem' := preserves_isAbsolutelyNormal_mul_one
  mul_mem' := preserves_isAbsolutelyNormal_mul_mul

theorem ratCast_mem_absolutelyNormalMulPreservers {q : ℚ} (hq : q ≠ 0) :
    (q : ℝ) ∈ absolutelyNormalMulPreservers := by sorry
/-- The multiplicative subgroup of `ℝˣ` consisting of all two-sided multiplicative preservers of
absolute normality. -/
def absolutelyNormalMulEquivPreservers : Subgroup ℝˣ where
  carrier := {α : ℝˣ | ∀ x : ℝ, IsAbsolutelyNormal x ↔ IsAbsolutelyNormal ((α : ℝ) * x)}
  one_mem' := fun x ↦ by simp
  mul_mem' := fun hα hβ x ↦ by
    rw [Units.val_mul, mul_assoc]
    exact (hβ x).trans (hα _)
  inv_mem' := fun {u} hu x ↦ by
    simpa [Units.val_inv_eq_inv_val] using (hu ((u : ℝ)⁻¹ * x)).symm

end Real

