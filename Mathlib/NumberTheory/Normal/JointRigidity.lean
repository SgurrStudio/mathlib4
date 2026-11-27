/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.JointWeyl
public import Mathlib.NumberTheory.Normal.MulRigidity
public import Mathlib.NumberTheory.Normal.Preservation
public import Mathlib.NumberTheory.Normal.Rigidity

/-!
# 2D `C²` affine rigidity for joint normality

Building on `Mathlib.NumberTheory.Normal.JointWeyl`, `Mathlib.NumberTheory.Normal.Rigidity`, and
`Mathlib.NumberTheory.Normal.MulRigidity`, we prove the 2D `C²` affine rigidity dichotomy for
jointly normal pairs `(x, y) ∈ ℝ × ℝ`:

1. **Fractal decay joint normality** (`ae_isJointlyAbsolutelyNormal_of_polyDecay`,
   `ae_isJointlyAbsolutelyNormal_of_polyDecayB`): any pushforward Cantor measure with polynomial
   Fourier decay is almost surely jointly absolutely normal with any fixed absolutely normal `y`.
2. **2D `C²` non-affine counterexample**
   (`Real.exists_isJointlyAbsolutelyNormal_not_isNormalIn_of_contDiff`): every non-affine `C²`
   function `F : ℝ × ℝ → ℝ` maps some jointly absolutely normal pair to a non-normal real.
3. **Full 2D `C²` affine rigidity dichotomy**
   (`Real.exists_affine_of_contDiff_two_preserves_isJointlyNormalIn`,
   `Real.exists_rat_affine_of_contDiff_two_preserves_isJointlyNormalIn`,
   `Real.contDiff_two_preserves_isJointlyNormalIn_dichotomy`,
   `Real.exists_const_contDiff_two_preserves_isJointlyNormalIn`): every `C²` map
   `F : ℝ × ℝ → ℝ × ℝ` preserving `IsJointlyNormalIn b` is either constant (with a jointly normal
   value) or an invertible rational-linear affine map `A(x, y) + c` with `A ∈ GL_2(ℚ)` and
   `c₁, c₂ ∈ normalAddPreservers hb`.
4. **Concrete 2D non-preservation corollaries** for `(x * y, y)`, `(x + y, x * y)`, and
   `(x ^ 2, y ^ 2)`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology ComplexConjugate
open scoped ENNReal
open NormalNumbers.DecayAeNormal NormalNumbers.ExplicitSquare
open NormalNumbers.CantorSelfSimilar NormalNumbers.QuarterCantorDecay
open NormalNumbers.BaseCantorDecay NormalNumbers.MulRigidity

/-! ### Part 4: 2D `C²` non-affine counterexample -/

namespace NormalNumbers.JointRigidity
/-- **Polynomial Fourier decay ⇒ a.s. joint absolute normality with any fixed absolutely normal
`y`**. -/
theorem ae_isJointlyAbsolutelyNormal_of_decay {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : Ω → ℝ) (hG : Measurable G) {C δ : ℝ}
    (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂μ‖ ≤ C * |ξ| ^ (-δ))
    {y : ℝ} (hy : Real.IsAbsolutelyNormal y) :
    ∀ᵐ ω ∂μ, Real.IsJointlyAbsolutelyNormal (G ω) y := by
  sorry

/-- Pushforward of quarter-Cantor measure with polynomial decay is a.s. jointly absolutely normal
with any fixed absolutely normal `y`. -/
theorem ae_isJointlyAbsolutelyNormal_of_polyDecay {F : ℝ → ℝ} (hF : Measurable F)
    (hd : PolyDecay F) {y : ℝ} (hy : Real.IsAbsolutelyNormal y) :
    ∀ᵐ ω ∂coinMeasure, Real.IsJointlyAbsolutelyNormal (F (cantorReal ω)) y := by
  sorry

/-- Pushforward of base-`b` Cantor measure with polynomial decay is a.s. jointly absolutely normal
with any fixed absolutely normal `y`. -/
theorem ae_isJointlyAbsolutelyNormal_of_polyDecayB {b : ℕ} {F : ℝ → ℝ} (hF : Measurable F)
    (hd : PolyDecayB b F) {y : ℝ} (hy : Real.IsAbsolutelyNormal y) :
    ∀ᵐ ω ∂coinMeasure, Real.IsJointlyAbsolutelyNormal (F (bReal b ω)) y := by
  sorry

/-- Window witness jointly normal with a fixed absolutely normal `y`. -/
theorem exists_joint_of_window {b : ℕ} (hb : 2 ≤ b) {f G G' G'' : ℝ → ℝ} {a A : ℝ} {q s : ℚ}
    (hs : s ≠ 0) (ha : 0 < a) (hGm : Measurable G)
    (hG : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt G (G' t) t)
    (hG' : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt G' (G'' t) t)
    (hlo : ∀ t ∈ Icc (0 : ℝ) 1, a ≤ |G'' t|) (hhi : ∀ t ∈ Icc (0 : ℝ) 1, |G'' t| ≤ A)
    (hsign : (∀ t ∈ Icc (0 : ℝ) 1, 0 < G'' t) ∨ ∀ t ∈ Icc (0 : ℝ) 1, G'' t < 0)
    (hfG : ∀ t ∈ Icc (0 : ℝ) 1, f (G t) = s * t + q)
    {y : ℝ} (hy : Real.IsAbsolutelyNormal y) :
    ∃ x : ℝ, Real.IsJointlyAbsolutelyNormal x y ∧ ¬ Real.IsNormalIn b (f x) := by
  sorry

/-- Core 1D local-inverse construction producing a witness jointly absolutely normal with a fixed
absolutely normal `y`. -/
theorem exists_joint_of_pos {b : ℕ} (hb : 2 ≤ b) {f F' F'' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt f (F' x) x) (hF' : ∀ x, HasDerivAt F' (F'' x) x)
    (hc1 : Continuous F') (hc2 : Continuous F'') {p : ℝ} (h1 : 0 < F' p) (h2 : F'' p ≠ 0)
    {y : ℝ} (hy : Real.IsAbsolutelyNormal y) :
    ∃ x : ℝ, Real.IsJointlyAbsolutelyNormal x y ∧ ¬ Real.IsNormalIn b (f x) := by
  sorry

/-- For any non-affine `C²` function `f : ℝ → ℝ` and any fixed absolutely normal `y`, there exists
`x` jointly absolutely normal with `y` such that `f x` is not normal in base `b`. -/
theorem exists_isJointlyAbsolutelyNormal_not_isNormalIn_of_contDiff_1d {b : ℕ} (hb : 2 ≤ b)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hna : ¬ ∃ a c : ℝ, ∀ x, f x = a * x + c)
    {y : ℝ} (hy : Real.IsAbsolutelyNormal y) :
    ∃ x : ℝ, Real.IsJointlyAbsolutelyNormal x y ∧ ¬ Real.IsNormalIn b (f x) := by
  sorry

/-- The set of absolutely normal numbers is dense in `ℝ`. -/
theorem dense_isAbsolutelyNormal : Dense {x : ℝ | Real.IsAbsolutelyNormal x} := by
  sorry

end NormalNumbers.JointRigidity
namespace Real
/-- **2D `C²` non-affine counterexample**: if `F₁ : ℝ × ℝ → ℝ` is `C²` and not globally affine,
then for every base `b ≥ 2` there exist jointly absolutely normal `x, y` with `F₁ (x, y)` not
normal in base `b`. -/
theorem exists_isJointlyAbsolutelyNormal_not_isNormalIn_of_contDiff {b : ℕ} (hb : 2 ≤ b)
    {F₁ : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 2 F₁)
    (hna : ¬ ∃ a₁ a₂ c : ℝ, ∀ p : ℝ × ℝ, F₁ p = a₁ * p.1 + a₂ * p.2 + c) :
    ∃ x y : ℝ, IsJointlyAbsolutelyNormal x y ∧ ¬ IsNormalIn b (F₁ (x, y)) := by
  sorry

end Real
/-! ### Part 5: Twisted multiplicative rigidity and full 2D `C²` affine rigidity -/

namespace NormalNumbers.JointRigidity
/-- For irrational `θ` and any real shift `d`, `θ * bReal b ω + d` is normal in base `b` for
almost every Cantor point `ω`. -/
theorem ae_isNormal_mul_bReal_add {b : ℕ} (hb : 2 ≤ b) {θ : ℝ} (hθ : Irrational θ) (d : ℝ) :
    ∀ᵐ ω ∂coinMeasure, IsNormal b (θ * bReal b ω + d) := by
  sorry

/-- **1D affine multiplicative-additive rigidity**: if `x ↦ r * x + c` with `r ≠ 0` preserves
base-`b` normality, then `r` is a nonzero rational and `c ∈ Real.normalAddPreservers hb`. -/
theorem rat_and_addPreserver_of_preserves_affine {b : ℕ} (hb : 2 ≤ b) {r c : ℝ} (hr : r ≠ 0)
    (hpres : ∀ x : ℝ, Real.IsNormalIn b x → Real.IsNormalIn b (r * x + c)) :
    (∃ q : ℚ, q ≠ 0 ∧ (q : ℝ) = r) ∧ c ∈ Real.normalAddPreservers hb := by
  sorry

/-- If an affine form `r₁ * x + r₂ * y + c` with `(r₁, r₂) ≠ (0, 0)` maps every base-`b` jointly
normal pair to a base-`b` normal number, then `r₁, r₂ ∈ ℚ` and `c ∈ normalAddPreservers hb`. -/
theorem rat_and_addPreserver_of_affine_joint {b : ℕ} (hb : 2 ≤ b) {r₁ r₂ c : ℝ}
    (hne : r₁ ≠ 0 ∨ r₂ ≠ 0)
    (hpres : ∀ x y : ℝ, Real.IsJointlyNormalIn b x y → Real.IsNormalIn b (r₁ * x + r₂ * y + c)) :
    (∃ q₁ q₂ : ℚ, (q₁ : ℝ) = r₁ ∧ (q₂ : ℝ) = r₂) ∧ c ∈ Real.normalAddPreservers hb := by
  sorry

end NormalNumbers.JointRigidity
namespace Real
/-- **2D `C²` affine rigidity (affine form)**: every `C²` map `F : ℝ × ℝ → ℝ × ℝ` preserving
base-`b` joint normality (`b ≥ 2`) is globally affine. -/
theorem exists_affine_of_contDiff_two_preserves_isJointlyNormalIn {b : ℕ} (hb : 2 ≤ b)
    {F : ℝ × ℝ → ℝ × ℝ} (hF : ContDiff ℝ 2 F)
    (hpres : ∀ x y : ℝ, IsJointlyNormalIn b x y →
      IsJointlyNormalIn b (F (x, y)).1 (F (x, y)).2) :
    ∃ a₁₁ a₁₂ c₁ a₂₁ a₂₂ c₂ : ℝ, ∀ x y : ℝ,
      F (x, y) = (a₁₁ * x + a₁₂ * y + c₁, a₂₁ * x + a₂₂ * y + c₂) := by
  sorry

/-- **Full 2D `C²` affine rigidity (non-constant case)**: every non-constant `C²` map
`F : ℝ × ℝ → ℝ × ℝ` preserving base-`b` joint normality (`b ≥ 2`) is of the form
`F (x, y) = (a₁₁ x + a₁₂ y + c₁, a₂₁ x + a₂₂ y + c₂)` with `(aᵢⱼ) ∈ GL_2(ℚ)` and
`c₁, c₂ ∈ normalAddPreservers hb`. -/
theorem exists_rat_affine_of_contDiff_two_preserves_isJointlyNormalIn {b : ℕ} (hb : 2 ≤ b)
    {F : ℝ × ℝ → ℝ × ℝ} (hF : ContDiff ℝ 2 F)
    (hnc : ¬ ∃ p₀ : ℝ × ℝ, ∀ p : ℝ × ℝ, F p = p₀)
    (hpres : ∀ x y : ℝ, IsJointlyNormalIn b x y →
      IsJointlyNormalIn b (F (x, y)).1 (F (x, y)).2) :
    ∃ (a₁₁ a₁₂ a₂₁ a₂₂ : ℚ) (c₁ c₂ : ℝ),
      a₁₁ * a₂₂ - a₁₂ * a₂₁ ≠ 0 ∧
      c₁ ∈ normalAddPreservers hb ∧ c₂ ∈ normalAddPreservers hb ∧
      ∀ x y : ℝ, F (x, y) = (a₁₁ * x + a₁₂ * y + c₁, a₂₁ * x + a₂₂ * y + c₂) := by
  sorry

/-- **Full dichotomy for `C²` preservers of base-`b` joint normality**: every `C²` map
`F : ℝ × ℝ → ℝ × ℝ` preserving `IsJointlyNormalIn b` (`b ≥ 2`) is either constant with a jointly
normal value, or an invertible rational-linear affine map shifted by `normalAddPreservers hb`. -/
theorem contDiff_two_preserves_isJointlyNormalIn_dichotomy {b : ℕ} (hb : 2 ≤ b)
    {F : ℝ × ℝ → ℝ × ℝ} (hF : ContDiff ℝ 2 F)
    (hpres : ∀ x y : ℝ, IsJointlyNormalIn b x y →
      IsJointlyNormalIn b (F (x, y)).1 (F (x, y)).2) :
    (∃ c₁ c₂ : ℝ, IsJointlyNormalIn b c₁ c₂ ∧ ∀ x y : ℝ, F (x, y) = (c₁, c₂)) ∨
    (∃ (a₁₁ a₁₂ a₂₁ a₂₂ : ℚ) (c₁ c₂ : ℝ),
      a₁₁ * a₂₂ - a₁₂ * a₂₁ ≠ 0 ∧
      c₁ ∈ normalAddPreservers hb ∧ c₂ ∈ normalAddPreservers hb ∧
      ∀ x y : ℝ, F (x, y) = (a₁₁ * x + a₁₂ * y + c₁, a₂₁ * x + a₂₂ * y + c₂)) := by
  sorry

/-- Sharpness of the non-constant hypothesis: constant `C²` maps with a jointly normal value
preserve `IsJointlyNormalIn b` yet have zero determinant and shift outside
`normalAddPreservers hb`. -/
theorem exists_const_contDiff_two_preserves_isJointlyNormalIn {b : ℕ} (hb : 2 ≤ b) :
    ∃ F : ℝ × ℝ → ℝ × ℝ, ContDiff ℝ 2 F ∧ (∃ p₀, ∀ p, F p = p₀) ∧
      ∀ x y : ℝ, IsJointlyNormalIn b x y →
        IsJointlyNormalIn b (F (x, y)).1 (F (x, y)).2 := by
  sorry

/-! ### Concrete 2D non-preservation corollaries -/

/-- Multiplication `x * y` does not preserve normality from jointly absolutely normal pairs. -/
theorem exists_isJointlyAbsolutelyNormal_not_isNormalIn_mul {b : ℕ} (hb : 2 ≤ b) :
    ∃ x y : ℝ, IsJointlyAbsolutelyNormal x y ∧ ¬ IsNormalIn b (x * y) := by
  sorry

/-- `(x, y) ↦ (x * y, y)` does not preserve joint normality in base `b ≥ 2`. -/
theorem not_preserves_isJointlyNormalIn_mul_snd {b : ℕ} (hb : 2 ≤ b) :
    ¬ ∀ x y : ℝ, IsJointlyNormalIn b x y → IsJointlyNormalIn b (x * y) y := by
  sorry

/-- `(x, y) ↦ (x + y, x * y)` does not preserve joint normality in base `b ≥ 2`. -/
theorem not_preserves_isJointlyNormalIn_add_mul {b : ℕ} (hb : 2 ≤ b) :
    ¬ ∀ x y : ℝ, IsJointlyNormalIn b x y → IsJointlyNormalIn b (x + y) (x * y) := by
  sorry

/-- `(x, y) ↦ (x ^ 2, y ^ 2)` does not preserve joint normality in base `b ≥ 2`. -/
theorem not_preserves_isJointlyNormalIn_sq_sq {b : ℕ} (hb : 2 ≤ b) :
    ¬ ∀ x y : ℝ, IsJointlyNormalIn b x y → IsJointlyNormalIn b (x ^ 2) (y ^ 2) := by
  sorry

end Real
