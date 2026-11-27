/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.BasePow
public import Mathlib.NumberTheory.Normal.Interleaving
public import Mathlib.NumberTheory.Normal.QuarterCantorDecay
public import Mathlib.NumberTheory.Normal.Rational
public import Mathlib.NumberTheory.Normal.Weyl

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Imported.NormalNumbers.VisitDeviationB
import Mathlib.Imported.TauCeti.Analysis.Fourier.Monomial
import Mathlib.Imported.TauCeti.MeasureTheory.Measure.AddCircle
import Mathlib.Imported.TauCeti.NumberTheory.Equidistribution.Weyl
import Mathlib.Imported.TauCeti.Topology.Instances.AddCircle.LiftIco

/-!
# Joint normality: 2D Weyl criterion, fixed-`x` a.e. joint normality, and `GL_2(ℚ)` invariance

We establish the Fourier-analytic and rational-linear invariance theory of jointly normal pairs
`(x, y) ∈ ℝ × ℝ`:

1. **2D Weyl criterion** (`Real.isJointlyNormalIn_iff_weyl`): `(x, y)` is jointly normal in
   base `b ≥ 2` iff all nontrivial 2D exponential sums `(1 / N) ∑_{n < N} e(h₁ b^n x + h₂ b^n y)`
   tend to `0`.
2. **Unified twisted Davenport–Erdős–LeVeque second-moment lemma** and **fixed-`x` a.e. joint
   normality** (`Real.ae_isJointlyNormalIn_of_isNormalIn`,
   `Real.ae_isJointlyAbsolutelyNormal_of_isAbsolutelyNormal`): for every fixed base-`b` normal
   (resp. absolutely normal) `x`, Lebesgue-almost every `y` is jointly normal with `x`.
3. **Irrational-slope counterexample** (`Real.ae_isJointlyAbsolutelyNormal_irrational_line`,
   `Real.not_preserves_isJointlyNormalIn_irrational_linear`): for any irrational `α` and real `u`,
   a.e. `y` satisfies `IsJointlyAbsolutelyNormal (-α * y + u) y`, so `(x, y) ↦ (x + α y + c, y)`
   does not preserve joint normality.
4. **`GL_2(ℚ)` and rational affine invariance** (`Real.IsJointlyNormalIn.div_nat`,
   `Real.IsJointlyNormalIn.linear_int`, `Real.IsJointlyNormalIn.linear_rat`,
   `Real.IsJointlyNormalIn.add_ratCast`, `Real.IsJointlyNormalIn.affine_rat`).
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology ComplexConjugate
open scoped ENNReal
open NormalNumbers.DecayAeNormal NormalNumbers.ExplicitSquare

namespace NormalNumbers.JointRigidity
/-! ### Helper lemmas for `ee` and 2D block counts -/

/-! ### Part 1: 2D Weyl Criterion -/

end NormalNumbers.JointRigidity
namespace Real
/-- **2D Weyl criterion for joint normality**: `(x, y)` is jointly normal in base `b ≥ 2` iff
all nontrivial 2D Weyl means `(1 / N) ∑_{n < N} e(h₁ b^n x + h₂ b^n y)` tend to `0`. -/
theorem isJointlyNormalIn_iff_weyl {b : ℕ} (hb : 2 ≤ b) (x y : ℝ) :
    IsJointlyNormalIn b x y ↔ ∀ h₁ h₂ : ℤ, (h₁, h₂) ≠ (0, 0) →
      Tendsto (fun N : ℕ ↦ (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        ee ((h₁ : ℝ) * (b : ℝ) ^ n * x + (h₂ : ℝ) * (b : ℝ) ^ n * y)) atTop (𝓝 0) := by
  sorry

end Real
/-! ### Part 2: Unified twisted second-moment lemma, fixed-`x` a.e. joint normality, and
irrational-slope counterexample -/

namespace NormalNumbers.JointRigidity
/-- Lacunary decay bound with an arbitrary nonzero real frequency `lam`. -/
theorem decay_at_diff_real {b : ℕ} (hb : 2 ≤ b) {C δ lam : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hlam : lam ≠ 0) {m n : ℕ} (hmn : m ≠ n) :
    C * |lam * ((b : ℝ) ^ n - (b : ℝ) ^ m)| ^ (-δ) ≤
      C * |lam| ^ (-δ) * 2 ^ δ * ((b : ℝ) ^ (-δ / 2)) ^ n * ((b : ℝ) ^ (-δ / 2)) ^ m := by
  sorry

/-- **Twisted second moment bound** under polynomial Fourier decay: adding any deterministic
phase `θ n` leaves the `O(N)` second-moment bound intact. -/
theorem twisted_second_moment_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {b : ℕ} (hb : 2 ≤ b) (G : Ω → ℝ) (hG : Measurable G)
    {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂μ‖ ≤ C * |ξ| ^ (-δ))
    (θ : ℕ → ℝ) {lam : ℝ} (hlam : lam ≠ 0) (N : ℕ) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (θ k + lam * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂μ ≤
      N + C * |lam| ^ (-δ) * 2 ^ δ * ((1 - (2 : ℝ) ^ (-δ / 2))⁻¹) ^ 2 := by
  sorry

/-- **Twisted Davenport–Erdős–LeVeque**: polynomial Fourier decay of `G_* μ` implies that for
every base `b ≥ 2`, nonzero real `lam`, and deterministic phase sequence `θ`, the twisted Weyl
means `(1 / N) ∑_{n < N} e(θ n + lam b^n G ω)` tend to `0` for `μ`-a.e. `ω`. -/
theorem ae_tendsto_twisted_weyl_of_decay {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {b : ℕ} (hb : 2 ≤ b) (G : Ω → ℝ) (hG : Measurable G)
    {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂μ‖ ≤ C * |ξ| ^ (-δ))
    (θ : ℕ → ℝ) {lam : ℝ} (hlam : lam ≠ 0) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ ↦ (N : ℂ)⁻¹ *
      ∑ n ∈ Finset.range N, ee (θ n + lam * (b : ℝ) ^ n * G ω)) atTop (𝓝 0) := by
  sorry

/-- Fourier decay of Lebesgue measure on `[0, 1)`: `‖∫_{Ico 0 1} e(ξ y) dy‖ ≤ 1 / |ξ|`. -/
theorem norm_integral_Ico_ee_le {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖∫ y, ee (ξ * y) ∂(volume.restrict (Ico (0 : ℝ) 1))‖ ≤ 1 * |ξ| ^ (-1 : ℝ) := by
  sorry

end NormalNumbers.JointRigidity
namespace Real
/-- **Fixed-`x` almost-everywhere joint normality**: for every fixed `x` normal in base `b ≥ 2`,
Lebesgue-almost every `y : ℝ` is jointly normal with `x` in base `b`. -/
theorem ae_isJointlyNormalIn_of_isNormalIn {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (hx : IsNormalIn b x) :
    ∀ᵐ y ∂(volume : Measure ℝ), IsJointlyNormalIn b x y := by
  sorry

/-- **Fixed-`x` almost-everywhere joint absolute normality**: for every fixed absolutely normal `x`,
Lebesgue-almost every `y : ℝ` is jointly absolutely normal with `x`. -/
theorem ae_isJointlyAbsolutelyNormal_of_isAbsolutelyNormal {x : ℝ} (hx : IsAbsolutelyNormal x) :
    ∀ᵐ y ∂(volume : Measure ℝ), IsJointlyAbsolutelyNormal x y := by
  sorry

/-- **Irrational-slope counterexample**: for every irrational `α` and real `u`, Lebesgue-almost
every `y : ℝ` satisfies `IsJointlyAbsolutelyNormal (-α * y + u) y`. -/
theorem ae_isJointlyAbsolutelyNormal_irrational_line {α : ℝ} (hα : Irrational α) (u : ℝ) :
    ∀ᵐ y ∂(volume : Measure ℝ), IsJointlyAbsolutelyNormal (-α * y + u) y := by
  sorry

/-- An irrational-slope shear `(x, y) ↦ (x + α * y + c, y)` does not preserve joint normality. -/
theorem not_preserves_isJointlyNormalIn_irrational_linear {b : ℕ} (hb : 2 ≤ b)
    {α : ℝ} (hα : Irrational α) (c : ℝ) :
    ¬ ∀ x y : ℝ, IsJointlyNormalIn b x y → IsJointlyNormalIn b (x + α * y + c) y := by
  sorry

end Real
/-! ### Part 3: `GL_2(ℚ)` and rational affine invariance of joint normality -/

namespace NormalNumbers.JointRigidity
end NormalNumbers.JointRigidity
namespace Real
/-- Dividing both coordinates of a base-`b` jointly normal pair by a positive integer preserves
joint normality in base `b`. -/
theorem IsJointlyNormalIn.div_nat {b : ℕ} (hb : 2 ≤ b) {x y : ℝ} {D : ℕ} (hD : 0 < D)
    (h : IsJointlyNormalIn b x y) : IsJointlyNormalIn b (x / D) (y / D) := by
  sorry

/-- Nonsingular integer linear transformations preserve joint normality in base `b ≥ 2`. -/
theorem IsJointlyNormalIn.linear_int {b : ℕ} (hb : 2 ≤ b) {x y : ℝ}
    {a₁₁ a₁₂ a₂₁ a₂₂ : ℤ} (hdet : a₁₁ * a₂₂ - a₁₂ * a₂₁ ≠ 0)
    (h : IsJointlyNormalIn b x y) :
    IsJointlyNormalIn b (a₁₁ * x + a₁₂ * y) (a₂₁ * x + a₂₂ * y) := by
  sorry

/-- **`GL_2(ℚ)` invariance of joint normality**: every invertible rational linear transformation
preserves joint normality in base `b ≥ 2`. -/
theorem IsJointlyNormalIn.linear_rat {b : ℕ} (hb : 2 ≤ b) {x y : ℝ}
    {a₁₁ a₁₂ a₂₁ a₂₂ : ℚ} (hdet : a₁₁ * a₂₂ - a₁₂ * a₂₁ ≠ 0)
    (h : IsJointlyNormalIn b x y) :
    IsJointlyNormalIn b (a₁₁ * x + a₁₂ * y) (a₂₁ * x + a₂₂ * y) := by
  sorry

/-- Rational translations preserve joint normality in base `b ≥ 2`. -/
theorem IsJointlyNormalIn.add_ratCast {b : ℕ} (hb : 2 ≤ b) {x y : ℝ} (r₁ r₂ : ℚ)
    (h : IsJointlyNormalIn b x y) : IsJointlyNormalIn b (x + r₁) (y + r₂) := by
  sorry

/-- Invertible rational affine transformations preserve joint normality in base `b ≥ 2`. -/
theorem IsJointlyNormalIn.affine_rat {b : ℕ} (hb : 2 ≤ b) {x y : ℝ}
    {a₁₁ a₁₂ a₂₁ a₂₂ : ℚ} (hdet : a₁₁ * a₂₂ - a₁₂ * a₂₁ ≠ 0) (r₁ r₂ : ℚ)
    (h : IsJointlyNormalIn b x y) :
    IsJointlyNormalIn b (a₁₁ * x + a₁₂ * y + r₁) (a₂₁ * x + a₂₂ * y + r₂) := by
  sorry

/-- Invertible rational linear transformations preserve joint absolute normality. -/
theorem IsJointlyAbsolutelyNormal.linear_rat {x y : ℝ}
    {a₁₁ a₁₂ a₂₁ a₂₂ : ℚ} (hdet : a₁₁ * a₂₂ - a₁₂ * a₂₁ ≠ 0)
    (h : IsJointlyAbsolutelyNormal x y) :
    IsJointlyAbsolutelyNormal (a₁₁ * x + a₁₂ * y) (a₂₁ * x + a₂₂ * y) := by
  sorry

/-- Rational translations preserve joint absolute normality. -/
theorem IsJointlyAbsolutelyNormal.add_ratCast {x y : ℝ} (r₁ r₂ : ℚ)
    (h : IsJointlyAbsolutelyNormal x y) :
    IsJointlyAbsolutelyNormal (x + r₁) (y + r₂) := by
  sorry

end Real
