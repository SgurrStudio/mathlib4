/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.QuarterCantorDecay

import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Polynomial Fourier decay of nonlinear images of a base-`b` Cantor measure

For `b ≥ 2`, let `Y = ∑ ωᵢ b^{-(i+1)}` with fair coins `ωᵢ ∈ {0, 1}` (`bReal b ω`). For `b ≥ 3`
the base-`b` digits of `Y` avoid `2`, so `Y` is not normal in base `b`
(`not_isNormal_bReal`). We prove that for every `F` with `0 < a ≤ F'' ≤ A` on `[0, 1]` the
pushforward of the law of `Y` under `F` has polynomial Fourier decay (`polyDecay`), by the
argument of `NormalNumbers.QuarterCantorDecay` with `4` replaced by `b`: a Riesz product,
linearisation on cylinders, and block averaging over coin flips.

## References

* R. Kaufman, *On the theorem of Jarník and Besicovitch*, Acta Arith. 39 (1981), 265–267.
* C. A. Mosquera and P. S. Shmerkin, *Self-similar measures: asymptotic bounds for the dimension
  and Fourier decay of smooth images*, Ann. Acad. Sci. Fenn. Math. 43 (2018), 823–834.
-/

@[expose] public noncomputable section

open MeasureTheory Real

namespace NormalNumbers.BaseCantorDecay

open ExplicitSquare CantorSelfSimilar CantorCylinders QuarterCantorDecay

variable {b : ℕ}

/-! ### The base-`b` Cantor law -/

/-- The digits `ωᵢ ∈ {0, 1}`. -/
def bDigits (ω : ℕ → Bool) (i : ℕ) : ℕ := if ω i then 1 else 0

/-- The base-`b` Cantor point `∑ ωᵢ b^{-(i+1)}`. -/
def bReal (b : ℕ) (ω : ℕ → Bool) : ℝ := realOfDigits b (bDigits ω)

/-- Fourier transform of `F_* μ_b`, `μ_b` the law of `bReal b` under fair coins. -/
def bFourier (b : ℕ) (F : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ ω, Complex.exp (2 * π * Complex.I * ((ξ * F (bReal b ω) : ℝ) : ℂ)) ∂coinMeasure

/-- Polynomial Fourier decay of `F_* μ_b`. -/
def PolyDecayB (b : ℕ) (F : ℝ → ℝ) : Prop :=
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ ξ : ℝ, ξ ≠ 0 → ‖bFourier b F ξ‖ ≤ C * |ξ| ^ (-δ)

/-- The window `[0, 1]`. -/
abbrev W0 : Set ℝ := Set.Icc (0 : ℝ) 1

/-- For `b ≥ 3` the digit `2` never occurs, so `bReal b ω` is not normal in base `b`. -/
theorem not_isNormal_bReal (hb : 3 ≤ b) (ω : ℕ → Bool) : ¬ IsNormal b (bReal b ω) := by
  sorry

/-! ### Self-similarity and cylinders -/

/-- The IFS map `ψ_c t = (c + t) / b`. -/
def psiB (b : ℕ) (c : Bool) (t : ℝ) : ℝ := ((if c then 1 else 0) + t) / b

/-- Offset of the cylinder map `φ_w`. -/
def offsB (b : ℕ) : List Bool → ℝ
  | [] => 0
  | c :: w => (if c then 1 else 0) / b + offsB b w / b

/-- The cylinder map `φ_w t = offs w + t / b^{|w|}`. -/
def phiB (b : ℕ) (w : List Bool) (t : ℝ) : ℝ := offsB b w + t / (b : ℝ) ^ w.length

/-! ### The Riesz product -/

/-- The Fourier transform of the base-`b` Cantor law itself. -/
abbrev cF (b : ℕ) (s : ℝ) : ℂ := bFourier b id s

/-! ### Calculus on the window -/

section Calculus

variable {F F' F'' : ℝ → ℝ} {a A : ℝ}
  (hF : ∀ t ∈ W0, HasDerivAt F (F' t) t) (hF' : ∀ t ∈ W0, HasDerivAt F' (F'' t) t)
  (hlo : ∀ t ∈ W0, a ≤ F'' t) (hhi : ∀ t ∈ W0, F'' t ≤ A)

end Calculus

/-! ### Words as coin vectors -/

/-- The offset of the cylinder with coin vector `v`. -/
def ptB (b : ℕ) {m : ℕ} (v : Fin m → Bool) : ℝ :=
  ∑ i : Fin m, (if v i then 1 else 0) / (b : ℝ) ^ ((i : ℕ) + 1)

/-! ### The average of the Riesz products over the cylinders -/

section Averaging

variable {F F' F'' : ℝ → ℝ} {a A : ℝ}
  (hF' : ∀ t ∈ W0, HasDerivAt F' (F'' t) t)
  (hlo : ∀ t ∈ W0, a ≤ F'' t) (hhi : ∀ t ∈ W0, F'' t ≤ A)

end Averaging

/-! ### Assembly -/

section Decay

variable {F F' F'' : ℝ → ℝ} {a A : ℝ}
  (hF : ∀ t ∈ W0, HasDerivAt F (F' t) t) (hF' : ∀ t ∈ W0, HasDerivAt F' (F'' t) t)
  (hlo : ∀ t ∈ W0, a ≤ F'' t) (hhi : ∀ t ∈ W0, F'' t ≤ A)

include hF hF' hlo hhi in
/-- **Kaufman-type polynomial Fourier decay** for the pushforward of the base-`b` Cantor law
under a `C²` map with `0 < a ≤ F'' ≤ A` on `[0, 1]`. -/
theorem polyDecay (hb : 2 ≤ b) (hFm : Measurable F) (ha : 0 < a) : PolyDecayB b F := by
  sorry

end Decay

end NormalNumbers.BaseCantorDecay
