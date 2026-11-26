/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Imported.NormalNumbers.CantorCylinders

import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Polynomial Fourier decay of nonlinear images of the quarter-Cantor measure

Let `μ` be the law of `cantorReal ω` under fair coins (the quarter-Cantor measure of
`NormalNumbers.ExplicitSquare`, supported in `[1/2, 2/3]`). We prove that for every `F` with
`a ≤ F'' ≤ A` on `[1/2, 1]` (`0 < a`), the pushforward `F_* μ` has polynomial Fourier decay
(`NormalNumbers.QuarterCantorDecay.polyDecay`). This is the input that
`NormalNumbers.ExplicitSquare` cites as `BakerBanajiQuarterCantor`.

## Proof (after Kaufman)

1. **Riesz product.** Self-similarity gives `|μ̂(s)| = |cos(π s / 8)| |μ̂(s / 4)|`, hence
   `|μ̂(s)| ≤ ∏_{k < K} |cos(π s / (8 · 4^k))|`.
2. **Linearisation.** Split `μ` into the `2^m` cylinders of depth `m`
   (`CantorCylinders.pushFourier_cylinders`). On a cylinder `F` is affine up to an error
   `A · 16^{-m}`, so `|\widehat{F_* μ}(ξ)| ≤ 2^{-m} ∑_w |μ̂(ξ F'(p_w) / 4^m)| + 2π A |ξ| 16^{-m}`.
3. **Averaging.** Flipping the `i`-th coin of `w` moves `p_w` by `4^{-i} / 8`, hence moves
   `F'(p_w)` by `≍ 4^{-i}` because `F'' ≍ 1`. At the scale `k = J - i` this moves the Riesz
   factor's phase by an amount in `[c, 1 - c]`, so on average over that coin the factor is at most
   `ρ < 1`. Treating digit blocks of length `r` one at a time (after truncating the digits beyond
   the block, which costs a small `e`) bounds the average of the product by `(ρ + e)^L`.

## References

* R. Kaufman, *On the theorem of Jarník and Besicovitch*, Acta Arith. 39 (1981), 265–267.
* C. A. Mosquera and P. S. Shmerkin, *Self-similar measures: asymptotic bounds for the dimension
  and Fourier decay of smooth images*, Ann. Acad. Sci. Fenn. Math. 43 (2018), 823–834.
* S. Baker and A. Banaji, *Polynomial Fourier decay for fractal measures and their pushforwards*,
  Math. Ann. 392 (2025).
-/

@[expose] public noncomputable section

open MeasureTheory Real

namespace NormalNumbers.QuarterCantorDecay

open ExplicitSquare CantorSelfSimilar CantorCylinders

/-! ### Basic facts about the quarter-Cantor law -/

/-- The window `[1/2, 1]`, which contains every quarter-Cantor point and every cylinder. -/
abbrev W : Set ℝ := Set.Icc (1 / 2 : ℝ) 1

section Decay

variable {F F' F'' : ℝ → ℝ} {a A : ℝ}
  (hF : ∀ t ∈ W, HasDerivAt F (F' t) t) (hF' : ∀ t ∈ W, HasDerivAt F' (F'' t) t)
  (hlo : ∀ t ∈ W, a ≤ F'' t) (hhi : ∀ t ∈ W, F'' t ≤ A)

include hF hF' hlo hhi in
/-- **Kaufman-type polynomial Fourier decay** for the pushforward of the quarter-Cantor law
under a `C²` map with `0 < a ≤ F'' ≤ A` on the window. -/
theorem polyDecay (hFm : Measurable F) (ha : 0 < a) : PolyDecay F := by
  sorry

end Decay

end NormalNumbers.QuarterCantorDecay
