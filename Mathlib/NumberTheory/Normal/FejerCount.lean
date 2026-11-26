/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Counting points in a short interval with Fejér squares

For a real sequence `x` and `K > 0`, the number of `n < L` with `x n - c ∈ [0, 1 / K)` modulo one
is at most `8 L / K + (16 / K) ∑_{1 ≤ h < K} |∑_{n < L} e(h x n)|`,
where `e(t) = exp(2 π i t)`.

This is the quantitative form of Weyl's criterion used by Davenport–Erdős: the indicator of a
short interval is dominated by the Fejér square `(2 / K²) |∑_{j < K} e(j t)|²`, which is a
trigonometric polynomial of degree `< K`.

## Main statements

* `Complex.card_fract_sub_lt_le`: the counting bound above.
-/

@[expose] public section

open Finset
open scoped Real

namespace Complex

/-- The additive character `e(t) = exp(2 π i t)` of `ℝ / ℤ`, as a complex number. -/
noncomputable def cexpTwoPi (t : ℝ) : ℂ := exp (2 * π * I * t)

/-- The Weyl sum `∑_{n < L} e(h x_n)`. -/
noncomputable def weylSum (x : ℕ → ℝ) (L : ℕ) (h : ℤ) : ℂ :=
  ∑ n ∈ range L, cexpTwoPi (h * x n)

/-- **Counting with Fejér squares**: the number of `n < L` with `x n - c ∈ [0, 1/K) mod 1` is
at most `8 L / K` plus the Weyl sums of `x` with frequencies `1 ≤ h < K`. -/
theorem card_fract_sub_lt_le (x : ℕ → ℝ) (c : ℝ) {K : ℕ} (hK : 0 < K) (L : ℕ) :
    (((range L).filter fun n ↦ Int.fract (x n - c) < 1 / K).card : ℝ) ≤
      8 * L / K + 16 / K * ∑ h ∈ Ico 1 K, ‖weylSum x L h‖ := by
  sorry

end Complex
