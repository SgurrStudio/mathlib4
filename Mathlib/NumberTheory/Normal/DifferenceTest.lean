/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Imported.TauCeti.Analysis.SpecificLimits.VanDerCorput
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Exponential sums with polynomial phases: the `d`-th difference test

For a real polynomial `φ` of degree `d` we bound `∑_{n < L} e(φ(n))`, where `e(x) = exp(2πix)`,
in terms of its leading coefficient `α` alone: if `α` is small, but not too small compared with
`L ^ (-d)`, the sum is `o(L)`. Unlike Weyl's inequality this needs no rational approximation to
`α`, so it needs no divisor bound. It is the input for the Davenport–Erdős theorem, where
`α = h a / b ^ m` is the leading coefficient of `h f(n) / b ^ m`.

The proof applies van der Corput's inequality (`TauCeti.vanDerCorput_inequality`, imported from
Tau Ceti) `d - 1` times, each time lowering the degree by one, and ends with a geometric series.

## Main statements

* `Polynomial.norm_polyExpSum_pow_le`: the `d`-th difference test.
-/

@[expose] public section

open Complex Finset

namespace Polynomial

/-- The exponential sum `∑_{n < L} e(φ(n))` of a real polynomial phase. -/
noncomputable def polyExpSum (φ : ℝ[X]) (L : ℕ) : ℂ :=
  ∑ n ∈ range L, exp (2 * Real.pi * I * φ.eval (n : ℝ))

/-- **The `d`-th difference test**: a polynomial phase of degree `d` whose leading coefficient `α`
is small but not too small has a small exponential sum. -/
theorem norm_polyExpSum_pow_le {d : ℕ} (hd : 1 ≤ d) : ∃ K : ℝ, 0 < K ∧
    ∀ (N L H : ℕ) (φ : ℝ[X]) (α : ℝ), 1 ≤ H → H ≤ N → L ≤ N → φ.natDegree ≤ d →
      φ.coeff d = α → 0 < α → (d.factorial : ℝ) * α * (H : ℝ) ^ (d - 1) ≤ 1 / 2 →
        (‖polyExpSum φ L‖ / N) ^ 2 ^ (d - 1) ≤
          K * (1 / H + (1 + Real.log H) ^ (d - 1) / (α * N * (H : ℝ) ^ (d - 1))) := by
  sorry

end Polynomial
