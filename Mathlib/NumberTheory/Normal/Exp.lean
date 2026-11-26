/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Imported.TauCeti.NumberTheory.DiophantineApproximation.Exponent
public import Mathlib.NumberTheory.Normal.Basic

/-!
# Irrationality exponent and base-`b` digit bounds for `e = exp 1`

While the normality of `e = Real.exp 1` remains open (see `Wanted/NumberTheory/Normal/PiExp.lean`),
the Hermite–Padé integrals
$$I_n = \int_0^1 \frac{x^n (1 - x)^n}{n!} e^x \, dx, \qquad
  J_n = \int_0^1 \frac{x^{n+1} (1 - x)^n}{n!} e^x \, dx$$
yield simultaneous integer linear forms `I_n = A_n e - B_n` and `J_n = C_n e - D_n` with
determinant `A_n D_n - B_n C_n = (-1)^{n+1}`, `|A_n|, |C_n| ≤ 8^n (n+1)!`, and
`0 < I_n, J_n ≤ e / (4^n n!)`.

This gives a short, self-contained proof of:

* `Real.irrational_exp_one`: `e = exp 1` is irrational.
* `Real.irrationalityExponent_exp_one`: the irrationality exponent of `e` (in the sense of
  `TauCeti.irrationalityExponent`) equals `2`.
* `Real.exists_zero_run_le_of_irrationalityExponent_lt`: for any irrational `x` with
  `TauCeti.irrationalityExponent x < μ`, runs of `m` consecutive base-`b` zeros starting at
  position `n` satisfy `m ≤ (μ - 1) * n + C`.
* `Real.exists_zero_run_le_exp_one`: in every base `b ≥ 2` and for every `ε > 0`, runs of `m`
  consecutive zeros in the base-`b` expansion of `e` starting at position `n` have length at most
  `(1 + ε) * n + C`.

## References

* [C. S. Davis, *Rational approximations to e*][Davis1978]
* [Y. Bugeaud, *Distribution modulo one and Diophantine approximation*][Bugeaud2012]
-/

@[expose] public section

open Filter Topology
open scoped ENNReal

namespace Real

/-- `e = Real.exp 1` is irrational. -/
theorem irrational_exp_one : Irrational (Real.exp 1) := by
  sorry

/-- The irrationality exponent of `e = Real.exp 1` is `2`. -/
theorem irrationalityExponent_exp_one :
    TauCeti.irrationalityExponent (Real.exp 1) = 2 := by
  sorry

/-- Any irrational number with irrationality exponent strictly less than `μ` has base-`b` zero
runs starting at position `n` of length at most `(μ - 1) * n + C`. -/
theorem exists_zero_run_le_of_irrationalityExponent_lt {b : ℕ} (hb : 2 ≤ b) {x μ : ℝ}
    (hx : Irrational x) (hμ : TauCeti.irrationalityExponent x < ENNReal.ofReal μ) :
    ∃ C : ℝ, ∀ n m : ℕ, (∀ j < m, digit b x (n + j) = 0) →
      (m : ℝ) ≤ (μ - 1) * n + C := by
  sorry

/-- Unconditional digit bound for `e = Real.exp 1`: in every base `b ≥ 2` and for every `ε > 0`,
runs of `m` consecutive zeros starting at position `n` have length at most `(1 + ε) * n + C`. -/
theorem exists_zero_run_le_exp_one {b : ℕ} (hb : 2 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n m : ℕ, (∀ j < m, digit b (Real.exp 1) (n + j) = 0) →
      (m : ℝ) ≤ (1 + ε) * n + C := by
  sorry

end Real
