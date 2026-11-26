/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.Real.Pi.Irrational
public import Mathlib.NumberTheory.Normal.BaileyCrandall
public import Mathlib.NumberTheory.Normal.BasePow
public import Mathlib.NumberTheory.Normal.Rational

/-!
# The BBP formula and Bailey–Crandall reduction for `π` and `log 2`

We prove the **Bailey–Borwein–Plouffe (BBP) formula** for `π` (1997):
$$\pi = \sum_{k=0}^\infty \frac{1}{16^k}
  \left(\frac{4}{8k+1} - \frac{2}{8k+4} - \frac{1}{8k+5} - \frac{1}{8k+6}\right).$$
Combined with the Bailey–Crandall shadowing theorem (`Mathlib/NumberTheory/Normal/BaileyCrandall`),
Maxfield's theorem (`Mathlib/NumberTheory/Normal/BasePow`), and `irrational_pi`, we obtain:

* `Real.isNormalIn_two_pi_iff`: `π` is normal in base `2` (and base `16`) if and only if the
  explicit base-`16` BBP orbit `bbpOrbit 16 bbpPiCoeff` is equidistributed modulo one.
* `Real.not_hasFiniteAttractorModOne_bbpOrbit_pi`: the BBP orbit of `π` does not converge to a
  finite subset of `UnitAddCircle`.
* `Real.isNormalIn_two_pi_of_hypothesisA`: Bailey–Crandall's Hypothesis A for the `π` orbit
  implies that `π` is normal in base `2`.
* `Real.isNormalIn_two_log_two_iff`: `log 2` is normal in base `2` if and only if the orbit
  `x₀ = 0`, `x_{n+1} = fract (2 x_n + 1 / (n + 1))` is equidistributed modulo one.

## References

* [D. H. Bailey, P. Borwein, S. Plouffe, *On the rapid computation of various polylogarithmic
  constants*][BaileyBorweinPlouffe1997]
* [D. H. Bailey, R. E. Crandall, *On the random character of fundamental constant
  expansions*][BaileyCrandall2001]
-/

@[expose] public section

open Filter Topology

namespace Real

/-- The `k`-th rational coefficient of the Bailey–Borwein–Plouffe formula for `π`. -/
noncomputable def bbpPiCoeff (k : ℕ) : ℝ :=
  4 / (8 * k + 1) - 2 / (8 * k + 4) - 1 / (8 * k + 5) - 1 / (8 * k + 6)

/-- **Bailey–Borwein–Plouffe (BBP) formula** for `π`. -/
theorem pi_eq_tsum_bbp : π = ∑' k : ℕ, bbpPiCoeff k / (16 : ℝ) ^ k := by
  sorry

/-- `π / 16` is the BBP series `bbpSum 16 bbpPiCoeff`. -/
theorem pi_div_sixteen_eq_bbpSum : π / 16 = bbpSum 16 bbpPiCoeff := by
  sorry

/-- `π` is normal in base `16` if and only if its BBP orbit is equidistributed modulo one. -/
theorem isNormalIn_sixteen_pi_iff :
    IsNormalIn 16 π ↔ IsEquidistributedModOne (bbpOrbit 16 bbpPiCoeff) := by
  sorry

/-- `π` is normal in base `2` if and only if its base-`16` BBP orbit is equidistributed
modulo one. -/
theorem isNormalIn_two_pi_iff :
    IsNormalIn 2 π ↔ IsEquidistributedModOne (bbpOrbit 16 bbpPiCoeff) := by
  sorry

/-- Because `π` is irrational, its BBP orbit does not have a finite attractor modulo one. -/
theorem not_hasFiniteAttractorModOne_bbpOrbit_pi :
    ¬ HasFiniteAttractorModOne (bbpOrbit 16 bbpPiCoeff) := by
  sorry

/-- **Bailey–Crandall (2001)**: Hypothesis A for the `π` BBP orbit implies that `π` is normal in
base `2`. -/
theorem isNormalIn_two_pi_of_hypothesisA
    (hA : HasFiniteAttractorModOne (bbpOrbit 16 bbpPiCoeff) ∨
      IsEquidistributedModOne (bbpOrbit 16 bbpPiCoeff)) :
    IsNormalIn 2 π := by
  sorry

/-- The Mercator series `log 2 = ∑' k, 1 / ((k + 1) * 2 ^ (k + 1))` as a BBP sum. -/
theorem log_two_eq_bbpSum : Real.log 2 = bbpSum 2 (fun k ↦ ((k : ℝ) + 1)⁻¹) := by
  sorry

/-- `log 2` is normal in base `2` if and only if the Bailey–Crandall orbit
`x₀ = 0`, `x_{n+1} = fract (2 x_n + 1 / (n + 1))` is equidistributed modulo one. -/
theorem isNormalIn_two_log_two_iff :
    IsNormalIn 2 (Real.log 2) ↔
      IsEquidistributedModOne (bbpOrbit 2 (fun k ↦ ((k : ℝ) + 1)⁻¹)) := by
  sorry

end Real
