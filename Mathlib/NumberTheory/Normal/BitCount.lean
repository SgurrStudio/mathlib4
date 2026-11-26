/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.NumberTheory.Normal.Algebraic

/-!
# Algebraic irrationals have many ones in their binary expansion

Bailey, Borwein, Crandall and Pomerance proved that if `x` is an irrational algebraic number of
degree `d`, then for some `c > 0` and all large `N` there are at least `c * N ^ (1 / d)` ones
among the first `N` binary digits of `x`. `Mathlib.NumberTheory.Normal.SqrtTwo` treats `√2`. This
file treats all algebraic irrationals.

## Proof

We follow §6–7 of the paper, with Liouville's zero-run bound `Real.exists_zero_run_le` in place
of the Thue–Siegel–Roth step (this only changes the constant). Shift `x` into `[1, 2)` and let
`P = ∑ A_d X ^ d` be an integer polynomial of degree `D` with `P(x) = 0` and `A_D > 0`. For a fixed
`N`, let `F = ∑_{p ∈ S} X ^ p ∈ ℕ[X]`, where `S ∋ 0` is the set of positions of the ones among the
first `N` binary digits, so that `F(1/2) = ⌊x * 2 ^ N⌋ / 2 ^ N` and `s = F(1) = |S|`.

* For `R : ℕ` put `T(R) = ∑_d A_d ∑_{n > R} [Xⁿ] F ^ d / 2 ^ (n - R)`. Then `2 ^ R * P(F(1/2)) - T(R)`
  is an integer and `|P(F(1/2))| ≪ 2 ^ (-N)`, so `T(R)` is within `1/4` of an integer for
  `R ≤ N - c₀`.
* Since `∑_R ∑_{n > R} [Xⁿ] F ^ d / 2 ^ (n - R) ≤ F(1) ^ d`, at most `≪ s ^ D` values of `R` have
  `T(R) ≥ 3/4`.
* `T(R - 1) = (T(R) + ∑_d A_d [X^R] F ^ d) / 2`. Between consecutive points of the support of
  `F ^ (D - 1)` (there are at most `s ^ (D - 1)` of them) only the `d = D` term survives, so
  `T` stays `≥ 3/4` going leftwards from a point of the support of `F ^ D`, as long as the
  lower powers have no support slightly to the right. Liouville's bound places a point of the
  support of `F ^ D` a fixed fraction `1/D` into every gap, so `T(R) ≥ 3/4` for a proportion
  `1/D` of all `R ≤ N`, up to `O(s ^ D)`.

Hence `N ≤ E * s ^ D + c` for constants `E, c`.

## Main statements

* `Real.exists_le_mul_card_digit_eq_one_pow`: if `x` is an irrational root of a nonzero integer
  polynomial `f`, there are `E, c` with `N ≤ E * (#ones among the first N digits + 1) ^ deg f + c`.
* `Real.eventually_le_card_digit_eq_one`: the same, as `c * N ^ (1 / deg f) ≤ #ones` for large `N`.
* `Real.eventually_le_card_digit_eq_one_of_isAlgebraic`: the Bailey–Borwein–Crandall–Pomerance
  bound with `d` the degree of `x` over `ℚ`.

## References

* [D. H. Bailey, J. M. Borwein, R. E. Crandall, C. Pomerance,
  *On the binary expansions of algebraic numbers*][baileyborweincrandallpomerance2004]
-/

@[expose] public section

open Polynomial Filter

namespace Real

variable {x : ℝ}

/-- **Bailey–Borwein–Crandall–Pomerance**, explicit form. If `x` is an irrational root of a
nonzero integer polynomial `f`, there are constants `E` and `c` such that for every `N`, if `k`
ones occur among the first `N` binary digits of `x`, then `N ≤ E * (k + 1) ^ f.natDegree + c`. -/
theorem exists_le_mul_card_digit_eq_one_pow (hx : Irrational x) {f : ℤ[X]} (f0 : f ≠ 0)
    (fx : aeval x f = 0) : ∃ E c : ℕ, ∀ N : ℕ,
      N ≤ E * (((Finset.range N).filter fun n ↦ digit 2 x n = 1).card + 1) ^ f.natDegree + c := by
  sorry

/-- **Bailey–Borwein–Crandall–Pomerance.** If `x` is an irrational root of a nonzero integer
polynomial `f` of degree `d`, then there is `c > 0` such that for all large `N` at least
`c * N ^ (1 / d)` of the first `N` binary digits of `x` are ones. -/
theorem eventually_le_card_digit_eq_one (hx : Irrational x) {f : ℤ[X]} (f0 : f ≠ 0)
    (fx : aeval x f = 0) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ^ (1 / (f.natDegree : ℝ)) ≤
        ((Finset.range N).filter fun n ↦ digit 2 x n = 1).card := by
  sorry

/-- **Bailey–Borwein–Crandall–Pomerance.** If `x` is an irrational algebraic number of degree `d`,
then there is `c > 0` such that for all large `N` at least `c * N ^ (1 / d)` of the first `N`
binary digits of `x` are ones. -/
theorem eventually_le_card_digit_eq_one_of_isAlgebraic (halg : IsAlgebraic ℚ x)
    (hx : Irrational x) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ^ (1 / ((minpoly ℚ x).natDegree : ℝ)) ≤
        ((Finset.range N).filter fun n ↦ digit 2 x n = 1).card := by
  sorry

end Real
