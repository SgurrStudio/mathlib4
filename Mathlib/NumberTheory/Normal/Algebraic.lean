/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Basic
public import Mathlib.NumberTheory.Transcendental.Liouville.Basic
public import Mathlib.RingTheory.Localization.Integral

/-!
# Digits of algebraic numbers: Liouville-type gap bounds

Borel's conjecture (see `Wanted/NumberTheory/Normal/Basic.lean`) predicts that the base-`b`
expansion of an irrational algebraic number looks random. Very little is known in this direction.
The most elementary result is a consequence of Liouville's inequality: if `x` is a root of a
nonzero integer polynomial of degree `d`, then a run of zeros in the base-`b` expansion of `x`
starting at position `n` has length at most `(d - 1) * n + C`, for a constant `C` depending only on
`x` and `b`. Equivalently, every window `[n, d * n + C)` of positions contains a nonzero digit.

The idea is that a run of `m` zeros after position `n` gives a rational approximation
`⌊x * b ^ n⌋ / b ^ n` of `x` with error less than `b ^ (-(n + m))`, while Liouville's inequality
bounds the error from below by a constant times `b ^ (-(n * d))`.

## Main statements

* `Real.fract_lt_of_digit_eq_zero`: if the first `m` digits of `y ∈ [0, 1)` vanish, then
  `y < b ^ (-m)`.
* `Real.exists_zero_run_le`: zero runs in the expansion of an irrational root of a nonzero
  integer polynomial of degree `d` starting at position `n` have length at most
  `(d - 1) * n + C`.
* `Real.exists_digit_ne_zero_of_isAlgebraic`: for an irrational algebraic number, some
  `d ≥ 1` and `C` are such that every window `[n, d * n + C)` contains a nonzero digit.

## References

* [D. H. Bailey, J. M. Borwein, R. E. Crandall, C. Pomerance,
  *On the binary expansions of algebraic numbers*][BaileyBorweinCrandallPomerance2004]
* [Y. Bugeaud, *Distribution modulo one and Diophantine approximation*][Bugeaud2012]
-/

@[expose] public section

open Polynomial

namespace Real

variable {b : ℕ} {x : ℝ}

/-- If the first `m` base-`b` digits of `y ∈ [0, 1)` all vanish, then `y < b ^ (-m)`, i.e.
`y * b ^ m < 1`. -/
theorem mul_pow_lt_one_of_digit_eq_zero (hb : 0 < b) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) {m : ℕ}
    (h : ∀ j < m, digit b y j = 0) : y * (b : ℝ) ^ m < 1 := by
  sorry

/-- If the base-`b` digits of `x` at positions `n, n + 1, …, n + m - 1` all vanish, then
`x` is within `b ^ (-(n + m))` of the rational number `⌊x * b ^ n⌋ / b ^ n`. -/
theorem abs_sub_floor_div_lt_of_digit_eq_zero (hb : 0 < b) {n m : ℕ}
    (h : ∀ j < m, digit b x (n + j) = 0) :
    |x - ⌊x * (b : ℝ) ^ n⌋ / (b : ℝ) ^ n| < ((b : ℝ) ^ (n + m))⁻¹ := by
  sorry

/-- **Liouville bound on zero runs.** Let `x` be an irrational root of a nonzero integer
polynomial `f`. Then there is a constant `C` such that any run of zero digits in the base-`b`
expansion of `x` starting at position `n` has length at most `(f.natDegree - 1) * n + C`. -/
theorem exists_zero_run_le (hb : 2 ≤ b) (hx : Irrational x) {f : ℤ[X]} (f0 : f ≠ 0)
    (fx : aeval x f = 0) :
    ∃ C : ℕ, ∀ n m : ℕ, (∀ j < m, digit b x (n + j) = 0) → m ≤ (f.natDegree - 1) * n + C := by
  sorry

/-- For an irrational algebraic number `x` and a base `b ≥ 2`, there are `d ≥ 1` and `C` such that
every window of positions `[n, d * n + C)` contains a nonzero base-`b` digit of `x`. In particular
the gaps between consecutive nonzero digits grow at most geometrically. -/
theorem exists_digit_ne_zero_of_isAlgebraic (hb : 2 ≤ b) (halg : IsAlgebraic ℚ x)
    (hx : Irrational x) :
    ∃ d C : ℕ, 1 ≤ d ∧ ∀ n : ℕ, ∃ i, n ≤ i ∧ i < d * n + C ∧ digit b x i ≠ 0 := by
  sorry

end Real
