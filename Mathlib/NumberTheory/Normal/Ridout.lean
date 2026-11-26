/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Imported.SubspaceTheorems.DiophantineApproximation.PrimeProducts
public import Mathlib.Imported.SubspaceTheorems.DiophantineApproximation.Ridout
public import Mathlib.NumberTheory.Normal.Basic

/-!
# Runs of equal digits in algebraic numbers are `o(n)`

Borel's conjecture (see `Wanted/NumberTheory/Normal/Basic.lean`) predicts that the base-`b`
expansion of an irrational algebraic number `x` looks random. Liouville's inequality only shows
that a run of zeros starting at position `n` has length `O(n)`. **Ridout's theorem** improves this
to `o(n)`: for every `ε > 0`, eventually every run of zeros, or of the digit `b - 1`, starting at
position `n` has length at most `ε * n`.

A run of `m` zeros at position `n` makes `x` within `b ^ (-(n + m))` of `p / b ^ n` with
`p = ⌊x * b ^ n⌋`. The denominator `b ^ n` is a product of primes dividing `b`, and Ridout's theorem
(`Rat.finite_setOf_ridout`, with the primes of `b` as `S₂`) says only finitely many such
rationals approximate `x` to within `(b ^ n) ^ (-(1 + ε))`. Since `x` is irrational, each of
those finitely many rationals stays a fixed distance from `x`, so for large `n` none of them
occurs. A run of digits `b - 1` gives the approximation `(p + 1) / b ^ n` from above.

## Main statements

* `Real.eventually_lt_abs_sub_div_pow`: for `x` algebraic and irrational, eventually in `n`, every
  `p / b ^ n ∈ [0, 1]` is farther than `(b ^ n) ^ (-(1 + ε))` from `x`.
* `Real.eventually_zero_run_le_mul`: runs of zeros starting at position `n` have length at most
  `ε * n` for large `n`.
* `Real.eventually_pred_run_le_mul`: the same for runs of the digit `b - 1`.

## References

* [D. Ridout, *Rational approximations to algebraic numbers*, Mathematika 4 (1957)]
* [Y. Bugeaud, *Distribution modulo one and Diophantine approximation*][Bugeaud2012], Ch. 8
-/

@[expose] public section

open Filter

namespace Real

variable {b : ℕ} {x : ℝ}

/-- If the first `m` base-`b` digits of `y ∈ [0, 1)` vanish, then `y * b ^ m < 1`.
(A copy of the lemma of the same name in `Mathlib/NumberTheory/Normal/Algebraic.lean` on the
Liouville branch; drop it when the two files meet.) -/
private theorem mul_pow_lt_one_of_digit_eq_zero' (hb : 0 < b) {m : ℕ} :
    ∀ {y : ℝ}, 0 ≤ y → y < 1 → (∀ j < m, digit b y j = 0) → y * (b : ℝ) ^ m < 1 := by
  sorry

/-- If the first `m` base-`b` digits of `y ∈ [0, 1)` are all `b - 1`, then
`(1 - y) * b ^ m ≤ 1`. -/
private theorem one_sub_mul_pow_le_one_of_digit_eq_pred (hb : 0 < b) {m : ℕ} :
    ∀ {y : ℝ}, 0 ≤ y → y < 1 → (∀ j < m, digit b y j = b - 1) → (1 - y) * (b : ℝ) ^ m ≤ 1 := by
  sorry

/-- **Ridout's theorem for `b`-adic approximations.** For `x` algebraic and irrational, `b ≥ 2` and
`ε > 0`, eventually in `n` every rational `p / b ^ n` with `0 ≤ p ≤ b ^ n` is farther than
`(b ^ n) ^ (-(1 + ε))` from `x`. -/
theorem eventually_lt_abs_sub_div_pow (hb : 2 ≤ b) (halg : IsAlgebraic ℚ x) (hx : Irrational x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℤ, 0 ≤ p → p ≤ (b : ℤ) ^ n →
      ((b : ℝ) ^ n) ^ (-(1 + ε)) < |x - p / (b : ℝ) ^ n| := by
  sorry

/-- **Zero runs in algebraic numbers are `o(n)`** (Ridout). For `x` algebraic and irrational,
`b ≥ 2` and `ε > 0`, eventually in `n` every run of zeros in the base-`b` expansion of `x`
starting at position `n` has length at most `ε * n`. This strengthens the Liouville bound
`(d - 1) * n + C`. -/
theorem eventually_zero_run_le_mul (hb : 2 ≤ b) (halg : IsAlgebraic ℚ x) (hx : Irrational x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (∀ j < m, digit b x (n + j) = 0) → (m : ℝ) ≤ ε * n := by
  sorry

/-- **Runs of the digit `b - 1` in algebraic numbers are `o(n)`** (Ridout). -/
theorem eventually_pred_run_le_mul (hb : 2 ≤ b) (halg : IsAlgebraic ℚ x) (hx : Irrational x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (∀ j < m, digit b x (n + j) = b - 1) → (m : ℝ) ≤ ε * n := by
  sorry

end Real
