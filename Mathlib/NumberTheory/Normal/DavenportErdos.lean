/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.NumberTheory.Normal.CopelandErdos

/-!
# The Davenport–Erdős theorem

Let `f` be a non-constant polynomial with integer coefficients taking positive values at the
positive integers. **Davenport and Erdős** (1952) proved that the number
`0.f(1) f(2) f(3) …`, obtained by concatenating the base-`b` expansions of `f(1), f(2), …`, is
normal in base `b`. For `f = X` this is Champernowne's theorem
(`Mathlib.NumberTheory.Normal.Champernowne`); for `f = X ^ 2` it says `0.1 4 9 16 25 …` is normal.

Copeland–Erdős (`Real.isNormalIn_concatenation`) does not apply: the values of a polynomial of
degree `d ≥ 2` have density `N ^ (1 / d - 1)` in `[1, N]`, below the `N ^ (θ - 1)` it needs
for every `θ < 1`.

## Main statements

* `Real.isNormalIn_concatenation_polynomial`: the Davenport–Erdős theorem.
* `Real.isNormalIn_concatenation_sq`: Besicovitch's theorem, the case `f = X ^ 2`.

## Proof

Following Davenport and Erdős, it suffices by Piatetski-Shapiro's criterion
(`Real.isNormalIn_of_eventually_le`) to bound, for `n ∈ [N, 2N)`, how often a block `w` occurs
at a fixed distance from the end of the expansion of `f(n)`. The digits at distance `s` from the
end of `f(n)` are `⌊f(n) / b ^ s⌋ mod b ^ k`, and these are equidistributed by Weyl's inequality
for the polynomial `f(n) / b ^ (s + k)` (proved by van der Corput differencing, Tau Ceti's
`vanDerCorput_inequality`), except for the `O(1)` leading digits.

For squares there is an elementary proof by **Pollack and Vandehey**, which we follow for
`Real.isNormalIn_concatenation_sq`: by the few-bad-terms criterion
(`Real.isNormalSeq_concatDigit_of_concatBad`) it is enough that few `n ^ 2` have a bad block
frequency. Cut `n ^ 2 = u * b ^ ℓ + v` with `b ^ ℓ ≈ n`. The upper half `u` takes each value at
most `b ^ ℓ / n` times, and the lower half `v = n ^ 2 mod b ^ ℓ` takes each value rarely on average
since `x ^ 2 ≡ y ^ 2 [MOD b ^ ℓ]` has few solutions; so few `n` have a bad half.

## References

* [H. Davenport, P. Erdős, *Note on normal decimals*][DavenportErdos1952]
* [A. S. Besicovitch, *The asymptotic distribution of the numerals in the decimal representation
  of the squares of the natural numbers*][Besicovitch1935]
* [P. Pollack, J. Vandehey, *Besicovitch, bisection, and the normality of
  0.(1)(4)(9)(16)(25)…*][PollackVandehey2015]
* [Y. Nakai, I. Shiokawa, *Discrepancy estimates for a class of normal numbers*][NakaiShiokawa1992]
-/

@[expose] public section

open Polynomial

namespace Real

/-- **The Davenport–Erdős theorem**: if `f` is a non-constant integer polynomial with `f(n) > 0`
for all `n ≥ 1`, then `0.f(1) f(2) f(3) …` is normal in every base `b ≥ 2`. -/
theorem isNormalIn_concatenation_polynomial {b : ℕ} [NeZero b] (hb : 2 ≤ b) {f : ℤ[X]}
    (hf : 0 < f.natDegree) (hpos : ∀ n : ℕ, 0 < f.eval ((n : ℤ) + 1)) :
    IsNormalIn b (concatenation b fun n ↦ (f.eval ((n : ℤ) + 1)).toNat) := by
  sorry

/-- **Besicovitch's theorem**: the concatenation `0.1 4 9 16 25 …` of the squares is normal in
every base `b ≥ 2`. -/
theorem isNormalIn_concatenation_sq {b : ℕ} [NeZero b] (hb : 2 ≤ b) :
    IsNormalIn b (concatenation b fun n ↦ (n + 1) ^ 2) := by
  sorry

end Real
