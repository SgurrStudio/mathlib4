/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.NumberTheory.Real.Irrational

/-!
# The binary expansion of `√2` has many ones

Borel's conjecture predicts that about half of the first `N` binary digits of `√2` are ones.
Bailey, Borwein, Crandall and Pomerance proved that there are at least of the order of `√N`
of them. This file formalises their argument for `√2`, which is elementary:

* Let `i = ⌊√2 * 2 ^ N⌋`. Then `i ^ 2 = 2 ^ (2 * N + 1) - k` with `0 < k ≤ 2 * i < 2 ^ (N + 2)`,
  so the binary expansion of `i ^ 2` contains at least `N - 1` ones.
* The number `s(n)` of ones in the binary expansion of `n` satisfies `s(a + b) ≤ s(a) + s(b)` and
  `s(a * b) ≤ s(a) * s(b)`, so `N - 1 ≤ s(i ^ 2) ≤ s(i) ^ 2`.
* Finally `s(i)` is one more than the number of ones among the first `N` binary digits of `√2`.

## Main definitions

* `Nat.bitSum n`: the number of ones in the binary expansion of `n`.

## Main statements

* `Nat.bitSum_add_le`, `Nat.bitSum_mul_le`: subadditivity and submultiplicativity of `bitSum`.
* `Real.bitSum_floor_mul_two_pow`: the ones in `⌊x * 2 ^ N⌋` are the ones of `⌊x⌋` together with
  the ones among the first `N` binary digits of `x`.
* `Real.le_card_digit_sqrt_two_eq_one`: if `c` is the number of ones among the first `N` binary
  digits of `√2`, then `N ≤ (c + 1) ^ 2 + 1`.

## References

* [D. H. Bailey, J. M. Borwein, R. E. Crandall, C. Pomerance,
  *On the binary expansions of algebraic numbers*][baileyborweincrandallpomerance2004]
-/

@[expose] public section

namespace Nat

/-- The number of ones in the binary expansion of `n`, i.e. the sum of its binary digits. -/
def bitSum (n : ℕ) : ℕ := (Nat.digits 2 n).sum

@[simp]
theorem bitSum_zero : bitSum 0 = 0 := by simp [bitSum]

theorem bitSum_eq (n : ℕ) : bitSum n = n % 2 + bitSum (n / 2) := by
  sorry

@[simp]
theorem bitSum_one : bitSum 1 = 1 := by
  sorry

theorem bitSum_two_mul (m : ℕ) : bitSum (2 * m) = bitSum m := by
  sorry

theorem bitSum_two_mul_add_one (m : ℕ) : bitSum (2 * m + 1) = bitSum m + 1 := by
  sorry

/-- The number of ones is subadditive: adding can only merge ones through carries. -/
theorem bitSum_add_le (a b : ℕ) : bitSum (a + b) ≤ bitSum a + bitSum b := by
  sorry

/-- The number of ones is submultiplicative. -/
theorem bitSum_mul_le (a b : ℕ) : bitSum (a * b) ≤ bitSum a * bitSum b := by
  sorry

theorem bitSum_two_pow_sub_one (M : ℕ) : bitSum (2 ^ M - 1) = M := by
  sorry

theorem bitSum_le_of_lt_two_pow {M n : ℕ} (hn : n < 2 ^ M) : bitSum n ≤ M := by
  sorry

end Nat

namespace Real

open Nat

/-- The ones in the binary expansion of `⌊x * 2 ^ N⌋` are the ones of `⌊x⌋` together with the ones
among the first `N` binary digits of `x`. -/
theorem bitSum_floor_mul_two_pow {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    bitSum ⌊x * 2 ^ N⌋₊ = bitSum ⌊x⌋₊ + ∑ n ∈ Finset.range N, digit 2 x n := by
  sorry

/-- **Bailey–Borwein–Crandall–Pomerance for `√2`.** If `c` is the number of ones among the first
`N` binary digits of `√2`, then `N ≤ (c + 1) ^ 2 + 1`. In particular `c ≥ √(N - 1) - 1`. -/
theorem le_card_digit_sqrt_two_eq_one (N : ℕ) :
    N ≤ (((Finset.range N).filter fun n ↦ digit 2 √2 n = 1).card + 1) ^ 2 + 1 := by
  sorry

end Real
