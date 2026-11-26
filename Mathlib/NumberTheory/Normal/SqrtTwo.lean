/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.NumberTheory.Normal.Basic
public import Mathlib.NumberTheory.Real.Irrational

import Mathlib.Algebra.Order.Floor.Semifield

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
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [bitSum, Nat.digits_def' (by norm_num) hn, List.sum_cons]
    rfl

@[simp]
theorem bitSum_one : bitSum 1 = 1 := by
  rw [bitSum_eq]
  simp

theorem bitSum_two_mul (m : ℕ) : bitSum (2 * m) = bitSum m := by
  rw [bitSum_eq]
  have h1 : 2 * m % 2 = 0 := by omega
  have h2 : 2 * m / 2 = m := by omega
  rw [h1, h2, zero_add]

theorem bitSum_two_mul_add_one (m : ℕ) : bitSum (2 * m + 1) = bitSum m + 1 := by
  rw [bitSum_eq]
  have h1 : (2 * m + 1) % 2 = 1 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  rw [h1, h2, add_comm]

/-- The number of ones is subadditive: adding can only merge ones through carries. -/
theorem bitSum_add_le (a b : ℕ) : bitSum (a + b) ≤ bitSum a + bitSum b := by
  suffices ∀ n a b, a + b = n → bitSum (a + b) ≤ bitSum a + bitSum b from this _ a b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hab
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
      simp
    rw [bitSum_eq (a + b), bitSum_eq a, bitSum_eq b]
    by_cases h : a % 2 = 1 ∧ b % 2 = 1
    · have h1 : (a + b) / 2 = (a / 2 + b / 2) + 1 := by omega
      have h2 : (a + b) % 2 = 0 := by omega
      rw [h1, h2]
      have e1 := ih (a / 2 + b / 2 + 1) (by omega) (a / 2 + b / 2) 1 rfl
      have e2 := ih (a / 2 + b / 2) (by omega) (a / 2) (b / 2) rfl
      rw [bitSum_one] at e1
      omega
    · have h1 : (a + b) / 2 = a / 2 + b / 2 := by omega
      have h2 : (a + b) % 2 = a % 2 + b % 2 := by omega
      rw [h1, h2]
      have := ih (a / 2 + b / 2) (by omega) (a / 2) (b / 2) rfl
      omega

/-- The number of ones is submultiplicative. -/
theorem bitSum_mul_le (a b : ℕ) : bitSum (a * b) ≤ bitSum a * bitSum b := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    have hdec : a * b = 2 * (a * (b / 2)) + a * (b % 2) := by
      conv_lhs => rw [← Nat.div_add_mod b 2]
      ring
    rw [hdec]
    refine (bitSum_add_le _ _).trans ?_
    rw [bitSum_two_mul]
    have h1 := ih (b / 2) (by omega)
    have h2 : bitSum (a * (b % 2)) = bitSum a * (b % 2) := by
      rcases Nat.mod_two_eq_zero_or_one b with h | h <;> simp [h]
    rw [h2, bitSum_eq b, mul_add]
    linarith

theorem bitSum_two_pow_sub_one (M : ℕ) : bitSum (2 ^ M - 1) = M := by
  induction M with
  | zero => simp
  | succ M ih =>
    have : 2 ^ (M + 1) - 1 = 2 * (2 ^ M - 1) + 1 := by
      have := Nat.one_le_two_pow (n := M)
      rw [pow_succ]
      omega
    rw [this, bitSum_two_mul_add_one, ih]

theorem bitSum_le_of_lt_two_pow {M n : ℕ} (hn : n < 2 ^ M) : bitSum n ≤ M := by
  induction M generalizing n with
  | zero =>
    obtain rfl : n = 0 := by simpa using hn
    simp
  | succ M ih =>
    rw [bitSum_eq]
    have := ih (n := n / 2) (by rw [pow_succ] at hn; omega)
    omega

end Nat

namespace Real

open Nat

/-- The ones in the binary expansion of `⌊x * 2 ^ N⌋` are the ones of `⌊x⌋` together with the ones
among the first `N` binary digits of `x`. -/
theorem bitSum_floor_mul_two_pow {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    bitSum ⌊x * 2 ^ N⌋₊ = bitSum ⌊x⌋₊ + ∑ n ∈ Finset.range N, digit 2 x n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    have hdiv : ⌊x * 2 ^ (N + 1)⌋₊ / 2 = ⌊x * 2 ^ N⌋₊ := by
      rw [← Nat.floor_div_natCast]
      congr 1
      push_cast
      ring
    have hdig : digit 2 x N = ⌊x * 2 ^ (N + 1)⌋₊ % 2 := by
      simp only [digit, Nat.cast_ofNat]
      rw [← Int.natCast_floor_eq_floor (by positivity)]
      omega
    rw [bitSum_eq ⌊x * 2 ^ (N + 1)⌋₊, hdiv, hdig, add_comm]

/-- **Bailey–Borwein–Crandall–Pomerance for `√2`.** If `c` is the number of ones among the first
`N` binary digits of `√2`, then `N ≤ (c + 1) ^ 2 + 1`. In particular `c ≥ √(N - 1) - 1`. -/
theorem le_card_digit_sqrt_two_eq_one (N : ℕ) :
    N ≤ (((Finset.range N).filter fun n ↦ digit 2 √2 n = 1).card + 1) ^ 2 + 1 := by
  set c := ((Finset.range N).filter fun n ↦ digit 2 √2 n = 1).card with hc
  have hsum : ∑ n ∈ Finset.range N, digit 2 √2 n = c := by
    rw [hc, Finset.card_filter]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    have := digit_lt (b := 2) (by norm_num) √2 n
    split_ifs <;> omega
  set i := ⌊√2 * 2 ^ N⌋₊ with hi_def
  set S := 2 * (2 ^ N) ^ 2 with hS
  have hi : i = Nat.sqrt S := by
    rw [hi_def, ← Real.nat_floor_real_sqrt_eq_nat_sqrt, hS]
    congr 1
    push_cast
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
  have h1 : ⌊√2⌋₊ = 1 := by
    have := @Real.nat_floor_real_sqrt_eq_nat_sqrt 2
    rw [Nat.cast_ofNat] at this
    rw [this]
    exact (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  have hsI : bitSum i = c + 1 := by
    rw [hi_def, bitSum_floor_mul_two_pow (Real.sqrt_nonneg 2), h1, bitSum_one, hsum, add_comm]
  have hle : i ^ 2 ≤ S := hi ▸ Nat.sqrt_le' S
  have hlt : S < (i + 1) ^ 2 := hi ▸ Nat.lt_succ_sqrt' S
  have hne : i ^ 2 ≠ S := by
    intro h
    have hR : ((i : ℝ) / 2 ^ N) ^ 2 = 2 := by
      have : ((i : ℝ)) ^ 2 = 2 * (2 ^ N) ^ 2 := by exact_mod_cast h
      rw [div_pow, this]
      field_simp
    have hs : √2 = (i : ℝ) / 2 ^ N := by
      have := Real.sqrt_sq (show 0 ≤ (i : ℝ) / 2 ^ N by positivity)
      rwa [hR] at this
    exact irrational_sqrt_two ⟨(i : ℚ) / 2 ^ N, by push_cast; exact hs.symm⟩
  have hpos : 0 < 2 ^ N := Nat.two_pow_pos N
  have hi2 : i < 2 ^ (N + 1) := by
    rw [pow_succ]
    by_contra! H
    have : (2 ^ N * 2) ^ 2 ≤ i ^ 2 := Nat.pow_le_pow_left H 2
    nlinarith
  have hS1 : S - 1 = 2 ^ (2 * N + 1) - 1 := by
    rw [hS]
    ring_nf
  have hsplit : S - 1 = i ^ 2 + (S - i ^ 2 - 1) := by omega
  have hk : S - i ^ 2 - 1 < 2 ^ (N + 2) := by
    have h3 : (i + 1) ^ 2 = i ^ 2 + 2 * i + 1 := by ring
    have h4 : 2 ^ (N + 2) = 2 * 2 ^ (N + 1) := by ring
    omega
  have hA : 2 * N + 1 ≤ bitSum (i ^ 2) + bitSum (S - i ^ 2 - 1) := by
    calc 2 * N + 1 = bitSum (S - 1) := by rw [hS1, bitSum_two_pow_sub_one]
      _ ≤ _ := hsplit ▸ bitSum_add_le _ _
  have hB : bitSum (i ^ 2) ≤ (c + 1) ^ 2 := by
    rw [sq, sq, ← hsI]
    exact bitSum_mul_le i i
  have hC := bitSum_le_of_lt_two_pow hk
  omega

end Real
