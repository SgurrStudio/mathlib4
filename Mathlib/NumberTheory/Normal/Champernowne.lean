/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.CopelandErdos

/-!
# Champernowne's constant is normal

The base-`b` *Champernowne constant* is the real number `0.1 2 3 … (b-1) 10 11 …` obtained by
concatenating the base-`b` expansions of the positive integers `1, 2, 3, …`. In base ten it is
`0.12345678910111213…`. We prove **Champernowne's theorem** (D. G. Champernowne, 1933): this
number is normal in base `b` for every `b ≥ 2`.

## Main definitions

* `Real.champernowneStart b t`: the position (counted from `0`) at which the expansion of the
  integer `t + 1` starts, i.e. the total number of base-`b` digits of `1, …, t`.
* `Real.champernowneDigit b n`: the `n`-th digit of the concatenation.
* `Real.champernowne b`: the base-`b` Champernowne constant.

## Main statements

* `Real.isNormalIn_champernowne`: Champernowne's theorem.

## Proof

The Champernowne constant is the concatenation `Real.concatenation b (· + 1)` of the positive
integers, which contain `N` terms up to `N + 1`. Hence it is the special case `a n = n + 1` of the
Copeland–Erdős theorem `Real.isNormalIn_concatenation`.

## References

* [D. G. Champernowne, *The construction of decimals normal in the scale of ten*][Champernowne1933]
-/

@[expose] public section

open Filter Topology

namespace Real

/-- The position (counted from `0`) at which the base-`b` expansion of the integer `t + 1` starts in
the Champernowne word `1 2 3 …`, i.e. the total number of base-`b` digits of `1, …, t`. -/
def champernowneStart (b t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range t, (Nat.log b (i + 1) + 1)

theorem exists_lt_champernowneStart_succ (b n : ℕ) : ∃ t, n < champernowneStart b (t + 1) :=
  exists_lt_concatStart_succ b (· + 1) n

/-- The `n`-th digit (counted from `0`) of the base-`b` Champernowne word `1 2 3 …` obtained by
concatenating the base-`b` expansions of the positive integers. -/
noncomputable def champernowneDigit (b n : ℕ) : ℕ :=
  open Classical in
  let t := Nat.find (exists_lt_champernowneStart_succ b n)
  (t + 1) / b ^ (champernowneStart b (t + 1) - 1 - n) % b

/-- The base-`b` Champernowne constant `0.1 2 3 … (b-1) 10 11 …`. -/
noncomputable def champernowne (b : ℕ) [NeZero b] : ℝ :=
  ofDigits fun n ↦ Fin.ofNat b (champernowneDigit b n)

theorem champernowneStart_eq_concatStart (b : ℕ) :
    champernowneStart b = concatStart b (· + 1) := rfl

theorem champernowneDigit_eq_concatDigit (b : ℕ) :
    champernowneDigit b = concatDigit b (· + 1) := rfl

/-- The Champernowne constant is the concatenation of the positive integers. -/
theorem champernowne_eq_concatenation (b : ℕ) [NeZero b] :
    champernowne b = concatenation b (· + 1) := rfl

/-- **Champernowne's theorem**: the base-`b` Champernowne constant is normal in base `b`. -/
theorem isNormalIn_champernowne {b : ℕ} [NeZero b] (hb : 2 ≤ b) :
    IsNormalIn b (champernowne b) := by
  refine isNormalIn_concatenation hb (strictMono_id.add_const 1) Nat.one_pos fun θ hθ ↦ ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have : ((Finset.range (N + 1)).filter fun i ↦ i + 1 ≤ N) = Finset.range N := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]
  calc (N : ℝ) ^ θ ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hθ.le
    _ = N := Real.rpow_one _

/-- The decimal Champernowne constant `0.123456789101112…` is normal in base ten. -/
theorem isNormalIn_ten_champernowne : IsNormalIn 10 (champernowne 10) :=
  isNormalIn_champernowne (by norm_num)

end Real
