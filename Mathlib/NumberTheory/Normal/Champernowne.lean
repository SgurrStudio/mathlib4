/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.Real.OfDigits
public import Mathlib.NumberTheory.Normal.Borel

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

* `Real.digit_champernowne`: the base-`b` digits of `champernowne b` are `champernowneDigit b`.
* `Real.isNormalIn_champernowne`: Champernowne's theorem.

## Proof sketch

A block `w` of length `k` lying inside the expansion of an integer `m` with its last digit at
position `s` from the right occurs iff `⌊m / b ^ s⌋ ≡ code(w) [MOD b ^ k]`. For fixed `s`, the
integers `m ≤ T` that are long enough form an interval, on which this congruence holds with
frequency `b⁻ᵏ` up to an error `2 b ^ (s + k)`. Summing over `s` the total error is `O(T)`,
blocks straddling two integers contribute at most `(k - 1) T`, while the number of digits written
up to the integer `T` grows like `T log T`.

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

theorem exists_lt_champernowneStart_succ (b n : ℕ) : ∃ t, n < champernowneStart b (t + 1) := by
  sorry

/-- The `n`-th digit (counted from `0`) of the base-`b` Champernowne word `1 2 3 …` obtained by
concatenating the base-`b` expansions of the positive integers. -/
noncomputable def champernowneDigit (b n : ℕ) : ℕ :=
  open Classical in
  let t := Nat.find (exists_lt_champernowneStart_succ b n)
  (t + 1) / b ^ (champernowneStart b (t + 1) - 1 - n) % b

/-- The base-`b` Champernowne constant `0.1 2 3 … (b-1) 10 11 …`. -/
noncomputable def champernowne (b : ℕ) [NeZero b] : ℝ :=
  ofDigits fun n ↦ Fin.ofNat b (champernowneDigit b n)

variable {b : ℕ}

theorem champernowneDigit_lt (hb : 0 < b) (n : ℕ) : champernowneDigit b n < b := by
  sorry

/-- The base-`b` digits of the Champernowne constant are the digits of the Champernowne word. -/
theorem digit_champernowne [NeZero b] (hb : 2 ≤ b) (n : ℕ) :
    digit b (champernowne b) n = champernowneDigit b n := by
  sorry

/-- **Champernowne's theorem**: the base-`b` Champernowne constant is normal in base `b`. -/
theorem isNormalIn_champernowne [NeZero b] (hb : 2 ≤ b) : IsNormalIn b (champernowne b) := by
  sorry

/-- The decimal Champernowne constant `0.123456789101112…` is normal in base ten. -/
theorem isNormalIn_ten_champernowne : IsNormalIn 10 (champernowne 10) :=
  isNormalIn_champernowne (by norm_num)

end Real
