/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Stoneham

/-!
# Non-normality of Stoneham numbers in composite base `b * c`

For coprime integers `b, c ≥ 2`, `Real.isNormalIn_stoneham` establishes that the Stoneham number
`α_{b,c} = ∑_{k ≥ 1} 1 / (c ^ k * b ^ (c ^ k))` is normal in base `b`.
**Bailey and Borwein** (2012) proved that `α_{b,c}` is nevertheless **not** normal in base `b * c`
(and hence not absolutely normal): multiplying `α_{b,c}` by `(b * c) ^ (c ^ j)` makes the first
`j` terms an exact integer while the remaining tail is at most `2 * (c / b ^ (c - 1)) ^ (c ^ j)`.
Since `c < b ^ (c - 1)` for all coprime `b, c ≥ 2`, this forces a run of `Ω(c ^ j)` consecutive
base-`(b * c)` zero digits starting at position `c ^ j`, contradicting convergence of the `0`-digit
frequency to `(b * c)⁻¹`.

In particular, `stoneham 2 3` is an explicit constructive witness that base-`2` normality does not
imply base-`6` normality (or absolute normality).

## Main statements

* `Real.not_isNormalIn_mul_stoneham`: for coprime `b, c ≥ 2`, `¬ IsNormalIn (b * c) (stoneham b c)`.
* `Real.not_isNormalIn_six_stoneham_two_three`: `¬ IsNormalIn 6 (stoneham 2 3)`.
* `Real.not_isAbsolutelyNormal_stoneham`: for coprime `b, c ≥ 2`,
  `¬ IsAbsolutelyNormal (stoneham b c)`.

## References

* D. H. Bailey, J. M. Borwein, *Nonnormality of Stoneham constants*,
  Ramanujan J. 29 (2012), 409–422.
-/

@[expose] public section

namespace Real

/-- **Bailey–Borwein (2012)**: for coprime `b, c ≥ 2`, the Stoneham number `stoneham b c` is not
normal in base `b * c`. -/
theorem not_isNormalIn_mul_stoneham {b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c) (hbc : b.Coprime c) :
    ¬ IsNormalIn (b * c) (stoneham b c) := by
  sorry

/-- The Stoneham constant `α_{2,3}` is not normal in base `6` (despite being normal in base `2`,
see `Real.isNormalIn_two_stoneham_three`). -/
theorem not_isNormalIn_six_stoneham_two_three : ¬ IsNormalIn 6 (stoneham 2 3) := by
  sorry

/-- No Stoneham number `stoneham b c` (`b, c ≥ 2` coprime) is absolutely normal. -/
theorem not_isAbsolutelyNormal_stoneham {b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c) (hbc : b.Coprime c) :
    ¬ IsAbsolutelyNormal (stoneham b c) := by
  sorry

end Real
