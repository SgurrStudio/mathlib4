/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.PiatetskiShapiro

/-!
# Normality is invariant under rational affine maps

**Wall** (1949) proved that if `x` is normal in base `b`, then so is `q * x + r` for all rational
numbers `q ≠ 0` and `r`.

## Main statements

* `Real.IsNormalIn.mul_natCast`, `Real.IsNormalIn.div_natCast`, `Real.IsNormalIn.neg`:
  normality is preserved by multiplication and division by positive integers, and by negation.
* `Real.isNormalIn_mul_add_ratCast_iff`: `q * x + r` is normal in base `b` iff `x` is.

## Proof sketch

Both for `n * x` and for `x / m`, the block of `k` digits at position `i` is determined by the
block of `x` at position `i` together with a bounded amount of extra information (a carry
`< n`, respectively the residue of `⌊x * b ^ i⌋` modulo `m`). Hence each block of the new number
has upper frequency at most `C * b⁻ᵏ`, and Piatetski-Shapiro's criterion
(`Real.isNormalIn_of_eventually_le`) applies.

## References

* [D. D. Wall, *Normal Numbers*][Wall1949]
-/

@[expose] public section

namespace Real

variable {b : ℕ} {x : ℝ}

theorem IsNormalIn.mul_natCast (hb : 2 ≤ b) (h : IsNormalIn b x) {n : ℕ} (hn : 0 < n) :
    IsNormalIn b (x * n) := by
  sorry

theorem IsNormalIn.div_natCast (hb : 2 ≤ b) (h : IsNormalIn b x) {m : ℕ} (hm : 0 < m) :
    IsNormalIn b (x / m) := by
  sorry

theorem IsNormalIn.neg (hb : 2 ≤ b) (h : IsNormalIn b x) : IsNormalIn b (-x) := by
  sorry

/-- **Wall's theorem**: normality in base `b` is invariant under `x ↦ q * x + r` for rationals
`q ≠ 0` and `r`. -/
theorem isNormalIn_mul_add_ratCast_iff (hb : 2 ≤ b) {q : ℚ} (hq : q ≠ 0) (r : ℚ) :
    IsNormalIn b (q * x + r) ↔ IsNormalIn b x := by
  sorry

end Real
