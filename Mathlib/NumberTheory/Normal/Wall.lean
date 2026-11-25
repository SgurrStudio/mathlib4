/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Borel

/-!
# Wall's theorem: normality and equidistribution

A sequence `u : ℕ → ℝ` is *equidistributed modulo one* if for every interval `[a, c) ⊆ [0, 1]`
the proportion of `n < N` with `Int.fract (u n) ∈ [a, c)` tends to `c - a`.

We prove **Wall's theorem** (D. D. Wall, 1949): a real number `x` is normal in base `b ≥ 2` if and
only if the sequence `(x * b ^ n)` is equidistributed modulo one. Combined with Borel's normal
number theorem this shows that for almost every `x` the sequence `(x * b ^ n)` is equidistributed
modulo one.

## Main definitions

* `IsEquidistributedModOne u`: the sequence `u` is equidistributed modulo one.

## Main statements

* `Real.blockCount_eq_card_floor_fract`: the block `w` occurs at position `i` of the base-`b`
  expansion of `x` iff `Int.fract (x * b ^ i)` lies in the `b`-adic interval coded by `w`.
* `Real.isNormalIn_iff_isEquidistributedModOne`: Wall's theorem.
* `Real.ae_isEquidistributedModOne_mul_pow`: for almost every `x`, `(x * b ^ n)` is
  equidistributed modulo one.

## References

* [D. D. Wall, *Normal numbers*, PhD thesis, UC Berkeley, 1949][Wall1949]
* [L. Kuipers, H. Niederreiter, *Uniform distribution of sequences*][KuipersNiederreiter1974]
-/

@[expose] public section

open Filter Topology MeasureTheory Set

/-- A real sequence `u` is *equidistributed modulo one* if for every `0 ≤ a ≤ c ≤ 1` the
proportion of indices `n < N` such that `Int.fract (u n) ∈ [a, c)` tends to `c - a`. -/
def IsEquidistributedModOne (u : ℕ → ℝ) : Prop :=
  ∀ a c : ℝ, 0 ≤ a → a ≤ c → c ≤ 1 →
    Tendsto (fun N : ℕ ↦ (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico a c).card : ℝ) / N)
      atTop (𝓝 (c - a))

namespace Real

variable {b k : ℕ} {x : ℝ}

/-- The block `w` occurs at position `i` of the base-`b` expansion of `x` iff
`⌊Int.fract (x * b ^ i) * b ^ k⌋₊` is the integer whose base-`b` digits are `w`. -/
theorem blockCount_eq_card_floor_fract (hb : 0 < b) (w : Fin k → Fin b) (N : ℕ) :
    blockCount b x w N = ((Finset.range N).filter fun i ↦
      ⌊Int.fract (x * (b : ℝ) ^ i) * (b : ℝ) ^ k⌋₊ = blockCode w).card := by
  sorry

/-- **Wall's theorem**: `x` is normal in base `b ≥ 2` iff `(x * b ^ n)` is equidistributed modulo
one. -/
theorem isNormalIn_iff_isEquidistributedModOne (hb : 2 ≤ b) :
    IsNormalIn b x ↔ IsEquidistributedModOne fun n ↦ x * (b : ℝ) ^ n := by
  sorry

/-- For almost every `x`, the sequence `(x * b ^ n)` is equidistributed modulo one. -/
theorem ae_isEquidistributedModOne_mul_pow (hb : 2 ≤ b) :
    ∀ᵐ x : ℝ, IsEquidistributedModOne fun n ↦ x * (b : ℝ) ^ n := by
  sorry

end Real
