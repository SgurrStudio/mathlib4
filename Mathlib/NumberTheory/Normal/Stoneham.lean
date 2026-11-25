/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.PiatetskiShapiro
public import Mathlib.NumberTheory.Normal.Wall

/-!
# Stoneham numbers are normal

For coprime integers `b, c ≥ 2` the *Stoneham number* is
`α_{b,c} = ∑_{k ≥ 1} 1 / (c ^ k * b ^ (c ^ k))`.
**Stoneham** (1973) proved that `α_{b,c}` is normal in base `b` when `c` is an odd prime and `b`
is a primitive root modulo `c ^ 2`. **Bailey and Crandall** (2002) extended this to all coprime
`b, c ≥ 2`, and **Bailey and Misiurewicz** (2006) gave a short proof via a "hot spot" form of
**Piatetski-Shapiro's normality criterion**: `x` is normal in base `b` as soon as every block
of `k` digits has upper frequency at most `C * b⁻ᵏ` for a constant `C` independent of the block.

## Main definitions

* `Real.stoneham b c`: the Stoneham number `α_{b,c}`.

## Main statements

* `Real.isNormalIn_stoneham`: Stoneham numbers are normal (Bailey–Crandall).

## References

* [R. G. Stoneham, *On absolute (j, ε)-normality in the rational fractions with applications to
  normal numbers*][Stoneham1973]
* [D. H. Bailey, R. E. Crandall, *Random generators and normal numbers*][BaileyCrandall2002]
* [D. H. Bailey, M. Misiurewicz, *A strong hot spot theorem*][BaileyMisiurewicz2006]
* [I. I. Piatetski-Shapiro, *On the laws of distribution of the fractional parts of an
  exponential function*][PiatetskiShapiro1951]
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

/-- The *Stoneham number* `α_{b,c} = ∑_{k ≥ 1} 1 / (c ^ k * b ^ (c ^ k))`. -/
noncomputable def stoneham (b c : ℕ) : ℝ :=
  ∑' k : ℕ, ((c : ℝ) ^ (k + 1) * (b : ℝ) ^ (c ^ (k + 1)))⁻¹

/-- **Bailey–Crandall**: for coprime `b, c ≥ 2` the Stoneham number `α_{b,c}` is normal in
base `b`. -/
theorem isNormalIn_stoneham {c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c) (hbc : b.Coprime c) :
    IsNormalIn b (stoneham b c) := by
  sorry

/-- `α_{2,3} = ∑ 1 / (3 ^ k * 2 ^ (3 ^ k))` is normal in base two. -/
theorem isNormalIn_two_stoneham_three : IsNormalIn 2 (stoneham 2 3) :=
  isNormalIn_stoneham le_rfl (by norm_num) (by norm_num)

end Real
